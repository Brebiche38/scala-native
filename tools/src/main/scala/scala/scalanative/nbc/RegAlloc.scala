package scala.scalanative
package nbc

import scala.collection.mutable
import scala.scalanative.util.unsupported
import scala.scalanative.nir.{Inst, Local, Next, Val, Op}
import scala.scalanative.optimizer.analysis.ControlFlow.{Block, Edge, Graph => CFG}
import Math.{max, min}

object RegAlloc {
  type Allocator = Map[Local, Arg]

  val stats = mutable.Map.empty[Int, Int]

  def allocateRegisters(insts: Seq[Inst], cfg: CFG, printIntervals: Boolean = false): (Allocator, Int) = {
    // Interval computing
    val intervals = buildIntervals(cfg, insts.size)
    if (printIntervals) {
      intervals.foreach {
        case (Local("src", id), RegAlloc.Interval(ranges)) => println(id, ranges)
      }
    }

    // Linear scan algorithm
    var unhandled = intervals.toSeq.sortBy {
      case (_, i: Interval) => i.ranges.head._1
    }
    val active = mutable.Map.empty[Local, Interval]
    val inactive = mutable.Map.empty[Local, Interval]
    val handled = mutable.Map.empty[Local, Interval]

    val allocator = mutable.Map.empty[Local, Arg]
    var nextSpill = 8

    while (unhandled.nonEmpty) {
      val current: (Local, Interval) = unhandled.head
      unhandled = unhandled.tail
      val position = current._2.ranges.head._1

      active.foreach {
        case (l: Local, i: Interval) =>
          if (i.ranges.last._2 < position) {
            active.remove(l)
            handled.put(l, i)
          } else if (!i.covers(position)) {
            active.remove(l)
            inactive.put(l, i)
          }
      }

      inactive.foreach {
        case (l: Local, i: Interval) =>
          if (i.ranges.last._2 < position) {
            inactive.remove(l)
            handled.put(l, i)
          } else if (i.covers(position)) {
            inactive.remove(l)
            active.put(l, i)
          }
      }

      // Try to allocate
      val freeUntil = mutable.Map.empty[Int, Int]
      (0 to 7).foreach { i => freeUntil.put(i, Int.MaxValue) }

      active.foreach {
        case (l: Local, _: Interval) =>
          allocator.get(l) match {
            case Some(Arg.R(r)) if r < 8 =>
              freeUntil.put(r, 0)
            case _ => ()
          }
      }
      inactive.foreach {
        case (l: Local, i: Interval) =>
          allocator.get(l) match {
            case Some(Arg.R(r)) if r < 8 =>
              current._2.nextIntersection(i, position) match {
                case Some(p) => freeUntil.put(r, p)
                case None => ()
              }
            case _ => ()
          }
      }

      val (reg, maxVal) = freeUntil.maxBy(_._2)
      if (maxVal != 0 && current._2.ranges.last._2 < maxVal) {
        //println("putting", current._1.show, Arg.R(reg).toStr)
        allocator.put(current._1, Arg.R(reg))
      } else {
        // Allocation failed, allocate blocked regs
        val nextUse = mutable.Map.empty[Int, Int]
        (0 to 7).foreach { i => nextUse.put(i, Int.MaxValue) }

        active.foreach {
          case (l, i) => allocator.get(l) match {
            case Some(Arg.R(r)) if r < 8 =>
              nextUse.put(r, i.nextUse(current._2.start))
            case _ => ()
          }
        }
        inactive.foreach {
          case (l, i) => allocator.get(l) match {
            case Some(Arg.R(r)) if r < 8 =>
              current._2.nextIntersection(i, position) match {
                case Some(p) => nextUse.put(r, p)
                case None => ()
              }
            case _ => ()
          }
        }

        val (reg, maxVal) = nextUse.max
        if (current._2.start < maxVal) {
          //println("putting", current._1.show, Arg.R(nextSpill).toStr)
          allocator.put(current._1, Arg.R(nextSpill))
          nextSpill += 1
        } else {
          //println("updating", )
          allocator.filter {
            case (_, Arg.R(r)) => r == reg
          }.foreach { case (local, _) =>
            allocator.update(local, Arg.R(nextSpill))
            //nextSpill += 1
          }
          /*
          allocator.update(allocator.find {
            case (_, Arg.R(r)) => r == reg
          }.head._1, Arg.R(nextSpill))
          */
          //println("putting", current._1.show, Arg.R(reg).toStr)
          allocator.put(current._1, Arg.R(reg))
          nextSpill += 1
        }
      }

      allocator.get(current._1) match {
        case Some(Arg.R(r)) =>
          active.put(current._1, current._2)
        case _ => ()
      }

    }

    stats.get(nextSpill - 8) match {
      case Some(i) => stats.update(nextSpill - 8, i+1)
      case None    => stats.put(nextSpill - 8, 1)
    }
    (allocator.toMap, nextSpill - 8)
  }

  def buildIntervals(cfg: CFG, size: Int): Map[Local, Interval] = {
    var instId = size
    val loopHeaders = mutable.Map.empty[Block, Int]
    val visited = mutable.Set.empty[Block]
    val intervals = mutable.Map.empty[Local, Interval]
    val liveIn = mutable.Map.empty[Block, Set[Local]]

    cfg.all.reverse.foreach { block =>
      val blockStart = instId - block.insts.size
      val blockEnd = instId

      // All variables live in and parameters to the successor blocks are live now
      var live: Set[Local] = block.outEdges.flatMap {
        case Edge(_, to, next) =>
          if (!visited.contains(to) && !loopHeaders.contains(to))
            loopHeaders.put(to, blockEnd)

          val liveNext: Set[Local] = liveIn.getOrElse(to, Set())
          val nextParams: Set[Local] = next match {
            case Next.Label(_, args) =>
              args.flatMap {
                case Val.Local(n, _) => Set(n)
                case _ => Set[Local]()
              }.toSet
            case Next.Case(Val.Local(v, _), _) => Set(v)
            case _ => Set()
          }
          liveNext union nextParams
      }.toSet

      // All live variables are live during the block
      live.foreach { local =>
        val interval = intervals.getOrElse(local, new Interval(Seq()))
        intervals.update(local, interval.addRange(blockStart, blockEnd))
      }

      // Set intervals for operands
      block.insts.reverse.foreach { inst =>
        // Output
        inst match {
          case Inst.Let(n, _) =>
            val interval = intervals.getOrElse(n, new Interval(Seq((blockStart, blockEnd))))
            intervals.update(n, interval.setFrom(instId))
            live = live - n
          case Inst.Label(_, params) =>
            params.foreach { case Val.Local(param, _) => live = live - param }
          case _ => ()
        }
        // Input
        val operands: Seq[Val] = inst match {
          case Inst.Let(_, op) =>
            op match {
              case Op.Call(_, ptr, args, _) => // TODO unwind is Unwind or None
                ptr +: args
              case Op.Load(_, ptr, _) =>
                Seq(ptr)
              case Op.Store(_, ptr, value, _) =>
                Seq(ptr,value)
              case Op.Elem(_, ptr, indexes) =>
                ptr +: indexes
              case Op.Extract(aggr, _) =>
                Seq(aggr)
              case Op.Insert(aggr, value, _) =>
                Seq(aggr, value)
              case Op.Stackalloc(_, n) =>
                Seq(n)
              case Op.Bin(_, _, l, r) =>
                Seq(l, r)
              case Op.Comp(_, _, l, r) =>
                Seq(l, r)
              case Op.Conv(_, _, value) =>
                Seq(value)
              case Op.Select(cond, thenv, elsev) =>
                Seq(cond, thenv, elsev)
              case Op.Classalloc(_) =>
                Seq()
              case Op.Field(obj, _) =>
                Seq(obj)
              case Op.Method(obj, _) =>
                Seq(obj)
              case Op.Dynmethod(obj, _) =>
                Seq(obj)
              case Op.Module(_, _) => // TODO unwind is Unwind or None
                Seq()
              case Op.As(_, obj) =>
                Seq(obj)
              case Op.Is(_, obj) =>
                Seq(obj)
              case Op.Copy(value) =>
                Seq(value)
              case Op.Sizeof(_) =>
                Seq()
              case Op.Closure(_, fun, captures) =>
                fun +: captures
              case Op.Box(_, obj) =>
                Seq(obj)
              case Op.Unbox(_, obj) =>
                Seq(obj)
            }
          case Inst.If(v, _, _) => Seq(v)
          case Inst.Switch(v, _, _) => Seq(v)
          case Inst.Ret(v) => Seq(v)
          case Inst.Throw(v, _) => Seq(v)
          case _ => Seq()
        }
        operands.foreach {
          case Val.Local(opd, _) =>
            val interval = intervals.getOrElse(opd, new Interval(Seq()))
            intervals.update(opd, interval.addRange(blockStart, instId))
            live = live + opd
          case _ => ()
        }
        instId -= 1
      }

      // Remove block parameters from live set
      block.params.foreach { case Val.Local(param, _) =>
        live = live - param
      }

      // Handle backward edges
      loopHeaders.get(block) match {
        case Some(endId) => live.foreach { opd =>
          val interval = intervals.getOrElse(opd, new Interval(Seq()))
          intervals.update(opd, interval.addRange(blockStart, endId))
        }
        case None => ()
      }

      // Set live variables at beginning of block
      liveIn.put(block, live)

      visited += block
      instId -= 1
    }
    assert(instId == 0)
    intervals.toMap
  }

  case class Interval(val ranges: Seq[(Int, Int)]) {
    def start: Int = ranges.head._1
    def end: Int = ranges.last._2

    def addRange(start: Int, end: Int): Interval = {
      val (prologue, next) = ranges.span { case (_, e) => e < start - 1 }
      val (middle, epilogue) = next.span { case (s, _) => s <= end + 1 }

      val middleRange =
        if (middle.nonEmpty) (min(start, middle.head._1), max(end, middle.last._2)) else (start, end)

      val newRanges = prologue ++ Seq(middleRange) ++ epilogue
      new Interval(newRanges)
    }

    def setFrom(from: Int): Interval = {
      val (_, he) = ranges.head
      new Interval((from, he) +: ranges.tail)
    }

    def covers(p: Int): Boolean = {
      ranges.exists {
        case (s: Int, e: Int) =>
          s <= p && p <= e
      }
    }

    def nextUse(pos: Int): Int = {
      max(pos, ranges.dropWhile { case (_, e) => e < pos }.head._1)
    }

    def nextIntersection(that: Interval, pos: Int): Option[Int] = { // TODO suboptimal
      (pos to max(this.ranges.last._2, that.ranges.last._2)).foreach {
        i => if (this.covers(i) && that.covers(i)) return Some(i)
      }
      return None
    }

    def show(): String = {
      ranges.toString
    }
  }
}
