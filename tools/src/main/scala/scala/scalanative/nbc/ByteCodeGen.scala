package scala.scalanative
package nbc

import java.{lang => jl}
import java.nio.ByteBuffer
import java.nio.file.Paths

import scala.collection.mutable
import scala.scalanative.util.{ShowBuilder, unsupported}
import scala.scalanative.io.{VirtualDirectory, withScratchBuffer}
import scala.scalanative.optimizer.analysis.ControlFlow.{Block, Edge, Graph => CFG}
import scala.scalanative.nir._
import scala.scalanative.nbc.Opcode._
import scala.scalanative.nbc.RegAlloc.Allocator
import scala.scalanative.optimizer.analysis.ClassHierarchy.Class
import scala.scalanative.optimizer.analysis.ClassHierarchyExtractors.{ClassRef, FieldRef}
import scala.scalanative.optimizer.analysis.MemoryLayout

object ByteCodeGen {

  /** Generate code for given assembly. */
  def apply(config: tools.Config, assembly: Seq[Defn]): Unit = {
    val env = assembly.map(defn => defn.name -> defn).toMap

    withScratchBuffer { buffer =>
      val defns    = assembly
      val impl     = new Impl(config.target, env, defns, config.targetDirectory, buffer)
      //val codepath = "code.nbc"
      //val datapath = "data.nbc"
      val path     = "bin.nbc"
      impl.gen()
      buffer.flip
      config.targetDirectory.write(Paths.get(path), buffer)
    }
  }

  private final class Impl(target: String,
                           env: Map[Global, Defn],
                           defns: Seq[Defn],
                           targetDirectory: VirtualDirectory,
                           buffer: ByteBuffer) {
    //val builder         = new ShowBuilder

    val bytecode        = mutable.Buffer.empty[Instr]

    var nextOffset: Offset = 0
    var bytesPut        = 0
    val globalOffsets   = mutable.Map.empty[Global, Offset]
    val stringOffsets   = mutable.Map.empty[String, Offset]

    var currentFun: Global = _
    var nextReg         = 0
    val funBytecode     = mutable.Buffer.empty[Instr]
    val labelOffsets    = mutable.Map.empty[Local, Offset]

    var nextPrintOffset = 0

    val definitions = defns.sortBy {
      case Defn.Const(_,_,ty,_) => MemoryLayout.sizeOf(ty)
      case Defn.Var(_,_,ty,_)   => MemoryLayout.sizeOf(ty)
      case _: Defn.Define       => Integer.MAX_VALUE-1
      case _: Defn.Declare      => Integer.MAX_VALUE
      case _                    => -1
    }

    //import builder._

    def gen(): Unit = {
      // Step 1: produce bytecode
      genDefns(definitions)

      bytecode.foreach(genBinary)

      // Step 2: resolve global offsets and print result
      /*
      bytecode.foreach(printBytecode)
      buffer.put(builder.toString.getBytes)
      */
      // TODO include scalanative functions
    }

    def genDefns(defns: Seq[Defn]): Unit = {
      defns.foreach {
        case Defn.Const(_, name, ty, rhs) =>
          genGlobalDefn(name, ty, rhs)
        case Defn.Var(_, name, ty, rhs) =>
          genGlobalDefn(name, ty, rhs)
        case Defn.Define(_, name, sig, insts) =>
          genFunctionDefn(name, sig, insts)
        case Defn.Declare(_, name, sig) => // TODO builtins? (a lot)
          //println(name.show)
        case _ => ()
      }
    }

    def genGlobalDefn(name: nir.Global,
                      ty: nir.Type,
                      rhs: nir.Val): Unit = {
      globalOffsets.put(name, nextOffset)

      genGlobal(ty, rhs)
    }

    def genGlobal(ty: nir.Type, v: nir.Val): Unit = {
      ty match {
        case nir.Type.Struct(_,tys) => {
          val nir.Val.Struct(_, vals) = v
          vals.zip(tys).foreach { case (inv, inty) =>
            genGlobal(inty, inv)
          }
        }
        case nir.Type.Array(aty,n) => v match {
          case nir.Val.Array(_, vs) =>
            vs.foreach(genGlobal(aty, _))
          case nir.Val.Chars(s) =>
            s.foreach { char =>
              genGlobal(aty, Val.Short(char.toShort))
            }
            genGlobal(aty, Val.Short(0))
        }
        case _ => genBC(Data(MemoryLayout.sizeOf(ty) * 8), Seq(argFromVal(v)))
      }
    }

    def genFunctionDefn(name: Global,
                        sig: Type,
                        insts: Seq[Inst]): Unit = {
      globalOffsets.put(name, nextOffset)

      // Initialize register allocation
      nextReg = 0
      currentFun = name
      funBytecode.clear()
      labelOffsets.clear()
      //labelOffsets.put(name, mutable.Map.empty[Local, Offset])

      val cfg = CFG(insts)

      val allocator = RegAlloc.allocateRegisters(insts, cfg)

      genBC(Function(name), Seq(Arg.I(nextReg)))

      cfg.foreach { block =>
        genBlock(block)(cfg, allocator)
      }

      convertLabels()
    }

    /* Dummy register allocation
    def allocateRegisters(insts: Seq[Inst], cfg: CFG): Unit = {
      insts.foreach(allocateInst)
    }

    def allocateInst(inst: Inst): Unit = inst match {
      case Inst.Let(n, _) => allocate(n)
      case Inst.Label(_, ps) => ps.foreach {
        case Val.Local(n, _) => allocate(n)
      }
      case _ => ()
    }

    def allocate(n: Local): Unit = {
      allocator.put(n, Arg.R(nextReg))
      nextReg += 1
    }
    */

    def convertLabels(): Unit = {
      funBytecode.foreach {
        case (offset, opcode, args) =>
          val newArgs = args.map {
            case Arg.L(l) => Arg.M(labelOffsets.getOrElse(l, {
              unsupported(l)
            }))
            case a        => a
          }
          bytecode.append((offset, opcode, newArgs))
      }
    }

    def genBlock(block: Block)(implicit cfg: CFG, allocator: Allocator): Unit = {
      val Block(name, params, insts, isEntry) = block

      labelOffsets.put(name, nextOffset)

      // Prologue
      if (isEntry) {
        params.foreach { p =>
          genBytecode(Pop(convertSize(p.ty)), Seq(p))
        }
        //insts.foreach(genInst)
      } else if (block.isRegular) {
        //insts.foreach(genInst)
        // Epilogue
        /* TODO
        if (block.isRegular) {
          block.outEdges.foreach { case Edge(_, to, Next.Label(_, vals)) =>
            to.params.zipWithIndex.foreach { case (param, id) =>
              genBytecode(Mov(convertSize(param.valty)), Seq(param, vals(id))) // TODO check
            }
          }
        }
        */
      } else if (block.isExceptionHandler) {
        genUnsupported()
        //insts.foreach(genInst)
      }
      insts.foreach(genInst)
    }

    def genInst(inst: Inst)(implicit allocator: Allocator): Unit = inst match {
      case inst: Inst.Let =>
        genLet(inst)

      case Inst.Label(_, _) =>
        ()

      case Inst.Unreachable =>
        genBytecode(Halt, Seq())

      case Inst.Ret(value) =>
        if (isReturnable(value.ty)) {
          genBytecode(Push(convertSize(value.ty)), Seq(value))
        }
        genBytecode(Ret, Seq())

      case Inst.Jump(next) =>
        genBC(Jump, Seq(getNext(next)))

      case Inst.If(cond, thenp, elsep) =>
        genBytecode(UCmp(convertSize(cond.ty)), Seq(Val.True, cond))
        genBC(Ifne, Seq(getNext(elsep)))
        genBC(Jump, Seq(getNext(thenp)))

      case Inst.Switch(scrut, default, cases) =>
        cases.zipWithIndex.foreach { case (next, id) =>
          genBytecode(UCmp(convertSize(scrut.ty)), Seq(Val.Int(id), scrut)) // TODO types don't match
          genBC(Ifeq, Seq(getNext(next)))
        }
        genBC(Jump, Seq(getNext(default)))

      case Inst.None =>
        ()

      case Inst.Throw(_, _) =>
        genUnsupported()
    }

    def genLet(inst: Inst.Let)(implicit allocator: Allocator): Unit = {
      val op  = inst.op
      val lhs = Val.Local(inst.name, op.resty)

      op match {
        case call: Op.Call =>
          genCall(lhs, call)

        case Op.Load(ty, ptr) =>
          genBytecode(Load(convertSize(ty)), Seq(lhs, ptr))

        case Op.Store(ty, ptr, value) =>
          genBytecode(Store(convertSize(ty)), Seq(ptr, value))

        case Op.Bin(bin, ty, l, r) =>
          genBytecode(Mov(convertSize(ty)), Seq(lhs, l))
          genBytecode(convertBin(bin, ty), Seq(lhs, r))

        case Op.Comp(comp, ty, l, r) => {
          val (cmp, setif) = convertComp(comp, ty)
          genBytecode(cmp, Seq(l, r))
          genBytecode(Mov(convertSize(Type.Bool)), Seq(lhs, Val.False))
          genBytecode(setif, Seq(lhs))
        }

        case Op.Conv(conv, ty, value) =>
          genBytecode(convertConv(conv, value.ty, ty), Seq(lhs, value))

        case Op.Stackalloc(ty, n) =>
          val nb = n match {
            case Val.Int(i) => i
            case Val.None   => 1
          }
          genBytecode(Alloc, Seq(lhs, Val.Long(nb * MemoryLayout.sizeOf(ty))))

        case Op.Elem(ty, ptr, indexes) =>
          val size = MemoryLayout.sizeOf(ty)

          val firstComputable = indexes.head match {
            case _: Val.Byte   => true
            case _: Val.Short  => true
            case _: Val.Int    => true
            case _: Val.Long   => true
            case _: Val.Local  => false
            case _: Val.Global => false
          }

          val allComputable = indexes.tail.forall {
            case _: Val.Byte   => true
            case _: Val.Short  => true
            case _: Val.Int    => true
            case _: Val.Long   => true
            case _: Val.Local  => false
            case _: Val.Global => false
          }

          def value(v: Val): Long = v match {
            case Val.Byte(v)   => v
            case Val.Short(v)  => v
            case Val.Int(v)    => v
            case Val.Long(v)   => v
          }

          def fullSize(ty: Type): Int = ty match {
            case Type.Struct(_, tys) => tys.map(fullSize).sum
            case _ => 1
          }
          def sizeUntil(ty: Type, idx: Long): Int = ty match {
            case Type.Struct(_, tys) => tys.take(idx.toInt).map(fullSize).sum
          }
          def indexOf(ty: Type, idxs: Seq[Long]): Int = (ty, idxs) match {
            case (Type.Struct(_, tys), id +: ids) => sizeUntil(ty, id) + indexOf(tys(id.toInt), ids)
            case (_, Nil)                         => 0
          }

          if (!allComputable) {
            genUnsupported() // For now not supported
          } else if (firstComputable) { // Everything is known at compile time
            val outOffset = value(indexes.head) * size
            val inOffset = ty match {
              case Type.Struct(_, tys) => MemoryLayout(tys).tys(indexOf(ty, indexes.tail.map(value))).offset
              case _                   => 0
            }
            val offset = outOffset + inOffset
            genBytecode(Mov(64), Seq(lhs, ptr))
            genBytecode(Add(64), Seq(lhs, Val.Long(offset)))
          } else { // We don't know the first offset at compile time
            val inOffset = indexOf(ty, indexes.tail.map(value))
            genBytecode(Mov(64), Seq(lhs, Val.Long(size)))
            genBytecode(Mul(64), Seq(lhs, indexes.head))
            if (inOffset != 0) {
              genBytecode(Add(64), Seq(lhs, Val.Long(inOffset))) // TODO violates the no immediate binary policy
            }
          }

        case Op.Sizeof(ty) =>
          val size = MemoryLayout.sizeOf(ty)
          genBytecode(Mov(64), Seq(lhs, Val.Long(size)))

        case Op.As(ty, obj) =>
          genBytecode(Mov(convertSize(ty)), Seq(lhs, obj))

        case _ => {
          val (builtinId, retty, args): (Int, Type, Seq[Val]) = op match {
            case Op.Classalloc(name) => // needed
              (1, Type.Ptr, Seq(Val.Global(Global.Member(name, "type"), Type.Ptr)))

            case Op.Method(obj, name) => // needed
              (2, Type.Ptr, Seq(obj/*, Val.Global(name, Type.Ptr)*/)) // TODO method ID

            case Op.Is(ty, obj) => ty match {
              case Type.Class(name) =>
                (3, Type.Bool, Seq(obj, Val.Global(Global.Member(name, "type"), ty)))
              case Type.Trait(name) =>
                (4, Type.Bool, Seq(obj, Val.Global(Global.Member(name, "type"), ty)))
            }

            case Op.Field(obj, name) => // needed // TODO
              (5, Type.Ptr, Seq(obj/*, Val.Global(name, Type.Ptr)*/)) // TODO field ID

            /*
            // Not needed for hello world
            case Op.Select(cond, thenv, elsev) =>
            case Op.Copy(value) =>
            case Op.Throw(value, unwind) =>

            // Currently lowered
            case Op.Dynmethod(obj, signature) =>
            case Op.Module(?) =>
            case Op.Box(ty, obj) =>
            case Op.Unbox(ty, obj) =>

            // Not needed for any program
            Op.Extract, Op.Insert, Op.Closure (no occurence through CStruct)
            */

            case _ =>
              unsupported(op)
          }
          args.foreach { arg =>
            genBytecode(Push(convertSize(arg.ty)), Seq(arg))
          }
          genBC(Builtin(builtinId), Seq())
          if (isReturnable(retty)) {
            genBytecode(Pop(convertSize(retty)), Seq(lhs))
          }
        }
      }
    }

    def getNext(next: Next): Arg = Arg.L(next match {
      case Next.Label(n,_) => n
      case Next.Case(_,n)  => n
    })

    def genCall(dest: Val.Local, call: Op.Call)(implicit allocator: Allocator): Unit = call match {
      case Op.Call(ty, ptr, args, _) =>
        val Type.Function(argtys, retty) = ty

        // 1. Push arguments
        args.zip(argtys).reverse.foreach {
          case (arg, ty) if isReturnable(ty) =>
            // TODO check if arg.ty is ty (to be sure)
            genBytecode(Push(convertSize(ty)), Seq(arg))
          case _ => ()
        }

        // 2. call function
        genBytecode(Call, Seq(ptr))

        // 3. recover return value
        if (isReturnable(retty)) {
          genBytecode(Pop(convertSize(retty)), Seq(dest))
        }
    }

    def genBytecode(op: Opcode, args: Seq[Val])(implicit allocator: Allocator): Unit = {
      genBC(op, args.map(convertVal))
    }

    def genBC(op: Opcode, args: Seq[Arg]): Unit = {
      val immCount = args.map {
        case Arg.R(_) => 0
        case _        => 1
      }.sum

      val size = op match {
        case Data(s)         => s/8
        case Function(_)     => 0
        case Store(s)        => 2 + (args match {
          case Seq(arg1, arg2) =>
            val imm1 = arg1 match {
              case Arg.R(_) => 0
              case _        => 8
            }
            val imm2 = arg2 match {
              case Arg.R(_) => 0
              case _        => s/8
            }
            imm1 + imm2
        })
        case _ => 2 + immCount * op.immSize
      }

      // TODO padding for data
      //val padding = if (size > 0) (size - (nextOffset % size)) % size else 0
      val padding = 0
      val offset = nextOffset + padding
      nextOffset += padding + size

      funBytecode.append((offset, op, args))
    }

    def genBinary(in: Instr): Unit = {
      val (offset, op, args) = in
      while(bytesPut < offset) {
        buffer.put(0xde.toByte)
        bytesPut += 1
      }

      val bytes = op.toBin(args.map(convertGlobals)).toArray
      bytesPut += bytes.length
      buffer.put(bytes)
    }

    /*
    def printBytecode(in: Instr): Unit = {
      val (offset, op, args) = in

      // Print padding
      while (nextPrintOffset < offset) {
        printByte(nextPrintOffset, 0)
        nextPrintOffset += 1
      }

      // Print value
      op match {
        case Data(s) =>
          val Seq(arg) = args
          val str = convertGlobals(arg) match {
            case Arg.I(n) => f"$n%x"
            case Arg.F(n) => getDoubleHex(n)
            case Arg.M(a) => f"$a%x"
          }
          str.split("(?<=\\G..)").reverse.take(s.toInt).foreach { cc =>
            printByte(nextPrintOffset, Integer.parseInt(cc, 16).toByte)
            nextPrintOffset += 1
          }
        case Function(n) =>
          val Seq(arg) = args
          line("// Function " + n.show + " (" + arg.toStr + ")")
        case _ =>
          val opStr = op.toStr
          line(offset.toHexString + ": " + opStr + " "*(12 - opStr.length) + args.map(convertGlobals(_).toStr).mkString(", "))
          nextPrintOffset += 4
      }
    }

    def getDoubleHex(value: Double): String = {
      jl.Long.toHexString(jl.Double.doubleToRawLongBits(value))
    }

    def printByte(offset: Offset, byte: Byte): Unit = {
      //line(offset.toHexString + ": 0x" + "%02x".format(byte))
    }
    */

    def convertVal(iv: nir.Val)(implicit allocator: Allocator): Arg = iv match { // For bytecode arguments
      case Val.True          => Arg.I(1)
      case Val.False         => Arg.I(0)
      case Val.Zero(_)       => Arg.I(0)
      case Val.Undef(_)      => Arg.I(0)
      case Val.Byte(v)       => Arg.I(v)
      case Val.Short(v)      => Arg.I(v)
      case Val.Int(v)        => Arg.I(v)
      case Val.Long(v)       => Arg.I(v)
      case Val.Float(v)      => Arg.F(v)
      case Val.Double(v)     => Arg.F(v)
      case Val.Unit          => Arg.I(0) // TODO temporary
      case Val.Local(n, _)   =>
        allocator.getOrElse(n, Arg.R(-1) /*unsupported(n)*/ )
      case Val.Global(n, _)  => Arg.G(n)
      case _                 => unsupported(iv)
    }

    def convertGlobals(arg: Arg): Arg = arg match {
      case Arg.G(n)    => globalOffsets.get(n) match {
        case Some(o) => Arg.M(o)
        case None    =>
          println("g " + n.show)
          Arg.G(n)
        //unsupported(n)
      }
      case _           => arg
    }

    def genUnsupported()(implicit allocator: Allocator): Unit = {
      Seq(genBytecode(Halt, Seq()))
    }

    def isReturnable(v: nir.Val): Boolean = !(v == nir.Val.None || v == nir.Val.Unit)
    def isReturnable(t: nir.Type): Boolean = convertSize(t) > 0

    def argFromVal(v: nir.Val): Arg = v match { // For data section values
      case Val.True          => Arg.I(1)
      case Val.False         => Arg.I(0)
      case Val.Zero(_)       => Arg.I(0)
      case Val.Undef(_)      => Arg.I(0)
      case Val.Byte(v)       => Arg.I(v)
      case Val.Short(v)      => Arg.I(v)
      case Val.Int(v)        => Arg.I(v)
      case Val.Long(v)       => Arg.I(v)
      case Val.Float(v)      => Arg.F(v)
      case Val.Double(v)     => Arg.F(v)
      case Val.Global(n, _)  =>
        Arg.G(n)
      case _                 => unsupported(v)
    }
  }
}
