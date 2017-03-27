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
import scala.scalanative.nbc.{Bytecode => BC}
import scala.scalanative.optimizer.analysis.MemoryLayout

object ByteCodeGen {

  /** Generate code for given assembly. */
  def apply(config: tools.Config, assembly: Seq[Defn]): Unit = {
    val env = assembly.map(defn => defn.name -> defn).toMap

    withScratchBuffer { buffer =>
      val defns    = assembly
      val impl     = new Impl(config.target, env, defns, config.targetDirectory)
      val codepath = "code.nbc"
      val datapath = "data.nbc"
      withScratchBuffer { buffer =>
        impl.gen(buffer)
        buffer.flip
        config.targetDirectory.write(Paths.get(codepath), buffer)
      }
    }
  }

  private final class Impl(target: String,
                           env: Map[Global, Defn],
                           defns: Seq[Defn],
                           targetDirectory: VirtualDirectory) {
    val builder         = new ShowBuilder

    val bytecode        = mutable.Buffer.empty[BC.Instr]

    var nextOffset: BC.Offset = 0
    val globalOffsets   = mutable.Map.empty[Global, BC.Offset]
    val stringOffsets   = mutable.Map.empty[String, BC.Offset]

    var currentFun: Global = _
    val allocator       = mutable.Map.empty[Local, Arg]
    var nextReg         = 0
    val funBytecode     = mutable.Buffer.empty[BC.Instr]
    val labelOffsets    = mutable.Map.empty[Local, BC.Offset]

    var nextPrintOffset = 0

    val definitions = defns.sortBy {
      case Defn.Const(_,_,ty,_) => MemoryLayout.sizeOf(ty)
      case Defn.Var(_,_,ty,_)   => MemoryLayout.sizeOf(ty)
      case _: Defn.Define       => Integer.MAX_VALUE
      case _                    => -1
    }

    import builder._

    def gen(buffer: ByteBuffer) = {
      // Step 1: produce bytecode
      genDefns(definitions)

      // Step 2: resolve global offsets and print result
      bytecode.foreach(printBytecode)
      buffer.put(builder.toString.getBytes)
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
        case nir.Type.Array(aty,n) => {
          val nir.Val.Array(_, vs) = v
          vs.foreach(genGlobal(aty, _))
        }
        case _ => genBC(BC.Val(MemoryLayout.sizeOf(ty)), Seq(argFromVal(v)))
      }
    }

    def genFunctionDefn(name: Global,
                        sig: Type,
                        insts: Seq[Inst]): Unit = {
      globalOffsets.put(name, nextOffset)

      // Initialize register allocation
      allocator.clear()
      nextReg = 0
      currentFun = name
      funBytecode.clear()
      labelOffsets.clear()
      //labelOffsets.put(name, mutable.Map.empty[Local, BC.Offset])

      val cfg = CFG(insts)

      allocateRegisters(insts, cfg)

      genBC(BC.Function(name), Seq(Arg.I(nextReg)))

      cfg.foreach { block =>
        genBlock(block)(cfg)
      }

      convertLabels()
    }

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

    def convertLabels(): Unit = {
      funBytecode.foreach {
        case (offset, opcode, args) =>
          val newArgs = args.map {
            case Arg.L(l) => Arg.M(labelOffsets.getOrElse(l, {
              println(env(currentFun).show)
              println(labelOffsets)
              unsupported(l)
            }))
            case a        => a
          }
          bytecode.append((offset, opcode, newArgs))
      }
    }

    def genBlock(block: Block)(implicit cfg: CFG): Unit = {
      val Block(name, params, insts, isEntry) = block

      labelOffsets.put(name, nextOffset)

      // Prologue
      if (isEntry) {
        params.foreach { p =>
          genBytecode(BC.Pop(BC.convertSize(p.ty)), Seq(p))
        }
        //insts.foreach(genInst)
      } else if (block.isRegular) {
        //insts.foreach(genInst)
        // Epilogue
        /* TODO
        if (block.isRegular) {
          block.outEdges.foreach { case Edge(_, to, Next.Label(_, vals)) =>
            to.params.zipWithIndex.foreach { case (param, id) =>
              genBytecode(BC.Mov(BC.convertSize(param.valty)), Seq(param, vals(id))) // TODO check
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

    def genInst(inst: Inst): Unit = inst match {
      case inst: Inst.Let =>
        genLet(inst)

      case Inst.Label(_, _) =>
        ()

      case Inst.Unreachable =>
        genBytecode(BC.Halt, Seq())

      case Inst.Ret(value) =>
        if (isReturnable(value)) {
          genBytecode(BC.Push(BC.convertSize(value.ty)), Seq(value))
        }
        genBytecode(BC.Ret, Seq())

      case Inst.Jump(next) =>
        genBC(BC.Jump, Seq(getNext(next)))

      case Inst.If(cond, thenp, elsep) =>
        genBytecode(BC.UCmp(BC.convertSize(cond.ty)), Seq(Val.True, cond))
        genBC(BC.Ifne, Seq(getNext(elsep)))
        genBC(BC.Jump, Seq(getNext(thenp)))

      case Inst.Switch(scrut, default, cases) =>
        cases.zipWithIndex.foreach { case (next, id) =>
          genBytecode(BC.UCmp(BC.convertSize(scrut.ty)), Seq(Val.Int(id), scrut)) // TODO types don't match
          genBC(BC.Ifeq, Seq(getNext(next)))
        }
        genBC(BC.Jump, Seq(getNext(default)))

      case Inst.None =>
        ()

      case Inst.Throw(_, _) =>
        genUnsupported()
    }

    def genLet(inst: Inst.Let): Unit = {
      val op  = inst.op
      val lhs = Val.Local(inst.name, op.resty)

      op match {
        case call: Op.Call =>
          genCall(lhs, call)

        case Op.Load(ty, ptr) =>
          genBytecode(BC.Load(BC.convertSize(ty)), Seq(lhs, ptr))

        case Op.Store(ty, ptr, value) =>
          genBytecode(BC.Store(BC.convertSize(ty)), Seq(value, ptr))

        case Op.Bin(bin, ty, l, r) =>
          genBytecode(BC.Mov(BC.convertSize(ty)), Seq(lhs, l))
          genBytecode(BC.convertBin(bin, ty), Seq(lhs, r))

        case Op.Comp(comp, ty, l, r) => {
          val (cmp, setif) = BC.convertComp(comp, ty)
          genBytecode(cmp, Seq(l, r))
          genBytecode(BC.Mov(BC.convertSize(Type.Bool)), Seq(lhs, Val.False))
          genBytecode(setif, Seq(lhs))
        }

        case Op.Conv(conv, ty, value) =>
          genBytecode(BC.convertConv(conv, value.ty, ty), Seq(lhs, value))

        case Op.Elem(ty, ptr, indexes) =>
          val offset = Val.Int(0) // TODO pointer arithmetic
          genBytecode(BC.Add(64), Seq(ptr, offset))
          genBytecode(BC.Load(64 /* TODO compute */), Seq(lhs, ptr))
          genBytecode(BC.Sub(64), Seq(ptr, offset))

        // TODO types don't match
        case _ => {
          val (builtinId, retty, args): (Int, Type, Seq[Arg]) = op match {
            /*
            case Op.Extract(aggr, indexes) =>
              (-1, Type.Ptr, Seq()) // Unsupported

            case Op.Insert(aggr, value, indexes) =>
              (-1, Type.Ptr, Seq()) // Unsupported
            */

            case Op.Stackalloc(ty, n) =>
              val nb = n match {
                case Val.Int(i) => i
                case Val.None   => 1 // TODO 0?
              }
              (1, Type.Ptr, Seq(Arg.I(MemoryLayout.sizeOf(ty) * nb)))


            case Op.Classalloc(name) =>
              (2, Type.Ptr, Seq(Arg.G(name)))

            case Op.Field(obj, name) =>
              (3, Type.Ptr, Seq(convertVal(obj), Arg.G(name)))

            case Op.Method(obj, name) =>
              (4, Type.Ptr, Seq(convertVal(obj), Arg.G(name)))

            case Op.Dynmethod(obj, signature) =>
              (5, Type.Ptr, Seq(convertVal(obj), Arg.S(signature)))

            case Op.Module(name, unwind) =>
              (6, Type.Void, Arg.G(name) +: (unwind match {
                case Next.None => Seq()
                case _         => Seq(Arg.L(unwind.name))
              }))

            case Op.As(ty, obj) =>
              (7, ty, Seq(Arg.I(BC.convertSize(ty)), convertVal(obj)))

            case Op.Is(ty, obj) =>
              (8, Type.Bool, Seq(Arg.I(BC.convertSize(ty)), convertVal(obj)))

            /*
            // ???
            case Op.Select(cond, thenv, elsev) =>
            case Op.Copy(value) =>
            case Op.Sizeof(ty) =>
            case Op.Closure(ty, fun, captures) =>
            case Op.Box(ty, obj) =>
            case Op.Unbox(ty, obj) =>
            case Op.Throw(value, unwind) =>
            */

            case _ =>
              (-1, Type.Void, Seq())
              //unsupported(op)
          }
          genBC(BC.Builtin(builtinId), convertVal(lhs) +: args)
        }
      }
    }

    def getNext(next: Next): Arg = Arg.L(next match {
      case Next.Label(n,_) => n
      case Next.Case(_,n)  => n
    })

    def genCall(dest: Val.Local, call: Op.Call): Unit = call match {
      case Op.Call(ty, ptr, args, _) =>
        val Type.Function(argtys, retty) = ty

        // 1. Push arguments
        args.zip(argtys).reverse.foreach { case (arg, ty) =>
          genBytecode(BC.Push(BC.convertSize(ty)), Seq(arg))
        }

        // 2. call function
        genBytecode(BC.Call, Seq(ptr))

        // 3. recover return value
        if (isReturnable(retty)) {
          genBytecode(BC.Pop(BC.convertSize(retty)), Seq(dest))
        }
    }

    def genBytecode(op: BC, args: Seq[Val]): Unit = {
      genBC(op, args.map(convertVal))
    }

    def genBC(op: BC, args: Seq[Arg]): Unit = {
      val size = op match {
        case Bytecode.Val(s)      => s
        case Bytecode.Function(_) => 0
        case _                    => 4
      }

      val padding = if (size > 0) (size - (nextOffset % size)) % size else 0
      val offset = nextOffset + padding
      nextOffset += padding + size

      funBytecode.append((offset, op, args))
    }

    def printBytecode(in: BC.Instr): Unit = {
      val (offset, op, args) = in

      // Print padding
      while (nextPrintOffset < offset) {
        printByte(nextPrintOffset, 0)
        nextPrintOffset += 1
      }

      // Print value
      op match {
        case BC.Val(s) =>
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
        case BC.Function(n) =>
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

    def printByte(offset: BC.Offset, byte: Byte): Unit = {
      //line(offset.toHexString + ": 0x" + "%02x".format(byte))
    }

    def convertVal(iv: nir.Val): Arg = iv match { // For bytecode arguments
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
      case Val.Unit          => Arg.None // TODO
      case Val.None          => Arg.None // TODO
      case Val.String(s)     => Arg.S(s)
      case Val.Local(n, _)   =>
        allocator.getOrElse(n, unsupported(n))
      case Val.Global(n, _)  => Arg.G(n)
      case _                 => unsupported(iv)
    }

    def convertGlobals(arg: Arg): Arg = arg match {
      case Arg.G(n)    => globalOffsets.get(n) match {
        case Some(o) => Arg.M(o)
        case None    =>
          //println("g " + n.show)
          Arg.G(n)
        //unsupported(n)
      }
      case Arg.S(s)    => Arg.M(stringOffsets.getOrElse(s, { println("s " + s); -1} /* unsupported(s) */))
      case _           => arg
    }

    def genUnsupported(): Unit = {
      Seq(genBytecode(BC.Halt, Seq()))
    }

    def isReturnable(v: nir.Val): Boolean = !(v == nir.Val.None || v == nir.Val.Unit)
    def isReturnable(t: nir.Type): Boolean = BC.convertSize(t) > 0

    def argFromVal(v: nir.Val): Arg = v match { // For data section values
      case Val.True          => Arg.I(1)
      case Val.False         => Arg.I(0)
      case Val.Zero(ty)      => Arg.I(0)
      case Val.Undef(ty)     => Arg.I(0)
      case Val.Byte(v)       => Arg.I(v)
      case Val.Short(v)      => Arg.I(v)
      case Val.Int(v)        => Arg.I(v)
      case Val.Long(v)       => Arg.I(v)
      case Val.Float(v)      => Arg.F(v)
      case Val.Double(v)     => Arg.F(v)
      case Val.String(s)     =>
        stringOffsets.put(s, nextOffset)
        Arg.S(s)
      //case Val.Chars(v)      => "c\"" + v + "\\00\""
      // TODO Chars or String or both?
      case Val.Global(n, _)  =>
        Arg.G(n)
      case _                 => unsupported(v)
    }
  }
}
