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
      val defns   = assembly
      val impl    = new Impl(config.target, env, defns, config.targetDirectory)
      val outpath = "out.nbc"
      withScratchBuffer { buffer =>
        impl.gen(buffer)
        buffer.flip
        config.targetDirectory.write(Paths.get(outpath), buffer)
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
    val labelOffsets    = mutable.Map.empty[Global, mutable.Map[Local, BC.Offset]]

    var currentFun: Global = _
    val allocator       = mutable.Map.empty[Local, Arg]
    var nextReg         = 0
    val funRegisters    = mutable.Map.empty[Global, Int]

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
      genBC(BC.Function(name), Seq())

      // Initialize register allocation
      allocator.clear()
      nextReg = 0
      currentFun = name
      labelOffsets.put(name, mutable.Map.empty[Local, BC.Offset])

      val cfg = CFG(insts)

      allocateRegisters(insts, cfg)

      cfg.foreach { block =>
        genBlock(block)(cfg)
      }
    }

    def allocateRegisters(insts: Seq[Inst], cfg: CFG): Unit = {
      insts.foreach(allocateInst)
      funRegisters.put(currentFun, nextReg)
    }

    def allocateInst(inst: Inst):Unit = inst match {
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

    def genBlock(block: Block)(implicit cfg: CFG): Unit = {
      val Block(_, params, insts, isEntry) = block

      // Prologue
      if (isEntry) {
        params.foreach { p =>
          genBytecode(BC.Pop(BC.convertSize(p.ty)), Seq(p))
        }
        insts.foreach(genInst)
      } else if (block.isRegular) {
        insts.foreach(genInst)
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
      }
    }

    def genInst(inst: Inst): Unit = inst match {
      case inst: Inst.Let =>
        genLet(inst)

      case Inst.Label(n, _) =>
        labelOffsets.update(currentFun, labelOffsets.getOrElse(currentFun, unsupported(currentFun)).updated(n, nextOffset))

      case Inst.Unreachable =>
        genBytecode(BC.Crash, Seq())

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

        // TODO types don't match
        case _ => {
          val (funname, retty, args): (String, Type, Seq[Val]) = op match {
            case Op.Elem(ty, ptr, indexes) =>
              ("scalanative_elem", ty, ptr +: indexes)

            case Op.Extract(aggr, indexes) => //x
              ???

            case Op.Insert(aggr, value, indexes) => //x
              ???

            case Op.Stackalloc(ty, n) => //x
              ("scalanative_stackalloc", Type.Ptr, Seq(Val.Int(BC.convertSize(ty)), n))

            case Op.Classalloc(name) =>
              ("scalanative_classalloc", Type.Ptr, Seq(Val.Global(name, Type.Class(name))))

            case Op.Field(obj, name) =>
              ("scalanative_field", Type.Ptr, Seq(obj, Val.Global(name, Type.Class(name))))

            case Op.Method(obj, name) =>
              ("scalanative_method", Type.Ptr, Seq(obj, Val.Global(name, Type.Class(name))))

            case Op.Dynmethod(obj, signature) =>
              ("scalanative_dynmethod", Type.Ptr, Seq(obj, Val.String(signature)))

            case Op.Module(name, unwind) =>
              ("scalanative_module", Type.Void, Seq(Val.Global(name, Type.Module(name))))

            case Op.As(ty, obj) =>
              ("scalanative_as", ty, Seq(Val.Int(BC.convertSize(ty)), obj))

            case Op.Is(ty, obj) =>
              ("scalanative_is", Type.Bool, Seq(Val.Int(BC.convertSize(ty)), obj))

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
              ("scalanative_unsupported", Type.Void, Seq())
              //unsupported(op)
          }

          val ty = Type.Function(args.map(_.ty), retty)
          genCall(lhs, Op.Call(ty, Val.Global(Global.Top(funname), ty), args, Next.None))
        }
      }
    }

    def getNext(next: Next): Arg = Arg.L(currentFun, next match {
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

      bytecode.append((offset, op, args))
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
          line("// Function " + n.show + " (" + funRegisters.getOrElse(n, unsupported(n)) + ")")
        case _ =>
          val opStr = op.toStr
          line(offset.toString + ": " + opStr + " "*(12 - opStr.length) + args.map(convertGlobals(_).toStr).mkString(", "))
          nextPrintOffset += 4
      }
    }

    def getDoubleHex(value: Double): String = {
      jl.Long.toHexString(jl.Double.doubleToRawLongBits(value))
    }

    def printByte(offset: BC.Offset, byte: Byte): Unit = {
      line(offset.toHexString + ": 0x" + "%02x".format(byte))
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
        case None    => Arg.G(n)
      }
      case Arg.S(s)    => Arg.M(stringOffsets.getOrElse(s, { println("s " + s); -1} /* unsupported(s) */))
      case Arg.L(f, n) => labelOffsets.getOrElse(f, unsupported(f)).get(n) match {
        case Some(l) => Arg.M(l)
        case None    => Arg.L(f,n)
      }
      case _           => arg
    }

    def genUnsupported(): Unit = {
      Seq(genBytecode(BC.Crash, Seq()))
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
