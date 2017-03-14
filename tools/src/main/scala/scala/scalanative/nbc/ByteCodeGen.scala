package scala.scalanative
package nbc

import java.{lang => jl}
import java.nio.ByteBuffer
import java.nio.file.Paths

import scala.collection.mutable
import scala.scalanative.util.{ShowBuilder, unsupported}
import scala.scalanative.io.{VirtualDirectory, withScratchBuffer}
import scala.scalanative.nbc.Bytecode.Offset
import scala.scalanative.optimizer.analysis.ControlFlow.{Block, Edge, Graph => CFG}
import scala.scalanative.nir._
import scala.scalanative.nbc.{Bytecode => BC}

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
    val fresh           = new Fresh("gen")
    val builder         = new ShowBuilder
    val globalOffsets   = mutable.Map.empty[Global, BC.Offset]
    val functionOffsets = mutable.Map.empty[Global, BC.Offset]
    val functionLengths = mutable.Map.empty[Global, BC.Offset]
    val allocator       = mutable.Map.empty[Local, Reg]
    var lastReg         = 0
    var nextOffset: BC.Offset = 0

    import builder._

    def gen(buffer: ByteBuffer) = {
      defns.filter {
        case _: Defn.Define => true
        case _ => false
      }.foreach(funLen)

      genDefns(defns)
      buffer.put(builder.toString.getBytes)
      // TODO include scalanative functions
    }

    def funLen(fun: Defn): Unit = {
      val Defn.Define(_,name,_,insts) = fun

      val length = insts.map {
        case Inst.Let(_, op)        => opLen(op)
        case Inst.Switch(_,_,cases) => 2 * cases.length + 1
        case _: Inst.If             => 3
        case _: Inst.Jump           => 1
        case Inst.Ret(_)            => 2
        case Inst.Unreachable       => 1
        case _                      => 0
      }.sum

      functionLengths.put(name, length)
    }

    def opLen(op: Op): BC.Offset = op match {
      case _: Op.Comp => 3
      case _: Op.Bin  => 2
      case _          => 1
    }

    def genDefns(defns: Seq[Defn]): Unit =
      defns
        .sortBy {
          case _: Defn.Const   => 1
          case _: Defn.Var     => 2
          case _: Defn.Define  => 3
          case _               => -1
        }
        .foreach { defn =>
          newline()
          genDefn(defn)
        }

    def genDefn(defn: Defn): Unit = {
      defn match {
        case Defn.Var(attrs, name, ty, rhs) => // DATA
          genGlobalDefn(name, ty, rhs)
        case Defn.Const(attrs, name, ty, rhs) => // DATA
          genGlobalDefn(name, ty, rhs)
        case Defn.Define(attrs, name, sig, blocks) => // CODE
          genFunctionDefn(attrs, name, sig, blocks)
        case defn =>
          ()
      }
    }

    def genGlobalDefn(name: nir.Global,
                      ty: nir.Type,
                      rhs: nir.Val): Unit = {
      globalOffsets.put(name, nextOffset)
      val size = BC.sizeof(ty)

      newline()
      str("0x")
      str(Integer.toHexString(nextOffset))
      str("[")
      str(size)
      str("]: ")
      genVal(rhs)

      nextOffset += size
    }

    def genFunctionDefn(attrs: Attrs,
                        name: Global,
                        sig: Type,
                        insts: Seq[Inst]): Unit = {
      functionOffsets.put(name, nextOffset)

      newline()
      str("0x")
      str(Integer.toHexString(nextOffset))
      str(": ")

      nextOffset += functionLengths.getOrElse(name, unsupported(name))

      // Initialize register allocation
      allocator.clear()
      lastReg = 0

      newline()
      val cfg = CFG(insts)
      cfg.foreach { block =>
        genBlock(block)(cfg)
      }
    }

    def genBlock(block: Block)(implicit cfg: CFG): Unit = {
      val Block(name, params, insts, isEntry) = block

      genBlockPrologue(block) // TODO Register allocation
      rep(insts) { inst =>
        genInst(inst)
      }
    }

    def genBlockPrologue(block: Block)(implicit cfg: CFG): Unit = {
      val params = block.params

      // TODO Register allocation

      if (block.isEntry) {
        ()
      } else if (block.isRegular) { // TODO
        params.zipWithIndex.foreach {
          case (Val.Local(name, ty), n) =>
            newline()
            str("%")
            genLocal(name)
            str(" = phi ")
            str(ty)
            str(" ")
            rep(block.inEdges, sep = ", ") { edge =>
              str("[")
              edge match {
                case Edge(from, _, Next.Label(_, vals)) =>
                  genVal(vals(n))
                  str(", %")
                  genLocal(from.name)
                  str(".")
                  str(from.splitCount)
              }
              str("]")
            }
        }
      } else if (block.isExceptionHandler) {
        ()
        //unsupported(block)
      }
    }

    def genInst(inst: Inst): Unit = inst match {
      case inst: Inst.Let =>
        genLet(inst)

      case Inst.Unreachable =>
        genBytecode(BC.Crash, Seq())

      case Inst.Ret(Val.None) =>
        genBytecode(BC.Ret, Seq())

      case Inst.Ret(value) =>
        genBytecode(BC.Push(BC.convertSize(value.ty)), Seq(value))
        genBytecode(BC.Ret, Seq(value))

      case Inst.Jump(next) =>
        genBytecode(BC.Jump, Seq(getOffset(next)))

      case Inst.If(cond, thenp, elsep) =>
        genBytecode(BC.UCmp(BC.convertSize(cond.ty)), Seq(Val.True, cond))
        genBytecode(BC.Ifne, Seq(getOffset(elsep)))
        genBytecode(BC.Jump, Seq(getOffset(thenp)))

      case Inst.Switch(scrut, default, cases) =>
        cases.zipWithIndex.foreach { case (next, id) =>
          genBytecode(BC.UCmp(BC.convertSize(scrut.ty)), Seq(Val.Int(id), scrut)) // TODO types don't match
          genBytecode(BC.Ifeq, Seq(getOffset(next)))
        }
        genBytecode(BC.Jump, Seq(getOffset(default)))

      case Inst.None =>
        ()

      case _ =>
        genUnsupported()
    }

    def genLet(inst: Inst.Let): Unit = {
      def isVoid(ty: Type): Boolean =
        ty == Type.Void || ty == Type.Unit || ty == Type.Nothing

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

            case Op.Extract(aggr, indexes) =>
              ("scalanative_elem", Type.Void, aggr +: indexes.map(Val.Int(_)))

            case Op.Insert(aggr, value, indexes) =>
              ("scalanative_insert", Type.Void, aggr +: value +: indexes.map(Val.Int(_)))

            case Op.Stackalloc(ty, n) => // TODO probably not
              ("scalanative_stackalloc", Type.Ptr, Seq(Val.Int(BC.convertSize(ty)), n))

            case Op.Classalloc(name) => // TODO types probably not good
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

    def genCall(dest: Val.Local, call: Op.Call): Unit = call match {
      case Op.Call(ty, ptr, args, _) =>
        val Type.Function(argtys, retty) = ty

        // 1. Push arguments
        args.zip(argtys).foreach { case (arg, ty) =>
          genBytecode(BC.Push(BC.convertSize(ty)), Seq(arg))
        }

        // 2. call function
        genBytecode(BC.Call, Seq(ptr))

        // 3. recover return value
        genBytecode(BC.Pop(BC.convertSize(retty)), Seq(dest))
    }

    def genBytecode(op: BC, args: Seq[Val]): Unit = { // TODO args are vals
      newline()
      str(op)
      str(" ")
      rep(args, sep=", ")(genVal)
    }

    def getOffset(next: Next): Val = {
      Val.Int(0) // TODO how?
    }

    def genVal(v: Val): Unit = v match {
      case Val.True      => str("1")
      case Val.False     => str("0")
      case Val.Zero(_)  => str("0")
      case Val.Undef(_) => str("0")
      case Val.Byte(v)   => str(v)
      case Val.Short(v)  => str(v)
      case Val.Int(v)    => str(v)
      case Val.Long(v)   => str(v)
      case Val.Float(v)  => genFloatHex(v)
      case Val.Double(v) => genDoubleHex(v)
      case Val.String(s) =>
        str("\"")
        str(s)
        str("\"")
      case Val.Unit      => str("") // TODO
      case Val.None      => str("") // TODO
      case Val.Struct(_, vs) =>
        str("{ ")
        rep(vs, sep = ", ")(genVal)
        str(" }")
      case Val.Array(_, vs) =>
        str("[ ")
        rep(vs, sep = ", ")(genVal)
        str(" ]")
      case Val.Chars(v) =>
        str("c\"")
        str(v)
        str("\\00\"")
      case Val.Local(n, ty) =>
        genLocal(n)
      case Val.Global(n, ty) =>
        genGlobal(n)
      case _ =>
        unsupported(v)
    }

    def genFloatHex(value: Float): Unit = {
      str("0x")
      str(jl.Long.toHexString(jl.Double.doubleToRawLongBits(value.toDouble)))
    }

    def genDoubleHex(value: Double): Unit = {
      str("0x")
      str(jl.Long.toHexString(jl.Double.doubleToRawLongBits(value)))
    }

    def genGlobal(g: Global): Unit = {
      val offset: Offset = globalOffsets.getOrElse(g, -1 /* unsupported(g) */)
      str("M[0x")
      str(Integer.toHexString(offset))
      str("]")
    }

    def genLocal(local: Local): Unit = {
      val reg = allocator.getOrElse(local, Reg.R(-1))
      str(reg)
    }

    def genUnsupported(): Unit = {
      genBytecode(BC.Crash, Seq())
    }
  }
}
