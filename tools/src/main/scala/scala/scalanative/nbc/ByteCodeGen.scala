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

    val globalOffsets   = mutable.Map.empty[Global, BC.Offset]
    val stringOffsets   = mutable.Map.empty[String, BC.Offset]
    var nextOffset: BC.Offset = 0
    val labelOffsets    = mutable.Map.empty[(Global, Local), BC.Offset]

    val allocator       = mutable.Map.empty[Local, Arg]
    var nextReg         = 0
    var currentFun: Global = _

    //var numDone: Int = 0

    import builder._

    def gen(buffer: ByteBuffer) = {
      val definitions = defns.sortBy {
        case _: Defn.Const  => 1
        case _: Defn.Var    => 2
        case _: Defn.Define => 3
        case _              => -1
      }
      // Step 1: resolve top and string addresses
      populateOffsets(definitions)

      // Step 2: produce output
      genDefns(definitions)
      buffer.put(builder.toString.getBytes)
      // TODO include scalanative functions
    }

    def populateOffsets(defns: Seq[Defn]): Unit = {
      defns.foreach {
        case Defn.Const(_, name, ty, rhs) =>
          populateGlobals(name, ty, rhs)
        case Defn.Var(_, name, ty, rhs) =>
          populateGlobals(name, ty, rhs)
        case Defn.Define(_, name, sig, insts) =>
          populateFunction(name, sig, insts)
        case _ => ()
      }
    }

    def populateGlobals(name: Global, ty: nir.Type, rhs: nir.Val): Unit = {
      globalOffsets.put(name, nextOffset)

      populateVal(rhs)
    }

    def populateFunction(name: Global, sig: Type, insts: Seq[Inst]): Unit = {
      globalOffsets.put(name, nextOffset)

      insts.foreach(populateInst(_)(name))
    }

    def populateInst(i: Inst)(implicit f: Global): Unit = i match {
      case nir.Inst.None             => ()
      case nir.Inst.Label(n, ps)     =>
        labelOffsets.put((f, n), nextOffset)
        nextOffset += ps.length
      case nir.Inst.Let(_, op)       => populateOp(op)
      case nir.Inst.Unreachable      => nextOffset += 1
      case nir.Inst.Ret(v)           => nextOffset += (if (isReturnable(v)) 2 else 1)
      case _: nir.Inst.Jump          => nextOffset += 1
      case _: nir.Inst.If            => nextOffset += 4
      case nir.Inst.Switch(_, _, cs) =>
        // TODO add cases to labels
        nextOffset += 1 + cs.length*2
      case _: nir.Inst.Throw         => nextOffset += 1
    }

    def populateOp(op: Op): Unit = op match {
      case Op.Call(Type.Function(_, resty), _, args, _) =>
        nextOffset += 1 + args.length + (if (isReturnable(resty)) 1 else 0)
      case _: Op.Bin  => nextOffset += 2
      case _: Op.Comp => nextOffset += 3
      case _          => nextOffset += 1
    }

    def isReturnable(v: nir.Val): Boolean = !(v == nir.Val.None || v == nir.Val.Unit)
    def isReturnable(t: nir.Type): Boolean = BC.convertSize(t) > 0

    def populateVal(v: nir.Val): Unit = v match {
      case nir.Val.None => nextOffset += 1
      case nir.Val.True => nextOffset += 1
      case nir.Val.False => nextOffset += 1
      case nir.Val.Zero(ty) => nextOffset += BC.sizeof(ty)
      case nir.Val.Undef(ty) => nextOffset += BC.sizeof(ty)
      case nir.Val.Byte(_) => nextOffset += 1
      case nir.Val.Short(_) => nextOffset += 2
      case nir.Val.Int(_) => nextOffset += 4
      case nir.Val.Long(_) => nextOffset += 8
      case nir.Val.Float(v) => nextOffset += 4
      case nir.Val.Double(v) => nextOffset += 8
      case nir.Val.Struct(n, vs) => vs.foreach(populateVal)
      case nir.Val.Array(ty, vs) => vs.foreach(populateVal)
      case nir.Val.Chars(v) => nextOffset += v.length
      case nir.Val.Global(n, ty) =>
        globalOffsets.put(n, nextOffset)
        nextOffset += 8
      case nir.Val.String(s) =>
        stringOffsets.put(s, nextOffset)
        nextOffset += s.length
    }

    def genDefns(defns: Seq[Defn]): Unit = {
      // 1. Generate constants
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
      newline()
      str("0x")
      str(Integer.toHexString(globalOffsets.getOrElse(name, throw new Exception("Offset should be in map"))))
      str("[")
      str(BC.sizeof(ty))
      str("]: ")

      genVal(rhs)
    }

    def genFunctionDefn(name: Global,
                        sig: Type,
                        insts: Seq[Inst]): Unit = {
      val offset = globalOffsets.getOrElse(name, throw new Exception("Function should have been populated"))

      /*
      line(name)
      line(sig)
      insts.foreach(line)
      */

      newline()
      str("0x")
      str(Integer.toHexString(offset))
      str(": ")

      // Initialize register allocation
      allocator.clear()
      nextReg = 0
      currentFun = name

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
        params.foreach { p =>
          allocator.put(p.name, Arg.R(nextReg))
          nextReg += 1

          genBytecode(BC.Pop(BC.convertSize(p.ty)), Seq(p))
        }
      } else if (block.isRegular) {
        params.zipWithIndex.foreach { case (param, id) =>
          allocator.put(param.name, Arg.R(nextReg))
          nextReg += 1

          block.inEdges.foreach { case Edge(_, _, Next.Label(_, vals)) =>
              genBytecode(BC.Mov(BC.convertSize(param.ty)), Seq(param, vals(id)))
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

      case Inst.Label(name, params) =>
        ()

      case Inst.Unreachable =>
        genBytecode(BC.Crash, Seq())

      case Inst.Ret(value) if BC.convertSize(value.ty) == 0 =>
        genBytecode(BC.Ret, Seq())

      case Inst.Ret(value) =>
        genBytecode(BC.Push(BC.convertSize(value.ty)), Seq(value))
        genBytecode(BC.Ret, Seq())

      case Inst.Jump(next) =>
        genBC(BC.Jump, Seq(Arg.M(getOffset(next))))

      case Inst.If(cond, thenp, elsep) =>
        genBytecode(BC.UCmp(BC.convertSize(cond.ty)), Seq(Val.True, cond))
        genBC(BC.Ifne, Seq(Arg.M(getOffset(elsep))))
        genBC(BC.Jump, Seq(Arg.M(getOffset(thenp))))

      case Inst.Switch(scrut, default, cases) =>
        cases.zipWithIndex.foreach { case (next, id) =>
          genBytecode(BC.UCmp(BC.convertSize(scrut.ty)), Seq(Val.Int(id), scrut)) // TODO types don't match
          genBC(BC.Ifeq, Seq(Arg.M(getOffset(next))))
        }
        genBC(BC.Jump, Seq(Arg.M(getOffset(default))))

      case Inst.None =>
        ()

      case Inst.Throw(_, _) =>
        genUnsupported()
    }

    def genLet(inst: Inst.Let): Unit = {
      val op  = inst.op
      val lhs = Val.Local(inst.name, op.resty)

      allocator.put(inst.name, Arg.R(nextReg))
      nextReg += 1

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
        args.zip(argtys).reverse.foreach { case (arg, ty) =>
          genBytecode(BC.Push(BC.convertSize(ty)), Seq(arg))
        }

        // 2. call function
        genBytecode(BC.Call, Seq(ptr))

        // 3. recover return value
        genBytecode(BC.Pop(BC.convertSize(retty)), Seq(dest))
    }

    def genBytecode(op: BC, args: Seq[Val]): Unit = {
      genBC(op, args.map(convertVal))
    }

    def genBC(op: BC, args: Seq[Arg]): Unit = {
      val opStr = op.toStr
      line(opStr + " "*(12 - opStr.length) + args.map(_.toStr).mkString(", "))
    }

    def getOffset(next: Next): BC.Offset = next match {
      case Next.Label(name, _) => labelOffsets.getOrElse((currentFun, name), -1)
      case Next.Case(_, name) => labelOffsets.getOrElse((currentFun, name), -1) // TODO not sure
    }

    def convertVal(iv: nir.Val): Arg = iv match {
      case Val.True          => Arg.I(1)
      case Val.False         => Arg.I(0)
      case Val.Zero(_)       => Arg.I(0)
      case Val.Undef(_)      => Arg.I(0)
      case Val.Byte(v)       => Arg.I(v)
      case Val.Short(v)      => Arg.I(v)
      case Val.Int(v)        => Arg.I(v)
      case Val.Long(v)       => Arg.I(v)
      case Val.Float(v)      => Arg.I(v)
      case Val.Double(v)     => Arg.I(v)
      case Val.Unit          => Arg.None // TODO
      case Val.None          => Arg.None // TODO
      case Val.String(s)     =>
        val addr: Int = stringOffsets.getOrElse(s, -1)
        Arg.I(addr)
      case Val.Local(n, ty)  => getLocal(n)
      case Val.Global(n, ty) => getGlobal(n)
      case _                 => unsupported(iv)
    }

    def genVal(v: Val): String = v match { // TODO goes off once the data section is fully implemented
      case Val.True          => "1"
      case Val.False         => "0"
      case Val.Zero(ty)      => "0 [" + ty + "]"
      case Val.Undef(ty)     => "0 [" + ty + "]"
      case Val.Byte(v)       => v.toString
      case Val.Short(v)      => v.toString
      case Val.Int(v)        => v.toString
      case Val.Long(v)       => v.toString
      case Val.Float(v)      => v.toString
      case Val.Double(v)     => v.toString
      case Val.String(s)     => "\"" + s + "\""
      case Val.Struct(_, vs) => "{ " + rep(vs, sep = ", ")(genVal) + " }"
      case Val.Array(_, vs)  => "[ " + rep(vs, sep = ", ")(genVal) + " ]"
      case Val.Chars(v)      => "c\"" + v + "\\00\""
      case Val.Global(n, ty) => "M[" + globalOffsets.getOrElse(n, -1).toString + "]"
      case _                 => unsupported(v)
    }

    def getGlobal(g: Global): Arg = {
      globalOffsets.get(g) match {
        case Some(offset) => Arg.M(offset)
        case None         => Arg.G(g)
      }
    }

    def getLocal(local: Local): Arg = {
      allocator.getOrElse(local, Arg.R(-1) /* unsupported(g) */)
    }

    def genUnsupported(): Unit = {
      Seq(genBytecode(BC.Crash, Seq()))
    }
  }
}
