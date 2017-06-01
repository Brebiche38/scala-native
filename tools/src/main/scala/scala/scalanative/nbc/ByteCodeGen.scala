package scala.scalanative
package nbc

import java.{lang => jl}
import java.nio.ByteBuffer
import java.nio.file.Paths

import scala.collection.mutable
import scala.scalanative.util.{Scope, ShowBuilder, unsupported}
import scala.scalanative.io.{VirtualDirectory, withScratchBuffer}
import scala.scalanative.optimizer.analysis.ControlFlow.{Block, Edge, Graph => CFG}
import scala.scalanative.nir._
import scala.scalanative.nbc.Opcode._
import scala.scalanative.nbc.RegAlloc.Allocator
import scala.scalanative.optimizer.analysis.ClassHierarchy.{Class, Trait, Top}
import scala.scalanative.optimizer.analysis.ClassHierarchyExtractors.{ClassRef, FieldRef, MethodRef, TraitRef}
import scala.scalanative.optimizer.analysis.MemoryLayout

object ByteCodeGen {

  /** Generate code for given assembly. */
  def apply(config: tools.Config, assembly: Seq[Defn], top: Top): Unit = Scope { implicit in =>
    val env = assembly.map(defn => defn.name -> defn).toMap
    val workdir = VirtualDirectory.real(config.workdir)

    withScratchBuffer { buffer1 =>
      withScratchBuffer { buffer2 =>
        val defns    = assembly
        val impl     = new Impl(config.target, env, defns, buffer1, buffer2)
        val path1    = "bin.nbc"
        val path2    = "txt.nbc"
        impl.gen(top)
        buffer1.flip
        workdir.write(Paths.get(path1), buffer1)
        buffer2.flip
        workdir.write(Paths.get(path2), buffer2)
      }
    }
  }

  private final class Impl(target: String,
                           env: Map[Global, Defn],
                           defns: Seq[Defn],
                           binbuf: ByteBuffer,
                           txtbuf: ByteBuffer) {
    val builder         = new ShowBuilder

    val bytecode        = mutable.Buffer.empty[Instr]
    var funStarts: Offset = 0

    var nextOffset: Offset = 0
    var bytesPut        = 0
    val globalOffsets   = mutable.Map.empty[Global, Offset]

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

    import builder._

    def gen(implicit top: Top): Unit = {
      // Step 1: produce bytecode
      genDefns(definitions)

      bytecode.foreach(genBinary)

      println("run 0x" + nextOffset.toHexString + " " + convertGlobals(Arg.G(Global.Top("main"))).toStr)

      // Step 2: resolve global offsets and print result
      bytecode.foreach(printBytecode)
      txtbuf.put(builder.toString.getBytes)
    }

    def genDefns(defns: Seq[Defn])(implicit top: Top): Unit = {
      defns.foreach {
        case Defn.Const(_, name, ty, rhs) =>
          genGlobalDefn(name, ty, rhs)
        case Defn.Var(_, name, ty, rhs) =>
          genGlobalDefn(name, ty, rhs)
        case Defn.Define(_, name, sig, insts) =>
          genFunctionDefn(name, sig, insts)
        //case Defn.Declare(attrs, name, sig) if attrs.isExtern => // TODO builtins? (a lot)
          //println("decl " + name.show)
        case _ => ()
      }
    }

    def genGlobalDefn(name: nir.Global,
                      ty: nir.Type,
                      rhs: nir.Val): Unit = {
      def getArgs(v: nir.Val): Seq[Arg] = v match {
        case nir.Val.Struct(_, vs) => vs flatMap getArgs
        case nir.Val.Array(_, vs)  => vs flatMap getArgs
        case nir.Val.Chars(s)      => s.map(Arg.I(_)) :+ Arg.I(0)
        case _                     => Seq(argFromVal(v))
      }
      val args = getArgs(rhs)

      val layout = MemoryLayout(Seq(ty))

      /*
      def getTpes(tpe: MemoryLayout.PositionedType): Seq[MemoryLayout.Tpe] = tpe match {
        case MemoryLayout.Tpe(size, offset, nir.Type.Array(arty, n)) =>
          val elemsize = size/n
          (for (i <- 0 until n) yield getTpes(MemoryLayout.Tpe(elemsize, offset + i * elemsize, arty))).flatten
        case t :MemoryLayout.Tpe => Seq(t)
        case _                   => Seq()
      }
      */

      val tpes = layout.tys.filter {
        case _: MemoryLayout.Tpe => true
        case _                   => false
      }

      /*
      if (args.length != tpes.length) {
        println(args)
        println(tpes)
      }
      println(args.length, tpes.length)
      */

      val maxSize = tpes.map(t => t.size).max
      if (nextOffset % maxSize != 0) {
        nextOffset += maxSize - (nextOffset % maxSize)
      }
      val mainOffset = nextOffset
      nextOffset += layout.size

      if (name == Global.Top("__dispatch")) {
        val nir.Val.Array(_, vals) = rhs
        println(mainOffset.toHexString, vals.length)
      }

      tpes.zip(args).foreach { case (MemoryLayout.Tpe(size, offset, _), arg) =>
        bytecode.append((mainOffset + offset, Data(size), Seq(arg)))
      }

      globalOffsets.put(name, mainOffset)
    }

    def genFunctionDefn(name: Global,
                        sig: Type,
                        insts: Seq[Inst])
                       (implicit top: Top): Unit = {
      globalOffsets.put(name, nextOffset)

      /*
      if (name == Global.Member(Global.Top("scala.runtime.ScalaRunTime$"), "array$underscore$length_java.lang.Object_i32")) {
        insts.foreach(i => println(i.show))
      }
      */

      // Initialize register allocation
      nextReg = 0
      currentFun = name
      funBytecode.clear()
      labelOffsets.clear()
      //labelOffsets.put(name, mutable.Map.empty[Local, Offset])

      val cfg = CFG(insts)

      val (allocator, spilledRegs) = RegAlloc.allocateRegisters(insts, cfg)

      /*
      if (spilledRegs > 40)
        println(name.show, spilledRegs)
      */

      genBC(Function(name), Seq(Arg.I(spilledRegs)))

      cfg.foreach { block =>
        genBlock(block)(cfg, allocator, top)
      }

      convertLabels()
    }

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

    def genBlock(block: Block)(implicit cfg: CFG, allocator: Allocator, top: Top): Unit = {
      val Block(name, params, insts, isEntry) = block

      labelOffsets.put(name, nextOffset)

      // Prologue
      if (isEntry) {
        params.foreach { p =>
          genBytecode(Pop(convertSize(p.ty)), Seq(p))
        }
      } else if (block.isExceptionHandler) {
        genUnsupported("exception handler")
      }


      if (block.isRegular) {
        insts.init.foreach(genInst)

        block.outEdges.foreach {
          case Edge(_, _ @ Block(_, params, _, _), Next.Label(_, args)) =>
            args.zip(params).foreach {
              case (arg, param) if convertSize(arg.ty) != 0 =>
                genBytecode(Mov(convertSize(arg.ty)), Seq(param, arg))
              case _ => ()
            }
          case _ => ()
        }

        genInst(insts.last)
      }
    }

    def genInst(inst: Inst)(implicit allocator: Allocator, top: Top): Unit = inst match {
      case inst: Inst.Let =>
        genLet(inst)

      case Inst.Label(_, _) =>
        ()

      case Inst.Unreachable =>
        genUnsupported("unreachable")

      case Inst.Ret(value) =>
        if (isReturnable(value.ty)) {
          genBytecode(Push(convertSize(value.ty)), Seq(value))
        }
        genBytecode(Ret, Seq())

      case Inst.Jump(next) =>
        genBC(Jump, Seq(getNext(next)))

      case Inst.If(cond, thenp, elsep) =>
        genBC(JumpIf, Seq(convertVal(cond), getNext(thenp)))
        genBC(Jump, Seq(getNext(elsep)))

      case Inst.Switch(scrut, default, cases) =>
        genUnsupported("switch") // TODO
        /*
        cases.zipWithIndex.foreach { case (next, id) =>
          genBC(JumpIf, Seq(Arg.I(id), convertVal(scrut), getNext(next)))
        }
        genBC(Jump, Seq(getNext(default)))
        */


      case Inst.None =>
        ()

      case Inst.Throw(_, _) =>
        genUnsupported("throw")
    }

    def genLet(inst: Inst.Let)(implicit allocator: Allocator, top: Top): Unit = {
      val op  = inst.op
      val lhs = Val.Local(inst.name, op.resty)

      op match {
        case call: Op.Call =>
          genCall(lhs, call)

        case Op.Load(ty, ptr, _) =>
          genBytecode(Load(convertSize(ty)), Seq(lhs, ptr))

        case Op.Store(ty, ptr, value, _) =>
          genBytecode(Store(convertSize(ty)), Seq(ptr, value))

        case Op.Bin(bin, ty, l, r) =>
          genBytecode(Mov(convertSize(ty)), Seq(lhs, l))
          genBytecode(convertBin(bin, ty), Seq(lhs, r))

        case Op.Comp(comp, ty, l, r) => {
          val (cmp, setif) = convertComp(comp, ty)
          genBytecode(Mov(convertSize(Type.Bool)), Seq(lhs, Val.False))
          genBytecode(cmp, Seq(l, r))
          genBytecode(setif, Seq(lhs))
        }

        case Op.Conv(conv, ty, value) =>
          genBytecode(convertConv(conv, value.ty, ty), Seq(lhs, value))

        case Op.Stackalloc(ty, n) =>
          val nb = n match {
            case Val.Long(i) => i
            case Val.None   => 1
          }
          val size = {
            val pureSize = MemoryLayout.sizeOf(ty)
            val alignment = MemoryLayout.findMax(Seq(ty))
            if (pureSize % alignment == 0) pureSize
            else pureSize + (alignment - pureSize % alignment)
          }
          val bytesSize = nb * size
          val wordsSize = bytesSize / 8 + (if (bytesSize % 8 == 0) 0 else 1)
          genBytecode(Alloc, Seq(lhs, Val.Long(wordsSize)))

        case Op.Elem(ty, ptr, indexes) =>
          val layout = MemoryLayout(Seq(ty))
          val size = MemoryLayout.sizeOf(ty)

          def value(v: Val): Long = v match {
            case Val.Byte(v)   => v
            case Val.Short(v)  => v
            case Val.Int(v)    => v
            case Val.Long(v)   => v
            case _             => 0
          }
          val offsets = layout.tys.collect {
            case MemoryLayout.Tpe(_, offset, _) => offset
          }
          val tpeIndex = MemoryLayout.elemIndex(ty, indexes.tail.map(value))
          val inOffset = offsets(tpeIndex.toInt)

          def computable(idx: Val) = idx match {
            case _: Val.Byte   => true
            case _: Val.Short  => true
            case _: Val.Int    => true
            case _: Val.Long   => true
            case _: Val.Local  => false
            case _: Val.Global => false
          }

          if (!indexes.tail.forall(computable)) {
            genUnsupported("elem of variable indexes") // TODO
          } else if (computable(indexes.head)) { // Everything is known at compile time
            val outOffset = value(indexes.head) * size
            val offset = outOffset + inOffset

            genBytecode(Push(64), Seq(Val.Long(0)))
            genBytecode(Push(64), Seq(Val.Long(offset)))
            genBytecode(Push(64), Seq(ptr))

            genBytecode(Mov(64), Seq(lhs, ptr))
            genBytecode(Add(64), Seq(lhs, Val.Long(offset)))

            genBytecode(Push(64), Seq(lhs))
            genBytecode(Builtin(18), Seq())
          } else { // We don't know the first offset at compile time
            genBytecode(Push(64), Seq(Val.Long(size)))
            genBytecode(Push(64), Seq(indexes.head))
            genBytecode(Push(64), Seq(ptr))

            genBytecode(Mov(64), Seq(lhs, Val.Long(size)))
            genBytecode(Mul(64), Seq(lhs, indexes.head))
            genBytecode(Add(64), Seq(lhs, ptr))
            if (inOffset != 0) {
              genBytecode(Add(64), Seq(lhs, Val.Long(inOffset)))
            }

            genBytecode(Push(64), Seq(lhs))
            genBytecode(Builtin(18), Seq())
          }

        case Op.Sizeof(ty) =>
          val size = MemoryLayout.sizeOf(ty)
          genBytecode(Mov(64), Seq(lhs, Val.Long(size)))

        case Op.As(ty, obj) =>
          genBytecode(Mov(convertSize(ty)), Seq(lhs, obj))

        case Op.Copy(value) =>
          genBytecode(Mov(convertSize(value.ty)), Seq(lhs, value))

        case _ => {
          val (builtinId, retty, args): (Int, Type, Seq[Val]) = op match {
            case Op.Classalloc(ClassRef(cls)) =>
              (1, Type.Ptr, Seq(Val.Global(cls.rtti.name, Type.Ptr), Val.Long(MemoryLayout.sizeOf(cls.layout.struct))))

            case Op.Field(obj, FieldRef(cls, fld)) =>
              (2, Type.Ptr, Seq(obj, Val.Global(cls.rtti.name, Type.Ptr), Val.Int(cls.fields.indexOf(fld) + 1)))

            case Op.Method(obj, MethodRef(cls: Class, meth)) if meth.isVirtual =>
              (3, Type.Ptr, Seq(obj, Val.Int(cls.vtable.index(meth))))
            case Op.Method(obj, MethodRef(cls: Class, meth)) if meth.isStatic =>
              (4, Type.Ptr, Seq(Val.Global(meth.name, Type.Ptr)))
            case Op.Method(obj, MethodRef(trt: Trait, meth)) =>
              //if (meth.id == 290) println(obj.show, trt.name.show, meth.name.show)
              (5, Type.Ptr, Seq(obj, top.tables.dispatchVal, Val.Int(meth.id), Val.Int(top.tables.dispatchOffset(meth.id))))

            case Op.Is(ClassRef(cls), obj) =>
                (6, Type.Bool, Seq(obj, Val.Global(cls.rtti.name, Type.Ptr)))
            case Op.Is(TraitRef(trt), obj) =>
                genUnsupported("is trait")
                (7, Type.Bool, Seq(obj, top.tables.classHasTraitVal, Val.Int(trt.id)))

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
          args.reverse.foreach { arg =>
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
        ptr match {
          case Val.Global(Global.Top("scalanative_init"), _) => genBytecode(Builtin(0), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.GC$"), "extern.scalanative_alloc"), _) =>
            genBytecode(Builtin(8), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.GC$"), "extern.scalanative_alloc_atomic"), _) =>
            genBytecode(Builtin(9), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.Intrinsics$"), "extern.llvm.memset.p0i8.i64"), _) =>
            genBytecode(Builtin(10), Seq())
            /*
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.unwind$"), "extern.scalanative_unwind_get_context"), _) =>
            genBytecode(Builtin(11), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.unwind$"), "extern.scalanative_unwind_init_local"), _) =>
            genBytecode(Builtin(12), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.unwind$"), "extern.scalanative_unwind_step"), _) =>
            genBytecode(Builtin(13), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.unwind$"), "extern.scalanative_unwind_get_proc_name"), _) =>
            genBytecode(Builtin(14), Seq())
            */
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.Intrinsics$"), "extern.llvm.ctpop.i32"), _) =>
            genBytecode(Builtin(15), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.Intrinsics$"), "extern.llvm.bswap.i32"), _) =>
            genBytecode(Builtin(16), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.Intrinsics$"), "extern.llvm.ctlz.i32"), _) =>
            genBytecode(Builtin(17), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.Platform$"), "extern.scalanative_platform_is_windows"), _) =>
            genBytecode(Builtin(19), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.posix.unistd$"), "extern.scalanative_environ"), _) =>
            genBytecode(Builtin(20), Seq())
          case _ => genBytecode(Call, Seq(ptr))
        }

        // 3. recover return value
        if (isReturnable(retty)) {
          genBytecode(Pop(convertSize(retty)), Seq(dest))
        }
    }

    def genBytecode(op: Opcode, args: Seq[Val])(implicit allocator: Allocator): Unit = {
      genBC(op, args.map(convertVal))
    }

    def genBC(op: Opcode, args: Seq[Arg]): Unit = {
      val size = op match {
        case Function(_)     => 2
        case _ =>
          val immSize = args.zipWithIndex.map { case (arg, idx) =>
            arg match {
              case Arg.R(r) if r < 8 => 0
              case Arg.R(_) => 2
              case Arg.L(_) => 8
              case Arg.G(_) => 8
              case Arg.I(_) => op.immSize(idx)
              case Arg.F(_) => op.immSize(idx)
            }
          }.sum
          2 + immSize
      }

      funBytecode.append((nextOffset, op, args))

      nextOffset += size
    }

    def genBinary(in: Instr): Unit = {
      val (offset, op, args) = in

      //println(offset, op, args)

      assert (bytesPut <= offset)

      while(bytesPut < offset) {
        binbuf.put(0xde.toByte)
        bytesPut += 1
      }

      val bytes = op.toBin(args.map(convertGlobals)).toArray
      bytesPut += bytes.length
      binbuf.put(bytes)
    }

    def printBytecode(in: Instr): Unit = {
      val (offset, op, args) = in

      // Print value
      val str = op match {
        case Data(s) =>
          val Seq(arg) = args
          "(" + s + ")" + (convertGlobals(arg) match {
            case Arg.I(n) => n.toString
            case Arg.F(n) => n.toString
            case Arg.M(a) => f"0x$a%x"
          })
        case Function(n) =>
          val Seq(arg) = args
          "// Function " + n.show + " (" + arg.toStr + ")"
        case _ =>
          val opStr = op.toStr
          opStr + " "*(12 - opStr.length) + args.map(convertGlobals(_).toStr).mkString(", ")
      }

      line(offset.toHexString + ": " + str)
    }

    def convertVal(iv: nir.Val)(implicit allocator: Allocator): Arg = iv match { // For bytecode arguments
      case Val.True          => Arg.I(1)
      case Val.False         => Arg.I(0)
      case Val.Zero(_)       => Arg.I(0) // TODO only zero[java.lang.Object] in comparisons...
      case Val.Undef(_)      => Arg.I(0) // Kept for passing unused function parameters
      case Val.Null          => Arg.I(0)
      case Val.Byte(v)       => Arg.I(v)
      case Val.Short(v)      => Arg.I(v)
      case Val.Int(v)        => Arg.I(v)
      case Val.Long(v)       => Arg.I(v)
      case Val.Float(v)      => Arg.F(v)
      case Val.Double(v)     => Arg.F(v)
      case Val.Unit          => Arg.I(0) // TODO only in java.lang.AbstractStringBuilder::init
      case Val.Local(n, _)   =>
        allocator.getOrElse(n, Arg.R(-1) ) // R(-1) needed for unused function parameters
      case Val.Global(n, _)  => Arg.G(n)
      case _                 => unsupported(iv)
    }

    def convertGlobals(arg: Arg): Arg = arg match {
      case Arg.G(n)    => globalOffsets.get(n) match {
        case Some(o) => Arg.M(o)
        case None    =>
          // println("g " + n.show)
          Arg.G(n)
        //unsupported(n)
      }
      case _           => arg
    }

    def genUnsupported(reason: String)(implicit allocator: Allocator): Unit = {
      genBytecode(Halt(reason), Seq())
    }

    def isReturnable(v: nir.Val): Boolean = !(v == nir.Val.None || v == nir.Val.Unit)
    def isReturnable(t: nir.Type): Boolean = convertSize(t) > 0

    def argFromVal(v: nir.Val): Arg = v match { // For data section values
      case Val.True          => Arg.I(1)
      case Val.False         => Arg.I(0)
      case Val.Zero(ty)      => Arg.I(0) // TODO this is probably more complex
      case Val.Byte(v)       => Arg.I(v)
      case Val.Short(v)      => Arg.I(v)
      case Val.Int(v)        => Arg.I(v)
      case Val.Long(v)       => Arg.I(v)
      case Val.Float(v)      => Arg.F(v)
      case Val.Double(v)     => Arg.F(v)
      case Val.Global(n, _)  =>
        Arg.G(n)
      case Val.None          => Arg.I(0)
      case Val.Null          => Arg.I(0)
      case _                 => unsupported(v)
    }
  }
}
