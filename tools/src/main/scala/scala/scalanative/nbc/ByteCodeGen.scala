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

  /** Generate bytecode for given assembly. */
  def apply(config: tools.Config, assembly: Seq[Defn], top: Top): Unit = Scope { implicit in =>
    val env = assembly.map(defn => defn.name -> defn).toMap
    val workdir = VirtualDirectory.real(config.workdir)

    withScratchBuffer { binbuf =>
      withScratchBuffer { txtbuf =>
        val defns    = assembly
        val impl     = new Impl(config.target, env, defns, binbuf, txtbuf)
        val binpath  = "bin.nbc"
        val txtpath  = "txt.nbc"
        impl.gen(top)
        binbuf.flip
        workdir.write(Paths.get(binpath), binbuf)
        txtbuf.flip
        workdir.write(Paths.get(txtpath), txtbuf)
      }
    }
  }

  private final class Impl(target: String,
                           env: Map[Global, Defn],
                           defns: Seq[Defn],
                           binbuf: ByteBuffer,
                           txtbuf: ByteBuffer) {
    // Global bytecode
    val bytecode           = mutable.Buffer.empty[Instr]
    val globalOffsets      = mutable.Map.empty[Global, Offset]
    var nextOffset: Offset = 0
    var bytesPut           = 0

    // Function-level structures
    var currentFun: Global = _
    val funBytecode     = mutable.Buffer.empty[Instr]
    val labelOffsets    = mutable.Map.empty[Local, Offset]

    def gen(implicit top: Top): Unit = {
      val definitions = defns.sortBy {
        case _: Defn.Const | _: Defn.Var => 0
        case _: Defn.Define              => 1
        case _                           => -1
      }

      // Step 1: produce bytecode
      genDefns(definitions)

      // Step 2: produce binary
      bytecode.foreach(genBinary)

      /*
      // Step 3: produce text
      val builder = new ShowBuilder
      bytecode.foreach(i => builder.line(printBytecode(i)))
      txtbuf.put(builder.toString.getBytes)
      */

      // Step 4: produce interpreter arguments
      println("run 0x" + nextOffset.toHexString + " " + convertGlobals(Arg.G(Global.Top("main"))).toStr)
      println("./main 0x" + nextOffset.toHexString + " " + convertGlobals(Arg.G(Global.Top("main"))).toStr)
    }

    def genDefns(defns: Seq[Defn])(implicit top: Top): Unit = {
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
      def getArgs(v: nir.Val): Seq[Arg] = v match {
        case nir.Val.Struct(_, vs) => vs flatMap getArgs
        case nir.Val.Array(_, vs)  => vs flatMap getArgs
        case nir.Val.Chars(s)      => s.map(Arg.I(_)) :+ Arg.I(0)
        case _                     => Seq(Arg.fromVal(v)(Map.empty))
      }
      val args = getArgs(rhs)

      val layout = MemoryLayout(Seq(ty))
      val tpes = layout.tys.filter {
        case _: MemoryLayout.Tpe => true
        case _                   => false
      }

      val maxSize = tpes.map(_.size).max
      if (nextOffset % maxSize != 0) { // Additional padding
        nextOffset += maxSize - (nextOffset % maxSize)
      }
      val mainOffset = nextOffset
      nextOffset += layout.size

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

      // Initialize function structures
      currentFun = name
      funBytecode.clear()
      labelOffsets.clear()

      val cfg = CFG(insts)

      val (allocator, spilledRegs) = RegAlloc.allocateRegisters(insts, cfg)
      genBytecodeWithArgs(Function(name), Seq(Arg.I(spilledRegs)))

      cfg.foreach { block =>
        genBlock(block)(cfg, allocator, top)
      }

      convertLabels()
    }

    def convertLabels(): Unit = {
      funBytecode.foreach {
        case (offset, opcode, args) =>
          val newArgs = args.map {
            case Arg.L(l) => Arg.M(labelOffsets(l))
            case a        => a
          }
          bytecode.append((offset, opcode, newArgs))
      }
    }

    def genBlock(block: Block)(implicit cfg: CFG, allocator: Allocator, top: Top): Unit = {
      val Block(name, params, insts, _) = block

      labelOffsets.put(name, nextOffset)

      if (block.isRegular) {
        params.foreach { p =>
          genBytecode(Pop(convertSize(p.ty)), Seq(p))
        }
        insts.foreach(genInst)
      } else if (block.isExceptionHandler) {
        genUnsupported("exception handler")
      }
    }

    def genInst(inst: Inst)(implicit cfg: CFG, allocator: Allocator, top: Top): Unit = inst match {
      case let: Inst.Let =>
        genLet(let)

      case Inst.Ret(value) =>
        genBytecode(Push(convertSize(value.ty)), Seq(value))
        genBytecode(currentFun match {
          case Global.Top("main") => FinalRet
          case _                  => Ret
        }, Seq())

      case Inst.Jump(Next.Label(dest, args)) =>
        args.reverse.foreach { arg =>
          genBytecode(Push(convertSize(arg.ty)), Seq(arg))
        }
        genBytecodeWithArgs(Jump, Seq(Arg.L(dest)))

      case Inst.If(cond, Next.Label(thenDest, thenArgs), Next.Label(elseDest, elseArgs)) =>
        thenArgs.reverse.foreach { arg =>
          genBytecode(Push(convertSize(arg.ty)), Seq(arg))
        }
        genBytecodeWithArgs(JumpIf, Seq(Arg.fromVal(cond), Arg.L(thenDest)))
        thenArgs.foreach { arg =>
          genBytecode(Pop(convertSize(arg.ty)), Seq(arg))
        }
        elseArgs.reverse.foreach { arg =>
          genBytecode(Push(convertSize(arg.ty)), Seq(arg))
        }
        genBytecodeWithArgs(Jump, Seq(Arg.L(elseDest)))

      case Inst.Throw(_, _) =>
        genUnsupported("throw")

      case Inst.Unreachable =>
        genUnsupported("unreachable")

      case _ => ()
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

          def computable(idx: Val) = idx match {
            case _: Val.Byte   => true
            case _: Val.Short  => true
            case _: Val.Int    => true
            case _: Val.Long   => true
            case _: Val.Local  => false
            case _: Val.Global => false
          }

          if (indexes.tail.forall(computable)) {
            def value(v: Val): Long = v match {
              case Val.Byte(v)   => v
              case Val.Short(v)  => v
              case Val.Int(v)    => v
              case Val.Long(v)   => v
            }
            val offsets = layout.tys.collect {
              case MemoryLayout.Tpe(_, offset, _) => offset
            }
            val tpeIndex = MemoryLayout.elemIndex(ty, indexes.tail.map(value))
            val inOffset = offsets(tpeIndex.toInt)

            if (computable(indexes.head)) { // Everything is known at compile time
              val outOffset = value(indexes.head) * size
              val offset = outOffset + inOffset
              genBytecode(Mov(64), Seq(lhs, ptr))
              genBytecode(Add(64), Seq(lhs, Val.Long(offset)))
            } else { // We don't know the first offset at compile time
              genBytecode(Mov(64), Seq(lhs, Val.Long(size)))
              genBytecode(Mul(64), Seq(lhs, indexes.head))
              genBytecode(Add(64), Seq(lhs, ptr))
              if (inOffset != 0) {
                genBytecode(Add(64), Seq(lhs, Val.Long(inOffset)))
              }
            }
          } else {
            genUnsupported("elem of variable indexes")
          }

        case Op.Sizeof(ty) =>
          val size = MemoryLayout.sizeOf(ty)
          genBytecode(Mov(64), Seq(lhs, Val.Long(size)))

        case Op.As(ty, obj) =>
          genBytecode(Mov(convertSize(ty)), Seq(lhs, obj))

        case Op.Copy(value) =>
          genBytecode(Mov(convertSize(value.ty)), Seq(lhs, value))

        case Op.Method(_, MethodRef(_: Class, meth)) if meth.isStatic =>
          genBytecode(Mov(64), Seq(lhs, Val.Global(meth.name, Type.Ptr)))

        case _ => {
          val (builtinId, retty, args): (Int, Type, Seq[Val]) = op match {
            case Op.Classalloc(ClassRef(cls)) =>
              (1, Type.Ptr, Seq(Val.Global(cls.rtti.name, Type.Ptr), Val.Long(MemoryLayout.sizeOf(cls.layout.struct))))

            case Op.Field(obj, FieldRef(cls: Class, fld)) =>
              (2, Type.Ptr, Seq(obj, Val.Global(cls.rtti.name, Type.Ptr), Val.Int(cls.layout.index(fld))))

            case Op.Method(obj, MethodRef(cls: Class, meth)) if meth.isVirtual =>
              (3, Type.Ptr, Seq(obj, Val.Int(cls.vtable.index(meth))))
            case Op.Method(obj, MethodRef(trt: Trait, meth)) =>
              (4, Type.Ptr, Seq(obj, top.tables.dispatchVal, Val.Int(meth.id), Val.Int(top.tables.dispatchOffset(meth.id))))

            case Op.Is(ClassRef(cls), obj) =>
              (5, Type.Bool, Seq(obj, Val.Global(cls.rtti.name, Type.Ptr)))
            case Op.Is(TraitRef(trt), obj) =>
              genUnsupported("is trait")
              (6, Type.Bool, Seq(obj, top.tables.classHasTraitVal, Val.Int(trt.id)))
          }

          // Generate builtin call
          args.reverse.foreach { arg =>
            genBytecode(Push(convertSize(arg.ty)), Seq(arg))
          }
          genBytecode(Builtin(builtinId), Seq())
          genBytecode(Pop(convertSize(retty)), Seq(lhs))
        }
      }
    }

    def genCall(dest: Val.Local, call: Op.Call)(implicit allocator: Allocator): Unit = call match {
      case Op.Call(ty, ptr, args, _) =>
        val Type.Function(_, retty) = ty

        // 1. Push arguments
        args.reverse.foreach { arg =>
          genBytecode(Push(convertSize(arg.ty)), Seq(arg))
        }

        // 2. Call function
        ptr match {
          case Val.Global(Global.Top("scalanative_init"), _) =>
            genBytecode(Builtin(0), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.GC$"), "extern.scalanative_alloc"), _) =>
            genBytecode(Builtin(1), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.GC$"), "extern.scalanative_alloc_atomic"), _) =>
            genBytecode(Builtin(1), Seq())

          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.Intrinsics$"), "extern.llvm.memset.p0i8.i64"), _) =>
            genBytecode(Builtin(7), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.Intrinsics$"), "extern.llvm.memmove.p0i8.p0i8.i64"), _) =>
            genBytecode(Builtin(8), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.Intrinsics$"), "extern.llvm.ctpop.i32"), _) =>
            genBytecode(Builtin(9), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.Intrinsics$"), "extern.llvm.bswap.i32"), _) =>
            genBytecode(Builtin(10), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.Intrinsics$"), "extern.llvm.ctlz.i32"), _) =>
            genBytecode(Builtin(11), Seq())

          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.Platform$"), "extern.scalanative_platform_is_windows"), _) =>
            genBytecode(Builtin(12), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.native.string$"), "extern.strlen"), _) =>
            genBytecode(Builtin(13), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.posix.unistd$"), "extern.scalanative_environ"), _) =>
            genBytecode(Builtin(14), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.posix.unistd$"), "extern.scalanative_stdin_fileno"), _) =>
            genBytecode(Builtin(15), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.posix.unistd$"), "extern.scalanative_stdout_fileno"), _) =>
            genBytecode(Builtin(16), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.posix.unistd$"), "extern.scalanative_stderr_fileno"), _) =>
            genBytecode(Builtin(17), Seq())
          case Val.Global(Global.Member(Global.Top("scala.scalanative.runtime.time$"), "extern.scalanative_nano_time"), _) =>
            genBytecode(Builtin(18), Seq())

          case Val.Global(Global.Member(Global.Top("scala.scalanative.posix.unistd$"), "extern.write"), _) =>
            genBytecode(Builtin(19), Seq())

          case _ => // Regular call
            genBytecode(Call, Seq(ptr))
        }

        // 3. recover return value
        genBytecode(Pop(convertSize(retty)), Seq(dest))
    }

    def genUnsupported(reason: String)(implicit allocator: Allocator): Unit = {
      genBytecode(Halt(reason), Seq())
    }

    def genBytecode(op: Opcode, args: Seq[Val])(implicit allocator: Allocator): Unit = {
      genBytecodeWithArgs(op, args.map(Arg.fromVal))
    }

    def genBytecodeWithArgs(op: Opcode, args: Seq[Arg]): Unit = {
      val size = op match {
        case Function(_)     => 2
        case _ =>
          val immSize = args.zipWithIndex.map { case (arg, idx) =>
            arg match {
              case Arg.R(r) if r < 8 => 0
              case Arg.R(_) => 2
              case Arg.L(_) => 8
              case Arg.G(_) => 8
              case Arg.I(_) => op.immSizes(idx)
              case Arg.F(_) => op.immSizes(idx)
            }
          }.sum
          2 + immSize
      }

      funBytecode.append((nextOffset, op, args))

      nextOffset += size
    }

    def genBinary(in: Instr): Unit = {
      val (offset, op, args) = in

      assert (bytesPut <= offset)

      while(bytesPut < offset) {
        binbuf.put(0x00.toByte)
        bytesPut += 1
      }

      val bytes = op.toBin(args.map(convertGlobals)).toArray
      bytesPut += bytes.length
      binbuf.put(bytes)
    }

    def printBytecode(in: Instr): String = {
      val (offset, op, args) = in

      offset.toHexString + ": " + op.show(args.map(convertGlobals))
    }

    def convertGlobals(arg: Arg): Arg = arg match {
      case Arg.G(n) => globalOffsets.get(n) match {
        case Some(o) => Arg.M(o)
        case None    => Arg.G(n)
      }
      case _        => arg
    }
  }
}
