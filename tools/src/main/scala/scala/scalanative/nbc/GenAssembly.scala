package scala.scalanative.nbc

import java.io.{BufferedWriter, File, FileWriter}

import scala.collection.mutable

object GenAssembly {
  // We use AT&T syntax

  val buffer: mutable.UnrolledBuffer[String] = mutable.UnrolledBuffer.empty[String]

  val builtins: Seq[(String, Seq[Int])] = // Builtin names, argument sizes
    Seq(
      ("scalanative_alloc", Seq(64)),        // alloc(long)
      ("scalanative_classalloc", Seq(64)),   // classalloc(ptr)
      ("scalanative_field", Seq(64, 64, 32)) // field(ptr, ptr, int)
      // ...
    )

  def p(op: Short, byte: Int): Byte = ((op & (0xf << 4*(3-byte))) >> 4*(3-byte)).toByte
  def sizeToBytes(size:Int): Int = size match {
    case 0 => 1
    case 1 => 2
    case 2 => 4
    case 3 => 8
  }

  def imm(value: Int): String = "$" + value
  def reg(num: Int, size: Int): String = {
    val suffix = size match {
      case 0 => "b"
      case 1 => "w"
      case 2 => "d"
      case 3 => ""
    }
    "%r" + (num + 8) + suffix
  }
  def arg(num: Byte): BinArg = num match {
    case r if r < 8 => Reg(r)
    case 0x8        => SReg
    case 0xc        => Imm
    case 0xf        => Mem
  }

  // %rax, %rdx, %rsp are used in special cases
  val rPC = "%rbp"
  val rL  = "%rcx"
  val rR  = "%rbx" // Spilled registers (has to be callee saved), TODO push spilled length on register stack
  val rSP = "%rsp" // Stack pointer (not managed by us)
  def rTmp1(size: Int) = size match { // Temporary register
    case 0 => "%sil"
    case 1 => "%si"
    case 2 => "%esi"
    case 3 => "%rsi"
  }
  def rTmp2(size: Int) = size match { // Temporary register
    case 0 => "%dil"
    case 1 => "%di"
    case 2 => "%edi"
    case 3 => "%rdi"
  }
  def getOperand(arg: BinArg, size: Int, tmp: Int => String, immOffset: Int): (String, Int) = {
    arg match {
      case Reg(r) => (reg(r, size), 0 + immOffset)
      case SReg   =>
        inst("movw", Seq(offset(rPC, immOffset), tmp(1)))
        (displ(rR, tmp(1), 8, 0), 2 + immOffset)
      case Mem    =>
        inst("movq", Seq(offset(rPC, immOffset), tmp(3)))
        (deref(tmp(size)), 8 + immOffset)
      case Imm   => (offset(rPC, immOffset), sizeToBytes(size) + immOffset)
    }
  }
  def getOperandF(arg: BinArg, size: Int, tmp: Int => String, immOffset: Int, reg: String): (String, Int) = {
    val (operand, off) = getOperand(arg, size + 2, tmp, immOffset)
    inst(opF("mov", size), Seq(operand, reg))
    (operand, off)
  }
  def allRegs: Seq[String] = Seq(rPC, rL, rR) ++ (0 until 8).map(reg(_,3))
  def deref(reg: String): String = "%gs:(" + reg + ")"
  def offset(reg: String, off: Int): String = "%gs:" + off + "(" + reg + ")" // Relative to data
  def displ(baseReg: String, displReg: String, factor: Int, off: Int): String =
    off + "(" + baseReg + "," + displReg + "," + factor + ")" // Relative to program address space (rR)
  def op(op: String, size: Int): String = op + (size match {
    case -1 => ""
    case 0 => "b"
    case 1 => "w"
    case 2 => "l"
    case 3 => "q"
  })
  def opF(op: String, size: Int): String = op + (size match {
    case 0 => "ss"
    case 1 => "sd"
  })

  def inst(opcode: String, args: Seq[String]): Unit = {
    val instr = opcode + " " + args.mkString(", ")
    buffer += instr
  }

  sealed abstract class BinArg
  final case class Reg(id: Int) extends BinArg
  final case object SReg extends BinArg
  final case object Mem extends BinArg
  final case object Imm extends BinArg

  def nullary(opcode: String, size: Int): Int = {
    inst(op(opcode, size), Seq())
    2
  }
  def unary(opcode: String, size: Int, arg1: Byte): Int = {
    val operation = op(opcode, size)
    val (operand, off) = getOperand(arg(arg1), size, rTmp1, 2)
    inst(operation, Seq(operand))
    off
  }
  def binary(opcode: String, size: Int, arg1: Byte, arg2: Byte): Int =
    customBinary(op(opcode, size), false, size, arg1, false, size, arg2)
  def binaryF(opcode: String, size: Int, arg1: Byte, arg2: Byte): Int =
    customBinary(opF(opcode, size), true, size, arg1, true, size, arg2)
  def customBinary(operation: String, float1: Boolean, size1: Int, arg1: Byte, float2: Boolean, size2: Int, arg2: Byte): Int = {
    val (operand2, off2) =
      if (float2) getOperandF(arg(arg2), size2, rTmp2, 2, "%xmm1")
      else getOperand(arg(arg2), size2, rTmp2, 2)
    val (operand1, off1) =
      if (float1) getOperandF(arg(arg1), size1, rTmp1, off2, "%xmm0")
      else getOperand(arg(arg1), size1, rTmp1, off2)
    if (!float1 && !float2 && (!arg(arg1).isInstanceOf[Reg]) && (!arg(arg2).isInstanceOf[Reg])) {
      inst(op("mov", size2), Seq(operand2, rTmp2(size2)))
      inst(operation, Seq(operand1, rTmp2(size2)))
      inst(op("mov", size2), Seq(rTmp2(size2), operand2))
    } else {
      inst(operation, Seq(if (float1) "%xmm1" else operand1, if (float2) "%xmm2" else operand2))
      if (float2) {
        inst(operation, Seq("%xmm1", operand2))
      }
    }
    off1
  }

  def genAssembly(opc: Short): String = {
    buffer.clear()

    val length = p(opc, 0) match {
      case 0x0 => // Move
        binary("mov", p(opc, 1), p(opc, 3), p(opc, 2))

      case 0x1 => // Stack
        if (p(opc, 2) != 0) throw new Exception()
        val operand = p(opc, 1) & 0x4 match {
          case 0x0 => "push"
          case 0x4 => "pop"
        }
        val size = p(opc, 1) & 0x3
        unary(operand, size, p(opc, 3))

      case 0x2 => // Memory
        if ((p(opc, 1) & 0x8) != 0) throw new Exception()
        val size = p(opc, 1) & 0x3
        binary("mov", size, p(opc, 3), p(opc, 2))

      case 0x3 => // Bitwise arithmetic
        val operand = p(opc, 1) & 0xc match {
          case 0x0 => "and"
          case 0x4 => "or"
          case 0x8 => "xor"
        }
        val size = p(opc, 1) & 0x3
        binary(operand, size, p(opc, 3), p(opc, 2))

      case 0x4 => // Integer arithmetic
        val operand = p(opc, 1) & 0xc match {
          case 0x0 => "add"
          case 0x2 => "sub"
          case 0x4 => "mul"
        }
        val size = p(opc, 1) & 0x3
        binary(operand, size, p(opc, 3), p(opc, 2))

      case 0x5 => // Floating-point arithmetic
        val operand = p(opc, 1) & 0xc match {
          case 0x0 => "fadd"
          case 0x4 => "fsub"
          case 0x8 => "fmul"
        }
        val size = p(opc, 1) & 0x3
        binary(operand, size, p(opc, 3), p(opc, 2))

      case 0x6 => // Division
        val size = p(opc, 1) & 0x3
        p(opc, 1) & 0x8 match {
          case 0x0 => // Integer division
            // Step 1: Put divided in rdx:rax
            val (operand2, off2) = getOperand(arg(p(opc, 2)), size, rTmp2, 2)
            inst(op("mov", size), Seq(operand2, "%rax"))
            // Step 2: Sign or zero extend divided
            p(opc, 1) & 0x4 match {
              case 0x0 => // Signed division
                size match {
                  case 0x0 => inst("cbtw", Seq())
                  case 0x1 => inst("cwtd", Seq())
                  case 0x2 => inst("cdtq", Seq())
                  case 0x3 => inst("cqto", Seq())
                }
              case 0x4 => // Unsigned division
                inst(op("mov", size), Seq(imm(0), "%rdx"))
            }
            // Step 3: Divide
            val (operand1, off1) = getOperand(arg(p(opc, 3)), size, rTmp1, off2)
            inst(op(if ((p(opc, 1) & 0x4) == 0x0) "idiv" else "div", size), Seq(operand1))
            // Step 4: Get result
            inst(op("mov", size), Seq("%rax", operand2))
            off1
          case 0x8 => // Floating-point division
            if (size > 1) throw new Exception()
            binaryF("div", size, p(opc, 3), p(opc, 2))
        }

      case 0x7 => // Modulo
        val size = p(opc, 1) & 0x3
        p(opc, 1) & 0x8 match {
          case 0x0 => // Integer modulo
            // Step 1: Put divided in rdx:rax
            val (operand2, off2) = getOperand(arg(p(opc, 2)), size, rTmp2, 2)
            inst(op("mov", size), Seq(operand2, "%rax"))
            // Step 2: Sign or zero extend divided
            p(opc, 1) & 0x4 match {
              case 0x0 => // Signed modulo
                size match {
                  case 0x0 => inst("cbtw", Seq())
                  case 0x1 => inst("cwtd", Seq())
                  case 0x2 => inst("cdtq", Seq())
                  case 0x3 => inst("cqto", Seq())
                }
              case 0x4 => // Unsigned modulo
                inst(op("mov", size), Seq(imm(0), "%rdx"))
            }
            // Step 3: Divide
            val (operand1, off1) = getOperand(arg(p(opc, 3)), size, rTmp1, off2)
            inst(op("idiv", size), Seq(operand1))
            // Step 4: Get result
            inst(op("mov", size), Seq("%rdx", operand2))
            off1
          case 0x8 => // Floating-point modulo
            if (size > 1) throw new Exception()
            binaryF("fprem", size, p(opc, 3), p(opc, 2))
        }

      case 0x8 => // Truncation and floating-point extension
        p(opc, 1) & 0x8 match {
          case 0x0 =>
            val destsize = p(opc, 1) match {
              case 0x0 => 8
              case 0x1 => 8
              case 0x2 => 8
              case 0x3 => 16
              case 0x4 => 16
              case 0x5 => 32
            }
            binary("mov", destsize, p(opc, 3), p(opc, 2))
          case 0x8 =>
            val (operand, s1, s2) = p(opc, 1) match {
              case 0x8 => ("cvtsd2ss", 1, 0)
              case 0xf => ("cvtss2sd", 0, 1)
            }
            customBinary(operand, true, s1, p(opc, 3), true, s2, p(opc, 2))
        }

      case 0x9 => // Integer extension
        val operand = p(opc, 1) & 0x8 match {
          case 0x0 => "movzx"
          case 0x8 => "movsx"
        }
        val (s1, s2) = p(opc, 1) & 0x7 match {
          case 0x0 => (0,1)
          case 0x1 => (0,2)
          case 0x2 => (0,3)
          case 0x3 => (1,2)
          case 0x4 => (1,3)
          case 0x5 => (2,3)
        }
        customBinary(operand, false, s1, p(opc, 3), false, s2, p(opc, 2))

      case 0xa => // Floating-point to integer TODO unsigned conversion is tricky
        val size1 = p(opc, 1) & 0x4
        val size2 = p(opc, 1) & 0x3
        val operation = (size1, p(opc, 1) & 0x8) match {
          case (0x0, 0x0) => "cvttss2si"
          case (0x0, 0x8) => "cvttss2ui" // TODO probably not
          case (0x1, 0x0) => "cvttsd2si"
          case (0x1, 0x8) => "cvttsd2ui" // TODO probably not
        }
        customBinary(operation, true, size1, p(opc, 3), false, size2, p(opc, 2))

      case 0xb => // Integer to floating-point
        val size1 = p(opc, 1) & 0x6
        val size2 = p(opc, 1) & 0x1
        val operation = (size1, p(opc, 1) & 0x8) match {
          case (0x0, 0x0) => "cvttsi2ss"
          case (0x0, 0x8) => "cvttui2ss" // TODO probably not
          case (0x1, 0x0) => "cvttsi2sd"
          case (0x1, 0x8) => "cvttui2sd" // TODO probably not
        }
        customBinary(operation, false, size1, p(opc, 3), true, size2, p(opc, 2))

      case 0xc => // Control flow
        if (p(opc, 2) != 0) throw new Exception()
        val (operand, off) = getOperand(arg(p(opc, 3)), 8, rTmp1, 2)
        if (p(opc, 1) == 0x0) { // Call
          inst("movq", Seq(rPC, rL))
          inst("addq", Seq(imm(off), rL))
          inst("movq", Seq(operand, rPC))
          -1
        } else {
          val operation = p(opc, 1) match {
            case 0x1 => "jmp"
            case 0x2 => "je"
            case 0x3 => "jne"
            case 0x4 => "jbe"
            case 0x5 => "jb"
            case 0x6 => "jae"
            case 0x7 => "ja"
          }
          inst(operation, Seq(operand))
          -1
        }


      case 0xd => // Return and Halt
        p(opc, 2) match {
          case 0x0 => inst("movq", Seq(rL, rPC)) // TODO restore register stack pointer
          case 0xf => inst("ret", Seq()) // Return from tight loop function
        }
        -1

      case 0xe => // Conditional ops
        val operand = p(opc, 1) match {
          case 0x0 => "sete"
          case 0x1 => "setne"
          case 0x4 => "setle"
          case 0x5 => "setl"
          case 0x6 => "setge"
          case 0x7 => "setg"
          case 0x8 => "setbe"
          case 0x9 => "setb"
          case 0xa => "setae"
          case 0xb => "seta"
        }
        unary(operand, 0, p(opc, 3))

      case 0xf if (p(opc, 1) == 0xf) => // Alloc
        val (operand2, off2) = getOperand(arg(p(opc, 2)), 8, rTmp2, 2)
        val (operand1, off1) = getOperand(arg(p(opc, 3)), 2, rTmp1, off2)
        inst("addq", Seq(operand1, "%rsp"))
        inst("movq", Seq("%rsp", operand2))
        off1

      case 0xf => // Builtin functions
        val (name, args) = builtins(opc & 0xfff)

        // Step 1: save all registers on Register stack
        allRegs.zipWithIndex.foreach { case (reg, idx) =>
          inst("movq", Seq(reg, offset(rR, -idx*8))) // TODO same stack
        }

        // Step 2: Put arguments in registers (max. 6 arguments)
        val argRegs = Seq("%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9")
        args.zip(argRegs).reverse.foreach { case (size, reg) =>
          val suffix = size match {
            case 8  => "b"
            case 16 => "w"
            case 32 => "d"
            case 64 => "q"
          }
          inst("pop" + suffix, Seq(reg))
        }

        // Step 3: Call function
        inst("call", Seq(name))

        // Step 4: Get return value
        inst("pushq", Seq("%eax"))

        // Step 5: Restore state
        allRegs.zipWithIndex.foreach { case (reg, idx) =>
          inst("movq", Seq(offset(rR, -idx*8), reg))
        }
        2
    }
    if (length != -1) {
      inst("addq", Seq(imm(length), rPC))
    }
    inst("movw", Seq(deref(rPC), rTmp1(3)))
    inst("jmp", Seq("%es:(," + rTmp1(3) + ",8)"))

    "assembly_" + (0 until 4).map(i => Integer.toHexString(p(opc, i))).mkString("") + ":\n    " + buffer.mkString("\n    ") + "\n"
  }

  def apply(): Unit = {
    val file = new File("assembly.S")
    val bw = new BufferedWriter(new FileWriter(file))
    (0 to 0xffff).foreach { x =>
      try {
        val assembly = genAssembly(x.toShort)
        bw.write(assembly)
      } catch {
        case _ =>
          //println("No representation for " + Integer.toHexString(x))
      }
    }
    bw.close()
  }
}
