package scala.scalanative.nbc

import scala.collection.mutable

class GenAssembly {
  val buffer: mutable.UnrolledBuffer[String] = mutable.UnrolledBuffer.empty[String]

  def p(op: Short, byte: Int): Byte = ((op & (0xf << 4*(3-byte))) >> 4*(3-byte)).toByte
  def sizeToBytes(size:Int): Int = size match {
    case 0 => 1
    case 1 => 2
    case 2 => 4
    case 3 => 8
  }

  def reg(num: Int, size: Int): String = num match {
    case r if r < 8 =>
      val suffix = size match {
        case 0 => "b"
        case 1 => "w"
        case 2 => "d"
        case 3 => ""
      }
      "%r" + (num+8) + suffix
    case 0x8 => offset(rPC, 2)
    case 0xf =>
      buffer += inst("movw", Seq(offset(rPC, 2), rTmp(1)))

  }
  val rPC =  "%eax"
  val rR  =  "%ebp" // Spilled registers
  def rTmp(size: Int) = size match { // Temporary register
    case 0 => "%sil"
    case 1 => "%si"
    case 2 => "%rsi"
    case 3 => "%esi"
  }
  def offset(reg: String, off: Int): String = off + "(" + reg + ")"
  def op(op: String, size: Int): String = op + (size match {
    case 0 => "b"
    case 1 => "w"
    case 2 => "l"
    case 3 => "q"
  })

  def inst(opcode: String, args: Seq[String]): String = opcode + " " + args.mkString(", ")

  def nullary(opcode: String, size: Int): String = ""
  def unary(opcode: String, size: Int, arg1: Byte): String = ""
  def binary(opcode: String, size: Int, arg1: Byte, arg2: Byte): String = ""

  def genAssembly(opc: Short): String = {
    buffer.clear()

    p(opc, 0) match {
      case 0x0 => // Move
        binary("mov", p(opc, 1), p(opc, 2), p(opc, 3))

      case 0x1 => // Stack
        val operand = p(opc, 1) & 0x4 match {
          case 0x0 => "push"
          case 0x4 => "pop"
        }
        val size = p(opc, 1) & 0x3
        unary(operand, size, p(opc, 3))

      case 0x2 => // Memory
        val operand = p(opc, 1) & 0x4 match {
          case 0x0 => "store"
          case 0x4 => "load"
        }
        val size = p(opc, 2) & 0x3
        binary(operand, size, p(opc, 2), p(opc, 3))

      case 0x3 => // Bitwise arithmetic
        val operand = p(opc, 1) & 0xc match {
          case 0x0 => "and"
          case 0x4 => "or"
          case 0x8 => "xor"
        }
        val size = p(opc, 1) & 0x3
        binary(operand, size, p(opc, 2), p(opc, 3))

      case 0x4 => // Integer arithmetic
        val operand = p(opc, 1) & 0xc match {
          case 0x0 => "add"
          case 0x2 => "sub"
          case 0x4 => "mul"
        }
        val size = p(opc, 1) & 0x3
        binary(operand, size, p(opc, 2), p(opc, 3)) // TODO can't have spilled registers as r1

      case 0x5 => // Floating-point arithmetic
        () // TODO use special registers

      case 0x6 => // Division
        () // TODO complicated

      case 0x7 => // Modulo
        () // TODO complicated

      case 0x8 =>
        ()

      case 0x9 =>
        ()

      case 0xa =>
        ()

      case 0xb => // Conversions
        ()

      case 0xc => // Control flow
        ()

      case 0xd => // Return and Halt
        ()

      case 0xe => // Conditional ops // TODO SetIf instructions have to be specific to the used comparison
        ()

      case 0xf => // Builtin functions/Alloc
        ()
    }
    buffer.mkString("\n")
  }
}
