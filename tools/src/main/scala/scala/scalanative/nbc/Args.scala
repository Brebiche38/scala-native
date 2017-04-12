package scala.scalanative
package nbc

sealed abstract class Arg {
  val toStr: String

  def isImm: Boolean = this match {
    case Arg.R(_) => false
    case Arg.I(_) => true
    case Arg.F(_) => true
    case Arg.M(_) => true
  }

  def imm: Int = if (isImm) 1 else 0
}
object Arg {
  // Register
  case class R(id: Int) extends Arg {
    val toStr = "r" + id.toString
  }

  // Immediate int
  case class I(n: Long) extends Arg {
    val toStr = n.toString
  }

  // Immediate float
  case class F(n: Double) extends Arg {
    val toStr = n.toString
  }

  // Memory location
  case class M(addr: Opcode.Offset) extends Arg {
    val toStr = "0x" + addr.toHexString
  }

  // Nop, should not be used
  case object None extends Arg {
    val toStr = ""
  }

  // High-level, have to go before output

  // Global value
  case class G(name: nir.Global) extends Arg {
    val toStr = name.show
  }

  // In-function label
  case class L(label: nir.Local) extends Arg {
    val toStr = label.show
  }

  // String literal
  case class S(str: String) extends Arg {
    val toStr = str
  }
}