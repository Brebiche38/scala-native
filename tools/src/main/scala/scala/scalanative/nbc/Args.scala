package scala.scalanative
package nbc

sealed abstract class Arg {
  val toStr: String
}
object Arg {
  sealed abstract class Reg extends Arg

  /*
  // Special purpose registers

  // Program counter
  case object RPC extends Reg {
    val toStr = "rPC"
  }
  // Stack pointer
  case object RSP extends Reg {
    val toStr = "rSP"
  }
  // Link register
  case object RL extends Reg {
    val toStr = "rL"
  }
  // Flags register
  case object RF extends Reg {
    val toStr = "rF"
  }
  */

  // Register
  case class R(id: Int) extends Reg {
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
  case class M(addr: Bytecode.Offset) extends Arg {
    val toStr = "0x" + addr.toHexString
  }

  // Nop, should not be used
  case object None extends Arg {
    val toStr = ""
  }

  // High-level, have to go before output
  case class G(name: nir.Global) extends Arg {
    val toStr = name.show
  }

  case class L(label: nir.Local) extends Arg {
    val toStr = label.show
  }

  case class S(str: String) extends Arg {
    val toStr = str
  }
}