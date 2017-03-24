package scala.scalanative
package nbc

sealed abstract class Arg {
  val toStr: String
}
object Arg {
  sealed abstract class Reg extends Arg
  case object RPC extends Reg {
    val toStr = "rPC"
  }
  case object RSP extends Reg {
    val toStr = "rSP"
  }
  case object RL extends Reg {
    val toStr = "rL"
  }
  case object RF extends Reg {
    val toStr = "rF"
  }

  // Register
  case class R(id: Int) extends Reg {
    val toStr = "r" + id.toString
  }

  // Immediate int
  case class I(n: Long) extends Arg {
    val toStr = n.toString
  }

  //
  case class F(n: Double) extends Arg {
    val toStr = n.toString
  }

  case class M(addr: Bytecode.Offset) extends Arg {
    val toStr = "0x" + addr.toHexString
  }

  case object None extends Arg {
    val toStr = ""
  }

  // High-level, have to go before output
  case class G(name: nir.Global) extends Arg {
    val toStr = name.show
  }

  case class L(fun: nir.Global, label: nir.Local) extends Arg {
    val toStr = fun.show + ":" + label.show
  }

  case class S(str: String) extends Arg {
    val toStr = str
  }
}