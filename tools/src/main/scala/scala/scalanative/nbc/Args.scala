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

  case class R(id: Int) extends Reg {
    val toStr = "r" + id.toString
  }

  case class I(n: Number) extends Arg {
    val toStr = n.toString
  }

  case class G(name: nir.Global) extends Arg {
    val toStr = name.show
  }

  case class M(addr: Bytecode.Offset) extends Arg {
    val toStr = "0x" + addr.toHexString
  }

  case object None extends Arg {
    val toStr = ""
  }
}