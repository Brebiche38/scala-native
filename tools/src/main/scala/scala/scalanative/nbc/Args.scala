package scala.scalanative
package nbc

import scala.scalanative.nbc.RegAlloc.Allocator
import scala.scalanative.nir.Val

sealed abstract class Arg {
  val toStr: String
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

  // High-level, have to go before output

  // Global value
  case class G(name: nir.Global) extends Arg {
    val toStr = name.show
  }

  // In-function label
  case class L(label: nir.Local) extends Arg {
    val toStr = label.show
  }

  def fromVal(value: nir.Val)(implicit allocator: Allocator): Arg = value match {
    case Val.Zero(_)       => Arg.I(0)
    case Val.Undef(_)      => Arg.I(0)
    case Val.Unit          => Arg.I(0)
    case Val.Null          => Arg.I(0)
    case Val.None          => Arg.I(0)

    case Val.True          => Arg.I(1)
    case Val.False         => Arg.I(0)
    case Val.Byte(v)       => Arg.I(v)
    case Val.Short(v)      => Arg.I(v)
    case Val.Int(v)        => Arg.I(v)
    case Val.Long(v)       => Arg.I(v)
    case Val.Float(v)      => Arg.F(v)
    case Val.Double(v)     => Arg.F(v)

    case Val.Local(n, _)   => allocator.getOrElse(n, Arg.R(-1)) // R(-1) = unused variable
    case Val.Global(n, _)  => Arg.G(n)
  }
}