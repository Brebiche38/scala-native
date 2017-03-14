package scala.scalanative
package nbc

import scala.scalanative.nir._

sealed abstract class Reg
object Reg {
  case object RPC extends Reg
  case object RSP extends Reg
  case object RL extends Reg
  case object RF extends Reg
  case object R0 extends Reg
  case object R1 extends Reg
  case object R2 extends Reg
  case object R3 extends Reg
  case object R4 extends Reg
  case object R5 extends Reg
  case object R6 extends Reg
  case object R7 extends Reg

  case class R(id: Int) extends Reg
}