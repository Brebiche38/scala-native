package scala.scalanative
package nbc

import scala.scalanative.util.unsupported

sealed abstract class Bytecode

object Bytecode {
  type Offset = Int

  final case class Mov(size: Int) extends Bytecode
  
  sealed abstract class Arith extends Bytecode
  final case class Add (size: Int) extends Arith
  final case class FAdd(size: Int) extends Arith
  final case class Sub (size: Int) extends Arith
  final case class FSub(size: Int) extends Arith
  final case class Mul (size: Int) extends Arith
  final case class FMul(size: Int) extends Arith
  final case class Div (size: Int) extends Arith
  final case class UDiv(size: Int) extends Arith
  final case class FDiv(size: Int) extends Arith
  final case class Rem (size: Int) extends Arith
  final case class URem(size: Int) extends Arith
  final case class FRem(size: Int) extends Arith
  final case class Shl (size: Int) extends Arith
  final case class LShr(size: Int) extends Arith
  final case class AShr(size: Int) extends Arith
  final case class And (size: Int) extends Arith
  final case class Or  (size: Int) extends Arith
  final case class Xor (size: Int) extends Arith

  def convertBin(bin: nir.Bin, ty: nir.Type): Arith = {
    val size = convertSize(ty)
    bin match {
      case nir.Bin.Iadd => Add(size)
      case nir.Bin.Fadd => FAdd(size)
      case nir.Bin.Isub => Sub(size)
      case nir.Bin.Fsub => Sub(size)
      case nir.Bin.Imul => Mul(size)
      case nir.Bin.Fmul => Mul(size)
      case nir.Bin.Sdiv => Div(size)
      case nir.Bin.Udiv => UDiv(size)
      case nir.Bin.Fdiv => FDiv(size)
      case nir.Bin.Srem => Rem(size)
      case nir.Bin.Urem => URem(size)
      case nir.Bin.Frem => FRem(size)
      case nir.Bin.Shl  => Shl(size)
      case nir.Bin.Lshr => LShr(size)
      case nir.Bin.Ashr => AShr(size)
      case nir.Bin.And  => And(size)
      case nir.Bin.Or   => Or(size)
      case nir.Bin.Xor  => Xor(size)
    }
  }

  sealed abstract class Comp extends Bytecode
  final case class SCmp(size: Int) extends Comp
  final case class UCmp(size: Int) extends Comp
  final case class FCmp(size: Int) extends Comp

  sealed abstract class SetIf extends Bytecode
  final case object SetEq extends SetIf
  final case object SetNe extends SetIf
  final case object SetLt extends SetIf
  final case object SetLe extends SetIf
  final case object SetGt extends SetIf
  final case object SetGe extends SetIf

  def convertComp(comp: nir.Comp, ty: nir.Type): (Comp, SetIf) = {
    val size = convertSize(ty)
    comp match {
      case nir.Comp.Ieq => (SCmp(size),SetEq)
      case nir.Comp.Ine => (SCmp(size),SetNe)
      case nir.Comp.Ugt => (UCmp(size),SetGt)
      case nir.Comp.Uge => (UCmp(size),SetGe)
      case nir.Comp.Ult => (UCmp(size),SetLt)
      case nir.Comp.Ule => (UCmp(size),SetLe)
      case nir.Comp.Sgt => (SCmp(size),SetGt)
      case nir.Comp.Sge => (SCmp(size),SetGe)
      case nir.Comp.Slt => (SCmp(size),SetLt)
      case nir.Comp.Sle => (SCmp(size),SetLe)
      case nir.Comp.Feq => (FCmp(size),SetEq)
      case nir.Comp.Fne => (FCmp(size),SetNe)
      case nir.Comp.Fgt => (FCmp(size),SetGt)
      case nir.Comp.Fge => (FCmp(size),SetGe)
      case nir.Comp.Flt => (FCmp(size),SetLt)
      case nir.Comp.Fle => (FCmp(size),SetLe)
    }
  }

  sealed abstract class Conv extends Bytecode
  final case class Trunc(before: Int, after: Int) extends Conv
  final case class Zext(before: Int, after: Int) extends Conv
  final case class Sext(before: Int, after: Int) extends Conv
  final case class FpTrunc(before: Int, after: Int) extends Conv
  final case class FpExt(before: Int, after: Int) extends Conv
  final case class F2I(before: Int, after: Int) extends Conv
  final case class F2UI(before: Int, after: Int) extends Conv
  final case class I2F(before: Int, after: Int) extends Conv
  final case class UI2F(before: Int, after: Int) extends Conv

  def convertConv(conv: nir.Conv, ta: nir.Type, tb: nir.Type): Bytecode = {
    val sa = convertSize(ta)
    val sb = convertSize(tb)
    conv match {
      case nir.Conv.Trunc    => Trunc(sa, sb)
      case nir.Conv.Zext     => Zext(sa, sb)
      case nir.Conv.Sext     => Sext(sa, sb)
      case nir.Conv.Fptrunc  => FpTrunc(sa, sb)
      case nir.Conv.Fpext    => FpExt(sa, sb)
      case nir.Conv.Fptoui   => F2UI(sa, sb)
      case nir.Conv.Fptosi   => F2I(sa, sb)
      case nir.Conv.Uitofp   => UI2F(sa, sb)
      case nir.Conv.Sitofp   => I2F(sa, sb)
      case nir.Conv.Ptrtoint => Nop // ?
      case nir.Conv.Inttoptr => Nop // ?
      case nir.Conv.Bitcast  => Nop // ?
    }
  }

  sealed abstract class CF extends Bytecode
  final case object Jump extends CF
  final case object Ifeq extends CF
  final case object Ifne extends CF
  final case object Ifgt extends CF
  final case object Ifge extends CF
  final case object Iflt extends CF
  final case object Ifle extends CF
  final case object Call extends CF
  final case object Ret extends CF
  final case object Crash extends CF

  sealed abstract class Stack extends Bytecode
  final case class Push(size: Int) extends Stack
  final case class Pop(size: Int) extends Stack

  sealed abstract class Memory extends Bytecode
  final case class Load(size: Int) extends Memory
  final case class Store(size: Int) extends Memory

  final case object Nop extends Bytecode

  def convertSize(ty: nir.Type): Int = { // TODO complex types
    ty match {
      case nir.Type.None          => 0
      case nir.Type.Void          => 0
      //case nir.Type.Vararg        =>
      case nir.Type.Ptr           => 64 // TODO assume 64 bits
      case nir.Type.I(s, _)       => s
      case nir.Type.F(s)          => s
      case nir.Type.Unit          => 0
      case nir.Type.Nothing       => 0
      case nir.Type.Function(_,_) => 64 // pointer
      case nir.Type.Struct(_,_)   => 64 // TODO pointer not sufficient ?
      case nir.Type.Array(_,_)    => 64 // TODO pointer not sufficient ?
      case nir.Type.Class(_)      => 64 // TODO no!
      case nir.Type.Trait(_)      => 64 // TODO no!
      case nir.Type.Module(_)     => 64 // TODO no!
      case _                      => unsupported(ty)
    }
  }

  def sizeof(ty: nir.Type): Offset = ty match {
    case _ => 1
  }
}