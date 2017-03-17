package scala.scalanative
package nbc

import scala.scalanative.util.unsupported

sealed abstract class Bytecode {
  def toStr: String = this.getClass.getSimpleName.toLowerCase.filter(_.isLetter)
}

object Bytecode {
  type Offset = Int
  type Instr = (Bytecode, Seq[Arg])

  final case class Mov(size: Int) extends Bytecode {
    override def toStr: String = super.toStr + "." + size.toString
  }
  
  sealed abstract class Arith(val size: Int) extends Bytecode {
    override def toStr: String = super.toStr + "." + size.toString
  }
  final case class Add (override val size: Int) extends Arith(size)
  final case class FAdd(override val size: Int) extends Arith(size)
  final case class Sub (override val size: Int) extends Arith(size)
  final case class FSub(override val size: Int) extends Arith(size)
  final case class Mul (override val size: Int) extends Arith(size)
  final case class FMul(override val size: Int) extends Arith(size)
  final case class Div (override val size: Int) extends Arith(size)
  final case class UDiv(override val size: Int) extends Arith(size)
  final case class FDiv(override val size: Int) extends Arith(size)
  final case class Rem (override val size: Int) extends Arith(size)
  final case class URem(override val size: Int) extends Arith(size)
  final case class FRem(override val size: Int) extends Arith(size)
  final case class Shl (override val size: Int) extends Arith(size)
  final case class LShr(override val size: Int) extends Arith(size)
  final case class AShr(override val size: Int) extends Arith(size)
  final case class And (override val size: Int) extends Arith(size)
  final case class Or  (override val size: Int) extends Arith(size)
  final case class Xor (override val size: Int) extends Arith(size)

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

  sealed abstract class Comp(val size: Int) extends Bytecode {
    override def toStr: String = super.toStr + "." + size.toString
  }
  final case class SCmp(override val size: Int) extends Comp(size)
  final case class UCmp(override val size: Int) extends Comp(size)
  final case class FCmp(override val size: Int) extends Comp(size)

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

  sealed abstract class Conv(val before: Int, val after: Int) extends Bytecode {
    override def toStr: String = super.toStr + "." + before.toString + "." + after.toString
  }
  final case class Trunc(override val before: Int, override val after: Int) extends Conv(before, after)
  final case class Zext(override val before: Int, override val after: Int) extends Conv(before, after)
  final case class Sext(override val before: Int, override val after: Int) extends Conv(before, after)
  final case class FpTrunc(override val before: Int, override val after: Int) extends Conv(before, after)
  final case class FpExt(override val before: Int, override val after: Int) extends Conv(before, after)
  final case class F2I(override val before: Int, override val after: Int) extends Conv(before, after)
  final case class F2UI(override val before: Int, override val after: Int) extends Conv(before, after)
  final case class I2F(override val before: Int, override val after: Int) extends Conv(before, after)
  final case class UI2F(override val before: Int, override val after: Int) extends Conv(before, after)

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

  sealed abstract class Stack(val size: Int) extends Bytecode {
    override def toStr: String = super.toStr + "." + size.toString
  }
  final case class Push(override val size: Int) extends Stack(size)
  final case class Pop(override val size: Int) extends Stack(size)

  sealed abstract class Memory(val size: Int) extends Bytecode {
    override def toStr: String = super.toStr + "." + size.toString
  }
  final case class Load(override val size: Int) extends Memory(size)
  final case class Store(override val size: Int) extends Memory(size)

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
    case nir.Type.Ptr            => 8
    case nir.Type.I(w, _)        => w / 8
    case nir.Type.F(w)           => w / 8
    case nir.Type.Array(ty, n)   => n * sizeof(ty)
    case nir.Type.Struct(_, tys) => tys.map(sizeof).sum
    case nir.Type.Class(n)       => 0 // TODO
    case nir.Type.Trait(n)       => 0 // TODO
    case nir.Type.Module(n)      => 0 // TODO
  }

  def show(op: Bytecode, args: Seq[Arg]): String = {
    val opStr = op.toStr
    opStr + " "*(12 - opStr.length) + args.map(_.toStr).mkString(", ")
  }
}