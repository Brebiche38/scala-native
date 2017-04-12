package scala.scalanative
package nbc

import scala.scalanative.util.unsupported

sealed abstract class Opcode {
  def toStr: String = this.getClass.getSimpleName.toLowerCase.filter(_.isLetter)
  def toBin(args: Seq[Arg]): Seq[Byte]
  def immSize: Int = 0
}

object Opcode {
  type Offset = Long
  type Instr = (Offset, Opcode, Seq[Arg])

  def pack(fields: Seq[(Int, Int)]): Seq[Byte] = {
    val (packed, size) = fields.foldRight((BigInt(0), 0)) { case ((value, vsize), (buf, bsize)) =>
      (buf | ((value & ((1 << vsize) - 1)) << bsize), bsize + vsize)
    }
    assert(size % 8 == 0)
    packed.toByteArray.takeRight(size/8)
  }

  def packSize(s: Int): Int = s match {
    case 8  => 0x0
    case 16 => 0x1
    case 32 => 0x2
    case 64 => 0x3
    case _  => unsupported(s)
  }

  def packSizeF(s: Int): Int = s match {
    case 32 => 0x0
    case 64 => 0x1
  }

  def packImm(arg: Arg, s: Int): Seq[Byte] = arg match {
    case Arg.M(a) if s == 64 => packImmI(a, 64)
    case Arg.I(v)            => packImmI(v, s)
    case Arg.F(v)            => packImmF(v, s)
    case Arg.G(g)            => println(g.show); packImmI(0, s)
  }
  def packImmI(i: Long, s: Int): Seq[Byte] =
    BigInt(i).toByteArray.takeRight(s/8)

  def packImmF(i: Double, s: Int): Seq[Byte] = s match {
    case 32 => packImmI(java.lang.Float.floatToRawIntBits(i.toFloat).toLong, s)
    case 64 => packImmI(java.lang.Double.doubleToRawLongBits(i), s)
  }

  final case class Data(size: Long) extends Opcode {
    override def toStr: String = ""
    override def toBin(args: Seq[Arg]) = args match {
      case Seq(arg) => packImm(arg, (size*8).toInt)
    }
    override def immSize = size.toInt
  }

  // Not in the final code (only for debug purposes
  final case class Function(name: nir.Global) extends Opcode {
    override def toStr: String = name.show
    override def toBin(args: Seq[Arg]) = Seq()
  }

  final case class Mov(size: Int) extends Opcode {
    override def toStr: String = super.toStr + "." + size.toString

    override def toBin(args: Seq[Arg]) = args match {
      case Seq(Arg.R(r1), Arg.R(r2)) =>
        pack(Seq(
          (0x0, 4),
          (packSize(size), 4),
          (r1, 4),
          (r2, 4)
        ))
      case Seq(Arg.R(r1), arg2) =>
        pack(Seq(
          (0x0, 4),
          (packSize(size), 4),
          (r1, 4),
          (0x8, 4)
        )) ++ packImm(arg2, size)
    }

    override def immSize = size
  }

  sealed abstract class Arith(val size: Int) extends Opcode {
    override def toStr: String = super.toStr + "." + size.toString
    def opcode: Int
    override def toBin(args: Seq[Arg]) = args match {
      case Seq(Arg.R(r1), Arg.R(r2)) =>
        pack(Seq(
          (0x1, 2),
          (opcode, 5),
          (packSize(size), 2),
          (r1, 3),
          (r2, 4)
        ))
      case Seq(Arg.R(r1), arg2) =>
        pack(Seq(
          (0x1, 2),
          (opcode, 5),
          (packSize(size), 2),
          (r1, 3),
          (0x8, 4)
        )) ++ packImm(arg2, size)
    }
    override def immSize = size
  }

  final case class Add(override val size: Int) extends Arith(size) {
    override def opcode = 0x01
  }
  final case class FAdd(override val size: Int) extends Arith(size) {
    override def opcode = 0x11
  }
  final case class Sub (override val size: Int) extends Arith(size) {
    override def opcode = 0x02
  }
  final case class FSub(override val size: Int) extends Arith(size) {
    override def opcode = 0x12
  }
  final case class Mul (override val size: Int) extends Arith(size) {
    override def opcode = 0x03
  }
  final case class FMul(override val size: Int) extends Arith(size) {
    override def opcode = 0x13
  }
  final case class Div (override val size: Int) extends Arith(size) {
    override def opcode = 0x04
  }
  final case class UDiv(override val size: Int) extends Arith(size) {
    override def opcode = 0x0c
  }
  final case class FDiv(override val size: Int) extends Arith(size) {
    override def opcode = 0x14
  }
  final case class Rem (override val size: Int) extends Arith(size) {
    override def opcode = 0x05
  }
  final case class URem(override val size: Int) extends Arith(size) {
    override def opcode = 0x0d
  }
  final case class FRem(override val size: Int) extends Arith(size) {
    override def opcode = 0x15
  }
  final case class Shl (override val size: Int) extends Arith(size) {
    override def opcode = 0x19
  }
  final case class LShr(override val size: Int) extends Arith(size) {
    override def opcode = 0x1a
  }
  final case class AShr(override val size: Int) extends Arith(size) {
    override def opcode = 0x1b
  }
  final case class And (override val size: Int) extends Arith(size) {
    override def opcode = 0x1c
  }
  final case class Or  (override val size: Int) extends Arith(size) {
    override def opcode = 0x1d
  }
  final case class Xor (override val size: Int) extends Arith(size) {
    override def opcode = 0x1e
  }

  def convertBin(bin: nir.Bin, ty: nir.Type): Arith = {
    val size = convertSize(ty)
    bin match {
      case nir.Bin.Iadd => Add(size)
      case nir.Bin.Fadd => FAdd(size)
      case nir.Bin.Isub => Sub(size)
      case nir.Bin.Fsub => FSub(size)
      case nir.Bin.Imul => Mul(size)
      case nir.Bin.Fmul => FMul(size)
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

  sealed abstract class Comp(val size: Int) extends Opcode {
    override def toStr: String = super.toStr + "." + size.toString
    def opcode: Int
    override def toBin(args: Seq[Arg]) = args match {
      case Seq(Arg.R(r1), Arg.R(r2)) =>
        pack(Seq(
          (0x3, 4),
          (opcode, 2),
          (packSize(size), 2),
          (r1, 4),
          (r2, 4)
        ))
      case Seq(Arg.R(r1), arg2) =>
        pack(Seq(
          (0x3, 4),
          (opcode, 2),
          (packSize(size), 2),
          (r1, 4),
          (0x8, 4)
        )) ++ packImm(arg2, size)
      case Seq(arg1, Arg.R(r2)) =>
        pack(Seq(
          (0x3, 4),
          (opcode, 2),
          (packSize(size), 2),
          (0x8, 4),
          (r2, 4)
        )) ++ packImm(arg1, size)
      case Seq(arg1, arg2) =>
        pack(Seq(
          (0x3, 4),
          (opcode, 2),
          (packSize(size), 2),
          (0x8, 4),
          (0x8, 4)
        )) ++ packImm(arg1, size) ++ packImm(arg2, size)
    }
    override def immSize = size
  }
  final case class SCmp(override val size: Int) extends Comp(size) {
    override def opcode = 0x0
  }
  final case class UCmp(override val size: Int) extends Comp(size) {
    override def opcode = 0x1
  }
  final case class FCmp(override val size: Int) extends Comp(size) {
    override def opcode = 0x2
  }

  sealed abstract class SetIf extends Opcode {
    def opcode: Int
    override def toBin(args: Seq[Arg]) = args match {
      case Seq(Arg.R(r)) =>
        pack(Seq(
          (0xe, 4),
          (opcode, 4),
          (0x0, 4), // padding
          (r, 4)
        ))
    }
  }
  final case object SetEq extends SetIf {
    override def opcode = 0x0
  }
  final case object SetNe extends SetIf {
    override def opcode = 0x1
  }
  final case object SetLe extends SetIf {
    override def opcode = 0x4
  }
  final case object SetLt extends SetIf {
    override def opcode = 0x5
  }
  final case object SetGe extends SetIf {
    override def opcode = 0x6
  }
  final case object SetGt extends SetIf {
    override def opcode = 0x7
  }

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

  sealed abstract class Conv(val before: Int, val after: Int) extends Opcode {
    override def toStr: String = super.toStr + "." + before.toString + "." + after.toString
    def opcode: Int
    override def toBin(args: Seq[Arg]) = args match {
      case Seq(Arg.R(r1), Arg.R(r2)) =>
        pack(Seq(
          (0x2, 2),
          (opcode, 3),
          (packSize(before), 2),
          (packSize(after), 2),
          (r1, 3),
          (r2, 4)
        ))
      case Seq(Arg.R(r1), arg2) =>
        pack(Seq(
          (0x2, 2),
          (opcode, 3),
          (packSize(before), 2),
          (packSize(after), 2),
          (r1, 3),
          (0x8, 4)
        )) ++ packImm(arg2, before)
    }

    override def immSize: Int = before
  }
  final case class Trunc(override val before: Int, override val after: Int) extends Conv(before, after) {
    override def opcode = 0x0
  }
  final case class Zext(override val before: Int, override val after: Int) extends Conv(before, after) {
    override def opcode = 0x2
  }
  final case class Sext(override val before: Int, override val after: Int) extends Conv(before, after) {
    override def opcode = 0x3
  }
  final case class FpTrunc(override val before: Int, override val after: Int) extends Conv(before, after) {
    override def opcode = 0x1
  }
  final case class FpExt(override val before: Int, override val after: Int) extends Conv(before, after) {
    override def opcode = 0x1
  }
  final case class F2I(override val before: Int, override val after: Int) extends Conv(before, after) {
    override def opcode = 0x4
  }
  final case class F2UI(override val before: Int, override val after: Int) extends Conv(before, after) {
    override def opcode = 0x5
  }
  final case class I2F(override val before: Int, override val after: Int) extends Conv(before, after) {
    override def opcode = 0x6
  }
  final case class UI2F(override val before: Int, override val after: Int) extends Conv(before, after) {
    override def opcode = 0x7
  }

  def convertConv(conv: nir.Conv, ta: nir.Type, tb: nir.Type): Opcode = {
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
      case nir.Conv.Ptrtoint => Mov(sb)
      case nir.Conv.Inttoptr => Mov(sb)
      case nir.Conv.Bitcast  => Mov(sb)
    }
  }

  sealed abstract class CF extends Opcode {
    def opcode: Int
    override def toBin(args: Seq[Arg]) = args match {
      case Seq(Arg.R(r)) =>
        pack(Seq(
          (0xc, 4),
          (opcode, 4),
          (0x0, 4), // Padding
          (r, 4)
        ))
      case Seq(Arg.M(a)) =>
        pack(Seq(
          (0xc, 4),
          (opcode, 4),
          (0x0, 4), // Padding
          (0x8, 4)
        )) ++ packImmI(a, 64)
      case _ => Seq()
    }
    override def immSize: Int = 64
  }
  final case object Jump extends CF {
    override def opcode = 0x1
  }
  final case object Ifeq extends CF {
    override def opcode = 0x2
  }
  final case object Ifne extends CF {
    override def opcode = 0x3
  }
  final case object Ifle extends CF {
    override def opcode = 0x4
  }
  final case object Iflt extends CF {
    override def opcode = 0x5
  }
  final case object Ifge extends CF {
    override def opcode = 0x6
  }
  final case object Ifgt extends CF {
    override def opcode = 0x7
  }

  final case object Call extends CF {
    override def opcode = 0x0
  }
  final case class Builtin(id: Int) extends Opcode {
    override def toStr: String = super.toStr + "." + id.toString
    override def toBin(args: Seq[Arg]): Seq[Byte] = args match {
      case Seq() =>
        pack(Seq(
          (0xf, 4),
          (id, 12)
        ))
    }
  }
  final case object Ret extends CF {
    override def opcode = 0xd0
    override def toBin(args: Seq[Arg]): Seq[Byte] =
      pack(Seq(
        (opcode, 8),
        (0x0, 8) // Padding
      ))
  }
  final case object Halt extends CF {
    override def opcode = 0xdf
    override def toBin(args: Seq[Arg]): Seq[Byte] =
      pack(Seq(
        (opcode, 8),
        (0x0, 8) // Padding
      ))
  }

  sealed abstract class Stack(val size: Int) extends Opcode {
    override def toStr: String = super.toStr + "." + size.toString
    def opcode: Int
    override def toBin(args: Seq[Arg]) = args match {
      case Seq(Arg.R(r)) =>
        pack(Seq(
          (0x1, 4),
          (opcode, 2),
          (packSize(size), 2),
          (0x0, 4), // Padding
          (r, 4)
        ))
      case Seq(arg) =>
        pack(Seq(
          (0x1, 4),
          (opcode, 2),
          (packSize(size), 2),
          (0x0, 4), // Padding
          (0x8, 4)
        )) ++ packImm(arg, size)
    }

    override def immSize: Int = size
  }
  final case class Push(override val size: Int) extends Stack(size) {
    override def opcode = 0x0
  }
  final case class Pop(override val size: Int) extends Stack(size) {
    override def opcode = 0x1
  }
  final case object Alloc extends Opcode {
    override def toBin(args: Seq[Arg]) = args match {
      case Seq(Arg.R(r1), Arg.R(r2)) =>
        pack(Seq(
          (0xff, 8),
          (r1, 4),
          (r2, 4)
        ))
      case Seq(Arg.R(r1), Arg.I(v2)) =>
        pack(Seq(
          (0xff, 8),
          (r1, 4),
          (0x8, 4)
        )) ++ packImmI(v2, immSize) // Limit to shorts for now
    }
    override def immSize: Int = 16
  }

  sealed abstract class Memory(val size: Int) extends Opcode {
    override def toStr: String = super.toStr + "." + size.toString
    def opcode: Int
  }
  final case class Store(override val size: Int) extends Memory(size) {
    override def opcode = 0x0
    override def toBin(args: Seq[Arg]) = args match {
      case Seq(Arg.R(r1), Arg.R(r2)) =>
        pack(Seq(
          (0x2, 4),
          (opcode, 2),
          (packSize(size), 2),
          (r1, 4),
          (r2, 4)
        ))
      case Seq(Arg.R(r1), arg2) =>
        pack(Seq(
          (0x2, 4),
          (opcode, 2),
          (packSize(size), 2),
          (r1, 4),
          (0x8, 4)
        )) ++ packImm(arg2, size)
      case Seq(Arg.M(a1), Arg.R(r2)) =>
        pack(Seq(
          (0x2, 4),
          (opcode, 2),
          (packSize(size), 2),
          (0x8, 4),
          (r2, 4)
        )) ++ packImmI(a1, 64)
      case Seq(Arg.M(a1), arg2) =>
        pack(Seq(
          (0x2, 4),
          (opcode, 2),
          (packSize(size), 2),
          (0x8, 4),
          (0x8, 4)
        )) ++ packImmI(a1, 64) ++ packImm(arg2, size)
    }
    override def immSize: Int = 64
  }
  final case class Load(override val size: Int) extends Memory(size) {
    override def opcode = 0x1
    override def toBin(args: Seq[Arg]) = args match {
      case Seq(Arg.R(r1), Arg.R(r2)) =>
        pack(Seq(
          (0x2, 4),
          (opcode, 2),
          (packSize(size), 2),
          (r1, 4),
          (r2, 4)
        ))
      case Seq(Arg.R(r1), arg2) =>
        pack(Seq(
          (0x2, 4),
          (opcode, 2),
          (packSize(size), 2),
          (r1, 4),
          (0x8, 4)
        )) ++ packImm(arg2, 64)
    }
    override def immSize: Int = 64
  }

  final case object Nop extends Opcode {
    override def toBin(args: Seq[Arg]) = Seq()
  }

  def convertSize(ty: nir.Type): Int = { // TODO complex types
    ty match {
      //case nir.Type.None          => 0
      case nir.Type.Void          => 0
      case nir.Type.Vararg        => 64
      case nir.Type.Ptr           => 64 // TODO assume 64 bits
      case nir.Type.I(s, _)       => if (s == 1) 8 else s
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

  def show(op: Opcode, args: Seq[Arg]): String = {
    val opStr = op.toStr
    opStr + " "*(12 - opStr.length) + args.map(_.toStr).mkString(", ")
  }
}