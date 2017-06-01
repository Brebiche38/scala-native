package scala.scalanative.optimizer.analysis

import scala.scalanative.nir.Type.RefKind
import scala.scalanative.nir.{Type, Val}
import scala.scalanative.optimizer.analysis.MemoryLayout.PositionedType
import scala.scalanative.util.unsupported

final case class MemoryLayout(size: Long, tys: List[PositionedType]) {
  lazy val offsetArray: Seq[Val] = {
    val ptrOffsets =
      tys.collect {
        case MemoryLayout.Tpe(_, offset, _: RefKind) => Val.Long(offset)
      }

    ptrOffsets :+ Val.Long(-1)
  }

  def offsetTable(topTys: Seq[Type]): Seq[Val.Long] = {
    val (sum, firstTpes) = topTys.foldLeft((0L, Seq[Long]())) {
      case ((idx, prevIdxs), ty) =>
        (idx + MemoryLayout.elems(ty), prevIdxs :+ idx)
    }
    val tpeOffsets = tys.collect {
      case MemoryLayout.Tpe(_, off, _) => off
    }
    if (tpeOffsets.length != sum) {
      println()
      println(topTys)
      println(tys)
      println(tpeOffsets)
      println(topTys.map(x => (x, MemoryLayout.elems(x))))
    }
    firstTpes.map(x => Val.Long(tpeOffsets(x.toInt))) :+ Val.Long(-1)
  }
}

object MemoryLayout {

  sealed abstract class PositionedType {
    def size: Long
    def offset: Long
  }

  final case class Tpe(size: Long, offset: Long, ty: Type)
      extends PositionedType
  final case class Padding(size: Long, offset: Long) extends PositionedType

  def sizeOf(ty: Type): Long = ty match {
    case primitive: Type.Primitive => math.max(primitive.width / 8, 1)
    case Type.Array(arrTy, n)      => MemoryLayout(Seq.fill(n)(arrTy)).size
    case Type.Struct(_, tys)       => MemoryLayout(tys).size
    case Type.Nothing | Type.Ptr | _: Type.Trait | _: Type.Module |
        _: Type.Class =>
      8
    case _ => unsupported(s"sizeOf $ty")
  }

  def elems(ty: Type): Long = ty match {
    case Type.Struct(_, tys) => tys.map(elems).sum
    case Type.Array(ty, n)   => n * elems(ty)
    case _                   => 1
  }

  def elemIndex(ty: Type, ids: Seq[Long]): Long = (ty, ids) match {
    case (Type.Struct(_, tys), id +: idxs) =>
      tys.take(id.toInt).map(elems).sum + elemIndex(tys(id.toInt), idxs)
    case (Type.Array(innerTy, _), id +: idxs) =>
      elems(innerTy) * id + elemIndex(innerTy, idxs)
    case (_, Seq()) =>
      0
  }

  def findMax(tys: Seq[Type]): Long = tys.foldLeft(0L) {
    case (acc, Type.Struct(_, innerTy)) => math.max(acc, findMax(innerTy))
    case (acc, Type.Array(innerTy, _))  => math.max(acc, sizeOf(innerTy))
    case (acc, ty)                      => math.max(acc, sizeOf(ty))
  }

  def apply(tys: Seq[Type]): MemoryLayout = {
    val (size, potys) = impl(tys, 0)

    MemoryLayout(size, potys.reverse)
  }
  private def impl(tys: Seq[Type],
                   offset: Long): (Long, List[PositionedType]) = {
    if (tys.isEmpty) {
      return (0, List())
    }

    val sizes = tys.map(sizeOf)

    val maxSize = findMax(tys)

    val (size, positionedTypes) =
      (tys zip sizes).foldLeft((offset, List[PositionedType]())) {
        case ((index, potys), (ty, size)) if size > 0 =>
          ty match {
            case Type.Struct(_, stys) =>
              val innerAlignment = findMax(stys)
              val pad =
                if (index                    % innerAlignment == 0) 0
                else innerAlignment - (index % innerAlignment)
              val (innerSize, innerTys) = impl(stys, index + pad)

              (index + pad + innerSize,
               innerTys ::: Padding(pad, index) :: potys)

            case Type.Array(ty, n) =>
              val (innerSize, innerTys) = impl(Seq.fill(n)(ty), index)
              (index + innerSize, innerTys ::: potys)

            case _ =>
              val pad = if (index % size == 0) 0 else size - (index % size)
              (index + pad + size,
               Tpe(size, index + pad, ty) :: Padding(pad, index) :: potys)

          }
        case ((index, potys), _) => (index, potys)

      }

    val finalPad = if (size % maxSize == 0) 0 else maxSize - (size % maxSize)
    val potys =
      if (finalPad > 0) {
        Padding(finalPad, size) :: positionedTypes
      } else {
        positionedTypes
      }

    (potys.foldLeft(0L) { case (acc, poty) => acc + poty.size }, potys)
  }
}
