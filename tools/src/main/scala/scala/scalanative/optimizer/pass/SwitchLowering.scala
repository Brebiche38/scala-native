package scala.scalanative
package optimizer
package pass

import analysis.ClassHierarchy.Top
import nir._
import scala.scalanative.optimizer.analysis.MemoryLayout

/** Maps sizeof computation to pointer arithmetics over null pointer. */
class SwitchLowering(top: Top) extends Pass {
  implicit val fresh: Fresh = top.fresh

  override def onInsts(insts: Seq[Inst]): Seq[Inst] = {
    val buf = new nir.Buffer
    import buf._

    insts.foreach {

      case Inst.Switch(v, default, cases) =>
        val labels = (cases :+ default).map(_ => fresh())
        val comps = (cases :+ default).map(_ => fresh())

        jump(Next.Label(labels(0), Seq()))
        cases.zipWithIndex.foreach { case (Next.Case(caseval, dest), id) =>
          label(labels(id))
          let(comps(id), Op.Comp(Comp.Ieq, v.ty, v, caseval))
          branch(Val.Local(comps(id), Type.Bool), Next.Label(dest, Seq()), Next.Label(labels(id+1), Seq()))
        }
        label(labels(cases.length)) // Default label
        jump(default)
        //let(n, Op.Copy(Val.Long(MemoryLayout.sizeOf(ty))))

      case inst =>
        buf += inst
    }

    buf.toSeq
  }
}

object SwitchLowering extends PassCompanion {
  override def apply(config: tools.Config, top: Top) =
    new SwitchLowering(top)
}
