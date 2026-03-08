import HopfieldNet.CReals.Analytic.Basic
import HopfieldNet.CReals.CRealComplete
import HopfieldNet.CReals.CRealRealEquiv

namespace Computable
namespace CReal
namespace Analytic

open Computable.CReal.Completeness

structure HasConstructiveTaylorLimit {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) where
  sequence : GeneralCauSeq

noncomputable def toCReal {V : Type} [Fintype V] [DecidableEq V]
    {A : AnalyticReal V} (hA : HasConstructiveTaylorLimit A) : Computable.CReal :=
  hA.sequence.limG

noncomputable def toReal {V : Type} [Fintype V] [DecidableEq V]
    {A : AnalyticReal V} (hA : HasConstructiveTaylorLimit A) : ℝ :=
  Computable.CReal.toReal (toCReal hA)

end Analytic
end CReal
end Computable
