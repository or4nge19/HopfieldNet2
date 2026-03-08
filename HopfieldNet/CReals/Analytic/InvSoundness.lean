import HopfieldNet.CReals.Analytic.CRealSemantics
import HopfieldNet.CReals.CRealPre2.InvTranscendental

namespace Computable
namespace CReal
namespace Analytic

open AnalyticReal

/--
Constructive inversion data should eventually be discharged by producing a `CReal.Pre.InvWitness`
for the denotation associated to an analytic frontend.
-/
structure InvWitnessData {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) where
  witness : Computable.CReal.Pre.InvWitness (Computable.CReal.Pre.one)

@[simp] theorem invM1_out_init_zero {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) :
    (AnalyticReal.invM1 A).init (AnalyticReal.invM1 A).out = 0 := by
  rfl

end Analytic
end CReal
end Computable
