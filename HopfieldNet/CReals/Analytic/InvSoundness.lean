import HopfieldNet.CReals.Analytic.MulSoundness
import HopfieldNet.CReals.CRealPre2.InvTranscendental

namespace Computable
namespace CReal
namespace Analytic

open AnalyticReal

/--
Constructive inversion of `invM1` needs explicit separation from the singularity at `-1`.
We package that information at the approximation level rather than pretending inversion
is total on analytic fronts.
-/
structure InvWitnessData {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) where
  radius : ℚ
  radius_pos : 0 < radius
  eventuallySeparated :
    ∃ N : ℕ, ∀ n ≥ N, radius ≤ |1 + AnalyticReal.approxSum A n|

namespace InvWitnessData

def ofUniformLowerBound {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (radius : ℚ) (hr : 0 < radius)
    (hsep : ∀ n, radius ≤ |1 + AnalyticReal.approxSum A n|) :
    InvWitnessData A where
  radius := radius
  radius_pos := hr
  eventuallySeparated := ⟨0, by simpa using hsep⟩

noncomputable def constZero : InvWitnessData (AnalyticReal.const 0) :=
  ofUniformLowerBound (A := AnalyticReal.const 0) 1 (by norm_num) (by
    intro n
    cases n with
    | zero =>
        norm_num [AnalyticReal.approxSum, AnalyticReal.approxSumAt]
    | succ n =>
        rw [AnalyticReal.approxSum_eq_approxSumAt_one, approxSumAt_const_succ]
        norm_num)

noncomputable def constOne : InvWitnessData (AnalyticReal.const 1) :=
  ofUniformLowerBound (A := AnalyticReal.const 1) 1 (by norm_num) (by
    intro n
    cases n with
    | zero =>
        norm_num [AnalyticReal.approxSum, AnalyticReal.approxSumAt]
    | succ n =>
        rw [AnalyticReal.approxSum_eq_approxSumAt_one, approxSumAt_const_succ]
        norm_num)

end InvWitnessData

@[simp] theorem invM1_out_init_zero {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) :
    (AnalyticReal.invM1 A).init (AnalyticReal.invM1 A).out = 0 := by
  rfl

end Analytic
end CReal
end Computable
