import HopfieldNet.CReals.Analytic.InvSoundness
import HopfieldNet.CReals.Mobius.CRealBridge

namespace Computable
namespace CReal
namespace Analytic

structure CertifiedMobiusBridge {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (hA : HasConstructiveTaylorLimit A) where
  out : Computable.Mobius.DigitStream
  agrees :
    Computable.Mobius.toCReal out = toCReal hA

private theorem toReal_abs (x : Computable.CReal) :
    Computable.CReal.toReal |x| = |Computable.CReal.toReal x| := by
  by_cases hx : 0 ≤ x
  · have hxR : 0 ≤ Computable.CReal.toReal x := by
      simpa using Computable.CReal.toReal_mono hx
    simp [abs_of_nonneg hx, abs_of_nonneg hxR]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hxR : Computable.CReal.toReal x ≤ 0 := by
      simpa using Computable.CReal.toReal_mono hx'
    simp [abs_of_nonpos hx', abs_of_nonpos hxR, Computable.CReal.toReal_neg]

private theorem analytic_const_toReal_zero :
    toReal (HasConstructiveTaylorLimit.const 0) = 0 := by
  let hA : HasConstructiveTaylorLimit (AnalyticReal.const 0) :=
    HasConstructiveTaylorLimit.const 0
  let A : ℝ := toReal hA
  change A = 0
  have hle : A ≤ 0 := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    rcases exists_rat_btwn hε with ⟨δq, hδq0, hδqε⟩
    have hδq0' : (0 : ℚ) < δq := by exact_mod_cast hδq0
    rcases approxSum_converges (A := AnalyticReal.const 0) hA δq hδq0' with ⟨N, hN⟩
    have hC :
        |((AnalyticReal.approxSum (AnalyticReal.const 0) (N + 1) : ℚ) : Computable.CReal) - toCReal hA|
          ≤ (δq : Computable.CReal) := hN (N + 1) (Nat.le_succ N)
    have hR :
        |((AnalyticReal.approxSum (AnalyticReal.const 0) (N + 1) : ℚ) : ℝ) - A| ≤ (δq : ℝ) := by
      have hR' := Computable.CReal.toReal_mono hC
      simpa [A, toReal, toCReal, toReal_abs, sub_eq_add_neg,
        Computable.CReal.toReal_add, Computable.CReal.toReal_neg] using hR'
    rw [AnalyticReal.approxSum_eq_approxSumAt_one, approxSumAt_const_succ] at hR
    have hAbs : |A| < ε := by
      simpa using lt_of_le_of_lt hR hδqε
    linarith [(abs_lt.mp hAbs).2]
  have hge : 0 ≤ A := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    rcases exists_rat_btwn hε with ⟨δq, hδq0, hδqε⟩
    have hδq0' : (0 : ℚ) < δq := by exact_mod_cast hδq0
    rcases approxSum_converges (A := AnalyticReal.const 0) hA δq hδq0' with ⟨N, hN⟩
    have hC :
        |((AnalyticReal.approxSum (AnalyticReal.const 0) (N + 1) : ℚ) : Computable.CReal) - toCReal hA|
          ≤ (δq : Computable.CReal) := hN (N + 1) (Nat.le_succ N)
    have hR :
        |((AnalyticReal.approxSum (AnalyticReal.const 0) (N + 1) : ℚ) : ℝ) - A| ≤ (δq : ℝ) := by
      have hR' := Computable.CReal.toReal_mono hC
      simpa [A, toReal, toCReal, toReal_abs, sub_eq_add_neg,
        Computable.CReal.toReal_add, Computable.CReal.toReal_neg] using hR'
    rw [AnalyticReal.approxSum_eq_approxSumAt_one, approxSumAt_const_succ] at hR
    have hAbs : |A| < ε := by
      simpa using lt_of_le_of_lt hR hδqε
    linarith [(abs_lt.mp hAbs).1]
  exact _root_.le_antisymm hle hge

private theorem analytic_const_toReal_one :
    toReal (HasConstructiveTaylorLimit.const 1) = 1 := by
  let hA : HasConstructiveTaylorLimit (AnalyticReal.const 1) :=
    HasConstructiveTaylorLimit.const 1
  let A : ℝ := toReal hA
  change A = 1
  have hle : A ≤ 1 := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    rcases exists_rat_btwn hε with ⟨δq, hδq0, hδqε⟩
    have hδq0' : (0 : ℚ) < δq := by exact_mod_cast hδq0
    rcases approxSum_converges (A := AnalyticReal.const 1) hA δq hδq0' with ⟨N, hN⟩
    have hC :
        |((AnalyticReal.approxSum (AnalyticReal.const 1) (N + 1) : ℚ) : Computable.CReal) - toCReal hA|
          ≤ (δq : Computable.CReal) := hN (N + 1) (Nat.le_succ N)
    have hR :
        |((AnalyticReal.approxSum (AnalyticReal.const 1) (N + 1) : ℚ) : ℝ) - A| ≤ (δq : ℝ) := by
      have hR' := Computable.CReal.toReal_mono hC
      simpa [A, toReal, toCReal, toReal_abs, sub_eq_add_neg,
        Computable.CReal.toReal_add, Computable.CReal.toReal_neg] using hR'
    rw [AnalyticReal.approxSum_eq_approxSumAt_one, approxSumAt_const_succ] at hR
    have hAbs : |1 - A| < ε := by
      simpa using lt_of_le_of_lt hR hδqε
    linarith [(abs_lt.mp hAbs).1]
  have hge : 1 ≤ A := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    rcases exists_rat_btwn hε with ⟨δq, hδq0, hδqε⟩
    have hδq0' : (0 : ℚ) < δq := by exact_mod_cast hδq0
    rcases approxSum_converges (A := AnalyticReal.const 1) hA δq hδq0' with ⟨N, hN⟩
    have hC :
        |((AnalyticReal.approxSum (AnalyticReal.const 1) (N + 1) : ℚ) : Computable.CReal) - toCReal hA|
          ≤ (δq : Computable.CReal) := hN (N + 1) (Nat.le_succ N)
    have hR :
        |((AnalyticReal.approxSum (AnalyticReal.const 1) (N + 1) : ℚ) : ℝ) - A| ≤ (δq : ℝ) := by
      have hR' := Computable.CReal.toReal_mono hC
      simpa [A, toReal, toCReal, toReal_abs, sub_eq_add_neg,
        Computable.CReal.toReal_add, Computable.CReal.toReal_neg] using hR'
    rw [AnalyticReal.approxSum_eq_approxSumAt_one, approxSumAt_const_succ] at hR
    have hAbs : |1 - A| < ε := by
      simpa using lt_of_le_of_lt hR hδqε
    linarith [(abs_lt.mp hAbs).2]
  exact _root_.le_antisymm hle hge

@[simp] theorem analytic_const_toCReal_zero :
    toCReal (HasConstructiveTaylorLimit.const 0) = 0 := by
  apply Computable.CReal.toReal_injective
  simpa [toReal] using analytic_const_toReal_zero

@[simp] theorem analytic_const_toCReal_one :
    toCReal (HasConstructiveTaylorLimit.const 1) = 1 := by
  apply Computable.CReal.toReal_injective
  simpa [toReal] using analytic_const_toReal_one

namespace CertifiedMobiusBridge

noncomputable def constZero :
    CertifiedMobiusBridge (AnalyticReal.const 0) (HasConstructiveTaylorLimit.const 0) where
  out := Computable.Mobius.DigitStream.zeroDigits
  agrees := by
    simp [analytic_const_toCReal_zero]

noncomputable def constOne :
    CertifiedMobiusBridge (AnalyticReal.const 1) (HasConstructiveTaylorLimit.const 1) where
  out := Computable.Mobius.DigitStream.oneDigits
  agrees := by
    simp [analytic_const_toCReal_one]

end CertifiedMobiusBridge

end Analytic
end CReal
end Computable
