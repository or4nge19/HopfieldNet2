import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.GDelta.MetrizableSpace
import Rebuild.StatMech.FiniteGibbs.Core

/-!
# Rebuild Finite Gibbs Zero-Temperature Limit

This module provides the analytical bounds and topological limits required to prove
that stochastic Gibbs updates correctly converge to deterministic (best-response)
updates in the limit over inverse temperature $\beta \to \infty$ (i.e. $T \to 0^+$).

It rescues the core architectural proofs previously established in the legacy `ZeroTemp.lean`
and ports them to the generalized measure-theoretic foundation.
-/

set_option autoImplicit false

open Filter Topology
open scoped ENNReal NNReal

namespace Rebuild.StatMech.FiniteGibbs

/-- The logistic probability associated to a difference `x`.
    This corresponds to `P(s=1) = 1 / (1 + exp(-x))` -/
noncomputable def logisticProb (x : ℝ) : ℝ :=
  (1 : ℝ) / (1 + Real.exp (-x))

lemma logisticProb_nonneg (x : ℝ) : 0 ≤ logisticProb x := by
  unfold logisticProb
  exact div_nonneg zero_le_one (add_nonneg zero_le_one (le_of_lt (Real.exp_pos _)))

lemma logisticProb_le_one (x : ℝ) : logisticProb x ≤ 1 := by
  unfold logisticProb
  have h_pos : 0 < 1 + Real.exp (-x) := add_pos zero_lt_one (Real.exp_pos _)
  rw [div_le_iff₀ h_pos]
  linarith [Real.exp_pos (-x)]

/-- As `x → +∞`, `logisticProb x → 1`. -/
lemma logisticProb_tendsto_atTop :
    Tendsto logisticProb atTop (𝓝 (1 : ℝ)) := by
  have hx_neg : Tendsto (fun x : ℝ => -x) atTop atBot :=
    (tendsto_neg_atBot_iff).mpr tendsto_id
  have h_exp : Tendsto (fun x => Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hx_neg
  have h_cont : ContinuousAt (fun r : ℝ => (1 : ℝ) / (1 + r)) 0 :=
    (continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num))
  have h_comp :
      Tendsto (fun x => (1 : ℝ) / (1 + Real.exp (-x))) atTop (𝓝 ((1 : ℝ) / (1 + 0))) :=
    ContinuousAt.tendsto h_cont |>.comp h_exp
  unfold logisticProb
  simpa using h_comp

/-- As `x → -∞`, `logisticProb x → 0`. -/
lemma logisticProb_tendsto_atBot :
    Tendsto logisticProb atBot (𝓝 (0 : ℝ)) := by
  have h_le_exp : ∀ x : ℝ, logisticProb x ≤ Real.exp x := by
    intro x
    unfold logisticProb
    have hxpos : 0 < Real.exp (-x) := Real.exp_pos _
    have hz_le : Real.exp (-x) ≤ 1 + Real.exp (-x) := by linarith
    have : (1 : ℝ) / (1 + Real.exp (-x)) ≤ (1 : ℝ) / Real.exp (-x) :=
      one_div_le_one_div_of_le hxpos hz_le
    simpa [one_div, Real.exp_neg] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds Real.tendsto_exp_atBot
    (fun _ => logisticProb_nonneg _)
    h_le_exp

/-- Limit of the logistic probability `logisticProb (β * c)` as `β → +∞`. -/
lemma tendsto_logistic_scaled_of_pos {c : ℝ} (hc : 0 < c) :
    Tendsto (fun β : ℝ => logisticProb (β * c)) atTop (𝓝 (1 : ℝ)) := by
  have h_mul : Tendsto (fun β : ℝ => β * c) atTop atTop :=
    tendsto_id.atTop_mul_const hc
  exact logisticProb_tendsto_atTop.comp h_mul

lemma tendsto_logistic_scaled_of_neg {c : ℝ} (hc : c < 0) :
    Tendsto (fun β : ℝ => logisticProb (β * c)) atTop (𝓝 (0 : ℝ)) := by
  have hc_pos : 0 < -c := neg_pos.mpr hc
  have h_mul_pos : Tendsto (fun β : ℝ => β * (-c)) atTop atTop :=
    tendsto_id.atTop_mul_const hc_pos
  have h_mul : Tendsto (fun β : ℝ => β * c) atTop atBot := by
    have : (fun β : ℝ => β * c) = fun β => -(β * (-c)) := by ext; ring
    rw [this]
    exact tendsto_neg_atTop_atBot.comp h_mul_pos
  exact logisticProb_tendsto_atBot.comp h_mul

lemma tendsto_logistic_scaled_of_eq_zero {c : ℝ} (hc : c = 0) :
    Tendsto (fun β : ℝ => logisticProb (β * c)) atTop (𝓝 ((1 : ℝ) / 2)) := by
  have : (fun β : ℝ => logisticProb (β * c)) = fun _ => 1 / 2 := by
    ext β
    have h1 : 1 + 1 = (2 : ℝ) := by norm_num
    simp [logisticProb, hc, Real.exp_zero, h1]
  rw [this]
  exact tendsto_const_nhds

end Rebuild.StatMech.FiniteGibbs
