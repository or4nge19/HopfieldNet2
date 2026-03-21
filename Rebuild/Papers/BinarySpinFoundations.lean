import Rebuild.Models.BinarySpin.Pairwise

/-!
# Binary-Spin Foundations

Paper-facing statements built from the canonical pairwise binary-spin model.

This layer should re-export mathematically meaningful results while hiding as much
implementation detail as possible from later paper modules.
-/

set_option autoImplicit false

namespace Rebuild.Papers.BinarySpinFoundations

open Rebuild.Core
open Rebuild.Models.BinarySpin.Pairwise

section Finite

variable {σ Site : Type*} [TwoState σ] [Fintype Site] [DecidableEq Site]

noncomputable abbrev positiveOverwrite (τ : State σ Site) (i : Site) : State σ Site :=
  overwrite τ i TwoState.pos

noncomputable abbrev negativeOverwrite (τ : State σ Site) (i : Site) : State σ Site :=
  overwrite τ i TwoState.neg

/-- The field contribution to the energy difference between the positive and negative
single-site overwrites is exactly the external field times the encoding scale. -/
theorem field_term_flip_relation (encoding : TwoStateEncoding σ)
    (p : Parameters Site) (τ : State σ Site) (i : Site) :
    fieldTerm encoding p (positiveOverwrite τ i)
      - fieldTerm encoding p (negativeOverwrite τ i)
      = p.externalField i * encoding.scale :=
  fieldTerm_overwrite_pos_neg encoding p τ i

/-- Overwriting a site does not change its own local field because the diagonal coupling
is forced to vanish. -/
theorem localField_self_overwrite_invariant (encoding : TwoStateEncoding σ)
    (p : Parameters Site) (τ : State σ Site) (i : Site) (s : σ) :
    localField encoding p (overwrite τ i s) i = localField encoding p τ i :=
  localField_overwrite_self encoding p τ i s

/-- The deterministic single-site update is idempotent. -/
theorem update_idempotent (encoding : TwoStateEncoding σ)
    (p : Parameters Site) (i : Site) (τ : State σ Site) :
    updateAt encoding p i (updateAt encoding p i τ) = updateAt encoding p i τ :=
  updateAt_idempotent encoding p i τ

/--
Given a flip-energy identity

$$E(s^+) - E(s^-) = - \, \kappa L$$

with $\kappa \ge 0$, we obtain the expected order implications from the sign of $L$.
-/
theorem energy_order_from_flip_id
    {Eplus Eminus κ L : ℝ}
    (hdiff : Eplus - Eminus = -κ * L)
    (hκ : 0 ≤ κ) :
    (0 ≤ L → Eplus ≤ Eminus) ∧
    (L ≤ 0 → Eminus ≤ Eplus) := by
  constructor
  · intro hL
    have hκL : 0 ≤ κ * L := mul_nonneg hκ hL
    have hsub : Eplus - Eminus ≤ 0 := by
      rw [hdiff, neg_mul]
      exact neg_nonpos.mpr hκL
    exact sub_nonpos.mp hsub
  · intro hL
    have hκL : κ * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ hL
    have hrev : Eminus - Eplus = κ * L := by
      have := congrArg Neg.neg hdiff
      simpa [neg_sub, neg_mul, neg_neg] using this
    have hsub : Eminus - Eplus ≤ 0 := by
      rw [hrev]
      exact hκL
    exact sub_nonpos.mp hsub

end Finite

section Signed

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- In the signed-spin (`±1`) specialization, the field contribution to the one-site
true/false overwrite difference is exactly twice the external field. -/
theorem signed_field_term_flip_relation
    (p : Parameters Site) (τ : SignedState Site) (i : Site) :
    fieldTerm TwoStateEncoding.boolSigned p (overwrite τ i true)
      - fieldTerm TwoStateEncoding.boolSigned p (overwrite τ i false)
      = 2 * p.externalField i :=
  Rebuild.Models.BinarySpin.Pairwise.signedFieldTerm_overwrite_true_false p τ i

/-- In the signed-spin specialization, overwriting site `i` does not change its own
local field. -/
theorem signed_localField_self_overwrite_invariant
    (p : Parameters Site) (τ : SignedState Site) (i : Site) (s : Spin) :
    signedLocalField p (overwrite τ i s) i = signedLocalField p τ i :=
  Rebuild.Models.BinarySpin.Pairwise.signedLocalField_overwrite_self p τ i s

/-- In the signed-spin specialization, the deterministic single-site update is idempotent. -/
theorem signed_update_idempotent
    (p : Parameters Site) (i : Site) (τ : SignedState Site) :
    signedUpdateAt p i (signedUpdateAt p i τ) = signedUpdateAt p i τ :=
  Rebuild.Models.BinarySpin.Pairwise.signedUpdateAt_idempotent p i τ

/-- For the signed-spin specialization, the contribution of the updated row `i` to the
quadratic term changes by twice the interaction field. -/
theorem signed_rowContribution_self_true_false
    (p : Parameters Site) (τ : SignedState Site) (i : Site) :
    Rebuild.Models.BinarySpin.Pairwise.signedRowContribution p (overwrite τ i true) i
      - Rebuild.Models.BinarySpin.Pairwise.signedRowContribution p (overwrite τ i false) i
      = 2 * interactionField TwoStateEncoding.boolSigned p τ i :=
  Rebuild.Models.BinarySpin.Pairwise.signedRowContribution_self_true_false p τ i

/-- For the signed-spin specialization, an off-site row `a ≠ i` changes only through the
single coupling with site `i`. -/
theorem signed_rowContribution_offsite_true_false
    (p : Parameters Site) (τ : SignedState Site) {a i : Site} (hai : a ≠ i) :
    Rebuild.Models.BinarySpin.Pairwise.signedRowContribution p (overwrite τ i true) a
      - Rebuild.Models.BinarySpin.Pairwise.signedRowContribution p (overwrite τ i false) a
      = 2 * p.coupling a i * signedSpinValue (τ a) :=
  Rebuild.Models.BinarySpin.Pairwise.signedRowContribution_offsite_true_false p τ hai

/-- In the signed-spin specialization, the true/false overwrite energy difference is
`-2` times the local field. -/
theorem signed_flip_energy_relation
    (p : Parameters Site) (τ : SignedState Site) (i : Site) :
    signedEnergyFn p (overwrite τ i true) - signedEnergyFn p (overwrite τ i false)
      = -2 * signedLocalField p τ i :=
  Rebuild.Models.BinarySpin.Pairwise.signedFlipEnergyRelation p τ i

/-- A single deterministic signed-spin update never increases the energy. -/
theorem signed_update_energy_nonincreasing
    (p : Parameters Site) (τ : SignedState Site) (i : Site) :
    signedEnergyFn p (signedUpdateAt p i τ) ≤ signedEnergyFn p τ := by
  have horder := energy_order_from_flip_id
    (Eplus := signedEnergyFn p (overwrite τ i true))
    (Eminus := signedEnergyFn p (overwrite τ i false))
    (κ := (2 : ℝ))
    (L := signedLocalField p τ i)
    (by simpa using signed_flip_energy_relation p τ i)
    (by positivity)
  cases hs : τ i with
  | false =>
      have hτ : overwrite τ i false = τ := by
        funext j
        by_cases hji : j = i
        · subst hji
          simp [overwrite, hs]
        · simp [overwrite, hji]
      by_cases hL : 0 ≤ signedLocalField p τ i
      · have hupdate : signedUpdateAt p i τ = overwrite τ i true := by
          simp [signedUpdateAt, updateAt, hL,
            (show (TwoState.pos : Bool) = true by rfl)]
        have hle : signedEnergyFn p (overwrite τ i true) ≤ signedEnergyFn p (overwrite τ i false) :=
          horder.1 hL
        simpa [hupdate, hτ] using hle
      · have hL' : signedLocalField p τ i ≤ 0 := le_of_not_ge hL
        have hupdate : signedUpdateAt p i τ = overwrite τ i false := by
          simp [signedUpdateAt, updateAt, hL,
            (show (TwoState.neg : Bool) = false by rfl)]
        have hle : signedEnergyFn p (overwrite τ i false) ≤ signedEnergyFn p (overwrite τ i true) :=
          horder.2 hL'
        rw [hupdate, hτ]
  | true =>
      have hτ : overwrite τ i true = τ := by
        funext j
        by_cases hji : j = i
        · subst hji
          simp [overwrite, hs]
        · simp [overwrite, hji]
      by_cases hL : 0 ≤ signedLocalField p τ i
      · have hupdate : signedUpdateAt p i τ = overwrite τ i true := by
          simp [signedUpdateAt, updateAt, hL,
            (show (TwoState.pos : Bool) = true by rfl)]
        rw [hupdate, hτ]
      · have hL' : signedLocalField p τ i ≤ 0 := le_of_not_ge hL
        have hupdate : signedUpdateAt p i τ = overwrite τ i false := by
          simp [signedUpdateAt, updateAt, hL,
            (show (TwoState.neg : Bool) = false by rfl)]
        have hle : signedEnergyFn p (overwrite τ i false) ≤ signedEnergyFn p (overwrite τ i true) :=
          horder.2 hL'
        simpa [hupdate, hτ] using hle

/-- Exact sitewise fixed-point criterion for the signed asynchronous update.
Because ties are resolved toward `true`, the negative spin is stable only for a
strictly negative local field. -/
theorem signed_update_eq_self_iff
    (p : Parameters Site) (τ : SignedState Site) (i : Site) :
    signedUpdateAt p i τ = τ ↔
      (τ i = true ∧ 0 ≤ signedLocalField p τ i)
        ∨ (τ i = false ∧ signedLocalField p τ i < 0) := by
  cases hs : τ i with
  | false =>
      constructor
      · intro hfix
        right
        refine ⟨by simp, ?_⟩
        by_contra hnonneg
        have hL : 0 ≤ signedLocalField p τ i := le_of_not_gt hnonneg
        have hsite := congrArg (fun σ => σ i) hfix
        simp [signedUpdateAt, updateAt, hs, hL,
          (show (TwoState.pos : Bool) = true by rfl)] at hsite
      · rintro (⟨htrue, hL⟩ | ⟨hfalse, hlt⟩)
        · cases htrue
        · funext k
          by_cases hki : k = i
          · subst k
            have hL : ¬ 0 ≤ signedLocalField p τ i := not_le.mpr hlt
            simp [signedUpdateAt, updateAt, hs, hL,
              (show (TwoState.neg : Bool) = false by rfl)]
          · simp [signedUpdateAt, updateAt, hki]
  | true =>
      constructor
      · intro hfix
        left
        refine ⟨by simp, ?_⟩
        by_contra hneg
        have hsite := congrArg (fun σ => σ i) hfix
        simp [signedUpdateAt, updateAt, hs, hneg,
          (show (TwoState.neg : Bool) = false by rfl)] at hsite
      · rintro (⟨htrue, hL⟩ | ⟨hfalse, hlt⟩)
        · funext k
          by_cases hki : k = i
          · subst k
            simp [signedUpdateAt, updateAt, hs, hL,
              (show (TwoState.pos : Bool) = true by rfl)]
          · simp [signedUpdateAt, updateAt, hki]
        · cases hfalse

/-- A signed asynchronous update strictly decreases the energy when the current spin
strictly disagrees with the sign of the local field. -/
theorem signed_update_energy_strictly_decreasing
    (p : Parameters Site) (τ : SignedState Site) (i : Site)
    (hstrict : (τ i = true ∧ signedLocalField p τ i < 0)
      ∨ (τ i = false ∧ 0 < signedLocalField p τ i)) :
    signedEnergyFn p (signedUpdateAt p i τ) < signedEnergyFn p τ := by
  rcases hstrict with htrue | hfalse
  · rcases htrue with ⟨hspin, hlt⟩
    have hupdate : signedUpdateAt p i τ = overwrite τ i false := by
      simp [signedUpdateAt, updateAt, not_le.mpr hlt,
        (show (TwoState.neg : Bool) = false by rfl)]
    have hτ : overwrite τ i true = τ := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [overwrite, hspin]
      · simp [overwrite, hji]
    have hrev :
        signedEnergyFn p (overwrite τ i false) - signedEnergyFn p (overwrite τ i true)
          = 2 * signedLocalField p τ i := by
      have := congrArg Neg.neg (signed_flip_energy_relation p τ i)
      simpa [neg_sub, neg_mul, neg_neg, mul_comm, mul_left_comm, mul_assoc] using this
    have hsub :
        signedEnergyFn p (overwrite τ i false) - signedEnergyFn p (overwrite τ i true) < 0 := by
      rw [hrev]
      exact mul_neg_of_pos_of_neg (by norm_num) hlt
    simpa [hupdate, hτ] using sub_lt_zero.mp hsub
  · rcases hfalse with ⟨hspin, hlt⟩
    have hupdate : signedUpdateAt p i τ = overwrite τ i true := by
      simp [signedUpdateAt, updateAt, le_of_lt hlt,
        (show (TwoState.pos : Bool) = true by rfl)]
    have hτ : overwrite τ i false = τ := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [overwrite, hspin]
      · simp [overwrite, hji]
    have hsub :
        signedEnergyFn p (overwrite τ i true) - signedEnergyFn p (overwrite τ i false) < 0 := by
      rw [signed_flip_energy_relation]
      exact mul_neg_of_neg_of_pos (by norm_num) hlt
    simpa [hupdate, hτ] using sub_lt_zero.mp hsub

end Signed

end Rebuild.Papers.BinarySpinFoundations
