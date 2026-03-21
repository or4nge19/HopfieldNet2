import Rebuild.Bridges.HopfieldPatternsToGibbs
import Rebuild.Papers.BinarySpinFoundations

/-!
# Hopfield Foundations

Paper-facing results for the canonical Hopfield layer.
-/

set_option autoImplicit false

namespace Rebuild.Papers.HopfieldFoundations

open Rebuild.Bridges
open Rebuild.Papers.BinarySpinFoundations
open Rebuild.Models.Hopfield

section Finite

variable {PatternIndex Site : Type*}
variable [Fintype PatternIndex] [Fintype Site] [DecidableEq Site]

/-- A stored pattern has maximal self-overlap under the signed-spin encoding. -/
theorem stored_pattern_self_overlap {PatternIndex Site : Type*} [Fintype Site]
    (ξ : PatternFamily PatternIndex Site) (μ : PatternIndex) :
    overlap ξ (ξ μ) μ = Fintype.card Site :=
  self_overlap ξ μ

/-- The Hebbian coupling built from a family of patterns is symmetric. -/
theorem hebbian_coupling_symmetric {PatternIndex Site : Type*}
    [Fintype PatternIndex] [DecidableEq Site] (ξ : PatternFamily PatternIndex Site) :
    (hebbianCoupling ξ).IsSymm :=
  hebbianCoupling_symmetric ξ

/-- The Hebbian coupling has zero diagonal, matching the canonical pairwise model. -/
theorem hebbian_coupling_zero_diag {PatternIndex Site : Type*}
    [Fintype PatternIndex] [DecidableEq Site]
    (ξ : PatternFamily PatternIndex Site) (i : Site) :
    hebbianCoupling ξ i i = 0 :=
  hebbianCoupling_zero_diag ξ i

/-- The canonical Hebbian parameters satisfy the pairwise model symmetry axiom. -/
theorem hebbianParameters_symmetric
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0) :
    (hebbianParameters ξ externalField).coupling.IsSymm :=
  hebbian_coupling_symmetric ξ

/-- The canonical Hebbian parameters satisfy the pairwise model zero-diagonal axiom. -/
theorem hebbianParameters_zero_diag
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0) (i : Site) :
    (hebbianParameters ξ externalField).coupling i i = 0 :=
  hebbian_coupling_zero_diag ξ i

/-- In a Hebbian Hopfield model, overwriting site `i` does not change its own local field. -/
theorem hebbian_localField_self_overwrite_invariant
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0)
    (τ : State Site) (i : Site) (s : Spin) :
    localField (hebbianParameters ξ externalField) (Function.update τ i s) i
      = localField (hebbianParameters ξ externalField) τ i := by
  simpa [Rebuild.Models.BinarySpin.Pairwise.overwrite]
    using localField_self_overwrite_invariant
      Rebuild.Core.TwoStateEncoding.boolSigned (hebbianParameters ξ externalField) τ i s

/-- The canonical asynchronous Hebbian single-site update is idempotent. -/
theorem hebbian_update_idempotent
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0)
    (i : Site) (τ : State Site) :
    hebbianUpdateAt ξ externalField i (hebbianUpdateAt ξ externalField i τ)
      = hebbianUpdateAt ξ externalField i τ := by
  simpa [hebbianUpdateAt]
    using update_idempotent
      Rebuild.Core.TwoStateEncoding.boolSigned (hebbianParameters ξ externalField) i τ

/-- For the canonical Hebbian Hopfield model, the field contribution to the one-site
true/false overwrite energy difference is exactly twice the external field. -/
theorem hebbian_signed_field_term_flip_relation
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0)
    (τ : State Site) (i : Site) :
    Rebuild.Models.BinarySpin.Pairwise.fieldTerm Rebuild.Core.TwoStateEncoding.boolSigned
        (hebbianParameters ξ externalField) (Function.update τ i true)
      - Rebuild.Models.BinarySpin.Pairwise.fieldTerm Rebuild.Core.TwoStateEncoding.boolSigned
          (hebbianParameters ξ externalField) (Function.update τ i false)
      = 2 * externalField i := by
  simpa [Rebuild.Models.BinarySpin.Pairwise.overwrite]
    using Rebuild.Papers.BinarySpinFoundations.signed_field_term_flip_relation
      (hebbianParameters ξ externalField) τ i

/-- In the canonical Hebbian Hopfield model, the signed-spin local field is invariant
under overwriting the site being tested. -/
theorem hebbian_signed_localField_self_overwrite_invariant
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0)
    (τ : State Site) (i : Site) (s : Spin) :
    Rebuild.Models.BinarySpin.Pairwise.signedLocalField
        (hebbianParameters ξ externalField) (Function.update τ i s) i
      = Rebuild.Models.BinarySpin.Pairwise.signedLocalField
          (hebbianParameters ξ externalField) τ i := by
  simpa [Rebuild.Models.BinarySpin.Pairwise.overwrite]
    using Rebuild.Papers.BinarySpinFoundations.signed_localField_self_overwrite_invariant
      (hebbianParameters ξ externalField) τ i s

/-- For the canonical Hebbian Hopfield model, the true/false overwrite energy difference
is `-2` times the signed local field. -/
theorem hebbian_signed_flip_energy_relation
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0)
    (τ : State Site) (i : Site) :
    Rebuild.Models.BinarySpin.Pairwise.signedEnergyFn
        (hebbianParameters ξ externalField) (Function.update τ i true)
      - Rebuild.Models.BinarySpin.Pairwise.signedEnergyFn
          (hebbianParameters ξ externalField) (Function.update τ i false)
      = -2 * Rebuild.Models.BinarySpin.Pairwise.signedLocalField
          (hebbianParameters ξ externalField) τ i := by
  simpa [Rebuild.Models.BinarySpin.Pairwise.overwrite]
    using Rebuild.Papers.BinarySpinFoundations.signed_flip_energy_relation
      (hebbianParameters ξ externalField) τ i

/--
Any future proof of the signed Hebbian flip-energy identity immediately yields the
expected order implications for the positive and negative single-site overwrites.
-/
theorem hebbian_energy_order_from_flip_id
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0)
    {τPos τNeg : State Site} {κ L : ℝ}
    (hdiff : hebbianEnergy ξ externalField τPos - hebbianEnergy ξ externalField τNeg = -κ * L)
    (hκ : 0 ≤ κ) :
    (0 ≤ L → hebbianEnergy ξ externalField τPos ≤ hebbianEnergy ξ externalField τNeg) ∧
    (L ≤ 0 → hebbianEnergy ξ externalField τNeg ≤ hebbianEnergy ξ externalField τPos) :=
by
  constructor
  · intro hL
    have hκL : 0 ≤ κ * L := mul_nonneg hκ hL
    have hsub : hebbianEnergy ξ externalField τPos - hebbianEnergy ξ externalField τNeg ≤ 0 := by
      rw [hdiff, neg_mul]
      exact neg_nonpos.mpr hκL
    exact sub_nonpos.mp hsub
  · intro hL
    have hκL : κ * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ hL
    have hrev : hebbianEnergy ξ externalField τNeg - hebbianEnergy ξ externalField τPos = κ * L := by
      have := congrArg Neg.neg hdiff
      simpa [neg_sub, neg_mul, neg_neg] using this
    have hsub : hebbianEnergy ξ externalField τNeg - hebbianEnergy ξ externalField τPos ≤ 0 := by
      rw [hrev]
      exact hκL
    exact sub_nonpos.mp hsub

/-- A single canonical asynchronous Hebbian Hopfield update never increases the energy. -/
theorem hebbian_update_energy_nonincreasing
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0)
    (τ : State Site) (i : Site) :
    hebbianEnergy ξ externalField (hebbianUpdateAt ξ externalField i τ)
      ≤ hebbianEnergy ξ externalField τ := by
  simpa [hebbianEnergy, hebbianUpdateAt]
    using Rebuild.Papers.BinarySpinFoundations.signed_update_energy_nonincreasing
      (hebbianParameters ξ externalField) τ i

/-- Exact sitewise fixed-point criterion for the canonical Hebbian asynchronous update. -/
theorem hebbian_update_eq_self_iff
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0)
    (τ : State Site) (i : Site) :
    hebbianUpdateAt ξ externalField i τ = τ ↔
      (τ i = true ∧ localField (hebbianParameters ξ externalField) τ i ≥ 0)
        ∨ (τ i = false ∧ localField (hebbianParameters ξ externalField) τ i < 0) := by
  simpa [hebbianUpdateAt, localField]
    using Rebuild.Papers.BinarySpinFoundations.signed_update_eq_self_iff
      (hebbianParameters ξ externalField) τ i

/-- A canonical Hebbian asynchronous update strictly decreases the energy when the
current spin strictly disagrees with the sign of the local field. -/
theorem hebbian_update_energy_strictly_decreasing
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0)
    (τ : State Site) (i : Site)
    (hstrict : (τ i = true ∧ localField (hebbianParameters ξ externalField) τ i < 0)
      ∨ (τ i = false ∧ 0 < localField (hebbianParameters ξ externalField) τ i)) :
    hebbianEnergy ξ externalField (hebbianUpdateAt ξ externalField i τ)
      < hebbianEnergy ξ externalField τ := by
  simpa [hebbianEnergy, hebbianUpdateAt, localField]
    using Rebuild.Papers.BinarySpinFoundations.signed_update_energy_strictly_decreasing
      (hebbianParameters ξ externalField) τ i hstrict

end Finite

end Rebuild.Papers.HopfieldFoundations
