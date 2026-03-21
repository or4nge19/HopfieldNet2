import Rebuild.Models.Hopfield.Basic

open scoped BigOperators

set_option autoImplicit false

namespace Rebuild.Models.Hopfield

open Rebuild.Models.BinarySpin.Pairwise

abbrev Pattern (Site : Type*) := State Site
abbrev PatternFamily (PatternIndex Site : Type*) := PatternIndex → Pattern Site

section Finite

variable {PatternIndex Site : Type*}
variable [Fintype PatternIndex] [Fintype Site] [DecidableEq Site]

noncomputable def overlap (ξ : PatternFamily PatternIndex Site)
    (τ : State Site) (μ : PatternIndex) : ℝ :=
  ∑ i, spinValue (ξ μ i) * spinValue (τ i)

omit [Fintype PatternIndex] [DecidableEq Site] in
lemma self_overlap (ξ : PatternFamily PatternIndex Site) (μ : PatternIndex) :
    overlap ξ (ξ μ) μ = Fintype.card Site := by
  calc
    overlap ξ (ξ μ) μ = ∑ i : Site, (1 : ℝ) := by
      unfold overlap
      apply Finset.sum_congr rfl
      intro i _
      rcases ξ μ i <;> simp [spinValue]
    _ = Fintype.card Site := by
      simp

noncomputable def hebbianEntry (ξ : PatternFamily PatternIndex Site) (i j : Site) : ℝ :=
  if i = j then 0 else
    (∑ μ, spinValue (ξ μ i) * spinValue (ξ μ j)) / (Fintype.card PatternIndex : ℝ)

noncomputable def hebbianCoupling (ξ : PatternFamily PatternIndex Site) : Matrix Site Site ℝ :=
  fun i j => hebbianEntry ξ i j

omit [Fintype Site] in
lemma hebbianCoupling_symmetric (ξ : PatternFamily PatternIndex Site) :
    (hebbianCoupling ξ).IsSymm := by
  ext i j
  by_cases hij : i = j
  · simp [hebbianCoupling, hebbianEntry, hij]
  · have hji : j ≠ i := by
      intro hjiEq
      exact hij hjiEq.symm
    simp [Matrix.transpose_apply, hebbianCoupling, hebbianEntry, hij, hji, mul_comm]

omit [Fintype Site] in
lemma hebbianCoupling_zero_diag (ξ : PatternFamily PatternIndex Site) (i : Site) :
    hebbianCoupling ξ i i = 0 := by
  simp [hebbianCoupling, hebbianEntry]

noncomputable def parametersOfPatterns (ξ : PatternFamily PatternIndex Site)
    (externalField : Site → ℝ := fun _ => 0) : Parameters Site where
  coupling := hebbianCoupling ξ
  externalField := externalField
  symmetric := hebbianCoupling_symmetric ξ
  zero_diag := hebbianCoupling_zero_diag ξ

end Finite

end Rebuild.Models.Hopfield
