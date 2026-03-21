import Rebuild.Models.BinarySpin.Pairwise

open scoped BigOperators
open Matrix

namespace Rebuild.Models.BinarySpin.Hopfield

variable {Site : Type*} [Fintype Site] [DecidableEq Site]
variable {PatternIdx : Type*} [Fintype PatternIdx]

/-- A pattern family is a collection of configurations, typically in {±1}.
We use `Site → ℝ` for the pattern values directly to match the spin space `ℝ`. -/
abbrev Patterns (Site PatternIdx : Type*) := PatternIdx → Site → ℝ

-- Helper to sum over patterns
noncomputable def hebbianCoupling (ξ : Patterns Site PatternIdx) (N : ℝ) : Matrix Site Site ℝ :=
  fun i j => if i = j then 0 else (1 / N) * ∑ μ, ξ μ i * ξ μ j

omit [Fintype Site] in
lemma hebbian_zero_diag (ξ : Patterns Site PatternIdx) (N : ℝ) (i : Site) :
    hebbianCoupling ξ N i i = 0 := by
  simp [hebbianCoupling]

omit [Fintype Site] in
lemma hebbian_symm (ξ : Patterns Site PatternIdx) (N : ℝ) :
    (hebbianCoupling ξ N).IsSymm := by
  ext i j
  change hebbianCoupling ξ N j i = hebbianCoupling ξ N i j
  simp only [hebbianCoupling]
  by_cases h : i = j
  · subst h; rfl
  · have h2 : j ≠ i := Ne.symm h
    simp only [h, h2, if_false]
    congr 1
    apply Finset.sum_congr rfl
    intro μ _
    ring

/-- Constructor mapping a Hopfield pattern family into the standard Pairwise.Parameters. -/
noncomputable def hopfieldParameters (ξ : Patterns Site PatternIdx) (N : ℝ) (field : Site → ℝ := fun _ => 0) : Pairwise.Parameters Site where
  coupling := hebbianCoupling ξ N
  externalField := field
  symmetric := hebbian_symm ξ N
  zero_diag := hebbian_zero_diag ξ N

end Rebuild.Models.BinarySpin.Hopfield
