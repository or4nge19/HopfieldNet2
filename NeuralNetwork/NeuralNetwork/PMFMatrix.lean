import MCMC.Finite.Core
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.ENNReal.BigOperators

/-!
# PMF-to-matrix bridge (finite, discrete)

For finite state spaces, a Markov chain can be represented equivalently as:
- a function `κ : α → PMF α` (row kernels as probability mass functions), or
- a row-stochastic matrix `P : Matrix α α ℝ`.

This module provides a small adapter and proves stochasticity of the resulting matrix.

This is intended as a reusable building block for connecting `NeuralNetwork` kernels to
the `MCMC.Finite` Perron–Frobenius infrastructure.
-/

namespace NeuralNetwork
namespace PMFMatrix

open scoped BigOperators ENNReal

variable {α : Type} [Fintype α]

/-- Convert a `PMF`-valued kernel to an ℝ-valued transition matrix by `ENNReal.toReal`. -/
def pmfToMatrix (κ : α → PMF α) : Matrix α α ℝ :=
  fun x y => (κ x y).toReal

omit [Fintype α] in
lemma pmfToMatrix_nonneg (κ : α → PMF α) (x y : α) :
    0 ≤ pmfToMatrix (κ := κ) x y := by
  simp [pmfToMatrix]

lemma pmfToMatrix_row_sum (κ : α → PMF α) (x : α) :
    (∑ y : α, pmfToMatrix (κ := κ) x y) = 1 := by
  have h_ne_top : ∀ y : α, κ x y ≠ ∞ := fun y => (κ x).apply_ne_top y
  have h_toReal_finset :
      ENNReal.toReal ((Finset.univ : Finset α).sum (fun y => κ x y))
        = (Finset.univ : Finset α).sum (fun y => (κ x y).toReal) :=
    ENNReal.toReal_sum (s := (Finset.univ : Finset α))
      (f := fun y : α => κ x y) (by intro y _; exact h_ne_top y)
  have hsum_finset : ((Finset.univ : Finset α).sum (fun y => κ x y)) = (1 : ℝ≥0∞) := by
    simpa [tsum_fintype] using (PMF.tsum_coe (κ x))
  have hsum_toReal : ENNReal.toReal ((Finset.univ : Finset α).sum (fun y => κ x y)) = 1 := by
    simp [hsum_finset]
  have hrow : (Finset.univ : Finset α).sum (fun y => (κ x y).toReal) = 1 := by
    simpa [h_toReal_finset] using hsum_toReal
  simpa [pmfToMatrix] using hrow

/-- The induced matrix is row-stochastic (in the `MCMC.Finite` sense). -/
theorem pmfToMatrix_isStochastic [DecidableEq α] (κ : α → PMF α) :
    MCMC.Finite.IsStochastic (pmfToMatrix (κ := κ)) := by
  constructor
  · intro i j
    exact pmfToMatrix_nonneg (κ := κ) i j
  · intro i
    simpa using pmfToMatrix_row_sum (κ := κ) i

end PMFMatrix
end NeuralNetwork
