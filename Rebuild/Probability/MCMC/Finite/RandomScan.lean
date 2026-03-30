import Rebuild.Probability.MCMC.Finite.Core

/-!
# Rebuild Finite MCMC Random Scan

Uniform random-scan mixing for finite families of transition matrices.
-/

set_option autoImplicit false

open Matrix Finset
open scoped BigOperators

namespace Rebuild.Probability.MCMC.Finite

variable {Update State : Type*} [Fintype Update] [Fintype State]

/-- Uniform random-scan average of a finite family of transition matrices. -/
noncomputable def randomScanMatrix (K : Update → TransitionMatrix State) :
    TransitionMatrix State :=
  fun x y => (∑ u : Update, K u x y) / (Fintype.card Update : ℝ)

omit [Fintype State] in
lemma randomScanMatrix_nonneg
    (K : Update → TransitionMatrix State)
    (hK_nonneg : ∀ u x y, 0 ≤ K u x y) (x y : State) :
    0 ≤ randomScanMatrix K x y := by
  unfold randomScanMatrix
  refine div_nonneg ?_ (by positivity)
  exact Finset.sum_nonneg (fun u _ => hK_nonneg u x y)

section NonemptyUpdate

variable [Nonempty Update]

theorem randomScanMatrix_isStochastic
    (K : Update → TransitionMatrix State)
    (hK_stoch : ∀ u, IsStochastic (K u)) :
    IsStochastic (randomScanMatrix K) := by
  constructor
  · intro x y
    exact randomScanMatrix_nonneg K (fun u x y => (hK_stoch u).1 x y) x y
  · intro x
    have hcard_pos : 0 < (Fintype.card Update : ℝ) := by
      exact_mod_cast (Nat.cast_pos.mpr Fintype.card_pos)
    calc
      ∑ y : State, randomScanMatrix K x y
          = (∑ y : State, ∑ u : Update, K u x y) / (Fintype.card Update : ℝ) := by
              simp [randomScanMatrix, div_eq_mul_inv, Finset.sum_mul]
      _ = (∑ u : Update, ∑ y : State, K u x y) / (Fintype.card Update : ℝ) := by
            congr 1
            simpa using
              (Finset.sum_comm
                (s := (Finset.univ : Finset State))
                (t := (Finset.univ : Finset Update))
                (f := fun y u => K u x y))
      _ = (∑ u : Update, (1 : ℝ)) / (Fintype.card Update : ℝ) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro u _
            simpa using (hK_stoch u).2 x
      _ = 1 := by
            field_simp [hcard_pos.ne']
            simp

end NonemptyUpdate

theorem randomScanMatrix_reversible
    (K : Update → TransitionMatrix State) {π : stdSimplex ℝ State}
    (hK_rev : ∀ u, IsReversible (K u) π) :
    IsReversible (randomScanMatrix K) π := by
  intro x y
  calc
    π.val x * randomScanMatrix K x y
        = (∑ u : Update, π.val x * K u x y) / (Fintype.card Update : ℝ) := by
            simp [randomScanMatrix, div_eq_mul_inv, Finset.mul_sum,
              mul_left_comm, mul_comm, mul_assoc]
    _ = (∑ u : Update, π.val y * K u y x) / (Fintype.card Update : ℝ) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro u _
          exact hK_rev u x y
    _ = π.val y * randomScanMatrix K y x := by
          simp [randomScanMatrix, div_eq_mul_inv, Finset.mul_sum,
            mul_left_comm, mul_comm, mul_assoc]

section NonemptyUpdate

variable [Nonempty Update]

theorem randomScanMatrix_stationary
    (K : Update → TransitionMatrix State) {π : stdSimplex ℝ State}
    (hK_stoch : ∀ u, IsStochastic (K u))
    (hK_rev : ∀ u, IsReversible (K u) π) :
    IsStationary (randomScanMatrix K) π :=
  IsReversible.isStationary
    (hP := randomScanMatrix_isStochastic K hK_stoch)
    (h_rev := randomScanMatrix_reversible K hK_rev)

noncomputable def randomScanChain [DecidableEq State] [Nonempty State]
    (K : Update → TransitionMatrix State) (π : stdSimplex ℝ State)
    (hK_stoch : ∀ u, IsStochastic (K u))
    (hK_rev : ∀ u, IsReversible (K u) π)
    (h_irred : Matrix.IsIrreducible (randomScanMatrix K))
    (h_prim : Matrix.IsPrimitive (randomScanMatrix K)) :
    FiniteChain State where
  transition := randomScanMatrix K
  invariant := π
  stochastic := randomScanMatrix_isStochastic K hK_stoch
  stationary := randomScanMatrix_stationary K hK_stoch hK_rev
  irreducible := h_irred
  primitive := h_prim

end NonemptyUpdate

end Rebuild.Probability.MCMC.Finite
