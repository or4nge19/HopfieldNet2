import HopfieldNet.CReals.CRealsFast
import MCMC.Finite.IntervalBoundsFast

/-!
# Building a `Ball` transition matrix from partial approximators

Many executable certified computations return **partial** approximators
`ℕ → Option Ball` (they may fail at low precision and succeed once enough precision is requested).

This file provides a small, fully-rigorous adapter:

- given `κ? : n → n → (ℕ → Option Ball)` and a precision index `m`,
  if all entries succeed at `m`, we extract a `Matrix n n Ball`.

This is useful for connecting fast, executable interval kernels to the MCMC interval-bound theory.
-/

namespace MCMC.Finite
namespace FastApproxMatrix

open Computable.Fast

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A partial, precision-indexed ball-valued approximator. -/
abbrev FastApprox : Type := ℕ → Option Ball

/--
Extract a `Ball` matrix at precision index `m` if all entries of `κ?` succeed at `m`.
-/
noncomputable def ballMatrixAt? (κ? : n → n → FastApprox) (m : ℕ) : Option (Matrix n n Ball) :=
by
  classical
  exact
    if h : ∀ i j : n, ∃ b : Ball, κ? i j m = some b then
      some (fun i j => Classical.choose (h i j))
    else
      none

theorem ballMatrixAt?_spec
    {κ? : n → n → FastApprox} {m : ℕ} {B : Matrix n n Ball}
    (hB : ballMatrixAt? (n := n) κ? m = some B) :
    ∀ i j : n, κ? i j m = some (B i j) := by
  classical
  by_cases h : ∀ i j : n, ∃ b : Ball, κ? i j m = some b
  · -- success case: `ballMatrixAt?` returns `some ...`
    simp [ballMatrixAt?, h] at hB
    cases hB
    intro i j
    simpa using (Classical.choose_spec (h i j))
  · -- failure case: contradiction, since `ballMatrixAt?` would be `none`
    simp [ballMatrixAt?, h] at hB

/--
If each entry-approximator encloses the corresponding real value (when it succeeds),
then the extracted `Ball` matrix encloses the full real matrix pointwise.
-/
theorem ballContainsReal_of_ballMatrixAt?
    {κ? : n → n → FastApprox} {m : ℕ} {B : Matrix n n Ball} {P : Matrix n n ℝ}
    (hB : ballMatrixAt? (n := n) κ? m = some B)
    (hκ : ∀ i j, ∀ b, κ? i j m = some b → IntervalBoundsFast.ballContainsReal b (P i j)) :
    ∀ i j, IntervalBoundsFast.ballContainsReal (B i j) (P i j) := by
  intro i j
  have hij : κ? i j m = some (B i j) := ballMatrixAt?_spec (n := n) (κ? := κ?) (m := m) (B := B) hB i j
  exact hκ i j (B i j) hij

end FastApproxMatrix
end MCMC.Finite

