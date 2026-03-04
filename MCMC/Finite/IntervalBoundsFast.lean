import HopfieldNet.CReals.CRealsFast
import MCMC.Finite.IntervalBounds

/-!
# Interval bounds from `Computable.Fast.Ball`

This module connects the executable interval type `Computable.Fast.Ball` (dyadic balls) to the
generic interval-bound lemmas in `MCMC.Finite.IntervalBounds`.

It is *fully rigorous*: the only assumption is a per-entry enclosure hypothesis
`ballContainsReal (B i j) (P i j)`.
-/

namespace MCMC.Finite
namespace IntervalBoundsFast

open Matrix
open scoped BigOperators

open Computable.Fast

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Lower endpoint of a ball as a real number (via `ℚ`). -/
noncomputable def ballLoReal (b : Ball) : ℝ := (b.lo.toRat : ℝ)

/-- Upper endpoint of a ball as a real number (via `ℚ`). -/
noncomputable def ballHiReal (b : Ball) : ℝ := (b.hi.toRat : ℝ)

/-- Real-interval semantics for `Ball`. -/
noncomputable def ballContainsReal (b : Ball) (x : ℝ) : Prop :=
  ballLoReal b ≤ x ∧ x ≤ ballHiReal b

/-- Convert a `Ball`-matrix into lower/upper bound matrices. -/
noncomputable def boundsFromBallMatrix (B : Matrix n n Ball) : Matrix n n ℝ × Matrix n n ℝ :=
  (fun i j => ballLoReal (B i j), fun i j => ballHiReal (B i j))

theorem encloses_of_ballContainsReal
    {B : Matrix n n Ball} {P : Matrix n n ℝ}
    (hB : ∀ i j, ballContainsReal (B i j) (P i j)) :
    MCMC.Finite.IntervalBounds.Encloses
      (n := n)
      (boundsFromBallMatrix (n := n) B).1
      (boundsFromBallMatrix (n := n) B).2
      P := by
  intro i j
  have := hB i j
  exact this

/--
Dobrushin coefficient bound obtained from a `Ball`-matrix enclosure of `P`.
-/
theorem dobrushinCoeff_le_of_ballMatrix
    [Nonempty n] {B : Matrix n n Ball} {P : Matrix n n ℝ}
    (hB : ∀ i j, ballContainsReal (B i j) (P i j)) :
    Matrix.dobrushinCoeff P
      ≤ MCMC.Finite.IntervalBounds.dobrushinBound
          (n := n)
          (boundsFromBallMatrix (n := n) B).1
          (boundsFromBallMatrix (n := n) B).2 := by
  have hEncl :
      MCMC.Finite.IntervalBounds.Encloses
        (n := n)
        (boundsFromBallMatrix (n := n) B).1
        (boundsFromBallMatrix (n := n) B).2
        P :=
    encloses_of_ballContainsReal (n := n) (B := B) (P := P) hB
  exact MCMC.Finite.IntervalBounds.dobrushinCoeff_le_of_encloses (n := n) (L := _) (U := _) (P := P) hEncl

/--
One-step TV contraction bound obtained from a `Ball`-matrix enclosure of `P`.
-/
theorem tvDist_contract_le_of_ballMatrix
    [Nonempty n] {B : Matrix n n Ball} {P : Matrix n n ℝ}
    (hB : ∀ i j, ballContainsReal (B i j) (P i j))
    (p q : n → ℝ) (hp1 : ∑ j, p j = 1) (hq1 : ∑ j, q j = 1) :
    Matrix.tvDist (fun j => ∑ k, p k * P k j) (fun j => ∑ k, q k * P k j)
      ≤ MCMC.Finite.IntervalBounds.dobrushinBound
          (n := n)
          (boundsFromBallMatrix (n := n) B).1
          (boundsFromBallMatrix (n := n) B).2
          * Matrix.tvDist p q := by
  have hEncl :
      MCMC.Finite.IntervalBounds.Encloses
        (n := n)
        (boundsFromBallMatrix (n := n) B).1
        (boundsFromBallMatrix (n := n) B).2
        P :=
    encloses_of_ballContainsReal (n := n) (B := B) (P := P) hB
  simpa using
    (MCMC.Finite.IntervalBounds.tvDist_contract_le_of_encloses
      (n := n) (L := (boundsFromBallMatrix (n := n) B).1) (U := (boundsFromBallMatrix (n := n) B).2)
      (P := P) hEncl p q hp1 hq1)

end IntervalBoundsFast
end MCMC.Finite

