import MCMC.Finite.TotalVariation

/-!
# Interval bounds for finite-state Markov chains

This module provides *fully rigorous* lemmas that turn **per-entry interval enclosures** of a
transition matrix into certified upper bounds on:

- pairwise row total-variation distances, and
- the Dobrushin coefficient `Matrix.dobrushinCoeff`.

This is designed to be the bridge point for executable certified numerics:
once an algorithm produces a matrix of intervals that enclose the true transition probabilities,
the results here let you feed those enclosures into the `MCMC.Finite` convergence theory.
-/

namespace MCMC.Finite
namespace IntervalBounds

open Matrix Finset
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pointwise enclosure of a real matrix `P` by lower/upper bound matrices `L ≤ P ≤ U`. -/
def Encloses (L U P : Matrix n n ℝ) : Prop :=
  ∀ i j, L i j ≤ P i j ∧ P i j ≤ U i j

/--
If `a ∈ [la, ua]` and `b ∈ [lb, ub]`, then `|a - b|` is bounded by the worst-case interval gap.

This is the key elementary inequality used to bound TV distances from interval data.
-/
lemma abs_sub_le_max_of_mem
    {a b la ua lb ub : ℝ}
    (hla : la ≤ a) (hau : a ≤ ua)
    (hlb : lb ≤ b) (hub : b ≤ ub) :
    |a - b| ≤ max (ua - lb) (ub - la) := by
  set M : ℝ := max (ua - lb) (ub - la)
  have h1 : a - b ≤ ua - lb := by
    have h1a : a - b ≤ ua - b := sub_le_sub_right hau b
    have h1b : ua - b ≤ ua - lb := by
      -- from `lb ≤ b`, we get `-b ≤ -lb`, hence `ua + (-b) ≤ ua + (-lb)`
      have : -b ≤ -lb := neg_le_neg hlb
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (add_le_add_left this ua)
    exact h1a.trans h1b
  have h2 : b - a ≤ ub - la := by
    have h2a : b - a ≤ ub - a := sub_le_sub_right hub a
    have h2b : ub - a ≤ ub - la := by
      have : -a ≤ -la := neg_le_neg hla
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (add_le_add_left this ub)
    exact h2a.trans h2b
  have hx_le : a - b ≤ M := (h1.trans (le_max_left _ _))
  have hneg_le : -M ≤ a - b := by
    -- from `b - a ≤ M`, negate to get `-M ≤ -(b - a) = a - b`
    have : -M ≤ -(b - a) := neg_le_neg (h2.trans (le_max_right _ _))
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  exact (abs_le.mpr ⟨hneg_le, hx_le⟩)

/--
Upper bound on the TV distance between two **rows** of the true matrix `P`, using only the
interval enclosure `L ≤ P ≤ U`.
-/
lemma tvDist_row_le_of_encloses
    {L U P : Matrix n n ℝ} (h : Encloses (n := n) L U P)
    (i i' : n) :
    Matrix.tvDist (Matrix.rowDist P i) (Matrix.rowDist P i')
      ≤ (∑ j : n, max (U i j - L i' j) (U i' j - L i j)) / 2 := by
  classical
  -- expand TV distance into a finite sum, then bound termwise using `abs_sub_le_max_of_mem`
  have hterm :
      ∀ j : n, |P i j - P i' j|
        ≤ max (U i j - L i' j) (U i' j - L i j) := by
    intro j
    have hij : L i j ≤ P i j ∧ P i j ≤ U i j := h i j
    have hi'j : L i' j ≤ P i' j ∧ P i' j ≤ U i' j := h i' j
    -- apply the scalar inequality with swapped lower bounds
    simpa [Matrix.rowDist] using
      (abs_sub_le_max_of_mem
        (a := P i j) (b := P i' j)
        (la := L i j) (ua := U i j)
        (lb := L i' j) (ub := U i' j)
        hij.1 hij.2 hi'j.1 hi'j.2)
  have hsum :
      (∑ j : n, |P i j - P i' j|)
        ≤ ∑ j : n, max (U i j - L i' j) (U i' j - L i j) := by
    refine Finset.sum_le_sum ?_
    intro j _
    simpa using hterm j
  -- divide by 2 (TV definition)
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have := (div_le_div_of_nonneg_right hsum (show (0 : ℝ) ≤ 2 by norm_num))
  simp at this
  exact this

/--
Define a computable-looking “interval Dobrushin coefficient bound” from enclosures `L,U`:
the supremum (over row pairs) of the interval-implied TV upper bounds.
-/
noncomputable def dobrushinBound (L U : Matrix n n ℝ) : ℝ :=
  sSup { d | ∃ i i' : n, d = (∑ j : n, max (U i j - L i' j) (U i' j - L i j)) / 2 }

/-- The true Dobrushin coefficient is bounded by the interval Dobrushin bound. -/
theorem dobrushinCoeff_le_of_encloses
    [Nonempty n] {L U P : Matrix n n ℝ} (h : Encloses (n := n) L U P) :
    Matrix.dobrushinCoeff P ≤ dobrushinBound (n := n) L U := by
  classical
  -- show any row-pair TV distance is ≤ the corresponding interval bound, hence ≤ the supremum
  refine csSup_le ?hne ?hupper
  · -- nonempty: pick an arbitrary row-pair
    let i0 : n := Classical.arbitrary n
    refine ⟨Matrix.tvDist (Matrix.rowDist P i0) (Matrix.rowDist P i0), ?_⟩
    exact ⟨i0, i0, rfl⟩
  · intro d hd
    rcases hd with ⟨i, i', rfl⟩
    -- show TV(row i, row i') ≤ corresponding bound ≤ supremum
    have htv :
        Matrix.tvDist (Matrix.rowDist P i) (Matrix.rowDist P i')
          ≤ (∑ j : n, max (U i j - L i' j) (U i' j - L i j)) / 2 :=
      tvDist_row_le_of_encloses (n := n) (L := L) (U := U) (P := P) h i i'
    have hleSup :
        (∑ j : n, max (U i j - L i' j) (U i' j - L i j)) / 2
          ≤ dobrushinBound (n := n) L U := by
      -- membership into the defining set for `sSup`
      have hmem :
          (∑ j : n, max (U i j - L i' j) (U i' j - L i j)) / 2
            ∈ { d | ∃ a b : n,
                d = (∑ j : n, max (U a j - L b j) (U b j - L a j)) / 2 } := by
        exact ⟨i, i', rfl⟩
      -- boundedness: finite range hence bounded above
      let f : (n × n) → ℝ :=
        fun p => (∑ j : n, max (U p.1 j - L p.2 j) (U p.2 j - L p.1 j)) / 2
      have hset_eq :
          { d | ∃ a b : n,
              d = (∑ j : n, max (U a j - L b j) (U b j - L a j)) / 2 }
            = Set.range f := by
        ext x; constructor
        · intro hx; rcases hx with ⟨a, b, rfl⟩; exact ⟨⟨a, b⟩, rfl⟩
        · intro hx; rcases hx with ⟨⟨a, b⟩, rfl⟩; exact ⟨a, b, rfl⟩
      have hbdd : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
      -- `le_csSup` on the range representation
      simpa [dobrushinBound, hset_eq, f] using (le_csSup hbdd (by simpa [hset_eq, f] using hmem))
    -- combine
    exact htv.trans hleSup

/--
Interval-driven TV contraction bound: if `L ≤ P ≤ U`, then the Dobrushin-based contraction
theorem holds with `dobrushinBound L U` (an explicit upper bound computable from the enclosure).
-/
theorem tvDist_contract_le_of_encloses
    [Nonempty n] {L U P : Matrix n n ℝ} (h : Encloses (n := n) L U P)
    (p q : n → ℝ) (hp1 : ∑ j, p j = 1) (hq1 : ∑ j, q j = 1) :
    Matrix.tvDist (fun j => ∑ k, p k * P k j) (fun j => ∑ k, q k * P k j)
      ≤ dobrushinBound (n := n) L U * Matrix.tvDist p q := by
  have hδ : Matrix.dobrushinCoeff P ≤ dobrushinBound (n := n) L U :=
    dobrushinCoeff_le_of_encloses (n := n) (L := L) (U := U) (P := P) h
  have htv :=
    (Matrix.tvDist_contract (n := n) (P := P) (p := p) (q := q) hp1 hq1)
  have htv_nonneg : 0 ≤ Matrix.tvDist p q := Matrix.tvDist_nonneg (n := n) p q
  -- upgrade `δ(P)` to the enclosure-based bound
  exact htv.trans (mul_le_mul_of_nonneg_right hδ htv_nonneg)

end IntervalBounds
end MCMC.Finite

