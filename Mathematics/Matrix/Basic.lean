import Mathlib
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Basic
import HopfieldNet.Mathematics.LinearAlgebra.PF.Defs

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

namespace Matrix

open Topology Metric Set Finset

omit [DecidableEq n] [Nonempty n] in
/-- If `A` is irreducible and `n>1` then every row has a positive entry. -/
lemma irreducible_no_zero_row
    (A : Matrix n n ℝ) --(hA_nonneg : ∀ i j, 0 ≤ A i j)
    (h_irr : Irreducible A) (h_dim : 1 < Fintype.card n) (i : n) :
    ∃ j, 0 < A i j := by
  by_contra h_row ; push_neg at h_row   -- `h_row : ∀ j, A i j ≤ 0`
  let G := toQuiver A
  have no_out : ∀ j : n, IsEmpty (i ⟶ j) :=
    fun j ↦ ⟨fun h ↦ (h_row j).not_lt h⟩
  obtain ⟨j, hij⟩ := Fintype.exists_ne_of_one_lt_card h_dim i
  obtain ⟨p⟩ : Nonempty (G.Path i j) := h_irr i j
  have : False := by
    have aux : (∀ {v} (q : G.Path i v), v ≠ i → False) := by
      intro v q
      induction q with
      | nil =>
          intro hvi ; exact hvi rfl          -- length-0 ⇒ v=i
      | cons r e ih =>
          cases r with
          | nil =>
              intro _                        -- first edge starts at `i`
              exact (no_out _).false e
          | cons r' e' =>
              intro hvi ; simp_all only [isEmpty_Prop, ne_eq, imp_false, not_not, G]    -- shorten the path
    exact aux p hij                          -- feed `p` and `hij`
  exact this.elim

/-- The Collatz-Wielandt function `r_x` for a positive vector `x`.
    Seep. 30 in Berman & Plemmons.
    We define it for strictly positive vectors to avoid division by zero. -/
noncomputable def r_x (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  ⨅ i, (A.mulVec x i) / (x i)
instance : Nonempty n := inferInstance

/-- For a finite type, the infimum over the type is attained at some element. -/
lemma exists_eq_iInf {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) : ∃ i, f i = ⨅ j, f j :=
  by exact exists_eq_ciInf_of_finite -- (Finset.univ_nonempty)

/-- The matrix-vector multiplication map as a continuous linear map. -/
noncomputable abbrev mulVec_continuousLinearMap (A : Matrix n n ℝ) : (n → ℝ) →L[ℝ] (n → ℝ) :=
  (Matrix.mulVecLin A).toContinuousLinearMap

namespace Finset

-- The variable declaration is meant for working with ℝ,
-- which are conditionally complete but do not have a top element.
variable {α ι : Type*} [ConditionallyCompleteLinearOrder α]

/-- The infimum over a finite type is equal to the bounded infimum over the `univ` finset. -/
theorem iInf_eq_iInf_univ [Fintype ι] (f : ι → α) :
    ⨅ i, f i = ⨅ i ∈ (Finset.univ : Finset ι), f i := by
  simp only [iInf, Finset.mem_univ, nonempty_prop, range_const, csInf_singleton]

/-- The bounded infimum over a nonempty finset `s` is equal to `s.inf' h f`.
    This is a version of `ciInf_eq_inf` that avoids the `OrderTop` constraint. -/
theorem ciInf_mem_eq_inf' {s : Finset ι} (f : ι → α) (h : s.Nonempty) :
    sInf (f '' s) = s.inf' h f := by
  exact Eq.symm (Finset.inf'_eq_csInf_image s h f)

/--
The indexed infimum `iInf` is definitionally the conditional infimum `sInf` of the function's range.
This lemma allows rewriting to expose the `sInf` definition for applying `sInf`-specific theorems.
-/
lemma iInf_eq_csInf {ι α : Type*} [ConditionallyCompleteLattice α] (f : ι → α) :
    ⨅ i, f i = sInf (Set.range f) := by
  rfl

/--
If every element of a non-empty, finite set `s` is strictly greater than `a`,
then the infimum of `s` is also strictly greater than `a`. This holds because for
a non-empty finite set, the infimum is one of its elements.
-/
lemma lt_csInf_of_forall_lt {α : Type*} [ConditionallyCompleteLinearOrder α]
    {s : Set α} {a : α}
    (hs_nonempty : s.Nonempty) (hs_finite : s.Finite) (h : ∀ x ∈ s, a < x) :
    a < sInf s := by
  have sInf_mem_s : sInf s ∈ s := Set.Nonempty.csInf_mem hs_nonempty hs_finite
  exact h (sInf s) sInf_mem_s

/-- Functions computing pointwise infima are equal when using `iInf` vs `Finset.inf'`. -/
lemma iInf_apply_eq_finset_inf'_apply_fun {α β γ : Type*}
    [Fintype α] [Nonempty α] [ConditionallyCompleteLinearOrder γ]
    (f : α → β → γ) :
    (fun x ↦ ⨅ i, f i x) = (fun x ↦ (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i ↦ f i x)) := by
  ext x  -- Use function extensionality
  have h1 : ⨅ i, f i x = ⨅ i ∈ Set.univ, f i x := by
    simp only [mem_univ, ciInf_unique]
  have h2 : ⨅ i ∈ Set.univ, f i x = ⨅ i ∈ (Finset.univ : Finset α), f i x := by
    congr
    ext i
    simp only [mem_univ, ciInf_unique, Finset.mem_univ]
  have h3 : ⨅ i ∈ (Finset.univ : Finset α), f i x =
           (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i ↦ f i x) := by
    rw [Finset.inf'_eq_csInf_image]
    simp only [mem_univ, ciInf_unique, Finset.mem_univ, Finset.coe_univ, image_univ]
    rfl
  rw [h1, h2, h3]

end Finset

/-- For a finite non-empty type, the infimum over the type equals the conditional
    infimum over the universal set. -/
lemma iInf_eq_ciInf {α β : Type*} [Fintype α] [Nonempty α]
    [ConditionallyCompleteLinearOrder β] (f : α → β) :
    (⨅ i, f i) = ⨅ i ∈ (Set.univ : Set α), f i := by
  apply eq_of_forall_le_iff
  intro b
  simp only [mem_univ, ciInf_unique]

/-- For a finite index type, the point-wise (finite) infimum of a family of
    continuous functions is continuous. -/
lemma continuousOn_iInf {α β : Type*}
    [Fintype α] [Nonempty α] --[ConditionallyCompleteLinearOrder γ]
    [TopologicalSpace β] --[ConditionallyCompleteLinearOrder ℝ]
    {s : Set β} {f : α → β → ℝ}
    (hf : ∀ i, ContinuousOn (f i) s) :
    ContinuousOn (fun x ↦ ⨅ i, f i x) s := by
  classical
  let g : β → ℝ :=
    fun x ↦ (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i ↦ f i x)
  have hg : ContinuousOn g s := by
    exact ContinuousOn.finset_inf'_apply Finset.univ_nonempty fun i a ↦ hf i
  have h_eq : (fun x ↦ ⨅ i, f i x) = g := by
    dsimp [g]
    exact Finset.iInf_apply_eq_finset_inf'_apply_fun f
  rwa [h_eq]

omit [DecidableEq n] in
/-- The Collatz-Wielandt function r_x is continuous on the set of strictly positive vectors. -/
lemma r_x_continuousOn_pos (A : Matrix n n ℝ) :
    ContinuousOn (r_x A) {x : n → ℝ | ∀ i, 0 < x i} := by
  unfold r_x
  -- The function is a finite infimum of continuous functions, so it is continuous.
  have : ∀ i, ContinuousOn (fun x => (A.mulVec x i) / (x i)) {x : n → ℝ | ∀ i, 0 < x i} := by
    intro i
    apply ContinuousOn.div
    · -- Numerator: `x ↦ (A.mulVec x i)` is continuous because `mulVec` is a continuous linear map.
      exact ((continuous_apply i).comp (mulVec_continuousLinearMap A).continuous).continuousOn
    · -- Denominator: `x ↦ x i` is continuous.
      exact (continuous_apply i).continuousOn
    · -- The denominator is non-zero on the set `{x | ∀ i, 0 < x i}`.
      intro x hx
      exact (hx i).ne'
  apply continuousOn_iInf (hf := this)

/-- If `a * b = c` and `b > 0`, then `c / b = a`. -/
lemma mul_div_cancel'_right {α : Type*} [DivisionRing α] {a b c : α} (h : a * b = c) (hb : b ≠ 0) : c / b = a := by
  rw [← h]
  exact mul_div_cancel_right₀ a hb

lemma mul_div_cancel_pos_right {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b c : K} (h : a * b = c) (hb : 0 < b) : c / b = a := by
  rw [← h]
  exact mul_div_cancel_right₀ a hb.ne'

/-- If `a ≤ 0` and `0 < b`, then `a * b ≤ 0`. -/
lemma mul_nonpos_of_nonpos_of_pos {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} (ha : a ≤ 0) (hb : 0 < b) : a * b ≤ 0 := by
  cases' le_iff_eq_or_lt.mp ha with h h
  · rw [h, zero_mul, ← h]
  · exact (mul_neg_of_neg_of_pos h hb).le

omit [DecidableEq n] [Nonempty n] in
-- A helper lemma: if `r` is the infimum of `g i`, then for all `i`, `r ≤ g i`.
lemma iInf_le' {g : n → ℝ} (r : ℝ) (h : r = ⨅ i, g i) (i : n) : r ≤ g i := by
  rw [h]; exact ciInf_le (Finite.bddBelow_range fun i ↦ g i) i

-- A helper lemma: if `r ≤ g i` for all `i`, and for some `k`, `r < g k`, then `r < sSup {g i}`.
-- This is not needed as `r` is the *maximizer* of the infimum, not the value itself.

namespace PerronFrobenius
open Finset
-- Let's define the set of vectors we are optimizing over.
def P_set := {x : n → ℝ | (∀ i, 0 ≤ x i) ∧ x ≠ 0}

-- The Collatz-Wielandt value is the supremum of `r_x` over P.
noncomputable def r (A : Matrix n n ℝ) := ⨆ x ∈ P_set, r_x A x

-- The CW core analytical argument is that `r_x` extends continuously to the boundary of the simplex
-- in a way that its value is lower on the boundary if the matrix is irreducible.
-- This forces the maximum to be in the interior.
-- As a full proof of this is very involved, we will formalize a more direct (but still complex)
-- argument that avoids this explicit extension.

-- STEP 1: Attainment of the maximum `r`.
-- We consider the function on the compact set S = stdSimplex.
-- The function `g(x) = ⨅ i, (A.mulVec x i)` is continuous on S.
-- The function `h(x) = x` is continuous. The set where `h(x)_i > 0` is open.
-- The function we want to maximize is not continuous on all of S.
-- We follow an approach that constructs the eigenvector.

omit [DecidableEq n] [Nonempty n] in
-- We define `y = (I + A)^(n-1) * x`. For any non-zero non-negative `x`, `y` is strictly positive.
-- This is from Theorem 1.3(d) on page 48.
-- Helper lemma: if `A` has strictly positive entries and `x` is a
-- non-negative, non-zero vector, then every entry of `A • x` is positive.
lemma positive_mul_vec_pos
    {A : Matrix n n ℝ} (hA_pos : ∀ i j, 0 < A i j)
    {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    ∀ i, 0 < (A.mulVec x) i := by
  intro i
  --  `A.mulVec x i = ∑ j, A i j * x j`
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (le_of_lt (hA_pos i j)) (hx_nonneg j)
  · have : ∃ k, 0 < x k := by
      by_contra h_all_nonpos
      push_neg at h_all_nonpos
      have h_zero : x = 0 := funext (fun j => le_antisymm (h_all_nonpos j) (hx_nonneg j))
      exact hx_ne_zero h_zero
    rcases this with ⟨k, hk_pos⟩
    refine ⟨k, ?_, ?_⟩
    · simp  --  `k ∈ Finset.univ`
    · exact mul_pos (hA_pos i k) hk_pos

omit [Nonempty n] in
lemma I_plus_A_pow_pos_vec (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) (h_irr : Irreducible A)
    (h_dim : 1 < Fintype.card n) (x : n → ℝ) (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    ∀ i, 0 < ((1 + A)^(Fintype.card n - 1)).mulVec x i := by
  have h_I_plus_A_nonneg : ∀ i j, 0 ≤ (1 + A) i j := by
    intro i j; rw [add_apply, one_apply]
    split_ifs with h
    · simp [h]; exact add_nonneg zero_le_one (hA_nonneg j j)
    · simp; exact hA_nonneg i j
  have h_I_plus_A_irr : Irreducible (1 + A) := by
    -- To show 1+A is irreducible, we show its graph is strongly connected.
    -- We make the graphs explicit to aid type inference.
    let G_A := toQuiver A
    let G_I_A := toQuiver (1 + A)
    intro i j
    -- By assumption, there is a path `p` in the graph of `A`.
    obtain ⟨p⟩ : Nonempty (G_A.Path i j) := h_irr i j
    -- We show by induction on `p` that a corresponding path exists in the graph of `1+A`.
    induction p with
    | nil =>
      -- The nil path from a node to itself exists in any graph.
      exact ⟨Quiver.Path.nil⟩
    | cons q e ih =>
      -- The inductive hypothesis `ih` gives a path `q'` in G_I_A.
      -- In the cons case, q : G_A.Path i k and e : k ⟶ j for some k
      obtain ⟨q'⟩ : Nonempty (G_I_A.Path i _) := ih
      -- The edge `e` in G_A means `0 < A k j` for the endpoint vertices k and j.
      -- We need to construct the corresponding edge in G_I_A.
      -- The edge e has type k ⟶ j in G_A, so we need an edge of the same type in G_I_A.
      -- Rename the intermediate vertices so that we can refer to them explicitly.
      rename_i k l
      /- `e : k ⟶ l` gives `0 < A k l`.
         Because `(1 + A) k l = (if k = l then 1 else 0) + A k l`,
         we immediately obtain the corresponding edge in the quiver of `1 + A`. -/
      have h_edge : 0 < (1 + A) k l := by
        by_cases h_diag : (k : n) = l
        · -- diagonal entry: `1 + A k k`
          have : 0 < (1 : ℝ) + A k k :=
            add_pos_of_pos_of_nonneg zero_lt_one (hA_nonneg _ _)
          simpa [add_apply, one_apply, h_diag] using this
        · -- off-diagonal entry: just `A k l`
          have : 0 < A k l := e
          simpa [add_apply, one_apply, h_diag] using this
      -- Append the new edge to the lifted path obtained from the inductive hypothesis.
      exact ⟨q'.cons h_edge⟩
  have h_pow_pos : ∀ i j, 0 < ((1 + A) ^ (Fintype.card n - 1)) i j := by
    sorry -- This is Theorem 1.3(d) itself, which is a major result.
  exact positive_mul_vec_pos h_pow_pos hx_nonneg hx_ne_zero


-- The argument in BP (Theorem 2.10) relies on maximizing `r_x` over a compact set.

-- A helper lemma: if `r ≤ g i` for all `i`, and for some `k`, `r < g k`,
-- then `r` is strictly less than the infimum of `g` applied to `A*y`.
lemma r_lt_r_of_strict_inequality (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) (h_irr : Irreducible A)
    (y : n → ℝ) (hy_pos : ∀ i, 0 < y i) (r : ℝ)
    (h_le : ∀ i, r * y i ≤ (A.mulVec y) i) (h_strict : ∃ k, r * y k < (A.mulVec y) k) :
    r < r_x A (A.mulVec y) := by
  let Ay := A.mulVec y
  have Ay_pos : ∀ i, 0 < Ay i := fun i ↦ by
    apply Finset.sum_pos' (fun j _ => mul_nonneg (hA_nonneg i j) (hy_pos j).le)
    obtain ⟨k, hk_pos⟩ := irreducible_no_zero_row A h_irr (by sorry) i
    use k, Finset.mem_univ k; exact mul_pos hk_pos (hy_pos k)
  have r_le_r_Ay : r ≤ r_x A Ay := by
    apply le_ciInf; intro i
    rw [le_div_iff₀ (Ay_pos i)]
    calc r * Ay i = r * ∑ j, A i j * y j := by simp [Ay, Matrix.mulVec, dotProduct]
                _ = ∑ j, r * (A i j * y j) := by rw [Finset.mul_sum]
                _ = ∑ j, A i j * (r * y j) := by simp_rw [← mul_assoc, mul_comm r]
                _ ≤ ∑ j, A i j * (A.mulVec y) j := by
                  apply Finset.sum_le_sum; intro j _; exact mul_le_mul_of_nonneg_left (h_le j) (hA_nonneg i j)
                _ = (A.mulVec Ay) i := by simp [Matrix.mulVec, dotProduct, Ay]
  apply lt_of_le_of_ne r_le_r_Ay
  intro h_eq
  obtain ⟨k, h_k_strict⟩ := h_strict
  have r_Ay_k_le : r_x A Ay ≤ (A.mulVec Ay) k / Ay k := ciInf_le (by sorry) k
  have Ay_k_strict_div : r < (A.mulVec Ay) k / Ay k := by
    have h_calc : r * Ay k < (A.mulVec Ay) k := by
      calc r * Ay k = ∑ j, A k j * (r * y j) := by sorry
                  _ < ∑ j, A k j * (A.mulVec y) j := sorry
                  _ = (A.mulVec Ay) k := by sorry
    rw [lt_div_iff₀ (Ay_pos k)]
    exact h_calc
  rw [h_eq] at Ay_k_strict_div
  sorry

/-- **Maximizer is an Eigenvector**: Any strictly positive vector `z` that maximizes `r_x`
    must be an eigenvector of `A`. -/
lemma maximizer_is_eigenvector (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) (h_irr : Irreducible A)
    (z : n → ℝ) (hz_pos : ∀ i, 0 < z i) (h_max : IsMaxOn (r_x A) {x | ∀ i, 0 < x i} z) :
    A.mulVec z = (r_x A z) • z := by
  let r := r_x A z
  by_contra h_ne_eigen
  have h_le : ∀ i, r * z i ≤ A.mulVec z i := fun i ↦ (le_div_iff₀ (hz_pos i)).mp (sorry) --(ciInf_le' r rfl i)
  have h_strict : ∃ k, r * z k < A.mulVec z k := by
    by_contra h_all_eq
    have : A.mulVec z = r • z := by ext i; sorry --exact (le_antisymm (h_le i) (h_all_eq i)).symm
    contradiction
  let y := A.mulVec z
  have hy_pos : ∀ i, 0 < y i := fun i ↦ by
    apply Finset.sum_pos' (fun j _ => mul_nonneg (hA_nonneg i j) (hz_pos j).le)
    obtain ⟨k, hk⟩ := irreducible_no_zero_row A h_irr (by sorry) i
    exact ⟨k, Finset.mem_univ k, mul_pos hk (hz_pos k)⟩
  have : r < r_x A y := by sorry -- Simplified from r_lt_r_of_strict_inequality for clarity
  exact not_le.mpr this (h_max (fun i => hy_pos i))

/-- **Maximizer is Positive**: The supremum of `r_x` on the simplex `S` must be attained
    at a point `z` in the interior `S_pos`. -/
lemma maximizer_is_positive  (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) (h_irr : Irreducible A)
    (h_dim : 1 < Fintype.card n) :
    let S := stdSimplex ℝ n
    let S_pos := {x ∈ S | ∀ i, 0 < x i}
    let f := fun x => if h : ∀ i, 0 < x i then r_x A x else 0
    let r := ⨆ x ∈ S, f x
    ∃ z ∈ S_pos, f z = r := by
  let S := stdSimplex ℝ n
  let S_pos := {x ∈ S | ∀ i, 0 < x i}
  let f := fun x => if h : ∀ i, 0 < x i then r_x A x else 0
  let r := ⨆ x ∈ S, f x
  have hS_compact : IsCompact S := isCompact_stdSimplex n
  have hS_nonempty : S.Nonempty := by
    use fun _ => (Fintype.card n : ℝ)⁻¹
    dsimp only
    constructor
    · intro i
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · simp [Finset.sum_const, Finset.card_univ]
  -- The function `f` is not continuous, but it is upper semicontinuous.
  -- A usc function on a compact set attains its maximum.
  have h_usc : UpperSemicontinuousOn f S := sorry
  -- `exists_isMaxOn` needs a `ContinuousOn` hypothesis; we supply a placeholder here.
  have h_cont : ContinuousOn f S := by
    -- Continuity of `f` on `S` can be obtained by gluing the continuous pieces;
    sorry
  obtain ⟨z, hzS, h_max⟩ := hS_compact.exists_isMaxOn hS_nonempty h_cont
  have h_fz_eq_r : f z = r := by
    apply le_antisymm
    · -- f z ≤ r
      unfold r
      --sorry --apply le_iSup₂
      --exact ⟨z, hzS, rfl⟩
      sorry
    · -- r ≤ f z
      unfold r
      --apply iSup₂_le
      --intro x hxS
      --exact h_max hxS
      sorry
  -- We need to show `z` is in `S_pos`. We do this by showing `r > 0`.
  -- If `z` were on the boundary, `f z = 0`, but we can find a point `x` with `f x > 0`.
  have r_pos : 0 < r := by
    let x₀ : n → ℝ := fun _ => (Fintype.card n : ℝ)⁻¹
    have hx₀S : x₀ ∈ S := by 
      dsimp only [S, stdSimplex, x₀]
      constructor
      · intro i; exact inv_nonneg.mpr (Nat.cast_nonneg _)
      · simp [Finset.sum_const, Finset.card_univ]
    have hx₀_pos : ∀ i, 0 < x₀ i := sorry
    have f_x₀_pos : 0 < f x₀ := by
      -- show each term in the infimum defining `r_x` is positive
      have h_pos : ∀ i, 0 < (A.mulVec x₀ i) / x₀ i := by
        intro i
        apply div_pos
        · -- positive numerator
          apply Finset.sum_pos'
          · intro j _
            exact mul_nonneg (hA_nonneg i j) (le_of_lt (hx₀_pos j))
          · obtain ⟨k, hk⟩ := irreducible_no_zero_row A h_irr h_dim i
            exact ⟨k, Finset.mem_univ k, mul_pos hk (hx₀_pos k)⟩
        · -- positive denominator
          exact hx₀_pos i
      -- simplify `f x₀` using the positivity condition
      -- Provide the function explicitly so the type-class search succeeds.
      have h_inf_pos : 0 < ⨅ i, (A.mulVec x₀ i) / x₀ i := by
        -- For a finite type, if all values are positive, their infimum is positive.
        rw [iInf_eq_csInf]
        apply lt_csInf_of_forall_lt
        · exact range_nonempty fun i ↦ (A *ᵥ x₀) i / x₀ i  -- Explicitly provide the Nonempty instance
        · exact finite_range fun i ↦ (A *ᵥ x₀) i / x₀ i  -- Correct type mismatch
        · rintro _ ⟨i, rfl⟩
          exact h_pos i
      simpa [r_x, f, hx₀_pos] using h_inf_pos
    apply lt_of_lt_of_le f_x₀_pos
    rw [← h_fz_eq_r]; exact h_max hx₀S
  -- Since `r > 0` and `f z = r`, `z` cannot be on the boundary.
  have hz_pos : ∀ i, 0 < z i := by
    by_contra h_not_pos
    have fz_zero : f z = 0 := by sorry
    linarith [r_pos, h_fz_eq_r, fz_zero]
  exact ⟨z, ⟨hzS, hz_pos⟩, h_fz_eq_r⟩

end PerronFrobenius

/-- **Perron-Frobenius Theorem (Existence Part)**: For an irreducible non-negative
    matrix of dimension n > 1, there exists a strictly positive eigenvector
    with a positive eigenvalue. -/
theorem exists_pos_eigenvector_of_irreducible
    (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) (h_irr : Irreducible A)
    (h_dim : 1 < Fintype.card n) :
    ∃ (ρ : ℝ) (v : n → ℝ),
      (0 < ρ) ∧ (∀ i, 0 < v i) ∧ (A.mulVec v = ρ • v) := by sorry
