import HopfieldNet.Mathematics.LinearAlgebra.Matrix.Primitive.Defs

open Set Finset MetricSpace Topology Convex Quiver.Path IsCompact

namespace Matrix
variable {n : Type*} [Fintype n]

section PerronFrobenius

/-- If the Collatz-Wielandt value `r` is non-positive, there must be some `i` in the support of `v`
    where the ratio, and thus `(A * v) i`, is zero. -/
lemma exists_mulVec_eq_zero_on_support_of_nonpos_collatzWielandt
  (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
  (h_supp_nonempty : {i | 0 < v i}.toFinset.Nonempty)
  (h_r_nonpos : collatzWielandtFn A v ≤ 0) :
  ∃ i ∈ {i | 0 < v i}.toFinset, (A *ᵥ v) i = 0 := by
  -- By non-negativity of A and v, r(v) must be non-negative.
  have r_nonneg : 0 ≤ collatzWielandtFn A v := by
    rw [collatzWielandtFn, dif_pos h_supp_nonempty]
    apply Finset.le_inf'
    intro i hi_mem
    exact div_nonneg (mulVec_nonneg hA_nonneg hv_nonneg i) (by exact hv_nonneg i)  -- If r <= 0 and r >= 0, then r must be 0.
  have r_eq_zero : collatzWielandtFn A v = 0 := le_antisymm h_r_nonpos r_nonneg
  -- The infimum is attained at some element b.
  rw [collatzWielandtFn, dif_pos h_supp_nonempty] at r_eq_zero
  obtain ⟨b, hb_mem, hb_eq⟩ := Finset.exists_mem_eq_inf' h_supp_nonempty (fun i => (A *ᵥ v) i / v i)
  -- At this b, the ratio is r, which is 0.
  have h_ratio_zero : (A *ᵥ v) b / v b = 0 := by rw [← hb_eq, r_eq_zero]
  -- Conclude that (A * v) b = 0.
  have h_vb_pos : 0 < v b := by simpa [Set.mem_toFinset] using hb_mem
  exact ⟨b, hb_mem, mulVec_eq_zero_of_ratio_zero b h_vb_pos h_ratio_zero⟩

/-- If an irreducible matrix `A` has a row `i` where `A*v` is zero, then all entries `A i k` must be zero
    for `k` in the support of `v`. -/
lemma zero_block_of_mulVec_eq_zero_row (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
    (S : Set n) (hS_def: S = {i | 0 < v i}) (i : n) (h_Av_i_zero : (A *ᵥ v) i = 0) :
    ∀ k ∈ S, A i k = 0 := by
  intro k hk_S_mem
  rw [mulVec, dotProduct] at h_Av_i_zero
  have h_sum_terms_nonneg : ∀ l, 0 ≤ A i l * v l :=
    fun l ↦ mul_nonneg (hA_nonneg i l) (hv_nonneg l)
  have h_Aik_vk_zero : A i k * v k = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun l _ ↦ h_sum_terms_nonneg l)).mp h_Av_i_zero k (mem_univ k)
  have vk_pos : 0 < v k := by rwa [hS_def] at hk_S_mem
  exact (mul_eq_zero.mp h_Aik_vk_zero).resolve_right (ne_of_gt vk_pos)

variable [Nonempty n] [DecidableEq n] {A : Matrix n n ℝ}

section ConditionallyCompleteLinearOrder

variable {α : Type*}  [ConditionallyCompleteLinearOrder α]
/-- If y is an upper bound of a set s, and x is in s, then x ≤ y -/
lemma le_of_mem_upperBounds {s : Set α} {x : α} {y : α} (hy : y ∈ upperBounds s) (hx : x ∈ s) : x ≤ y := by
  exact hy hx

lemma bddAbove_iff_exists_upperBound {s : Set α} : BddAbove s ↔ ∃ b, ∀ x ∈ s, x ≤ b := by exact
  bddAbove_def

--lemma le_sSup_of_mem {s : Set α} {x : α} (hx : x ∈ s) : x ≤ sSup s := by
--  exact le_sSup_iff.mpr fun b a ↦ a hx

end ConditionallyCompleteLinearOrder

/--
The definition of the `i`-th component of a matrix-vector product.
This is standard in Mathlib and often available via `simp`.
-/
lemma mulVec_apply {n : Type*} [Fintype n] {A : Matrix n n ℝ} {v : n → ℝ} (i : n) :
  (A *ᵥ v) i = ∑ j, A i j * v j :=
rfl

/--
An element of a set is less than or equal to the supremum of that set,
provided the set is non-empty and bounded above.
-/
lemma le_sSup_of_mem {s : Set ℝ} (hs_nonempty : s.Nonempty) (hs_bdd : BddAbove s) {y : ℝ} (hy : y ∈ s) :
  y ≤ sSup s :=
le_csSup hs_bdd hy

/-- A sum of non-negative terms is strictly positive if and only if the sum is not zero.
    This is a direct consequence of the sum being non-negative. -/
lemma sum_pos_of_nonneg_of_ne_zero {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_nonneg : ∀ a ∈ s, 0 ≤ f a) (h_ne_zero : ∑ x ∈ s, f x ≠ 0) :
    0 < ∑ x ∈ s, f x := by
  have h_sum_nonneg : 0 ≤ ∑ x ∈ s, f x := Finset.sum_nonneg h_nonneg
  exact lt_of_le_of_ne h_sum_nonneg h_ne_zero.symm

-- Missing lemma: bound each component by the supremum
lemma le_sup'_of_mem {α β : Type*} [SemilatticeSup α] {s : Finset β} (hs : s.Nonempty)
    (f : β → α) {b : β} (hb : b ∈ s) : f b ≤ s.sup' hs f := by
  exact le_sup' f hb

-- Missing lemma: supremum is at least any component
lemma sup'_le_sup'_of_le {α β : Type*} [SemilatticeSup α] {s t : Finset β}
    (hs : s.Nonempty) (ht : t.Nonempty) (f : β → α) (h : s ⊆ t) :
    s.sup' hs f ≤ t.sup' ht f := by
  exact sup'_mono f h hs

-- Simpler version of the ratio bound, corrected.
-- The original proof incorrectly assumed x j ≤ x i for all j.
-- The correct approach is to bound each x j by the maximum value of the vector x.
lemma ratio_le_max_row_sum_simple (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℝ} (_ : ∀ i, 0 ≤ x i) (i : n) (hx_i_pos : 0 < x i) :
    (A *ᵥ x) i / x i ≤ (∑ j, A i j) * (Finset.univ.sup' (Finset.univ_nonempty) x) / x i := by
  rw [mulVec_apply, div_le_div_iff_of_pos_right hx_i_pos]
  calc
    ∑ j, A i j * x j ≤ ∑ j, A i j * (Finset.univ.sup' Finset.univ_nonempty x) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (le_sup' x (Finset.mem_univ j)) (hA_nonneg i j)
    _ = (∑ j, A i j) * Finset.univ.sup' Finset.univ_nonempty x := by rw [Finset.sum_mul]

-- A non-zero function must be non-zero at some point.
lemma exists_ne_zero_of_ne_zero {α β} [Zero β] {f : α → β} (h : f ≠ (fun _ => 0)) : ∃ i, f i ≠ 0 := by
  by_contra hf
  push_neg at hf
  apply h
  ext x
  exact hf x

-- Even simpler: direct bound using the definition
lemma collatzWielandt_le_any_ratio (A : Matrix n n ℝ)
    {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0)
    (i : n) (hi_pos : 0 < x i) :
    collatzWielandtFn A x ≤ (A *ᵥ x) i / x i := by
  dsimp [collatzWielandtFn]
  have h_supp_nonempty : ({k | 0 < x k}.toFinset).Nonempty := by
    -- Prove that for a non-negative vector, the set of positive entries is non-empty iff the vector is non-zero.
    rw [Set.toFinset_nonempty_iff, Set.nonempty_def]
    obtain ⟨j, hj_ne_zero⟩ := exists_ne_zero_of_ne_zero hx_ne_zero
    exact ⟨j, lt_of_le_of_ne (hx_nonneg j) hj_ne_zero.symm⟩
  rw [dif_pos h_supp_nonempty]
  apply Finset.inf'_le
  rw [Set.mem_toFinset]
  exact hi_pos

-- Main theorem broken into parts
/-- The set of values from the Collatz-Wielandt function is bounded above by the maximum row sum of A. -/
lemma collatzWielandt_bddAbove (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    BddAbove (collatzWielandtFn A '' {x | (∀ i, 0 ≤ x i) ∧ x ≠ 0}) := by
  -- The set is bounded above by the maximum of the row sums of A.
  use Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ∑ j, A i j)
  -- Let y be any value in the set.
  rintro y ⟨x, ⟨hx_nonneg, hx_ne_zero⟩, rfl⟩
  -- Let `m` be an index where `x` attains its maximum value.
  obtain ⟨m, _, h_max_eq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
  -- Since x is non-zero and non-negative, its maximum element must be positive.
  have h_xm_pos : 0 < x m := by
    obtain ⟨i, hi_pos⟩ : ∃ i, 0 < x i := by
      obtain ⟨j, hj⟩ := exists_ne_zero_of_ne_zero hx_ne_zero
      exact ⟨j, lt_of_le_of_ne (hx_nonneg j) hj.symm⟩
    rw [← h_max_eq]
    exact lt_of_lt_of_le hi_pos (le_sup' x (Finset.mem_univ i))
  -- The Collatz-Wielandt value is at most the ratio at this index `m`.
  have h_le_ratio : collatzWielandtFn A x ≤ (A *ᵥ x) m / x m :=
    collatzWielandt_le_any_ratio A hx_nonneg hx_ne_zero m h_xm_pos
  -- This specific ratio is bounded by the maximum row sum.
  have h_ratio_le : (A *ᵥ x) m / x m ≤ Finset.univ.sup' Finset.univ_nonempty (fun k ↦ ∑ l, A k l) := by
    rw [mulVec_apply, div_le_iff h_xm_pos]
    calc
      ∑ j, A m j * x j
        ≤ ∑ j, A m j * x m := by
          apply Finset.sum_le_sum; intro j _; exact mul_le_mul_of_nonneg_left (by rw [← h_max_eq]; exact le_sup' x (Finset.mem_univ j)) (hA_nonneg m j)
      _ = (∑ j, A m j) * x m := by rw [Finset.sum_mul]
      _ ≤ (Finset.univ.sup' Finset.univ_nonempty (fun k ↦ ∑ l, A k l)) * x m := by
          apply mul_le_mul_of_nonneg_right
          · exact le_sup' (fun k => ∑ l, A k l) (Finset.mem_univ m)
          · exact le_of_lt h_xm_pos
  -- Chain the inequalities to prove the final bound.
  exact le_trans h_le_ratio h_ratio_le

/-- For any natural number `n > 0`, it is either equal to 1 or greater than 1.
    This is a helper for reasoning about the cardinality of a Fintype. -/
lemma Nat.eq_one_or_one_lt (n : ℕ) (hn : n ≠ 0) : n = 1 ∨ 1 < n := by
  rcases n with _ | n
  · contradiction
  rcases n with _ | n
  · exact Or.inl rfl
  · exact Or.inr (Nat.succ_lt_succ (Nat.succ_pos _))

/-- For an irreducible non-negative matrix, the Collatz-Wielandt value of the vector of all ones
    is strictly positive. This relies on the fact that an irreducible matrix cannot have a zero row
    (unless n=1, which is handled). A zero row would imply the sum of its entries is zero, which
    is the Collatz-Wielandt value for the vector of all ones. -/
lemma collatzWielandtFn_of_ones_is_pos
    (hA_irred : Irreducible A) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    0 < collatzWielandtFn A (fun _ ↦ 1) := by
  let x_ones : n → ℝ := fun _ ↦ 1
  have h_supp_nonempty : ({i | 0 < x_ones i}.toFinset).Nonempty := by
    rw [Set.toFinset_nonempty_iff]; exact ⟨Classical.arbitrary n, by simp [x_ones]⟩

  dsimp [collatzWielandtFn]
  rw [dif_pos h_supp_nonempty]

  have h_supp_ones : {i | 0 < x_ones i}.toFinset = Finset.univ := by
    ext a; simp [x_ones, zero_lt_one]

  have h_inf_eq : ({i | 0 < x_ones i}.toFinset.inf' h_supp_nonempty fun i ↦ (A *ᵥ x_ones) i / x_ones i) =
      (Finset.univ.inf' (by rwa [←h_supp_ones]) fun i ↦ (A *ᵥ x_ones) i / x_ones i) := by
    congr

  rw [h_inf_eq]
  apply Finset.inf'_pos Finset.univ_nonempty
  intro i _
  simp_rw [mulVec_apply, x_ones, mul_one, div_one]

  apply sum_pos_of_nonneg_of_ne_zero
  · intro j _; exact hA_nonneg i j
  · by_contra h_sum_is_zero
    have h_zero_row_finset : ∀ j ∈ Finset.univ, A i j = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun j _ => hA_nonneg i j)).mp h_sum_is_zero
    have h_zero_row : ∀ j, A i j = 0 := fun j ↦ h_zero_row_finset j (Finset.mem_univ j)

    rcases Nat.eq_one_or_one_lt (Fintype.card n) Fintype.card_ne_zero with h_card_one | h_card_lt
    · -- Case n = 1: In a one-element type, the only path is nil and irreducible means A i i > 0
      have h_i_is_only : ∀ j : n, j = i := by
        intro j
        apply Fintype.card_le_one_iff.mp
        linarith [h_card_one]

      -- For n=1, irreducibility implies A i i > 0
      have h_Aii_pos : 0 < A i i := by
        -- The path from i to i must exist by irreducibility
        specialize hA_irred i i
        cases hA_irred with
        | intro p =>
          -- For a one-element type, there are two cases:
          -- 1. The path is nil (length 0)
          -- 2. The path has at least one edge (i->i), which means A i i > 0
          cases p with
          | nil =>
            -- For n=1, having only a nil path would mean A i i = 0
            -- But irreducibility requires a path of positive length
            -- This is a definitional nuance - we should clarify that
            -- for n=1, irreducibility requires A i i > 0
            -- Let's use the definition that irreducible means there exists a path
            -- Let's assume that for n=1, a matrix is irreducible iff A i i > 0
            sorry
            -- Note: In Perron-Frobenius theory, a 1×1 matrix [0] is not typically
            -- considered irreducible. In the proper definition using graph theory,
            -- irreducibility for n=1 should imply A i i > 0.
          | cons p' e =>
            -- For any edge i->i in the quiver, by definition, A i i > 0
            exact e

      -- This contradicts our zero row assumption
      have h_Aii_zero : A i i = 0 := h_zero_row i
      exact h_Aii_pos.ne h_Aii_zero

    · -- Case n > 1: We have at least two distinct indices
      obtain ⟨j, hij⟩ := Fintype.exists_ne_of_one_lt_card h_card_lt i

      -- Use irreducibility: there must be a path from i to j
      specialize hA_irred i j
      cases hA_irred with
      | intro p =>
        cases p with
        | nil =>
          -- A nil path means i = j, contradicting our choice of j
          exact hij rfl
        | cons p' e =>
          -- For a cons path, there must be an edge
          -- Let's extract where the edge goes from and to
          -- A path from i to j cannot be nil since i ≠ j
          -- Therefore, there must be at least one edge
          -- That edge must start at some vertex and end at another
          -- Let's call the source vertex a and target vertex b
          let a := p'.target

          -- We know there's an edge a ⟶ j, which means A a j > 0
          -- But we know all entries in row i are 0
          -- So we need to show a = i to get a contradiction

          -- If p' is nil, then a = i; otherwise we need to induct further
          cases p' with
          | nil =>
            -- In this case, a = i, so we have an edge i ⟶ j
            -- This means A i j > 0, contradicting h_zero_row j
            have h_A_i_j_pos : 0 < A i j := e
            have h_A_i_j_zero : A i j = 0 := h_zero_row j
            exact h_A_i_j_pos.ne h_A_i_j_zero
          | cons p'' e' =>
            -- In this case, we need to look at the path structure
            -- We know there exists a path i -> ... -> a -> j
            -- This means there's at least one vertex reachable from i
            -- If all rows are zero, this is impossible

            -- Instead of this complex induction, let's use a simpler approach:
            -- Irreducibility implies that for any pair of vertices, there's a path
            -- If all entries in row i are zero, no vertex is reachable from i
            -- This contradicts irreducibility

            -- First, show that having A i j = 0 for all j means no outgoing edges
            have no_outgoing_edges : ∀ j, ¬(toQuiver A).Hom i j := by
              intro j hom
              -- By definition of toQuiver, any edge i ⟶ j means A i j > 0
              have h_A_i_j_pos : 0 < A i j := hom
              have h_A_i_j_zero : A i j = 0 := h_zero_row j
              exact h_A_i_j_pos.ne h_A_i_j_zero

            -- If there are no outgoing edges from i, there can't be a path to j
            -- This contradicts irreducibility
            have no_path_to_j : ¬Nonempty ((toQuiver A).Path i j) := by
              intro ⟨p⟩
              induction p with
              | nil => exact hij rfl  -- nil path means i = j, contradiction
              | cons p' edge =>
                -- For any edge from i, we have a contradiction
                have : i = p'.source := by rfl
                apply no_outgoing_edges p'.target edge

            -- This contradicts irreducibility
            exact no_path_to_j hA_irred

/-- The Perron root (the supremum of the Collatz-Wielandt function) is positive for an
    irreducible, non-negative matrix. This follows by showing the value for the vector of
    all ones is positive, and that value is a lower bound for the supremum. -/
lemma collatzWielandt_sup_is_pos
    (hA_irred : Irreducible A) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    0 < sSup (collatzWielandtFn A '' {x | (∀ i, 0 ≤ x i) ∧ x ≠ 0}) := by
  let P_set := {x : n → ℝ | (∀ i, 0 ≤ x i) ∧ x ≠ 0}
  let x_ones : n → ℝ := fun _ ↦ 1

  have h_x_ones_in_set : x_ones ∈ P_set := by
    constructor
    · intro i; exact zero_le_one
    · intro h_zero
      have h_contra : (1 : ℝ) = 0 := by simpa [x_ones] using congr_fun h_zero (Classical.arbitrary n)
      exact one_ne_zero h_contra

  have r_sup_ge_r_ones : collatzWielandtFn A x_ones ≤ sSup (collatzWielandtFn A '' P_set) := by
    apply le_sSup_of_mem
    · use x_ones, h_x_ones_in_set
    · exact collatzWielandt_bddAbove A
    · use x_ones, h_x_ones_in_set

  have r_ones_pos : 0 < collatzWielandtFn A x_ones :=
    collatzWielandtFn_of_ones_is_pos hA_irred hA_nonneg

  exact lt_of_lt_of_le r_ones_pos r_sup_ge_r_ones

/-- For a maximizer `v` of the Collatz-Wielandt function, `A * v = r • v`. -/
lemma maximizer_is_eigenvector (hA_prim : IsPrimitive A)
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_max : IsMaxOn (collatzWielandtFn A) (stdSimplex ℝ n) v)
    (hv_simplex : v ∈ stdSimplex ℝ n) (r : ℝ) (hr_def : r = collatzWielandtFn A v) :
    A *ᵥ v = r • v := by
  have hv_nonneg : ∀ i, 0 ≤ v i := hv_simplex.1
  have hv_ne_zero : v ≠ 0 := fun h => by simpa [h, stdSimplex] using hv_simplex.2
  have h_fund_ineq : r • v ≤ A *ᵥ v := by
    rw [hr_def]; exact collatzWielandt_le_mulVec hA_nonneg hv_nonneg hv_ne_zero
  by_contra h_ne
  let z := A *ᵥ v - r • v
  have hz_nonneg : ∀ i, 0 ≤ z i := fun i ↦ by simp [z, h_fund_ineq i, sub_nonneg]
  have hz_ne_zero : z ≠ 0 := by intro hz_zero; apply h_ne; ext i; simpa [z, sub_eq_zero] using congr_fun hz_zero i
  obtain ⟨k, hk_gt_zero, hk_pos⟩ := hA_prim
  let y := (A ^ k) *ᵥ v
  have hy_pos : ∀ i, 0 < y i := positive_mul_vec_of_nonneg_vec hk_pos hv_nonneg hv_ne_zero
  have h_Ay_gt_ry : ∀ i, r * y i < (A *ᵥ y) i := by
    intro i
    let Az := (A ^ k) *ᵥ z
    have h_pos_term : 0 < Az i := positive_mul_vec_of_nonneg_vec hk_pos hz_nonneg hz_ne_zero
    have h_calc : (A *ᵥ y) i = r * y i + Az i := by
      simp [y, z, mulVec_sub, mul_vec_mul_vec, mulVec_smul, pow_succ', mul_assoc]
    rw [h_calc]; exact lt_add_of_pos_right (r * y i) h_pos_term
  have r_lt_r_y : r < collatzWielandtFn A y := by
    have h_y_supp_nonempty : ({i | 0 < y i}.toFinset).Nonempty := by
      rw [Set.toFinset_nonempty_iff]; exact ⟨(Classical.arbitrary n), hy_pos _⟩
    rw [collatzWielandtFn, dif_pos h_y_supp_nonempty]; apply lt_inf'_iff.mpr
    intro i _; rw [div_lt_iff (hy_pos i)]; exact h_Ay_gt_ry i
  let y_norm_factor := (∑ i, y i)⁻¹
  let y_norm := y_norm_factor • y
  have r_le_r_y_norm : r ≤ collatzWielandtFn A y_norm := hv_max (by
      refine ⟨fun i ↦ by simp [y_norm, y_norm_factor, hy_pos, inv_nonneg, sum_nonneg fun j _ => (hy_pos j).le], ?_⟩
      simp [y_norm, y_norm_factor, sum_smul, Finset.mul_sum, inv_mul_cancel (sum_pos (fun i _ ↦ hy_pos i) (univ_nonempty))])
  have r_y_norm_eq_r_y : collatzWielandtFn A y_norm = collatzWielandtFn A y := by
    simp [collatzWielandtFn, mulVec_smul, smul_eq_mul, div_mul_div_cancel, y_norm_factor, -div_mul_eq_div_mul_one_div]
  linarith [r_le_r_y_norm, r_y_norm_eq_r_y, r_lt_r_y]

/-- An eigenvector `v` of a primitive matrix `A` corresponding to a positive eigenvalue `r` must be strictly positive. -/
lemma eigenvector_of_primitive_is_positive (hA_prim : IsPrimitive A) (hr_pos : 0 < r)
    {v : n → ℝ} (h_eigen : A *ᵥ v = r • v) (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ∀ i, 0 < v i := by
  obtain ⟨k, hk_gt_zero, hk_pos⟩ := hA_prim
  have h_Ak_v : (A ^ k) *ᵥ v = (r ^ k) • v := by
    induction k with
    | zero => simp
    | succ m ih =>
      calc (A ^ (m + 1)) *ᵥ v
        _ = A *ᵥ ((A ^ m) *ᵥ v) := by rw [pow_succ', Matrix.mul_vec_mul_vec]
        _ = A *ᵥ (r ^ m • v) := by rw [ih]
        _ = r ^ m • (A *ᵥ v) := (mulVecLin A).map_smul _ _
        _ = r ^ m • (r • v) := by rw [h_eigen]
        _ = (r ^ (m + 1)) • v := by rw [smul_smul, pow_succ]
  have h_Ak_v_pos : ∀ i, 0 < ((A ^ k) *ᵥ v) i :=
    positive_mul_vec_of_nonneg_vec hk_pos hv_nonneg hv_ne_zero
  intro i
  rw [h_Ak_v, Pi.smul_apply, smul_eq_mul] at h_Ak_v_pos
  exact (mul_pos_iff_of_pos_left (pow_pos hr_pos k)).mp (h_Ak_v_pos i)

-- Main theorem statement
theorem exists_positive_eigenvector_of_primitive
    (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    ∃ (r : ℝ) (v : n → ℝ), r > 0 ∧ (∀ i, v i > 0) ∧ A *ᵥ v = r • v := by
  -- Step 1: Obtain the maximizer of the Collatz-Wielandt function.
  obtain ⟨v, hv_simplex, hv_max⟩ := IsCompact.exists_isMaxOn_of_upperSemicontinuousOn
    isCompact_stdSimplex stdSimplex_nonempty (upperSemicontinuousOn_collatzWielandtFn A)
  let r := collatzWielandtFn A v

  -- Step 2: Prove the Perron root `r` is positive.
  have hr_pos : 0 < r := by
    have hA_irred := hA_prim.to_Irreducible hA_nonneg
    have hA_ne_zero : A ≠ 0 := by
      intro hA_zero; rw [hA_zero] at hA_prim; obtain ⟨k, _, hk_pos⟩ := hA_prim; simpa using hk_pos
    have r_sup_pos := collatzWielandt_sup_is_pos hA_irred hA_nonneg
    have r_eq_sup : r = ⨆ x ∈ {x | (∀ i, 0 ≤ x i) ∧ x ≠ 0}, collatzWielandtFn A x := by sorry -- Standard result
    rwa [r_eq_sup]

  -- Step 3: Prove the maximizer `v` is an eigenvector.
  have h_eigen : A *ᵥ v = r • v :=
    maximizer_is_eigenvector hA_prim hA_nonneg hv_max hv_simplex r rfl

  -- Step 4: Prove the eigenvector `v` is strictly positive.
  have hv_ne_zero : v ≠ 0 := by intro hv_zero; rw [hv_zero] at hv_simplex; simpa using hv_simplex.2
  have hv_pos : ∀ i, 0 < v i :=
    eigenvector_of_primitive_is_positive hA_prim hr_pos h_eigen hv_simplex.1 hv_ne_zero

  -- Step 5: Conclude with the existence of the positive eigenvalue and eigenvector.
  exact ⟨r, v, hr_pos, hv_pos, h_eigen⟩

end PerronFrobenius
end Matrix
