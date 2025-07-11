import HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Uniqueness

open Quiver.Path

namespace Matrix
open Quiver

open CollatzWielandt
variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
variable {A : Matrix n n ℝ}


/-- **Perron–Frobenius, irreducible case (Existence part)**
If `A` is a non-negative irreducible matrix, then there exists a strictly positive eigenvalue `r > 0`
and a strictly positive eigenvector `v` (`∀ i, 0 < v i`) such that `A *ᵥ v = r • v`.

The proof uses the auxiliary matrix `B = 1 + A`, which is primitive, to apply the Perron-Frobenius theorem
for primitive matrices and translate the result back to `A`. -/
theorem exists_positive_eigenvector_of_irreducible
    (hA_irred : Irreducible A) :
    ∃ (r : ℝ) (v : n → ℝ),
      0 < r ∧ (∀ i, 0 < v i) ∧ A *ᵥ v = r • v := by
  -- 1.  We add the identity: `B := 1 + A`.
  let B : Matrix n n ℝ := 1 + A
  -- 1a.  Non-negativity of `B`.
  have hB_nonneg : ∀ i j, 0 ≤ B i j := by
    intro i j
    by_cases h_eq : i = j
    · subst h_eq
      have : (0 : ℝ) ≤ 1 + A i i := by
        have hAi : 0 ≤ A i i := hA_irred.1 i i
        linarith
      simpa [B] using this
    · have : 0 ≤ A i j := hA_irred.1 i j
      simpa [B, h_eq] using this
  -- 1b.  Positive diagonal entries of `B`.
  have hB_diag_pos : ∀ i, 0 < B i i := by
    intro i
    have : (0 : ℝ) < 1 + A i i := by
      have hAi : 0 ≤ A i i := hA_irred.1 i i
      linarith
    simpa [B] using this
  -- 1c.  `B` is irreducible.
  have hB_irred : Irreducible B := by
    rcases hA_irred with ⟨hA_nonneg, hA_conn⟩
    refine ⟨hB_nonneg, ?_⟩
    intro i j
    --  obtain an `A`-path.
    rcases hA_conn i j with ⟨⟨pA, hpA_len⟩⟩
    --  Every arrow of `A` is an arrow of `B`.
    letI GA : Quiver n := toQuiver A
    letI GB : Quiver n := toQuiver B
    --  Map a single arrow.
    have arrow_map :
        ∀ {u v : n}, GA.Hom u v → GB.Hom u v := by
      intro u v h_uv
      change 0 < B u v
      by_cases h_eq : u = v
      · subst h_eq
        have : (0 : ℝ) < 1 + A u u := by
          have : (0 : ℝ) < A u u := h_uv
          linarith
        simpa [B] using this
      · simpa [B, h_eq] using h_uv
    --  Lift a whole path.
    have rec_path : ∀ {u v : n}, GA.Path u v → GB.Path u v := by
      intro u v q
      induction q with
      | nil            => exact .nil
      | cons q' e ih   => exact .cons ih (arrow_map e)
    let loop : Path i i := (Path.nil : Path i i).cons (hB_diag_pos i)
    let pB : Path i j := loop.comp (rec_path pA)
    have hpB_len : pB.length > 0 := by
      rw [@length_comp]
      simp only [le_refl, gt_iff_lt, add_pos_iff, List.Nat.eq_of_le_zero, B]
      simp_all only [add_apply, le_refl, gt_iff_lt, cons_eq_comp_toPath, nil_comp, length_toPath, Nat.lt_one_iff,
        pos_of_gt, true_or, B, GA, GB, loop]
    exact ⟨⟨pB, hpB_len⟩⟩
  -- 1d.  `B` is primitive.
  have hB_prim : IsPrimitive B :=
    IsPrimitive.of_irreducible_pos_diagonal B hB_nonneg hB_irred hB_diag_pos
  -- 2.  Primitive Perron–Frobenius applied to `B`.
  obtain ⟨rB, v, hrB_pos, hv_pos, h_eig_B⟩ :=
    exists_positive_eigenvector_of_primitive (A := B) hB_prim hB_nonneg
  -- 3.  We translate the eigen-relation for `B` to one for `A`.
  have h_eig_A : A *ᵥ v = (rB - 1) • v := by
    have h_exp : v + A *ᵥ v = rB • v := by
      simpa [B, add_mulVec, one_mulVec] using h_eig_B
    have : A *ᵥ v = rB • v - v := eq_sub_of_add_eq' h_exp
    simpa [one_smul, sub_smul] using this
  -- 4.  We show that `rB - 1 > 0`.
  classical
  letI GA : Quiver n := toQuiver A
  -- 4a.  We find a positive entry of `A`.
  have h_pos_entry : ∃ i j, 0 < A i j := by
    let i₀ : n := Classical.arbitrary n
    rcases hA_irred.2 i₀ i₀ with ⟨⟨p₀, hp₀_len⟩⟩
    have h_pos_len : p₀.length > 0 := hp₀_len
    rcases Quiver.Path.path_decomposition_first_edge p₀ h_pos_len with
      ⟨j, e, -, -, -⟩
    exact ⟨i₀, j, e⟩
  rcases h_pos_entry with ⟨i₀, j₀, hA_pos⟩
  -- 4b.  The `i₀`-component of `A * v` is positive.
  have hAv_i₀_pos : 0 < (A *ᵥ v) i₀ := by
    have hvj₀_pos : 0 < v j₀ := hv_pos j₀
    have h_nonneg :
        ∀ k ∈ (Finset.univ : Finset n), 0 ≤ A i₀ k * v k := by
      intro k _
      exact mul_nonneg (hA_irred.1 _ _) (le_of_lt (hv_pos k))
    have h_sum_pos :
        0 < ∑ k, A i₀ k * v k := by
      have h_mem : j₀ ∈ (Finset.univ : Finset n) := by simp
      have h_pos_term : 0 < A i₀ j₀ * v j₀ := by
        exact mul_pos hA_pos hvj₀_pos
      exact sum_pos_of_mem h_nonneg j₀ h_mem h_pos_term
    simpa [mulVec_apply] using h_sum_pos
  -- 4c.  We use the `i₀`-component of the eigen-equation for `B`.
  have h_comp_eq :
      (v i₀) + (A *ᵥ v) i₀ = rB * v i₀ := by
    have := congr_fun h_eig_B i₀
    simpa [B, add_mulVec, one_mulVec, add_apply, Pi.smul_apply, smul_eq_mul] using this
  have hrB_gt_one : 1 < rB := by
    have hv_i₀_pos : 0 < v i₀ := hv_pos i₀
    have h_lhs_gt : v i₀ < rB * v i₀ := by
      have : v i₀ + (A *ᵥ v) i₀ > v i₀ := by
        have : (A *ᵥ v) i₀ > 0 := hAv_i₀_pos; linarith
      simpa [h_comp_eq] using this
    exact ((mul_lt_mul_iff_of_pos_right hv_i₀_pos).1
            (by simpa [one_mul] using h_lhs_gt))
  have hrA_pos : 0 < rB - 1 := sub_pos.mpr hrB_gt_one
  exact ⟨rB - 1, v, hrA_pos, hv_pos, h_eig_A⟩
