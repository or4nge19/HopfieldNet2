import Mathlib.Combinatorics.Quiver.Path
import HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Uniqueness

open Quiver.Path

namespace Matrix
open CollatzWielandt
variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
variable {A : Matrix n n ℝ}

/-- The unique positive eigenvalue corresponding to a positive eigenvector is the Perron root. -/
theorem eigenvalue_is_perron_root_of_positive_eigenvector {r : ℝ} {v : n → ℝ}
    (hA_irred : Irreducible A) (hA_nonneg : ∀ i j, 0 ≤ A i j) (hr_pos : 0 < r)
    (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    r = perronRoot A := by
  -- First, we need to show that r is at most the Perron root
  have hv_nonneg : ∀ i, 0 ≤ v i := fun i => le_of_lt (hv_pos i)
  have hv_ne_zero : v ≠ 0 := fun h_zero => (hv_pos (Classical.arbitrary n)).ne' (congr_fun h_zero (Classical.arbitrary n))

  have h_le : r ≤ perronRoot A := by
    -- r = collatzWielandtFn A v by the lemma eq_eigenvalue_of_positive_eigenvector
    rw [← eq_eigenvalue_of_positive_eigenvector hv_pos h_eig]
    -- And perronRoot A is the supremum of the collatzWielandtFn over P_set
    apply le_csSup_of_le (CollatzWielandt.bddAbove A hA_nonneg)
    -- v is in P_set (non-negative, non-zero)
    exact ⟨v, ⟨hv_nonneg, hv_ne_zero⟩, rfl⟩

  -- Now we need to show that the Perron root is at most r
  have h_ge : perronRoot A ≤ r := by
    -- First, get a positive eigenvector for the transpose matrix
    obtain ⟨r_pf, u, hr_pf_pos, hu_pos, hu_eig⟩ := exists_positive_eigenvector_of_irreducible hA_irred hA_nonneg
    have h_r_pf_eq_perron : r_pf = perronRoot A :=
      eigenvalue_is_perron_root_of_positive_eigenvector hA_irred hA_nonneg hr_pf_pos hu_pos hu_eig
    rw [← h_r_pf_eq_perron]

    -- Use the fact that the transpose has the same Perron root
    let A_T := Aᵀ
    have hAT_irred : Irreducible A_T := hA_irred.transpose hA_nonneg
    have hAT_nonneg : ∀ i j, 0 ≤ A_T i j := by simp [A_T]; exact fun i j ↦ hA_nonneg j i

    -- Get a positive eigenvector for the transpose
    obtain ⟨r_T, u_T, hr_T_pos, hu_T_pos, hu_T_eig⟩ := exists_positive_eigenvector_of_irreducible hAT_irred hAT_nonneg

    -- The left eigenvector of A_T is a right eigenvector of A
    have h_uT_left_eig : u_T ᵥ* A = r_T • u_T := by rwa [← vecMul_eq_mulVec_transpose]

    -- The eigenvalue of the transpose equals the Perron root of A
    have h_rT_eq_r_pf : r_T = r_pf := by
      rw [eigenvalue_is_perron_root_of_positive_eigenvector hAT_irred hAT_nonneg hr_T_pos hu_T_pos hu_T_eig,
          perronRoot_transpose_eq hA_nonneg, h_r_pf_eq_perron]

    -- Now we use the dot product to show r_T ≤ r
    rw [← h_rT_eq_r_pf] at h_uT_left_eig

    -- Dot product of left eigenvector with both sides of A*v = r*v
    have h_dot_eq : u_T ⬝ᵥ (A *ᵥ v) = u_T ⬝ᵥ (r • v) := by rw [h_eig]

    -- Manipulate the dot product
    rw [dotProduct_mulVec, h_uT_left_eig, dotProduct_smul, dotProduct_smul] at h_dot_eq

    -- We have r_T * (u_T ⬝ᵥ v) = r * (u_T ⬝ᵥ v)
    have h_dot_pos : 0 < u_T ⬝ᵥ v := dotProduct_pos_of_pos_of_pos hu_T_pos hv_pos

    -- This implies r_T = r or u_T ⬝ᵥ v = 0
    rw [mul_eq_mul_right_iff] at h_dot_eq
    cases h_dot_eq with
    | inl h_eq => exact h_eq.symm.le
    | inr h_zero => linarith [h_dot_pos]

  -- r = perronRoot A by antisymmetry
  exact le_antisymm h_le h_ge

/-- If equality holds in the triangle inequality for a sum of complex vectors,
    then all vectors must point in the same direction. -/
lemma triangle_equality_iff_aligned {n : ℕ} {v : Fin n → ℂ} (hv_nonzero : ∀ i, v i ≠ 0) :
    ‖∑ i, v i‖ = ∑ i, ‖v i‖ ↔
    ∃ (c : ℂ), ‖c‖ = 1 ∧ ∀ i, v i = ‖v i‖ * c := by
  constructor
  · intro h_eq
    -- Equality case in triangle inequality means all vectors are positive multiples of each other
    by_cases h_empty : n = 0
    · -- Trivial case: no vectors
      subst h_empty
      use 1
      simp [Complex.norm_one]

    -- Take any nonzero vector
    let i₀ : Fin n := ⟨0, by omega⟩
    let c := v i₀ / ‖v i₀‖
    have hc_norm_one : ‖c‖ = 1 := by
      simp [c, Complex.norm_div, Complex.norm_eq_abs]
      exact (abs_div_self (norm_pos_iff.mpr (hv_nonzero i₀))).symm

    use c, hc_norm_one
    intro i
    -- For each vector, we show it points in the same direction as v i₀
    have h_mul : v i * Complex.conj (v i₀) = ‖v i‖ * ‖v i₀‖ := by
      -- This is where the equality condition in the triangle inequality is used
      sorry -- Complete proof requires complex analysis techniques

    -- From the above, we can show v i = ‖v i‖ * c
    sorry -- Complete proof

  · -- The converse: if all vectors point in the same direction, the triangle inequality is an equality
    rintro ⟨c, hc_norm_one, h_aligned⟩
    calc ‖∑ i, v i‖
        = ‖∑ i, ‖v i‖ * c‖ := by congr; ext i; exact h_aligned i
      _ = ‖(∑ i, ‖v i‖) * c‖ := by simp [mul_sum]
      _ = |(∑ i, ‖v i‖)| * ‖c‖ := by rw [Complex.norm_mul]
      _ = (∑ i, ‖v i‖) * 1 := by rw [abs_of_nonneg (sum_nonneg (fun _ => norm_nonneg _)), hc_norm_one]
      _ = ∑ i, ‖v i‖ := by rw [mul_one]
