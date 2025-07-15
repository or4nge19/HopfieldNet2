import Mathlib.Combinatorics.Quiver.Path
import HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.CollatzWielandt
import HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import HopfieldNet.Mathematics.Analysis.CstarAlgebra.Classes
import HopfieldNet.Mathematics.LinearAlgebra.Matrix.Spectrum
import Mathlib

open Quiver.Path
set_option maxHeartbeats 0

namespace Matrix
open CollatzWielandt

open Quiver
open Matrix Classical Complex

/--
An equality between a real number `r` and its coercion to the complex numbers `↑r`
is true by definition.
-/
lemma Complex.ofReal_eq_coe (r : ℝ) : (r : ℂ) = ↑r := rfl

variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
variable {A : Matrix n n ℝ}

/--
If `u = ∑ i in s, v i`, `‖u‖ = ∑ i in s, ‖v i‖`, and `u ≠ 0`, then each `v i`
is aligned with `u`.
-/
lemma Complex.aligned_of_triangle_eq {u : ℂ} {v : ι → ℂ} {s : Finset ι}
  (h_eq : u = ∑ i ∈ s, v i) (h_sum : ‖u‖ = ∑ i ∈ s, ‖v i‖) (h_ne : u ≠ 0) :
  ∀ i ∈ s, v i ≠ 0 → v i / ↑‖v i‖ = u / ↑‖u‖ := by
  intro i hi hvi_ne_zero
  have hu_norm_ne_zero : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr h_ne
  have hvi_norm_ne_zero : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hvi_ne_zero
  have h_aligned := align_each_with_sum h_eq h_sum h_ne i hi
  rw [smul_eq_mul, smul_eq_mul] at h_aligned
  rw [mul_comm] at h_aligned
  field_simp [h_aligned, hu_norm_ne_zero, hvi_norm_ne_zero]

omit [Nonempty n] [DecidableEq n] in
/-- For an irreducible, non-negative matrix `A`, if `v` is an eigenvector for an eigenvalue `μ`,
then the vector `w` of absolute values of `v` satisfies the inequality `|μ| • w ≤ A *ᵥ w`.
This is a key step in the Perron-Frobenius theorem. -/
lemma abs_eigenvector_inequality
  (hA_nonneg : ∀ i j, 0 ≤ A i j)
  {μ : ℝ} {v : n → ℝ} (h_eig : A *ᵥ v = μ • v) :
  let w := fun i ↦ |v i|; |μ| • w ≤ A *ᵥ w := by
  intro w
  intro i
  calc
    (|μ| • w) i = |μ| * |v i| := by simp [w]
    _ = |μ * v i| := by rw [abs_mul]
    _ = |(μ • v) i| := by simp
    _ = |(A *ᵥ v) i| := by rw [← h_eig]
    _ = |∑ j, A i j * v j| := by simp [mulVec, dotProduct]
    _ ≤ ∑ j, |A i j * v j| := by exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, (A i j) * |v j| := by simp_rw [abs_mul, abs_of_nonneg (hA_nonneg i _)]
    _ = (A *ᵥ w) i := by simp [w, mulVec, dotProduct]

omit [Nonempty n] [DecidableEq n] in
/--
If the triangle equality holds for the complex eigenvector equation `A * x = lam * x`,
then the vector of norms `‖x‖` is a real eigenvector of `A` with eigenvalue `‖lam‖`.
-/
lemma norm_eigenvector_is_eigenvector_of_triangle_eq
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {lam : ℂ} {x : n → ℂ} (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = lam • x)
    (h_triangle_eq : ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖) :
    A *ᵥ (fun i => ‖x i‖) = (‖lam‖ : ℝ) • (fun i => ‖x i‖) := by
  funext i
  calc
    (A *ᵥ fun i => ‖x i‖) i
        = ∑ j, A i j * ‖x j‖ := by simp [mulVec_apply]
    _   = ∑ j, ‖(A i j : ℂ)‖ * ‖x j‖ := by simp_rw [Complex.norm_ofReal, abs_of_nonneg (hA_nonneg _ _)]
    _   = ∑ j, ‖(A i j : ℂ) * x j‖ := by simp_rw [norm_mul]
    _   = ‖∑ j, (A i j : ℂ) * x j‖ := (h_triangle_eq i).symm
    _   = ‖((A.map (algebraMap ℝ ℂ)) *ᵥ x) i‖ := by simp [mulVec_apply, map_apply, dotProduct]; rfl
    _   = ‖(lam • x) i‖ := by rw [hx_eig]
    _   = ‖lam * x i‖ := by rw [Pi.smul_apply]; rfl
    _   = ‖lam‖ * ‖x i‖ := by rw [norm_mul]
    _   = ((‖lam‖ : ℝ) • fun i => ‖x i‖) i := by simp [smul_eq_mul]

/--
Under the conditions of the main theorem, the eigenvalue `lam` must be non-zero.
-/
lemma eigenvalue_ne_zero_of_irreducible
    {A : Matrix n n ℝ} (hA_irred : Irreducible A)
    {lam : ℂ} {x : n → ℂ} (hx_ne_zero : x ≠ 0)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (‖lam‖ : ℝ) • (fun i => ‖x i‖)) :
    lam ≠ 0 := by
  intro h_lam_zero
  have h_norm_lam_zero : ‖lam‖ = 0 := by rwa [norm_eq_zero]
  have h_eig_zero_smul : A *ᵥ (fun i => ‖x i‖) = (0 : ℝ) • (fun i => ‖x i‖) := by
    rw [h_norm_lam_zero] at h_x_abs_eig
    exact h_x_abs_eig
  have h_eig_zero : A *ᵥ (fun i => ‖x i‖) = 0 := by
    simpa [zero_smul] using h_eig_zero_smul
  have h_x_abs_nonneg : ∀ i, 0 ≤ ‖x i‖ := fun i => norm_nonneg _
  have h_x_abs_ne_zero : (fun i => ‖x i‖) ≠ 0 := by
    contrapose! hx_ne_zero
    ext i
    exact norm_eq_zero.mp (congr_fun hx_ne_zero i)
  have h_x_abs_pos : ∀ i, 0 < ‖x i‖ :=
    eigenvector_is_positive_of_irreducible hA_irred h_eig_zero_smul h_x_abs_nonneg h_x_abs_ne_zero
  rcases hA_irred.exists_pos_entry with ⟨i, j, hAij_pos⟩
  have h_sum : (A *ᵥ (fun k => ‖x k‖)) i = 0 := by rw [h_eig_zero]; rfl
  rw [mulVec_apply] at h_sum
  have h_sum_pos : 0 < ∑ k, A i k * ‖x k‖ := by
    apply sum_pos_of_mem
    · intro k _
      exact mul_nonneg (hA_irred.1 i k) (h_x_abs_nonneg k)
    · exact Finset.mem_univ j
    · exact mul_pos hAij_pos (h_x_abs_pos j)
  exact h_sum_pos.ne' h_sum

omit [Fintype n] [Nonempty n] [DecidableEq n] in
/-- If a property `P` holds for at least one vertex `i₀` and propagates along the edges
of an irreducible matrix's graph (`P i ∧ A i j > 0 → P j`), then `P` holds for all vertices. -/
lemma Irreducible.eq_univ_of_propagate (hA_irred : Irreducible A) (P : n → Prop)
    (h_nonempty : ∃ i₀, P i₀)
    (h_propagate : ∀ i j, P i → 0 < A i j → P j) :
    ∀ i, P i := by
  classical
  let S : Set n := {i | P i}
  let T : Set n := {i | ¬ P i}
  by_contra h_not_all
  push_neg at h_not_all
  have hS_nonempty : (S : Set n).Nonempty := h_nonempty
  have hT_nonempty : (T : Set n).Nonempty := h_not_all
  have hS_ne_univ : (S : Set n) ≠ Set.univ := by
    intro h_eq
    rcases hT_nonempty with ⟨i, hi_T⟩
    have hPi : P i := by
      have : i ∈ S := by
        have : i ∈ (Set.univ : Set n) := Set.mem_univ i
        simp [h_eq] at this
        simp_all only [Set.mem_setOf_eq, Set.mem_univ, S, T]
      simpa [S] using this
    exact hi_T hPi
  obtain ⟨i, hi_S, j, hj_not_S, hAij_pos⟩ :=
    hA_irred.exists_edge_out S hS_nonempty hS_ne_univ
  have hPi : P i := by
    simpa [S] using hi_S
  have hPj : P j := h_propagate i j hPi hAij_pos
  exact hj_not_S (by
    simpa [S] using hPj)

lemma eq_zero_of_sum_eq_zero {ι : Type*} [Fintype ι]
  (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hsum : ∑ j, f j = 0) (i : ι) : f i = 0 := by
  by_contra hne0
  have hne : ¬ 0 = f i := mt Eq.symm hne0
  have hgt : 0 < f i := lt_iff_le_and_ne.mpr ⟨hf i, hne⟩
  have hsum_pos : 0 < ∑ j, f j :=
    Finset.sum_pos' (fun j _ => hf j) ⟨i, Finset.mem_univ i, hgt⟩
  simpa [hsum] using ne_of_gt hsum_pos

omit [Nonempty n] [DecidableEq n] in
/--
If equality holds in the triangle inequality for `∑ z_j`, then all non-zero `z_j`
are aligned with the sum.
-/
lemma aligned_of_all_nonneg_re_im
    {A : Matrix n n ℝ} {i : n} {x : n → ℂ}
    (h_sum_eq : ‖∑ j, (A i j : ℂ) * x j‖ =
                ∑ j, ‖(A i j : ℂ) * x j‖) :
    ∀ j, (A i j : ℂ) * x j ≠ 0 →
      ∃ c : ℝ, 0 ≤ c ∧
        (A i j : ℂ) * x j = c • (∑ k, (A i k : ℂ) * x k) := by
  classical
  let z : n → ℂ := fun j => (A i j : ℂ) * x j
  let s : ℂ     := ∑ j, z j
  have h_z_sum : ‖s‖ = ∑ j, ‖z j‖ := by
    simpa [z, s] using h_sum_eq
  intro j hz_ne_zero
  have hs_ne_zero : s ≠ 0 := by
    intro hs
    have h_norms_zero : ∑ j, ‖z j‖ = 0 := by
      simp_all only [Complex.norm_mul, norm_real, Real.norm_eq_abs, Finset.sum_def, ne_eq, mul_eq_zero, ofReal_eq_zero,
        not_or, norm_zero, z, s]
    have h_all_zero : ∀ k, ‖z k‖ = 0 := by
      intro k
      exact eq_zero_of_sum_eq_zero
              (fun k => ‖z k‖) (fun _ => norm_nonneg _) h_norms_zero k
    have h_zj_zero : z j = 0 := by
      apply norm_eq_zero.mp
      simpa using h_all_zero j
    exact hz_ne_zero h_zj_zero
  have h_align :=
    Complex.each_term_is_nonneg_real_multiple_of_sum_of_triangle_eq
      (s := Finset.univ)
      (v := z)
      (u := s)
      (by simp [s])
      (by simpa [s] using h_z_sum)
      hs_ne_zero
  rcases h_align j (by simp) with ⟨c, hc_nonneg, hcz⟩
  have hcz' : z j = (c : ℂ) * s := hcz
  have hcz_smul : z j = c • s := by simpa [smul_eq_mul] using hcz'
  refine ⟨c, hc_nonneg, ?_⟩
  simpa [z, s] using hcz_smul

/--
If a complex number `z` is a positive real multiple of another complex number `w`,
then they are aligned (i.e., have the same phase).
-/
lemma Complex.aligned_of_mul_of_real_pos
    {z w : ℂ} {c : ℝ}
    (hc_pos     : 0 < c)
    (h          : z = (c : ℂ) * w)
    (hw_ne_zero : w ≠ 0) :
    z / ↑‖z‖ = w / ↑‖w‖ := by
  have hz_ne_zero : z ≠ 0 := by
    rw [h, mul_ne_zero_iff]
    exact ⟨ofReal_ne_zero.mpr hc_pos.ne', hw_ne_zero⟩
  field_simp [ h,
               norm_mul,
               norm_ofReal,
               abs_of_pos hc_pos,
               norm_ne_zero_iff.mpr hw_ne_zero,
               norm_ne_zero_iff.mpr hz_ne_zero ]
  have hc_ne_zero   : (c : ℂ) ≠ 0       := ofReal_ne_zero.mpr hc_pos.ne'
  have hnormw_ne    : ‖w‖ ≠ 0           := (norm_ne_zero_iff.mpr hw_ne_zero)
  have hnormw_neC   : (↑‖w‖ : ℂ) ≠ 0    := ofReal_ne_zero.mpr hnormw_ne
  field_simp [hc_ne_zero, hnormw_neC]
  ring_nf

/--
If `z = λw` for a positive real scalar `λ`, then `z` and `w` are aligned.
-/
lemma Complex.aligned_of_eigenvalue {z w : ℂ} {lam : ℝ}
    (h_rel : z = (lam : ℂ) * w) (h_lam_pos : 0 < lam) (h_w_ne_zero : w ≠ 0) :
    z / ↑‖z‖ = w / ↑‖w‖ := by
  exact Complex.aligned_of_mul_of_real_pos h_lam_pos h_rel h_w_ne_zero

omit [Nonempty n] [DecidableEq n] in
lemma aligned_of_propagating_edge
    (_ : Irreducible A)
    {lam : ℝ}
    {x   : n → ℂ}
    (hx_eig        : (A.map (algebraMap ℝ ℂ)) *ᵥ x = (lam : ℂ) • x)
    (_    : x ≠ 0)
    (h_triangle_eq : ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖)
    (_   : A *ᵥ (fun i => ‖x i‖) = lam • (fun i => ‖x i‖))
    (h_lam_pos     : 0 < lam)
    (hx_abs_pos    : ∀ i, 0 < ‖x i‖)
    (u v : n) (hAuv_pos : 0 < A u v) (hxv_ne_zero : x v ≠ 0) :
    x v / ↑‖x v‖ = x u / ↑‖x u‖ := by
  let sum_u := ((A.map (algebraMap ℝ ℂ)) *ᵥ x) u
  have h_lam_ne_zero   : (lam : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (ne_of_gt h_lam_pos)
  have h_xu_ne_zero : x u ≠ 0 := by
    intro h
    have h_norm_zero : ‖x u‖ = 0 := by simp [h]
    have h_norm_pos : 0 < ‖x u‖ := hx_abs_pos u
    linarith
  have h_sum_u_ne_zero : sum_u ≠ 0 := by
    have h_rel : sum_u = (lam : ℂ) * x u := by
      simp [sum_u, ← Pi.smul_apply, ← hx_eig, smul_eq_mul]; aesop
    rw [h_rel]
    exact mul_ne_zero h_lam_ne_zero h_xu_ne_zero
  have h_Auv_xv_ne_zero : (A u v : ℂ) * x v ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr hAuv_pos.ne') hxv_ne_zero
  have h_xv_aligned_term :
      x v / ↑‖x v‖ = ((A u v : ℂ) * x v) / ↑‖(A u v : ℂ) * x v‖ := by
    symm
    exact
      Complex.aligned_of_mul_of_real_pos
        hAuv_pos
        rfl
        hxv_ne_zero
  have h_term_aligned_sum :
      ((A u v : ℂ) * x v) / ↑‖(A u v : ℂ) * x v‖ =
        sum_u / ↑‖sum_u‖ := by
    have h_sum_def : sum_u = ∑ j, (A u j : ℂ) * x j := by
      simp [sum_u, mulVec_apply]; rfl
    exact
      Complex.aligned_of_triangle_eq
        h_sum_def (h_triangle_eq u) h_sum_u_ne_zero
        v (by simp) h_Auv_xv_ne_zero
  have h_sum_aligned_xu :
      sum_u / ↑‖sum_u‖ = x u / ↑‖x u‖ := by
    have h_rel : sum_u = (lam : ℂ) * x u := by
      simp [sum_u, ← Pi.smul_apply, ← hx_eig, smul_eq_mul]; aesop
    exact
      Complex.aligned_of_eigenvalue
        h_rel h_lam_pos h_xu_ne_zero
  simp_all only [coe_algebraMap, coe_smul, ne_eq, Complex.norm_mul, norm_real, Real.norm_eq_abs, norm_pos_iff,
    not_false_eq_true, ofReal_eq_zero, Pi.smul_apply, real_smul, mul_eq_zero, or_self, or_false, ofReal_mul, sum_u]--simpa [h_xv_aligned_term, h_term_aligned_sum, h_sum_aligned_xu]

/--  `u = conj z / ‖z‖` satisfies `z * u = ‖z‖`. -/
lemma Complex.unit_of_norm_div_star {z : ℂ} (hz : z ≠ 0) :
    let u := star z / (‖z‖ : ℂ); z * u = (‖z‖ : ℂ) := by
  intro u
  have h₁ : (‖z‖ : ℂ) ≠ 0 := by
    simpa using (ofReal_ne_zero.mpr ((norm_ne_zero_iff).2 hz))
  field_simp [u, h₁]
  rw [mul_conj']; rw [@sq]

/--
If equality holds in the triangle inequality then the
eigen-vector is a constant–phase multiple of its pointwise norm.
The eigen-value is assumed to be a positive real number.
-/
lemma triangle_equality_implies_scalar_multiple_of_nonneg
    (hA_irred : Irreducible A)
    {lam : ℝ} (h_lam_pos : 0 < lam)
    {x   : n → ℂ}
    (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = (lam : ℂ) • x)
    (hx_ne_zero : x ≠ 0)
    (h_triangle_eq :
      ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ x = c • fun i => (‖x i‖ : ℂ) := by
  let x_abs : n → ℝ := fun i ↦ ‖x i‖
  have h_x_abs_eig' :
      A *ᵥ x_abs = (‖(lam : ℂ)‖ : ℝ) • x_abs :=
    norm_eigenvector_is_eigenvector_of_triangle_eq
      (A := A) (hA_nonneg := hA_irred.1)
      (lam := (lam : ℂ)) (x := x)
      hx_eig h_triangle_eq
  have h_x_abs_eig : A *ᵥ x_abs = lam • x_abs := by
    simpa [abs_of_pos h_lam_pos] using h_x_abs_eig'
  have hx_abs_pos : ∀ i, 0 < x_abs i := by
    apply eigenvector_is_positive_of_irreducible hA_irred h_x_abs_eig
    · intro i; exact norm_nonneg _
    · contrapose! hx_ne_zero
      ext i; exact norm_eq_zero.mp (congr_fun hx_ne_zero i)
  obtain ⟨i₀, hi₀_ne_zero⟩ := Function.exists_ne_zero_of_ne_zero hx_ne_zero
  let c : ℂ := x i₀ / ↑‖x i₀‖
  refine ⟨c, ?_, ?_⟩
  · have : ‖x i₀‖ ≠ 0 := by
      simp [norm_eq_zero]
      exact hi₀_ne_zero
    simp [c, norm_div, abs_of_pos (norm_pos_iff.mpr hi₀_ne_zero),
          norm_ofReal, this]
  · let P : n → Prop := fun i ↦ x i ≠ 0 → x i / ↑‖x i‖ = c
    have h_phase_const : ∀ i, P i := by
      have hP₀ : P i₀ := by
        intro _; simp [c]
      apply
        Irreducible.eq_univ_of_propagate hA_irred P
          ⟨i₀, hP₀⟩
      intro u v hPu hAuv_pos hxv_ne_zero
      have h_alignment :=
        aligned_of_propagating_edge
          hA_irred
          hx_eig hx_ne_zero
          h_triangle_eq h_x_abs_eig h_lam_pos
          hx_abs_pos u v hAuv_pos hxv_ne_zero
      have hxu_ne_zero : x u ≠ 0 := by
        intro hxu
        have x_zero : x = 0 := by
          ext i
          by_cases hi_eq_u : i = u
          · subst hi_eq_u; exact hxu
          · have xi_pos : 0 < ‖x i‖ := hx_abs_pos i
            have xi_ne_zero : x i ≠ 0 := by
              contrapose! xi_pos
              simp [xi_pos]
            simp_all only [coe_algebraMap, coe_smul, ne_eq, Complex.norm_mul, norm_real, Real.norm_eq_abs, norm_pos_iff,
              not_false_eq_true, forall_const, norm_zero, ofReal_zero, div_zero, Complex.norm_div, norm_norm,
              ofReal_div, Pi.zero_apply, c, x_abs, P]
        exact hx_ne_zero x_zero
      have hu_phase : x u / ↑‖x u‖ = c := hPu hxu_ne_zero
      have h_transitive : x v / ↑‖x v‖ = x u / ↑‖x u‖ := h_alignment
      exact Eq.trans h_transitive hu_phase
    funext i
    by_cases hxi : x i = 0
    · simp [hxi, c, smul_eq_mul]
    · have : x i / ↑‖x i‖ = c := h_phase_const i hxi
      have xi_norm_ne_zero : ‖x i‖ ≠ 0 := by
        contrapose! hxi
        simp_all only [coe_algebraMap, coe_smul, ne_eq, Complex.norm_mul, norm_real, Real.norm_eq_abs, norm_pos_iff,
          not_false_eq_true, forall_const, ofReal_zero, div_zero, norm_eq_zero, c, x_abs, P]
      have xi_coe_ne_zero : (‖x i‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr xi_norm_ne_zero

      calc x i
          = x i / ↑‖x i‖ * ↑‖x i‖ := by field_simp [xi_coe_ne_zero]
        _ = c * ↑‖x i‖ := by rw [this]
        _ = c • (↑‖x i‖) := by simp [smul_eq_mul]

/--
The conditional supremum of a non-empty, bounded above set of non-negative numbers is non-negative.
-/
lemma csSup_nonneg {s : Set ℝ} (hs_nonempty : s.Nonempty) (hs_bdd : BddAbove s)
    (hs_nonneg : ∀ x ∈ s, 0 ≤ x) :
    0 ≤ sSup s := by
  obtain ⟨y, hy_mem⟩ := hs_nonempty
  have h_y_nonneg : 0 ≤ y := hs_nonneg y hy_mem
  have h_y_le_sSup : y ≤ sSup s := le_csSup hs_bdd hy_mem
  exact le_trans h_y_nonneg h_y_le_sSup

/-- The Perron root of a non-negative matrix is non-negative. -/
lemma perronRoot_nonneg {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    0 ≤ perronRoot_alt A := by
  unfold perronRoot_alt
  apply csSup_nonneg
  · exact CollatzWielandt.set_nonempty
  · exact CollatzWielandt.bddAbove A hA_nonneg
  · rintro _ ⟨x, ⟨hx_nonneg, hx_ne_zero⟩, rfl⟩
    dsimp [collatzWielandtFn]
    split_ifs with h_supp_nonempty
    · apply Finset.le_inf'
      intro i hi_mem
      apply div_nonneg
      · exact mulVec_nonneg hA_nonneg hx_nonneg i
      · exact (Set.mem_toFinset.mp hi_mem).le
    · exact le_rfl

omit [Nonempty n] [DecidableEq n] in
/-- For a non-negative matrix A, if the row sums are all equal to λ, then λ is an eigenvalue
    with the all-ones vector as its eigenvector. -/
lemma row_sum_eigenvalue
    (_ : ∀ i j, 0 ≤ A i j) (lambda : ℝ) (h_row_sums : ∀ i, ∑ j, A i j = lambda) :
    A *ᵥ (fun _ => (1 : ℝ)) = lambda • (fun _ => (1 : ℝ)) := by
  ext i
  rw [mulVec_apply, Pi.smul_apply, smul_eq_mul]
  simp only [mul_one]
  rw [h_row_sums i]

/--
If `r > 0` is an eigenvalue of a non-negative irreducible matrix `A` with a
strictly positive right eigenvector `v`, then `r` is the Perron root of `A`. -/
theorem eigenvalue_is_perron_root_of_positive_eigenvector
    {r : ℝ} {v : n → ℝ}
    (_ : Irreducible A)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hr_pos   : 0 < r)
    (hv_pos   : ∀ i, 0 < v i)
    (h_eig    : A *ᵥ v = r • v) :
    r = perronRoot_alt A := by
  have h_ge : perronRoot_alt A ≤ r :=
    eigenvalue_is_ub_of_positive_eigenvector
      (A := A) hA_nonneg hr_pos hv_pos h_eig
  have h_le : r ≤ perronRoot_alt A := by
    rw [← eq_eigenvalue_of_positive_eigenvector hv_pos h_eig]
    have hv_nonneg : ∀ i, 0 ≤ v i := fun i ↦ (hv_pos i).le
    have hv_ne_zero : v ≠ 0 := by
      intro h0
      have : 0 < v (Classical.arbitrary n) := hv_pos _
      simp [h0] at this
    apply le_csSup (CollatzWielandt.bddAbove A hA_nonneg)
    rw [@Set.mem_image]
    exact ⟨v, ⟨hv_nonneg, hv_ne_zero⟩, rfl⟩
  exact le_antisymm h_le h_ge

omit [Nonempty n] in
/--
If an inequality lambda•w ≤ A•w holds for a non-negative non-zero vector w,
then lambda is bounded by the Collatz-Wielandt function value for w.
This is the property that the Collatz-Wielandt function gives
the maximum lambda satisfying such an inequality.
-/
theorem CollatzWielandt.le_of_subinvariant
    {A : Matrix n n ℝ} (_ : ∀ i j, 0 ≤ A i j)
    {w : n → ℝ} (hw_nonneg : ∀ i, 0 ≤ w i) (hw_ne_zero : w ≠ 0)
    {lambda : ℝ} (h_sub : lambda • w ≤ A *ᵥ w) :
    lambda ≤ collatzWielandtFn A w := by
  obtain ⟨i, hi⟩ := exists_pos_of_ne_zero hw_nonneg hw_ne_zero
  let S := {j | 0 < w j}.toFinset
  have hS_nonempty : S.Nonempty := ⟨i, by simp [S]; exact hi⟩
  rw [collatzWielandtFn, dif_pos hS_nonempty]
  apply Finset.le_inf'
  intro j hj
  have h_j : lambda * w j ≤ (A *ᵥ w) j := by
    simp_all only [ne_eq, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, S]
    apply h_sub
  have hw_j_pos : 0 < w j := by simpa [S] using hj
  exact (le_div_iff₀ hw_j_pos).mpr (h_sub j)

lemma perronRoot_transpose_eq
    (A : Matrix n n ℝ) (hA_irred : Irreducible A) :
    perronRoot_alt A = perronRoot_alt Aᵀ := by
  obtain ⟨r, v, hr_pos, hv_pos, hv_eig⟩ :=
    exists_positive_eigenvector_of_irreducible hA_irred
  have hr_eq_perron : r = perronRoot_alt A :=
    eigenvalue_is_perron_root_of_positive_eigenvector
      hA_irred hA_irred.1 hr_pos hv_pos hv_eig
  have hAT_irred : Irreducible Aᵀ :=
    Irreducible.transpose hA_irred.1 hA_irred
  obtain ⟨r', u, hr'_pos, hu_pos, hu_eig_T⟩ :=
    exists_positive_eigenvector_of_irreducible hAT_irred
  have hr'_eq_perron : r' = perronRoot_alt Aᵀ :=
    eigenvalue_is_perron_root_of_positive_eigenvector
      hAT_irred (fun i j ↦ hA_irred.1 j i) hr'_pos hu_pos hu_eig_T
  have hu_eig_left : u ᵥ* A = r' • u := by
    have : Aᵀ *ᵥ u = r' • u := hu_eig_T
    simpa [vecMul_eq_mulVec_transpose] using this
  have hv_nonneg : ∀ i, 0 ≤ v i := fun i ↦ (hv_pos i).le
  have hv_ne_zero : v ≠ 0 := by
    intro h
    have : 0 < v (Classical.arbitrary n) := hv_pos _
    simp [h] at this
  have h_dot_pos : 0 < u ⬝ᵥ v :=
    dotProduct_pos_of_pos_of_nonneg_ne_zero hu_pos hv_nonneg hv_ne_zero
  have h1 : u ⬝ᵥ (A *ᵥ v) = r * (u ⬝ᵥ v) := by
    simp [hv_eig, dotProduct_smul, smul_eq_mul]
  have h2 : (u ᵥ* A) ⬝ᵥ v = r' * (u ⬝ᵥ v) := by
    simp [hu_eig_left, dotProduct_smul_left, smul_eq_mul]
  have h_eq : r * (u ⬝ᵥ v) = r' * (u ⬝ᵥ v) := by
    calc
      r * (u ⬝ᵥ v) = u ⬝ᵥ (A *ᵥ v) := (h1.symm)
      _             = (u ᵥ* A) ⬝ᵥ v := by
                        simpa using dotProduct_mulVec u A v
      _             = r' * (u ⬝ᵥ v) := h2
  have hr_eq_r' : r = r' := by
    subst hr_eq_perron hr'_eq_perron
    simp_all only [ne_eq, dotProduct_smul, smul_eq_mul, smul_dotProduct, mul_eq_mul_right_iff]
    cases h_eq with
    | inl h => simp_all only
    | inr h_1 => simp_all only [lt_self_iff_false]
  calc
    perronRoot_alt A   = r   := by symm; simpa using hr_eq_perron
    _                  = r'  := hr_eq_r'
    _                  = perronRoot_alt Aᵀ := hr'_eq_perron

/-- If a finite sum of non-negative terms is positive, at least one term must be positive. -/
lemma exists_pos_of_sum_pos {ι : Type*} [Fintype ι] {f : ι → ℝ}
    (h_nonneg : ∀ i, 0 ≤ f i) (h_sum_pos : 0 < ∑ i, f i) :
    ∃ i, 0 < f i := by
  by_contra h_not_exists
  push_neg at h_not_exists
  have h_all_zero : ∀ i, f i = 0 := by
    intro i
    exact le_antisymm (h_not_exists i) (h_nonneg i)
  have h_sum_zero : ∑ i, f i = 0 := by
    exact Finset.sum_eq_zero (fun i _ => h_all_zero i)
  exact h_sum_pos.ne' h_sum_zero

/-- For a non-negative `a`, `a * b` is positive iff both `a` and `b` are positive. -/
lemma mul_pos_iff_of_nonneg_left {a b : ℝ} (ha_nonneg : 0 ≤ a) :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  refine' ⟨fun h_mul_pos => _, fun ⟨ha_pos, hb_pos⟩ => mul_pos ha_pos hb_pos⟩
  have ha_pos : 0 < a := by
    refine' lt_of_le_of_ne ha_nonneg fun ha_zero => _
    rw [ha_zero] at h_mul_pos
    subst ha_zero
    simp_all only [le_refl, zero_mul, lt_self_iff_false]
  simp_all only [mul_pos_iff_of_pos_left, and_self]

