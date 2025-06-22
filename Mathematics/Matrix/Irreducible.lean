import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Matrix.Mul

open BigOperators Finset

/-!
# Perron-Frobenius Theory for Matrices

This file develops the essential Perron-Frobenius theory for non-negative matrices.
It provides the spectral analysis of non-negative irreducible matrices, which underlies
applications like Markov chain convergence and spectral graph theory.

## Main Definitions

* `Matrix.toQuiver`: The directed graph associated with a matrix `A`.
* `Matrix.Irreducible`: A matrix `A` is irreducible if its associated directed graph is
  strongly connected.
* `Matrix.HasPerronFrobeniusProperty`: A matrix that is non-negative and irreducible.

## Main Results (TODO)

* The Perron-Frobenius theorem will be stated in several parts:
  1. For an irreducible non-negative matrix `A`, its spectral radius `ρ(A)` is a positive,
     simple eigenvalue.
  2. There exists a unique (up to scaling) strictly positive eigenvector corresponding to `ρ(A)`.
  3. If `A` has `h` eigenvalues with modulus `ρ(A)`, these are the `h`-th roots of unity
     scaled by `ρ(A)`.
-/

namespace Quiver.Path

variable {V : Type*} [Quiver V] {R : Type*} [MulOneClass R]

/-- The weight of a path, defined as the product of the weights of its arrows.
    This version of weight uses a weight function on pairs of vertices. -/
def weight_from_vertices (w : V → V → R) : ∀ {i j : V}, Path i j → R
  | _, _, .nil => 1
  | _, j, @Path.cons _ _ _ k _ p (_e : k ⟶ j) => weight_from_vertices w p * w k j

/-- The weight of a path is positive if the weight of each arrow is positive. -/
lemma weight_from_vertices_pos {V : Type*} [Quiver V] {w : V → V → ℝ}
    (hw : ∀ {i j : V} (_ : i ⟶ j), 0 < w i j)
    {i j : V} (p : Path i j) : 0 < p.weight_from_vertices w := by
  induction p with
  | nil =>
    simp [weight_from_vertices, zero_lt_one]
  | cons p e ih =>
    rw [weight_from_vertices]
    exact mul_pos ih (hw e)

end Quiver.Path

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma pow_nonneg {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) : ∀ i j, 0 ≤ (A ^ k) i j := by
  induction k with
  | zero =>
    intro i j
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ m ih =>
    intro i j
    rw [pow_succ, mul_apply]
    apply Finset.sum_nonneg
    intro l _
    exact mul_nonneg (ih i l) (hA l j)

variable [Nonempty n]

/-!
## Irreducibility
-/

/-- The directed graph associated with a matrix `A`, where an edge `i → j` exists if `A i j > 0`. -/
def toQuiver (A : Matrix n n ℝ) : Quiver n :=
  ⟨fun i j => 0 < A i j⟩

/-- A quiver is strongly connected if there is a path from any vertex to any other vertex. -/
abbrev IsStronglyConnected (G : Quiver n) : Prop := ∀ i j : n, Nonempty (G.Path i j)

/-- A matrix `A` is irreducible if its associated directed graph is strongly connected. -/
def Irreducible (A : Matrix n n ℝ) : Prop :=
  IsStronglyConnected (toQuiver A)

/-- A matrix has the Perron-Frobenius property if it is nonnegative and irreducible. -/
class HasPerronFrobeniusProperty (A : Matrix n n ℝ) : Prop where
  /-- All entries of the matrix are non-negative. -/
  nonneg : ∀ i j, 0 ≤ A i j
  /-- The matrix's associated graph is strongly connected. -/
  irreducible : Irreducible A

/-- A helper lemma stating that the product of two non-negative numbers is positive
iff both numbers are positive. -/
private lemma mul_pos_iff_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  constructor
  · intro h
    refine ⟨lt_of_le_of_ne ha ?_, lt_of_le_of_ne hb ?_⟩
    · rintro rfl; rw [zero_mul] at h; exact h.false
    · rintro rfl; rw [mul_zero] at h; exact h.false
  · rintro ⟨ha_pos, hb_pos⟩; exact mul_pos ha_pos hb_pos

def endpoint {V : Type*} [Quiver V] {a b : V} : Quiver.Path a b → V
| Quiver.Path.nil => a
| Quiver.Path.cons _ _ => b

namespace Finset

/-- If a finite sum is positive, then there exists at least one summand that is positive. -/
lemma exists_mem_of_sum_pos {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_pos : 0 < ∑ a ∈ s, f a) : ∃ a ∈ s, 0 < f a := by
  by_contra h
  push_neg at h
  have h_nonpos : ∀ a ∈ s, f a ≤ 0 := h
  have h_sum_nonpos : ∑ a ∈ s, f a ≤ 0 := by
    apply Finset.sum_nonpos h_nonpos
  linarith [h_pos, h_sum_nonpos]

/-- Variant for when we know all terms satisfy a non-negativity condition. -/
lemma exists_mem_of_sum_pos' {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_pos : 0 < ∑ a ∈ s, f a)
    (h_nonneg : ∀ a ∈ s, 0 ≤ f a) :
    ∃ a ∈ s, 0 < f a := by
  by_contra h
  push_neg at h
  have h_zero : ∀ a ∈ s, f a = 0 := by
    intro a ha
    exact le_antisymm (h a ha) (h_nonneg a ha)
  have h_sum_zero : ∑ a ∈ s, f a = 0 := by
    rw [← Finset.sum_const_zero]
    congr 1
    ext a
    simp_all only [sum_const_zero, lt_self_iff_false]
  linarith [h_pos, h_sum_zero]

end Finset

 omit [Nonempty n] in
-- (A^k)ᵢⱼ is positive iff there is at least one path of length k
-- from i to j with a positive weight.
theorem pow_entry_pos_iff_exists_path (A : Matrix n n ℝ) (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) (i j : n) :
    0 < (A ^ k) i j ↔ (letI := toQuiver A; ∃ p : Quiver.Path i j, p.length = k ∧ 0 < p.weight_from_vertices A) := by
  letI G := toQuiver A
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, one_apply, gt_iff_lt, zero_lt_one]
    constructor
    · intro h_pos
      split_ifs at h_pos with h_eq
      · subst h_eq
        use Quiver.Path.nil
        simp [Quiver.Path.length, Quiver.Path.weight_from_vertices]
      · simp only [lt_self_iff_false] at h_pos;
    · rintro ⟨p, hp_len, _⟩
      have h_eq : i = j := Quiver.Path.eq_of_length_zero p hp_len
      subst h_eq
      have : p = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero p hp_len
      subst this
      simp
  | succ m ih =>
    simp_rw [pow_succ, mul_apply]
    constructor
    · intro h_pos
      obtain ⟨l, hl_mem, hl_pos⟩ : ∃ l ∈ Finset.univ, 0 < (A ^ m) i l * A l j := by
        apply Finset.exists_mem_of_sum_pos' h_pos (fun x _ => mul_nonneg (pow_nonneg hA m i x) (hA x j))
      rw [mul_pos_iff_of_nonneg (pow_nonneg hA m i l) (hA l j)] at hl_pos
      obtain ⟨h_Am_pos, h_A_pos_val⟩ := hl_pos
      have h_Am_pos := (ih i l).mp h_Am_pos
      obtain ⟨p_il, hp_len, hp_weight⟩ := h_Am_pos
      use p_il.cons h_A_pos_val
      refine ⟨by simp [Quiver.Path.length_cons, hp_len], by simp [Quiver.Path.weight_from_vertices]; exact mul_pos hp_weight h_A_pos_val⟩
    · rintro ⟨p, hp_len, hp_weight⟩
      cases p with
      | nil => simp [Quiver.Path.length_nil] at hp_len
      | cons q e =>
        simp only [Quiver.Path.length_cons, Nat.succ.injEq] at hp_len
        have h_w_q_pos : 0 < q.weight_from_vertices A := by
          simp only [Quiver.Path.weight_from_vertices] at hp_weight
          exact Quiver.Path.weight_from_vertices_pos (fun {i j} x ↦ x) q
        cases q with
        | nil =>
          have h_m_zero : m = 0 := by simp [Quiver.Path.length_nil] at hp_len; exact hp_len.symm
          subst h_m_zero
          have h_Am_pos : 0 < (A ^ 0) i i := by
            apply (ih i i).mpr
            refine ⟨Quiver.Path.nil, by simp [Quiver.Path.length_nil], by simp [Quiver.Path.weight_from_vertices]⟩
          apply Finset.sum_pos'
          · intro l _
            exact mul_nonneg (pow_nonneg hA 0 i l) (hA l j)
          · refine ⟨i, Finset.mem_univ i, ?_⟩
            exact mul_pos h_Am_pos e
        | cons q' e' =>
          let intermediate_vertex := endpoint (q'.cons e')
          have h_Am_pos : 0 < (A ^ m) i intermediate_vertex := by
            apply (ih i intermediate_vertex).mpr
            refine ⟨q'.cons e', hp_len, h_w_q_pos⟩
          apply Finset.sum_pos'
          · intro l _
            exact mul_nonneg (pow_nonneg hA m i l) (hA l j)
          · refine ⟨intermediate_vertex, Finset.mem_univ intermediate_vertex, ?_⟩
            exact mul_pos h_Am_pos e

omit [Nonempty n] in
/-- A nonnegative matrix `A` is irreducible if and only if for every `i, j`, there exists a
natural number `k` such that `(A^k) i j > 0`. -/
theorem irreducible_iff_exists_pow_pos (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    Irreducible A ↔ ∀ i j, ∃ k, 0 < (A ^ k) i j := by
  letI G := toQuiver A
  constructor
  · intro h_irr i j
    obtain ⟨p⟩ := h_irr i j
    use p.length
    rw [pow_entry_pos_iff_exists_path A hA_nonneg]
    use p
    exact ⟨rfl, Quiver.Path.weight_from_vertices_pos (fun {i j} h => h) p⟩
  · intro h_exists i j
    obtain ⟨k, hk_pos⟩ := h_exists i j
    rw [pow_entry_pos_iff_exists_path A hA_nonneg] at hk_pos
    obtain ⟨p, _, _⟩ := hk_pos
    exact ⟨p⟩

end Matrix

namespace Matrix

variable {n : Type*} [Fintype n]

/-- If a matrix `A` is positive, then for any non-negative non-zero vector `v`,
the vector `A.mulVec v` is strictly positive. -/
lemma positive_mul_vec_pos {A : Matrix n n ℝ} (hA_pos : ∀ i j, 0 < A i j) {v : n → ℝ}
    (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ∀ i, 0 < (A.mulVec v) i := by
  haveI : Nonempty n := by
    obtain ⟨k, _⟩ := Function.ne_iff.mp hv_ne_zero
    exact ⟨k⟩
  intro i
  simp [mulVec, dotProduct]
  obtain ⟨k, hvk_ne_zero⟩ : ∃ k, v k ≠ 0 := by rwa [Function.ne_iff] at hv_ne_zero
  have hv_k_pos : 0 < v k := (hv_nonneg k).lt_of_ne' hvk_ne_zero
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hA_pos i j).le (hv_nonneg j)
  · use k, Finset.mem_univ k
    exact mul_pos (hA_pos i k) hv_k_pos

end Matrix

