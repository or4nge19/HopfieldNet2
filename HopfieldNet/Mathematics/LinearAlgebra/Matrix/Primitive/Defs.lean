import HopfieldNet.Mathematics.aux
import HopfieldNet.Mathematics.LinearAlgebra.Matrix.Spectrum
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Metrizable.CompletelyMetrizable

/-!
# Perron-Frobenius Theory for Matrices

This file develops the essential Perron-Frobenius theory for non-negative matrices.
It provides the spectral analysis of non-negative irreducible matrices, which underlies
applications like Markov chain convergence and spectral graph theory.

## Main Definitions

* `Matrix.toQuiver`: The directed graph associated with a matrix `A`.
* `Matrix.Irreducible`: A matrix `A` is irreducible if its associated directed graph is
  strongly connected.
* `Matrix.IsPrimitive`: A matrix `A` is primitive if some power of it is strictly positive.

## Main Results

The file builds towards the Perron-Frobenius theorem by formalizing key characterizations:

* `Matrix.irreducible_iff_exists_pow_pos`: A combinatorial characterization of
  irreducibility.
* `Matrix.pow_entry_pos_iff_exists_path`: A fundamental link between matrix powers and
  path existence in the associated graph.
-/

namespace Matrix
open Finset Quiver
variable {n : Type*} [Fintype n]

lemma pow_nonneg [DecidableEq n] {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) : ∀ i j, 0 ≤ (A ^ k) i j := by
  induction k with
  | zero => intro i j; simp [one_apply]; by_cases h : i = j <;> simp [h]
  | succ m ih =>
    intro i j; rw [pow_succ, mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hA l j)

def toQuiver (A : Matrix n n ℝ) : Quiver n :=
  ⟨fun i j => 0 < A i j⟩

abbrev IsStronglyConnected (G : Quiver n) : Prop := ∀ i j : n, Nonempty (Quiver.Path i j)

def Irreducible (A : Matrix n n ℝ) : Prop :=
  IsStronglyConnected (toQuiver A)

def IsPrimitive [DecidableEq n] (A : Matrix n n ℝ) : Prop :=
  ∃ k, k > 0 ∧ ∀ i j, 0 < (A ^ k) i j

/-- If `A` is irreducible and `n>1` then every row has a positive entry. -/
lemma irreducible_no_zero_row
    (A : Matrix n n ℝ) --(hA_nonneg : ∀ i j, 0 ≤ A i j)
    (h_irr : Irreducible A) (h_dim : 1 < Fintype.card n) (i : n) :
    ∃ j, 0 < A i j := by
  by_contra h_row ; push_neg at h_row   -- `h_row : ∀ j, A i j ≤ 0`
  letI G := toQuiver A
  have no_out : ∀ j : n, IsEmpty (i ⟶ j) :=
    fun j ↦ ⟨fun h ↦ (h_row j).not_lt h⟩
  obtain ⟨j, hij⟩ := Fintype.exists_ne_of_one_lt_card h_dim i
  obtain ⟨p⟩ : Nonempty (G.Path i j) := h_irr i j
  have : False := by
    have aux : (∀ {v} (q : G.Path i v), v ≠ i → False) := by
      intro v q
      induction q with
      | nil =>
          intro hvi ; exact hvi rfl
      | cons r e ih =>
          cases r with
          | nil =>
              intro _
              exact (no_out _).false e
          | cons r' e' =>
              intro hvi ; simp_all only [isEmpty_Prop, ne_eq, imp_false, not_not, G]
    exact aux p hij
  exact this.elim

section PerronFrobeniusTheorems

variable {A : Matrix n n ℝ}

open Classical in
lemma sum_pos_of_mem  {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_nonneg : ∀ a ∈ s, 0 ≤ f a) (a : α) (ha_mem : a ∈ s) (ha_pos : 0 < f a) :
    0 < ∑ x ∈ s, f x := by
  have h_sum_split : ∑ x ∈ s, f x = f a + ∑ x ∈ s.erase a, f x :=
    Eq.symm (add_sum_erase s f ha_mem)
  have h_erase_nonneg : 0 ≤ ∑ x ∈ s.erase a, f x :=
    Finset.sum_nonneg (λ x hx => h_nonneg x (Finset.mem_of_mem_erase hx))
  rw [h_sum_split]
  exact add_pos_of_pos_of_nonneg ha_pos h_erase_nonneg

theorem pow_entry_pos_iff_exists_path [DecidableEq n] (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) (i j : n) :
    letI := toQuiver A; 0 < (A ^ k) i j ↔ Nonempty {p : Path i j // p.length = k} := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, one_apply, Quiver.Path.length_nil, gt_iff_lt, zero_lt_one, nonempty_subtype]
    constructor
    · intro h_pos
      split_ifs at h_pos with h_eq
      · subst h_eq; exact ⟨letI := toQuiver A; Quiver.Path.nil, rfl⟩
      · exfalso; linarith [h_pos]
    · rintro ⟨p, hp⟩
      have h_eq : i = j := letI := toQuiver A; Quiver.Path.eq_of_length_zero p hp
      simp [h_eq]
  | succ m ih =>
    rw [pow_succ, mul_apply, nonempty_subtype]
    constructor
    · intro h_pos
      obtain ⟨l, hl_mem, hl_pos⟩ : ∃ l ∈ univ, 0 < (A ^ m) i l * A l j :=
        exists_mem_of_sum_pos h_pos fun x _ => mul_nonneg (pow_nonneg hA m i x) (hA x j)
      rcases (mul_pos_iff_of_nonneg (pow_nonneg hA m i l) (hA l j)).mp hl_pos with ⟨h_Am, h_A⟩
      obtain ⟨⟨p, hp_len⟩⟩ := (ih i l).mp h_Am
      exact ⟨letI := toQuiver A; p.cons h_A, by simp [Quiver.Path.length_cons, hp_len]⟩
    · rintro ⟨p, hp_len⟩
      cases p with
      | nil => simp [Quiver.Path.length] at hp_len
      | @cons b _ q e =>
        simp only [Quiver.Path.length_cons, Nat.succ.injEq] at hp_len
        have h_Am_pos : 0 < (A ^ m) i b := (ih i b).mpr ⟨q, hp_len⟩
        let h_A_pos := e
        have h_prod : 0 < (A ^ m) i b * A b j := mul_pos h_Am_pos h_A_pos
        exact sum_pos_of_mem
          (fun x _ => mul_nonneg (pow_nonneg hA m i x) (hA x j))
          b
          (Finset.mem_univ b)
          h_prod

theorem irreducible_iff_exists_pow_pos [DecidableEq n] (hA : ∀ i j, 0 ≤ A i j) :
    Irreducible A ↔ ∀ i j, ∃ k, 0 < (A ^ k) i j := by
  constructor
  · intro h_irr i j
    rcases h_irr i j with ⟨p⟩
    use letI := toQuiver A; p.length
    rw [pow_entry_pos_iff_exists_path hA]
    exact ⟨p, rfl⟩
  · intro h_exists i j
    obtain ⟨k, hk_pos⟩ := h_exists i j
    rw [pow_entry_pos_iff_exists_path hA] at hk_pos
    rcases hk_pos with ⟨p, _⟩
    exact ⟨p⟩

theorem IsPrimitive.to_Irreducible [DecidableEq n] (h_prim : IsPrimitive A) (hA : ∀ i j, 0 ≤ A i j) :
    Irreducible A := by
  rw [irreducible_iff_exists_pow_pos hA]
  intro i j
  obtain ⟨k, _hk_gt_zero, hk_pos⟩ := h_prim
  exact ⟨k, hk_pos i j⟩

end PerronFrobeniusTheorems
end Matrix

/-!
### The Perron-Frobenius Theorem for Primitive Matrices

This section formalizes Theorem 1.1 from Seneta's "Non-negative Matrices and Markov Chains".
The proof follows Seneta's logic precisely:
1. Define the Perron root `r` as the supremum of the Collatz-Wielandt function `r(x)`.
2. Use the fact that `r(x)` is upper-semicontinuous on a compact set (the standard simplex)
   to guarantee the supremum is attained by a vector `v`.
3. Prove that `v` is an eigenvector by a contradiction argument using the primitivity of `A`.
4. Prove that `v` is strictly positive, again using primitivity.
-/
namespace Matrix
section PerronFrobeniusMain
variable {n : Type*} [Fintype n] [Nonempty n]
variable {A : Matrix n n ℝ}

open LinearMap Set Filter Topology Finset
open scoped Convex Pointwise

/-- The Collatz-Wielandt function, `r(x)` in Seneta's notation.
For a non-zero, non-negative vector `x`, this is `min_{i | xᵢ > 0} (Ax)ᵢ / xᵢ`.
Seneta uses row vectors `x'T`; we use column vectors `Ax`. The logic is identical. -/
noncomputable def collatzWielandtFn (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  let supp := {i | 0 < x i}.toFinset
  if h : supp.Nonempty then
    supp.inf' h fun i => (A *ᵥ x) i / x i
  else 0

/-
/-- The Collatz-Wielandt function r_x for a positive vector `x`.
    See p. 30 in Berman & Plemmons.
    We define it for strictly positive vectors to avoid division by zero. -/
noncomputable def r_x (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  ⨅ i, (A.mulVec x i) / (x i)-/

instance : Nonempty n := inferInstance

/-- For a finite type, the infimum over the type is attained at some element. -/
lemma exists_eq_iInf {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) : ∃ i, f i = ⨅ j, f j :=
  exists_eq_ciInf_of_finite

/-- The matrix-vector multiplication map as a continuous linear map. -/
noncomputable abbrev mulVec_continuousLinearMap (A : Matrix n n ℝ) : (n → ℝ) →L[ℝ] (n → ℝ) :=
  (Matrix.mulVecLin A).toContinuousLinearMap

/-- Functions computing pointwise infima are equal when using `iInf` vs `Finset.inf'`. -/
lemma Finset.iInf_apply_eq_finset_inf'_apply_fun {α β γ : Type*}
    [Fintype α] [Nonempty α] [ConditionallyCompleteLinearOrder γ]
    (f : α → β → γ) :
    (fun x ↦ ⨅ i, f i x) = (fun x ↦ (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i ↦ f i x)) := by
  ext x
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

/-- For a finite index type, the point-wise (finite) infimum of a family of
    continuous functions is continuous. -/
lemma continuousOn_iInf {α β : Type*}
    [Fintype α] [Nonempty α]
    [TopologicalSpace β]
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

/-
-- The Collatz-Wielandt function r_x is continuous on the set of strictly positive vectors.
lemma r_x_continuousOn_pos (A : Matrix n n ℝ) :
    ContinuousOn (r_x A) {x : n → ℝ | ∀ i, 0 < x i} := by
  unfold r_x
  apply continuousOn_iInf
  intro i
  apply ContinuousOn.div
  · exact ((continuous_apply i).comp (mulVec_continuousLinearMap A).continuous).continuousOn
  · exact (continuous_apply i).continuousOn
  · exact fun x a ↦ Ne.symm (ne_of_lt (a i))-/

/-- The Collatz-Wielandt function is upper-semicontinuous.
Seneta relies on this fact (p.15, Appendix C) to use the Extreme Value Theorem.
`r(x)` is a minimum of functions `fᵢ(x) = (Ax)ᵢ / xᵢ`. Each `fᵢ` is continuous where `xᵢ > 0`.
The minimum of continuous functions is upper-semicontinuous. -/
theorem upperSemicontinuousOn_collatzWielandtFn
    (A : Matrix n n ℝ) : UpperSemicontinuousOn (collatzWielandtFn A) (stdSimplex ℝ n) := by
    have support_nonempty : ∀ x ∈ stdSimplex ℝ n, ({i | 0 < x i}.toFinset).Nonempty := by
      intro x hx
      obtain ⟨i, hi_pos⟩ := exists_pos_of_sum_one_of_nonneg hx.2 hx.1
      have hi_mem : i ∈ ({i | 0 < x i}.toFinset) := by simp [hi_pos]
      exact ⟨i, hi_mem⟩
    intro x₀ hx₀ c hc
    have supp_x₀ : {i | 0 < x₀ i}.toFinset.Nonempty := support_nonempty x₀ hx₀
    have fn_eq : collatzWielandtFn A x₀ = {i | 0 < x₀ i}.toFinset.inf' supp_x₀ (fun i => (A *ᵥ x₀) i / x₀ i) := by
      unfold collatzWielandtFn
      rw [dif_pos supp_x₀]
    let U := {y : n → ℝ | ∀ i ∈ {i | 0 < x₀ i}.toFinset, 0 < y i}
    have x₀_in_U : x₀ ∈ U := by
      intro i hi
      simp only [Set.mem_toFinset] at hi
      exact hi
    have U_open : IsOpen U := by
      have h_eq : U = ⋂ i ∈ {i | 0 < x₀ i}.toFinset, {y | 0 < y i} := by
        ext y
        simp only [Set.mem_iInter, Set.mem_setOf_eq]
        rfl
      rw [h_eq]
      apply isOpen_biInter_finset
      intro i _
      exact isOpen_lt continuous_const (continuous_apply i)
    let f := fun y => {i | 0 < x₀ i}.toFinset.inf' supp_x₀ fun i => (A *ᵥ y) i / y i
    have f_cont : ContinuousOn f U := by
      apply continuousOn_finset_inf' supp_x₀
      intro i hi
      apply ContinuousOn.div
      · exact continuous_apply i |>.comp_continuousOn ((mulVec_continuousLinearMap A).continuous.continuousOn)
      · exact (continuous_apply i).continuousOn
      · intro y hy
        simp only [Set.mem_setOf_eq] at hy
        exact (hy i hi).ne'
    have f_ge : ∀ y ∈ U ∩ stdSimplex ℝ n, collatzWielandtFn A y ≤ f y := by
      intro y hy
      have y_supp : {i | 0 < y i}.toFinset.Nonempty := support_nonempty y hy.2
      have fn_y : collatzWielandtFn A y = {i | 0 < y i}.toFinset.inf' y_supp fun i => (A *ᵥ y) i / y i := by
        unfold collatzWielandtFn
        rw [dif_pos y_supp]
      have supp_subset : {i | 0 < x₀ i}.toFinset ⊆ {i | 0 < y i}.toFinset := by
        intro i hi
        have hi' : 0 < x₀ i := by
          simp only [Set.mem_toFinset] at hi
          exact hi
        have : 0 < y i := hy.1 i hi
        simp only [Set.mem_toFinset]
        exact this
      rw [fn_y]
      apply finset_inf'_mono_subset supp_subset
    rw [fn_eq] at hc
    have : f x₀ < c := hc
    have cont_at : ContinuousAt f x₀ := f_cont.continuousAt (IsOpen.mem_nhds U_open x₀_in_U)
    have lt_eventually : ∀ᶠ y in 𝓝 x₀, f y < c :=
      Filter.Tendsto.eventually_lt_const hc cont_at
    rcases eventually_to_open lt_eventually with ⟨V, V_open, x₀_in_V, hV⟩
    let W := V ∩ U ∩ stdSimplex ℝ n
    have VU_open : IsOpen (V ∩ U) := IsOpen.inter V_open U_open
    have VU_mem : x₀ ∈ V ∩ U := ⟨x₀_in_V, x₀_in_U⟩
    have VU_nhds : V ∩ U ∈ 𝓝 x₀ := VU_open.mem_nhds VU_mem
    have W_nhdsWithin : W ∈ 𝓝[stdSimplex ℝ n] x₀ := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      exact ⟨V ∩ U, VU_nhds, by simp [W]⟩
    have h_final : ∀ y ∈ W, collatzWielandtFn A y < c := by
      intro y hy
      apply lt_of_le_of_lt
      · apply f_ge y
        exact ⟨And.right (And.left hy), hy.2⟩
      · exact hV y (And.left (And.left hy))
    exact Filter.mem_of_superset W_nhdsWithin (fun y hy => h_final y hy)

end PerronFrobeniusMain

end Matrix
