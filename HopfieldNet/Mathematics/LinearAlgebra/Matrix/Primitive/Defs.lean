import HopfieldNet.Mathematics.aux
import HopfieldNet.Mathematics.LinearAlgebra.Matrix.Spectrum
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import HopfieldNet.Combinatorics.Quiver.Path
import HopfieldNet.Topology.Compactness.ExtremeValueUSC

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

open Set Finset MetricSpace Topology Convex Quiver.Path

namespace Matrix
variable {n : Type*} --[Fintype n]

open Topology Metric Set Finset
section PerronFrobenius
open Finset Set IsCompact Topology Matrix
-- The set of vectors we are optimizing over.
def P_set := {x : n → ℝ | (∀ i, 0 ≤ x i) ∧ x ≠ 0}

-- The Collatz-Wielandt value is the supremum of `r_x` over P.
noncomputable def r (A : Matrix n n ℝ) [Fintype n] := ⨆ x ∈ P_set, collatzWielandtFn A x

-- We define `y = (I + A)^(n-1) * x`. For any non-zero non-negative `x`, `y` is strictly positive.
-- This is from Theorem 1.3(d) on page 48.
-- Helper lemma: if `A` has strictly positive entries and `x` is a
-- non-negative, non-zero vector, then every entry of `A • x` is positive.
lemma positive_mul_vec_pos [Fintype n]
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
    · simp only [Finset.mem_univ]  --  `k ∈ Finset.univ`
    · exact mul_pos (hA_pos i k) hk_pos

variable {A : Matrix n n ℝ} --[DecidableEq n] [Nonempty n]

theorem positive_mul_vec_of_nonneg_vec [Fintype n] (hA_pos : ∀ i j, 0 < A i j)
    {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ∀ i, 0 < (A *ᵥ v) i := by
  intro i
  simp only [mulVec, dotProduct]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (le_of_lt (hA_pos i j)) (hv_nonneg j)
  · have : ∃ k, 0 < v k := by
      by_contra h_all_nonpos
      push_neg at h_all_nonpos
      have h_zero : v = 0 := funext (fun j => le_antisymm (h_all_nonpos j) (hv_nonneg j))
      exact hv_ne_zero h_zero
    rcases this with ⟨k, hk_pos⟩
    refine ⟨k, Finset.mem_univ k, ?_⟩
    exact mul_pos (hA_pos i k) hk_pos

/-- If an entry `A i j` is positive, there is a path from `i` to `j` in the quiver. -/
lemma path_exists_of_pos_entry {A : Matrix n n ℝ} {i j : n} (h_pos : 0 < A i j) :
    letI := toQuiver A; Nonempty (Quiver.Path i j) := by
  letI G := toQuiver A
  let e : G.Hom i j := h_pos
  exact ⟨e.toPath⟩

/-- A matrix with all positive entries is irreducible. -/
lemma irreducible_of_all_entries_positive {A : Matrix n n ℝ} (hA : ∀ i j, 0 < A i j) :
    Irreducible A := by
  unfold Irreducible IsStronglyConnected
  intro i j
  exact path_exists_of_pos_entry (hA i j)

theorem exists_connecting_edge_of_irreducible {A : Matrix n n ℝ} (hA_irred : A.Irreducible)
    {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
    (S T : Set n) (hS_nonempty : S.Nonempty) (hT_nonempty : T.Nonempty)
    (h_partition : ∀ i, i ∈ S ↔ v i > 0)
    (h_complement : ∀ i, i ∈ T ↔ v i = 0) :
    ∃ (i j : n), i ∈ T ∧ j ∈ S ∧ 0 < A i j := by
  obtain ⟨i₀, hi₀_in_T⟩ := hT_nonempty
  obtain ⟨j₀, hj₀_in_S⟩ := hS_nonempty
  unfold Irreducible IsStronglyConnected toQuiver at hA_irred
  obtain ⟨p⟩ := hA_irred j₀ i₀
  obtain ⟨y, z, e, _, _, hy_not_T, hz_in_T, _⟩ :=
    @Quiver.Path.exists_boundary_edge n (toQuiver A) _ _ p T
    (fun h_j0_in_T => by
      have hj₀_pos : v j₀ > 0 := (h_partition j₀).mp hj₀_in_S
      have hj₀_zero : v j₀ = 0 := (h_complement j₀).mp h_j0_in_T
      exact ne_of_gt hj₀_pos hj₀_zero)
    hi₀_in_T
  have hy_in_S : y ∈ S := by
    by_contra hy_not_S
    have hy_in_T : y ∈ T := by
      cases' (lt_or_eq_of_le (hv_nonneg y)) with h_pos h_zero
      · rename_i right
        subst right
        simp_all only [gt_iff_lt, not_true_eq_false]
      · rename_i right
        subst right
        simp_all only [gt_iff_lt, not_true_eq_false]
    exact hy_not_T hy_in_T
  obtain ⟨p'⟩ := hA_irred i₀ j₀
  obtain ⟨y, z, e, _, _, hy_not_S, hz_in_S, _⟩ :=
    @Quiver.Path.exists_boundary_edge n (toQuiver A) _ _ p' S
    (fun h_i0_in_S => by
      have hi₀_zero : v i₀ = 0 := (h_complement i₀).mp hi₀_in_T
      have hi₀_pos : v i₀ > 0 := (h_partition i₀).mp h_i0_in_S
      exact ne_of_gt hi₀_pos hi₀_zero)
    hj₀_in_S
  have hy_in_T : y ∈ T := by
    by_contra hy_not_T
    have hy_in_S : y ∈ S := by
      cases' (lt_or_eq_of_le (hv_nonneg y)) with h_pos h_zero
      · exact (h_partition y).mpr h_pos
      · have hy_in_T' : y ∈ T := by aesop
        exact (hy_not_T hy_in_T').elim
    exact hy_not_S hy_in_S
  exact ⟨y, z, hy_in_T, hz_in_S, e⟩

lemma exists_boundary_crossing_in_support [DecidableEq n] [Fintype n]
    (hA_irred : Irreducible A) (_ : ∀ i j, 0 ≤ A i j)
    {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) (_ : v ≠ 0)
    (S T : Set n) (hS_nonempty : S.Nonempty) (hT_nonempty : T.Nonempty)
    (h_partition : ∀ i, i ∈ S ↔ v i > 0)
    (h_complement : ∀ i, i ∈ T ↔ v i = 0) :
    ∃ (i j : n), i ∈ T ∧ j ∈ S ∧ 0 < A i j := by
  obtain ⟨i₀, hi₀_in_T⟩ := hT_nonempty
  obtain ⟨j₀, hj₀_in_S⟩ := hS_nonempty
  unfold Irreducible IsStronglyConnected toQuiver at hA_irred
  obtain ⟨p⟩ := hA_irred i₀ j₀
  obtain ⟨y, z, e, _, _, hy_not_S, hz_in_S, _⟩ :=
    @Quiver.Path.exists_boundary_edge n (toQuiver A) _ _ p S
    (fun h_i0_in_S => by
      have hi₀_zero : v i₀ = 0 := (h_complement i₀).mp hi₀_in_T
      have hi₀_pos : v i₀ > 0 := (h_partition i₀).mp h_i0_in_S
      exact ne_of_gt hi₀_pos hi₀_zero)
    hj₀_in_S
  have hy_in_T : y ∈ T := by
    by_contra hy_not_T
    have hy_in_S : y ∈ S := by
      cases' (lt_or_eq_of_le (hv_nonneg y)) with h_pos h_zero
      · exact (h_partition y).mpr h_pos
      · have hy_in_T' : y ∈ T := by aesop
        exact (hy_not_T hy_in_T').elim
    exact hy_not_S hy_in_S
  exact ⟨y, z, hy_in_T, hz_in_S, e⟩

theorem irreducible_mulVec_ne_zero [DecidableEq n] [Fintype n]
    (hA_irred : Irreducible A) (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA_ne_zero : A ≠ 0)
    {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    A *ᵥ v ≠ 0 := by
  by_contra h_Av_zero
  let S : Set n := {i | v i > 0}
  let T : Set n := {i | v i = 0}
  have hS_nonempty : S.Nonempty := by
    by_contra hS_empty
    rw [Set.not_nonempty_iff_eq_empty] at hS_empty
    apply hv_ne_zero
    ext k
    have : v k ≤ 0 := by
      by_contra hv_pos
      have : k ∈ S := not_le.mp hv_pos
      rw [hS_empty] at this
      exact Set.not_mem_empty k this
    exact le_antisymm this (hv_nonneg k)
  by_cases hT_is_empty : T = ∅
  · -- All entries positive case
    have v_all_pos : ∀ i, v i > 0 := by
      intro i
      have hi_not_in_T : i ∉ T := by simp [hT_is_empty]
      have hi_ne_zero : v i ≠ 0 := by simpa [T] using hi_not_in_T
      exact lt_of_le_of_ne (hv_nonneg i) (id (Ne.symm hi_ne_zero))
    have A_is_zero : A = 0 := by
      ext k j
      have : (A *ᵥ v) k = 0 := congrFun h_Av_zero k
      rw [mulVec, dotProduct] at this
      have terms_nonneg : ∀ idx, 0 ≤ A k idx * v idx :=
        fun idx => mul_nonneg (hA_nonneg k idx) (le_of_lt (v_all_pos idx))
      have term_kj_is_zero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => terms_nonneg i)).mp this j (Finset.mem_univ _)
      exact (mul_eq_zero.mp term_kj_is_zero).resolve_right (v_all_pos j).ne'
    exact hA_ne_zero A_is_zero
  · -- Mixed case: we use boundary crossing
    have hT_nonempty : T.Nonempty := Set.nonempty_iff_ne_empty.mpr hT_is_empty
    obtain ⟨i, j, hi_T, hj_S, hA_ij_pos⟩ := exists_boundary_crossing_in_support
      hA_irred hA_nonneg hv_nonneg hv_ne_zero S T hS_nonempty hT_nonempty
      (fun i => by simp [S]) (fun i => by simp [T])
    have hA_ij_zero : A i j = 0 := by
      have : (A *ᵥ v) i = 0 := congrFun h_Av_zero i
      rw [mulVec, dotProduct] at this
      have terms_nonneg : ∀ k ∈ Finset.univ, 0 ≤ A i k * v k :=
        fun k _ => mul_nonneg (hA_nonneg i k) (hv_nonneg k)
      have term_j_is_zero := (Finset.sum_eq_zero_iff_of_nonneg terms_nonneg).mp this j (Finset.mem_univ _)
      have hv_j_pos : v j > 0 := by simp [S] at hj_S; exact hj_S
      exact (mul_eq_zero.mp term_j_is_zero).resolve_right (ne_of_gt hv_j_pos)
    exact (ne_of_gt hA_ij_pos) hA_ij_zero

-- Additional helper for the main theorem
theorem exists_collatzWielandt_maximizer [Fintype n] [Nonempty n] :
    ∃ v ∈ stdSimplex ℝ n, IsMaxOn (collatzWielandtFn A) (stdSimplex ℝ n) v := by
  have h_compact : IsCompact (stdSimplex ℝ n) := isCompact_stdSimplex
  have h_nonempty : (stdSimplex ℝ n).Nonempty := stdSimplex_nonempty
  have h_usc : UpperSemicontinuousOn (collatzWielandtFn A) (stdSimplex ℝ n) :=
    upperSemicontinuousOn_collatzWielandtFn A
  exact IsCompact.exists_isMaxOn_of_upperSemicontinuousOn h_compact h_nonempty h_usc

/-- The standard simplex in ℝⁿ is compact (Heine-Borel: closed and bounded in ℝⁿ).
    [Giaquinta-Modica, Theorem 6.3, cite: 230] -/
lemma IsCompact_stdSimplex [Fintype n] : IsCompact (stdSimplex ℝ n) := by
  -- stdSimplex is a closed and bounded subset of ℝⁿ
  exact _root_.isCompact_stdSimplex n

/-- The Collatz-Wielandt function is upper semicontinuous on the standard simplex.
    [Giaquinta-Modica, Definition 6.21, Exercise 6.28, cite: 235, 236] -/
lemma UpperSemicontinuousOn_collatzWielandtFn [Fintype n]  [Nonempty n]
    (A : Matrix n n ℝ) : UpperSemicontinuousOn (Matrix.collatzWielandtFn A) (stdSimplex ℝ n) := by
  exact Matrix.upperSemicontinuousOn_collatzWielandtFn A

/-- The Collatz-Wielandt function attains its maximum on the standard simplex.
    [Giaquinta-Modica, Theorem 6.24 (dual), cite: 235] -/
theorem exists_maximum_collatzWielandt [Fintype n] [Nonempty n] (A : Matrix n n ℝ) :
    ∃ v ∈ stdSimplex ℝ n, ∀ x ∈ stdSimplex ℝ n,
      Matrix.collatzWielandtFn A x ≤ Matrix.collatzWielandtFn A v := by
  exact exists_collatzWielandt_maximizer

theorem collatzWielandtFn_eq_iInf_of_nonempty
  {n : Type*} [Fintype n] [Nonempty n] (A : Matrix n n ℝ)
  (v : n → ℝ) (h : {i | 0 < v i}.toFinset.Nonempty) :
  collatzWielandtFn A v =
    ⨅ i : {i | 0 < v i}, (A *ᵥ v) i / v i := by
  dsimp [collatzWielandtFn]
  rw [dif_pos h]
  rw [Finset.inf'_eq_ciInf h]
  refine Function.Surjective.iInf_congr ?_ (fun b ↦ ?_) ?_
  intro i
  · simp_all only [toFinset_setOf]
    obtain ⟨val, property⟩ := i
    simp_all only [toFinset_setOf, mem_filter, Finset.mem_univ, true_and]
    apply Subtype.mk
    · exact property
  · simp_all
    obtain ⟨val, property⟩ := b
    simp_all only [Subtype.mk.injEq, exists_prop, exists_eq_right]
  simp [Set.mem_toFinset]

theorem mul_vec_mul_vec
  {n : Type*} [Fintype n] [Nonempty n] (A B : Matrix n n ℝ) (v : n → ℝ) :
  (A * B) *ᵥ v = A *ᵥ (B *ᵥ v) := by
  ext i
  simp only [mulVec, dotProduct, mul_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp [mul_assoc]

variable --{n : Type*} [Fintype n] [DecidableEq n]
          {A : Matrix n n ℝ} {r : ℝ}

/-- A non-negative, non-zero vector must have a positive component. -/
lemma exists_pos_of_ne_zero {v : n → ℝ} (h_nonneg : ∀ i, 0 ≤ v i) (h_ne_zero : v ≠ 0) :
    ∃ i, 0 < v i := by
  by_contra h_all_nonpos
  apply h_ne_zero
  ext i
  exact le_antisymm (by simp_all only [ne_eq, not_exists, not_lt, Pi.zero_apply]) (h_nonneg i)

/-- A set is nonempty if and only if its finite conversion is nonempty. -/
lemma Set.toFinset_nonempty_iff {α : Type*} [Fintype α] [DecidableEq α] (s : Set α) [Finite s] [Fintype s] :
    s.toFinset.Nonempty ↔ s.Nonempty := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, Set.mem_toFinset.mp hx⟩
  · intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, Set.mem_toFinset.mpr hx⟩

/-- Division inequality: a / b ≤ c ↔ a ≤ c * b when b > 0. -/
lemma div_le_iff {a b c : ℝ} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b := by
  rw [@le_iff_le_iff_lt_iff_lt]
  exact lt_div_iff₀ hb

/-- For real numbers, if `0 < b`, then `a ≤ c * b ↔ a / b ≤ c`. -/
lemma le_div_iff {a b c : ℝ} (hb : 0 < b) : a ≤ c * b ↔ a / b ≤ c := by
  rw [←div_le_iff hb]

/-- If r ≤ 0 and r is the infimum of non-negative ratios, then r = 0. -/
lemma collatzWielandt_val_eq_zero_of_nonpos [Fintype n] [Nonempty n] [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
    (S : Set n) (hS_def : S = {i | 0 < v i}) (hS_nonempty : S.Nonempty)
    (r : ℝ) (hr_def : r = collatzWielandtFn A v) (hr_nonpos : r ≤ 0) :
    r = 0 := by
  have r_ge_zero : 0 ≤ r := by
    rw [hr_def, collatzWielandtFn]
    have hS_finset_nonempty : { j | 0 < v j }.toFinset.Nonempty := by
      rwa [Set.toFinset_nonempty_iff, ← hS_def]
    rw [dif_pos hS_finset_nonempty]
    apply Finset.le_inf'
    intro j hj
    rw [Set.mem_toFinset] at hj
    exact div_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (hA_nonneg j k) (hv_nonneg k)) hj.le
  exact le_antisymm hr_nonpos r_ge_zero

/-- The ratio (A *ᵥ v) i / v i is nonnegative when A has nonnegative entries and v is nonnegative -/
lemma ratio_nonneg [Fintype n] (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
    (i : n) (hv_pos : 0 < v i) : 0 ≤ (A *ᵥ v) i / v i :=
  div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hA_nonneg i j) (hv_nonneg j)) hv_pos.le

/-- Each ratio is at least the Collatz-Wielandt value -/
lemma collatzWielandt_le_ratio [Fintype n] [Nonempty n] [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
    (S : Set n) (hS_def : S = {i | 0 < v i}) (hS_nonempty : S.Nonempty)
    (i : n) (hi_S : i ∈ S) : collatzWielandtFn A v ≤ (A *ᵥ v) i / v i := by
  rw [collatzWielandtFn]
  have hS_finset_nonempty : { j | 0 < v j }.toFinset.Nonempty := by
    rwa [Set.toFinset_nonempty_iff, ← hS_def]
  rw [dif_pos hS_finset_nonempty]
  apply Finset.inf'_le
  rw [Set.mem_toFinset, ← hS_def]
  exact hi_S

lemma Finset.inf'_pos {α : Type*} {s : Finset α} (hs : s.Nonempty)
    {f : α → ℝ} (h_pos : ∀ a ∈ s, 0 < f a) :
    0 < s.inf' hs f := by
  obtain ⟨b, hb_mem, h_fb_is_inf⟩ := s.exists_mem_eq_inf' hs f
  have h_fb_pos : 0 < f b := h_pos b hb_mem
  rw [h_fb_is_inf]
  exact h_fb_pos

lemma lt_not_le {α : Type*} [PartialOrder α] (x y : α) : x < y → ¬ (x ≥ y) := by
  intro h_lt h_ge
  exact not_le_of_lt h_lt h_ge

/-- For any non-negative, non-zero vector `v`, the Collatz-Wielandt value `r` satisfies
    `r • v ≤ A *ᵥ v`. This is the fundamental inequality derived from the definition of
    the Collatz-Wielandt function. -/
lemma collatzWielandt_le_mulVec [Fintype n] [Nonempty n] [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
    (hv_ne_zero : v ≠ 0) :
    (collatzWielandtFn A v) • v ≤ A *ᵥ v := by
  let r := collatzWielandtFn A v
  -- The support of `v` is non-empty because `v` is a non-zero vector.
  have hS_nonempty : ({i | 0 < v i}).Nonempty :=
    exists_pos_of_ne_zero hv_nonneg hv_ne_zero
  intro i
  by_cases hi_supp : v i > 0
  · -- If `v i > 0`, then `i` is in the support.
    have h_le_div : r ≤ (A *ᵥ v) i / v i :=
      collatzWielandt_le_ratio hA_nonneg hv_nonneg {i | 0 < v i} rfl hS_nonempty i hi_supp
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (le_div_iff₀ hi_supp).mp h_le_div
  · -- If `v i = 0`, we need to show `(r • v) i ≤ (A * v) i`.
    have h_vi_zero : v i = 0 := by linarith [hv_nonneg i, not_lt.mp hi_supp]
    simp only [Pi.smul_apply, smul_eq_mul, h_vi_zero, mul_zero]
    exact mulVec_nonneg hA_nonneg hv_nonneg i

/-- If the ratio (A *ᵥ v) i / v i = 0 and v i > 0, then (A *ᵥ v) i = 0. -/
lemma mulVec_eq_zero_of_ratio_zero [Fintype n] {v : n → ℝ} (i : n) (hv_pos : 0 < v i)
    (h_ratio_zero : (A *ᵥ v) i / v i = 0) :
    (A *ᵥ v) i = 0 := by
  rw [div_eq_zero_iff] at h_ratio_zero
  exact h_ratio_zero.resolve_right (ne_of_gt hv_pos)

/-- A zero matrix is not irreducible if the dimension is greater than 1. -/
lemma not_irreducible_of_zero_matrix {n : Type*} [Fintype n] [Nonempty n]
    (h_card_gt_one : 1 < Fintype.card n) : ¬ Irreducible (0 : Matrix n n ℝ) := by
  intro h_irred_contra
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card h_card_gt_one
  specialize h_irred_contra i j
  letI := toQuiver (0 : Matrix n n ℝ)
  have h_no_path : ¬ Nonempty (Quiver.Path i j) := by
      intro h
      obtain ⟨p⟩ := h
      induction p with
      | nil => exact hij rfl
      | cons p' e ih =>
        exact False.elim (lt_irrefl 0 e)
  exact h_no_path h_irred_contra

/-- If `A *ᵥ v` is zero on the support `S` of `v`, then for any `i ∈ S`, `A i k` must be zero
for all `k` where `v` is positive (i.e., `k ∈ S`). -/
lemma zero_block_of_mulVec_eq_zero [Fintype n] (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
    (S : Set n) (hS_def : S = {i | 0 < v i})
    (h_Av_zero : ∀ i ∈ S, (A *ᵥ v) i = 0) :
    ∀ i ∈ S, ∀ k ∈ S, A i k = 0 := by
  intro i hi_S k hk_S
  have h_sum_Aiv_eq_zero : (A *ᵥ v) i = 0 := h_Av_zero i hi_S
  rw [mulVec, dotProduct] at h_sum_Aiv_eq_zero
  have h_sum_terms_nonneg : ∀ l, 0 ≤ A i l * v l :=
    fun l ↦ mul_nonneg (hA_nonneg i l) (hv_nonneg l)
  have h_Aik_vk_zero : A i k * v k = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun l _ ↦ h_sum_terms_nonneg l)).mp h_sum_Aiv_eq_zero k (mem_univ k)
  rw [hS_def] at hk_S
  exact (mul_eq_zero.mp h_Aik_vk_zero).resolve_right (ne_of_gt hk_S)

end PerronFrobenius
end Matrix
