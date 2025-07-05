import HopfieldNet.Mathematics.Topology.Compactness.ExtremeValueUSC
import HopfieldNet.Mathematics.Combinatorics.Quiver.Path
import HopfieldNet.Mathematics.aux
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Metrizable.CompletelyMetrizable
namespace Matrix
open Finset Quiver
variable {n : Type*} [Fintype n]
/-!
### TThe Collatz-Wielandt function for  Matrices

-/
section PerronFrobenius
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

/-- The matrix-vector multiplication map as a continuous linear map. -/
noncomputable abbrev mulVec_continuousLinearMap (A : Matrix n n ℝ) : (n → ℝ) →L[ℝ] (n → ℝ) :=
  (Matrix.mulVecLin A).toContinuousLinearMap

omit [Nonempty n] in
/-- The standard simplex in ℝⁿ is compact (Heine-Borel: closed and bounded in ℝⁿ).
    [Giaquinta-Modica, Theorem 6.3, cite: 230] -/
private lemma IsCompact_stdSimplex : IsCompact (stdSimplex ℝ n) := by
  -- stdSimplex is a closed and bounded subset of ℝⁿ
  exact _root_.isCompact_stdSimplex n

namespace CollatzWielandt

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

/-- *The Collatz-Wielandt function is upper-semicontinuous*.
Seneta relies on this fact (p.15, Appendix C) to use the Extreme Value Theorem.
`r(x)` is a minimum of functions `fᵢ(x) = (Ax)ᵢ / xᵢ`. Each `fᵢ` is continuous where `xᵢ > 0`.
The minimum of continuous functions is upper-semicontinuous.
[Giaquinta-Modica, Definition 6.21, Exercise 6.28, pp: 235, 236] -/
theorem upperSemicontinuousOn
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

-- The set of vectors we are optimizing over.
def P_set := {x : n → ℝ | (∀ i, 0 ≤ x i) ∧ x ≠ 0}

-- The Collatz-Wielandt value is the supremum of `r_x` over P.
noncomputable def r (A : Matrix n n ℝ) [Fintype n] := ⨆ x ∈ P_set, collatzWielandtFn A x

/-- The Collatz-Wielandt function attains its maximum on the standard simplex.
    [Giaquinta-Modica, Theorem 6.24 (dual), p: 235] -/
theorem exists_maximizer :
    ∃ v ∈ stdSimplex ℝ n, IsMaxOn (collatzWielandtFn A) (stdSimplex ℝ n) v := by
  have h_compact : IsCompact (stdSimplex ℝ n) := isCompact_stdSimplex n
  have h_nonempty : (stdSimplex ℝ n).Nonempty := stdSimplex_nonempty
  have h_usc : UpperSemicontinuousOn (collatzWielandtFn A) (stdSimplex ℝ n) :=
    upperSemicontinuousOn A
  exact IsCompact.exists_isMaxOn_of_upperSemicontinuousOn h_compact h_nonempty h_usc

lemma eq_iInf_of_nonempty
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

omit [Nonempty n] in
/-- If r ≤ 0 and r is the infimum of non-negative ratios, then r = 0. -/
lemma val_eq_zero_of_nonpos [DecidableEq n]
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

omit [Nonempty n] in
/-- Each ratio is at least the Collatz-Wielandt value -/
lemma le_ratio [DecidableEq n]
    (_ : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (_ : ∀ i, 0 ≤ v i)
    (S : Set n) (hS_def : S = {i | 0 < v i}) (hS_nonempty : S.Nonempty)
    (i : n) (hi_S : i ∈ S) : collatzWielandtFn A v ≤ (A *ᵥ v) i / v i := by
  rw [collatzWielandtFn]
  have hS_finset_nonempty : { j | 0 < v j }.toFinset.Nonempty := by
    rwa [Set.toFinset_nonempty_iff, ← hS_def]
  rw [dif_pos hS_finset_nonempty]
  apply Finset.inf'_le
  rw [Set.mem_toFinset, ← hS_def]
  exact hi_S

omit [Nonempty n] in
/-- For any non-negative, non-zero vector `v`, the Collatz-Wielandt value `r` satisfies
    `r • v ≤ A *ᵥ v`. This is the fundamental inequality derived from the definition of
    the Collatz-Wielandt function. -/
lemma le_mulVec [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
    (hv_ne_zero : v ≠ 0) :
    (collatzWielandtFn A v) • v ≤ A *ᵥ v := by
  let r := collatzWielandtFn A v
  have hS_nonempty : ({i | 0 < v i}).Nonempty :=
    exists_pos_of_ne_zero hv_nonneg hv_ne_zero
  intro i
  by_cases hi_supp : v i > 0
  · have h_le_div : r ≤ (A *ᵥ v) i / v i :=
      le_ratio hA_nonneg hv_nonneg {i | 0 < v i} rfl hS_nonempty i hi_supp
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (le_div_iff₀ hi_supp).mp h_le_div
  · have h_vi_zero : v i = 0 := by linarith [hv_nonneg i, not_lt.mp hi_supp]
    simp only [Pi.smul_apply, smul_eq_mul, h_vi_zero, mul_zero]
    exact mulVec_nonneg hA_nonneg hv_nonneg i

omit [Fintype n] [Nonempty n] in
/-- If the Collatz-Wielandt value `r` is non-positive, there must be some `i` in the support of `v`
    where the ratio, and thus `(A * v) i`, is zero. -/
lemma exists_mulVec_eq_zero_on_support_of_nonpos [Fintype n]
  (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
  (h_supp_nonempty : {i | 0 < v i}.toFinset.Nonempty)
  (h_r_nonpos : collatzWielandtFn A v ≤ 0) :
  ∃ i ∈ {i | 0 < v i}.toFinset, (A *ᵥ v) i = 0 := by
  have r_nonneg : 0 ≤ collatzWielandtFn A v := by
    rw [collatzWielandtFn, dif_pos h_supp_nonempty]
    apply Finset.le_inf'
    intro i hi_mem
    exact div_nonneg (mulVec_nonneg hA_nonneg hv_nonneg i) (by exact hv_nonneg i)
  have r_eq_zero : collatzWielandtFn A v = 0 := le_antisymm h_r_nonpos r_nonneg
  rw [collatzWielandtFn, dif_pos h_supp_nonempty] at r_eq_zero
  obtain ⟨b, hb_mem, hb_eq⟩ := Finset.exists_mem_eq_inf' h_supp_nonempty (fun i => (A *ᵥ v) i / v i)
  have h_ratio_zero : (A *ᵥ v) b / v b = 0 := by rw [← hb_eq, r_eq_zero]
  have h_vb_pos : 0 < v b := by simpa [Set.mem_toFinset] using hb_mem
  exact ⟨b, hb_mem, mulVec_eq_zero_of_ratio_zero b h_vb_pos h_ratio_zero⟩

omit [Nonempty n] in
lemma le_any_ratio [DecidableEq n] (A : Matrix n n ℝ)
    {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0)
    (i : n) (hi_pos : 0 < x i) :
    collatzWielandtFn A x ≤ (A *ᵥ x) i / x i := by
  dsimp [collatzWielandtFn]
  have h_supp_nonempty : ({k | 0 < x k}.toFinset).Nonempty := by
    rw [Set.toFinset_nonempty_iff, Set.nonempty_def]
    obtain ⟨j, hj_ne_zero⟩ := Function.exists_ne_zero_of_ne_zero hx_ne_zero
    exact ⟨j, lt_of_le_of_ne (hx_nonneg j) hj_ne_zero.symm⟩
  rw [dif_pos h_supp_nonempty]
  apply Finset.inf'_le
  rw [Set.mem_toFinset]
  exact hi_pos

/-- The set of values from the Collatz-Wielandt function is bounded above by the maximum row sum of A. -/
lemma bddAbove [DecidableEq n] (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    BddAbove (collatzWielandtFn A '' {x | (∀ i, 0 ≤ x i) ∧ x ≠ 0}) := by
  use Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ∑ j, A i j)
  rintro y ⟨x, ⟨hx_nonneg, hx_ne_zero⟩, rfl⟩
  obtain ⟨m, _, h_max_eq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
  have h_xm_pos : 0 < x m := by
    obtain ⟨i, hi_pos⟩ : ∃ i, 0 < x i := by
      obtain ⟨j, hj⟩ := Function.exists_ne_zero_of_ne_zero hx_ne_zero
      exact ⟨j, lt_of_le_of_ne (hx_nonneg j) hj.symm⟩
    rw [← h_max_eq]
    exact lt_of_lt_of_le hi_pos (le_sup' x (Finset.mem_univ i))
  have h_le_ratio : collatzWielandtFn A x ≤ (A *ᵥ x) m / x m :=
    le_any_ratio A hx_nonneg hx_ne_zero m h_xm_pos
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
  exact le_trans h_le_ratio h_ratio_le

/-- The set of values from the Collatz-Wielandt function is non-empty. -/
lemma set_nonempty :
    (collatzWielandtFn A '' {x | (∀ i, 0 ≤ x i) ∧ x ≠ 0}).Nonempty := by
  let P_set := {x : n → ℝ | (∀ i, 0 ≤ x i) ∧ x ≠ 0}
  let x_ones : n → ℝ := fun _ ↦ 1
  have h_x_ones_in_set : x_ones ∈ P_set := by
    constructor
    · intro i; exact zero_le_one
    · intro h_zero
      have h_contra : (1 : ℝ) = 0 := by simpa [x_ones] using congr_fun h_zero (Classical.arbitrary n)
      exact one_ne_zero h_contra
  exact Set.Nonempty.image _ ⟨x_ones, h_x_ones_in_set⟩

omit [Fintype n] [Nonempty n] in
lemma smul [Fintype n] [Nonempty n] [DecidableEq n] {c : ℝ} (hc : 0 < c) (_ : ∀ i j, 0 ≤ A i j)
  {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne : x ≠ 0) :
  collatzWielandtFn A (c • x) = collatzWielandtFn A x := by
  dsimp [collatzWielandtFn]
  let S := {i | 0 < x i}.toFinset
  obtain ⟨i₀, hi₀⟩ := exists_pos_of_ne_zero hx_nonneg hx_ne
  have hS_nonempty : S.Nonempty := ⟨i₀, by simp [S, Set.mem_toFinset, hi₀]⟩
  have h_supp_eq : {i | 0 < (c • x) i}.toFinset = S := by
    ext i
    simp [S, Set.mem_toFinset, Set.mem_setOf_eq, smul_eq_mul, mul_pos_iff_of_pos_left hc]
  rw [dif_pos (h_supp_eq.symm ▸ hS_nonempty), dif_pos hS_nonempty]
  refine inf'_congr (Eq.symm h_supp_eq ▸ hS_nonempty) h_supp_eq ?_
  intro i hi
  simp only [mulVec_smul, smul_eq_mul, Pi.smul_apply]
  rw [mul_div_mul_left _ _ (ne_of_gt hc)]

end CollatzWielandt

end PerronFrobenius

end Matrix
#min_imports
