import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Exponential
import HopfieldNet.compareAux

set_option checkBinderAnnotations false
set_option linter.dupNamespace false


-- In Coq, IZR is the cast from Z to R. In Lean, this is `(↑· : ℤ → ℝ)`.
-- R is ℝ. Z is ℤ.
-- Coq's `radix` is a Z between 2 and max_Z. We define it as a subtype.
abbrev Radix := {β : ℤ // β ≥ 2}

namespace Rmissing
open Real

theorem Rle_0_minus (x y : ℝ) (h : x ≤ y) : 0 ≤ y - x :=
  sub_nonneg_of_le h
theorem Rabs_eq_Rabs (x y : ℝ) (h : abs x = abs y) : x = y ∨ x = -y :=
  abs_eq_abs.mp h
theorem Rabs_minus_le (x y : ℝ) (hy_nonneg : 0 ≤ y) (hy_le_2x : y ≤ 2 * x) :
    abs (x - y) ≤ x := by
  apply abs_le.mpr
  constructor <;> linarith -- `linarith` solves both goals

theorem Rabs_eq_R0 (x : ℝ) : abs x = 0 → x = 0 :=
  abs_eq_zero.mp

-- Rplus_eq_reg_r is add_right_cancel in Lean

theorem Rmult_lt_compat (r1 r2 r3 r4 : ℝ) (hr1_nonneg : 0 ≤ r1) (hr3_nonneg : 0 ≤ r3)
    (h12 : r1 < r2) (h34 : r3 < r4) : r1 * r3 < r2 * r4 := by
  -- Proof structure from Flocq:
  -- r1*r3 <= r1*r4 (by hr1_nonneg, h34.le)
  -- r1*r4 < r2*r4 (by h12, r4 > 0 from hr3_nonneg.trans_lt h34)
  have hr4_pos : 0 < r4 := hr3_nonneg.trans_lt h34
  calc
    r1 * r3 ≤ r1 * r4 := mul_le_mul_of_nonneg_left h34.le hr1_nonneg
    _       < r2 * r4 := mul_lt_mul_of_pos_right h12 hr4_pos

theorem Rmult_neq_reg_r (r1 r2 r3 : ℝ) (h : r2 * r1 ≠ r3 * r1) : r2 ≠ r3 :=
  fun heq => h (by rw [heq])

universe u
variable {M₀ : Type u} [Mul M₀] [Zero M₀] [IsLeftCancelMulZero M₀] {a : M₀}

lemma mul_right_inj₀ (ha : a ≠ 0) : Function.Injective (a * ·) :=
  fun _ _ => mul_left_cancel₀ ha
theorem Rmult_neq_compat_r (r1 r2 r3 : ℝ) (hr1_ne_0 : r1 ≠ 0) (hr23_ne : r2 ≠ r3) :
    r2 * r1 ≠ r3 * r1 :=
  fun h => hr23_ne ((mul_right_inj₀ hr1_ne_0 (by rw [mul_comm r2, mul_comm r3] at h; exact h)))
theorem Rmult_min_distr_r (r r1 r2 : ℝ) (hr_nonneg : 0 ≤ r) :
    min r1 r2 * r = min (r1 * r) (r2 * r) := by
  rcases le_total r1 r2 with h_le | h_le
  · rw [min_eq_left h_le, min_eq_left (mul_le_mul_of_nonneg_right h_le hr_nonneg)]
  · rw [min_eq_right h_le, min_eq_right (mul_le_mul_of_nonneg_right h_le hr_nonneg)]
theorem Rmult_min_distr_l (r r1 r2 : ℝ) (hr_nonneg : 0 ≤ r) :
    r * min r1 r2 = min (r * r1) (r * r2) := by
  simp_rw [mul_comm r, Rmult_min_distr_r r r1 r2 hr_nonneg]
theorem Rmin_opp (x y : ℝ) : min (-x) (-y) = -max x y := min_neg_neg x y
theorem Rmax_opp (x y : ℝ) : max (-x) (-y) = -min x y := max_neg_neg x y
theorem exp_le (x y : ℝ) (h : x ≤ y) : exp x ≤ exp y := exp_monotone h
theorem Rinv_lt (x y : ℝ) (hx_pos : 0 < x) (hxy : x < y) : y⁻¹ < x⁻¹ :=
  inv_strictAnti₀ hx_pos hxy
theorem Rinv_le (x y : ℝ) (hx_pos : 0 < x) (hxy : x ≤ y) : y⁻¹ ≤ x⁻¹ :=
  inv_anti₀ hx_pos hxy
theorem sqrt_ge_0 (x : ℝ) : 0 ≤ sqrt x := sqrt_nonneg x
theorem sqrt_neg (x : ℝ) (hx_nonpos : x ≤ 0) : sqrt x = 0 :=
  sqrt_eq_zero_of_nonpos hx_nonpos

lemma Rsqr_le_abs_0_alt (x y : ℝ) (h_sq_le : x^2 ≤ y^2) : x ≤ abs y :=
  (le_abs_self x).trans (sq_le_sq.mp h_sq_le)

theorem Rabs_le_inv (x y : ℝ) (h : abs x ≤ y) : -y ≤ x ∧ x ≤ y :=
  abs_le.mp h

-- Rabs_le is abs_le.mpr, Rabs_le_inv is abs_le.mp
-- Rabs_ge and Rabs_ge_inv for (x <= abs y) are le_abs and le_abs_iff
theorem Rabs_ge (x y : ℝ) (h : y ≤ -x ∨ x ≤ y) : x ≤ abs y := by
  rcases h with h_left | h_right
  · exact le_trans (le_neg_of_le_neg h_left) (neg_le_abs y)
  · exact le_trans h_right (le_abs_self y)

theorem Rabs_ge_inv (x y : ℝ) (h : x ≤ abs y) : y ≤ -x ∨ x ≤ y := by
  rcases le_or_gt 0 y with hy_nonneg | hy_neg
  · right; rw [abs_of_nonneg hy_nonneg] at h; exact h
  · left; rw [abs_of_neg hy_neg] at h
    exact le_neg_of_le_neg h

theorem Rabs_lt (x y : ℝ) (h : -y < x ∧ x < y) : abs x < y :=
  abs_lt.mpr h

theorem Rabs_lt_inv (x y : ℝ) (h : abs x < y) : -y < x ∧ x < y :=
  abs_lt.mp h

-- Rabs_lt is abs_lt.mpr, Rabs_lt_inv is abs_lt.mp
-- Rabs_gt and Rabs_gt_inv for (x < abs y) are lt_abs and lt_abs_iff
theorem Rabs_gt (x y : ℝ) (h : y < -x ∨ x < y) : x < abs y := by
  rcases h with h_left | h_right
  · exact (lt_neg_of_lt_neg h_left).trans_le (neg_le_abs y)
  · exact h_right.trans_le (le_abs_self y)

theorem Rabs_gt_inv (x y : ℝ) (h : x < abs y) : y < -x ∨ x < y := by
  rcases le_or_gt 0 y with hy_nonneg | hy_neg
  · right  -- Case: y ≥ 0
    rw [abs_of_nonneg hy_nonneg] at h
    exact h
  · left  -- Case: y < 0
    rw [abs_of_neg hy_neg] at h  -- h: x < -y
    exact lt_neg_of_lt_neg h  -- y < -x

end Rmissing

section IZR

theorem IZR_le_lt (m n p : ℤ) (h : m ≤ n ∧ n < p) :
    (↑m : ℝ) ≤ ↑n ∧ (↑n : ℝ) < ↑p :=
  ⟨Int.cast_le.mpr h.1, Int.cast_lt.mpr h.2⟩

theorem le_lt_IZR (m n p : ℤ) (h : (↑m : ℝ) ≤ ↑n ∧ (↑n : ℝ) < ↑p) :
    m ≤ n ∧ n < p :=
  ⟨Int.cast_le.mp h.1, Int.cast_lt.mp h.2⟩

theorem neq_IZR (m n : ℤ) (h_ne_cast : (↑m : ℝ) ≠ ↑n) : m ≠ n :=
  fun a ↦ h_ne_cast (congrArg Int.cast a)

end IZR

inductive Rcompare_prop (x y : ℝ) : Ordering → Prop
| lt : x < y → Rcompare_prop x y Ordering.lt
| eq : x = y → Rcompare_prop x y Ordering.eq
| gt : y < x → Rcompare_prop x y Ordering.gt

theorem Rcompare_spec (x y : ℝ) : Rcompare_prop x y (compare x y) :=
  match lt_trichotomy x y with
  | Or.inl hlt =>
      have : compare x y = Ordering.lt := compare_lt_iff_lt.mpr hlt
      this ▸ Rcompare_prop.lt hlt
  | Or.inr (Or.inl heq) =>
      have : compare x y = Ordering.eq := compare_eq_iff_eq.mpr heq
      this ▸ Rcompare_prop.eq heq
  | Or.inr (Or.inr hgt) =>
      have : compare x y = Ordering.gt := compare_gt_iff_gt.mpr hgt
      this ▸ Rcompare_prop.gt hgt

section Rcompare

theorem Rcompare_Lt (x y : ℝ) (h : x < y) : compare x y = Ordering.lt := compare_lt_iff_lt.mpr h
theorem Rcompare_Lt_inv (x y : ℝ) (h : compare x y = Ordering.lt) : x < y := compare_lt_iff_lt.mp h
theorem Rcompare_not_Lt (x y : ℝ) (h : y ≤ x) : compare x y ≠ Ordering.lt :=
  fun h_cmp_lt => not_lt_of_le h (compare_lt_iff_lt.mp h_cmp_lt)


theorem Rcompare_not_Lt_inv (x y : ℝ) (h_ne : compare x y ≠ Ordering.lt) : y ≤ x :=
  compare_ge_iff_ge.mp h_ne
theorem Rcompare_Eq (x y : ℝ) (h_eq : x = y) : compare x y = Ordering.eq := compare_eq_iff_eq.mpr h_eq
theorem Rcompare_Eq_inv (x y : ℝ) (h : compare x y = Ordering.eq) : x = y := compare_eq_iff_eq.mp h
theorem Rcompare_Gt (x y : ℝ) (h : y < x) : compare x y = Ordering.gt := compare_gt_iff_gt.mpr h

theorem Rcompare_Gt_inv (x y : ℝ) (h : compare x y = Ordering.gt) : y < x := compare_gt_iff_gt.mp h

theorem Rcompare_not_Gt (x y : ℝ) (h_le : x ≤ y) : compare x y ≠ Ordering.gt :=
  fun h_cmp_gt => not_le_of_gt (compare_gt_iff_gt.mp h_cmp_gt) h_le

theorem Rcompare_not_Gt_inv (x y : ℝ) (h_ne : compare x y ≠ Ordering.gt) : x ≤ y :=
  compare_le_iff_le.mp h_ne

theorem Rcompare_IZR (x y : ℤ) : compare (x : ℝ) (y : ℝ) = compare x y := by
  rcases lt_trichotomy x y with h | h | h
  · -- Case x < y
    rw [compare_lt_iff_lt.mpr (Int.cast_lt.mpr h), compare_lt_iff_lt.mpr h]
  · -- Case x = y
    rw [compare_eq_iff_eq.mpr (congrArg Int.cast h), compare_eq_iff_eq.mpr h]
  · -- Case y < x
    rw [compare_gt_iff_gt.mpr (Int.cast_lt.mpr h), compare_gt_iff_gt.mpr h]

theorem Rcompare_sym (x y : ℝ) : compare x y = (compare y x).swap := compare_swap x y

theorem Rcompare_opp (x y : ℝ) : compare (-x) (-y) = compare y x := by rw [compare_neg_neg, compare_swap]

theorem Rcompare_plus_r (z x y : ℝ) : compare (x + z) (y + z) = compare x y := compare_add_right_eq x y z

theorem Rcompare_plus_l (z x y : ℝ) : compare (z + x) (z + y) = compare x y := compare_add_left_eq x y z

theorem Rcompare_mult_r (z x y : ℝ) (hz_pos : 0 < z) :
    compare (x * z) (y * z) = compare x y := by
  by_cases h : x = y
  · rw [h]; simp [compare_eq_iff_eq.mpr rfl]
  · rcases lt_or_gt_of_ne h with h_lt | h_gt
    · have : x * z < y * z := mul_lt_mul_of_pos_right h_lt hz_pos
      rw [compare_lt_iff_lt.mpr this, compare_lt_iff_lt.mpr h_lt]
    · have : y * z < x * z := mul_lt_mul_of_pos_right h_gt hz_pos
      rw [compare_gt_iff_gt.mpr this, compare_gt_iff_gt.mpr h_gt]

theorem Rcompare_mult_l (z x y : ℝ) (hz_pos : 0 < z) :
    compare (z * x) (z * y) = compare x y := by
  rw [mul_comm z x, mul_comm z y]
  exact Rcompare_mult_r z x y hz_pos

theorem Rcompare_middle (x d u : ℝ) :
    compare (x - d) (u - x) = compare x ((d + u) / 2) := by
  rw [compare_sub_sub_equiv_compare_add_add x d u x]
  have h_x_plus_x_eq_2_mul_x : x + x = 2 * x := by ring
  have h_add_comm : u + d = d + u := by ring
  rw [h_add_comm]
  rw [h_x_plus_x_eq_2_mul_x]
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2_ne_zero : (2 : ℝ) ≠ 0 := ne_of_gt h2_pos
  have h_simp : 2 * ((d + u) / 2) = d + u := mul_div_cancel₀ (d + u) h2_ne_zero
  rw [← h_simp]
  convert Rcompare_mult_l 2 x ((d + u) / 2) h2_pos

theorem Rcompare_half_l (x y : ℝ) : compare (x / 2) y = compare x (2 * y) := by
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  rw [← Rcompare_mult_r 2 (x / 2) y h2_pos]
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel]
  rw [mul_comm]

theorem Rcompare_half_r (x y : ℝ) : compare x (y / 2) = compare (2 * x) y := by
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  rw [← Rcompare_mult_r 2 x (y / 2) h2_pos]
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel]
  rw [mul_comm]

--Theorem Rcompare_sqr : This is in `compareAux.lean`

theorem Rmin_compare (x y : ℝ) : min x y = match compare x y with
  | Ordering.lt => x
  | Ordering.eq => x
  | Ordering.gt => y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · rw [compare_lt_iff_lt.mpr hlt, min_eq_left_of_lt hlt]
  · rw [compare_eq_iff_eq.mpr heq, heq, min_self]
  · rw [compare_gt_iff_gt.mpr hgt, min_eq_right_of_lt hgt]

end Rcompare


namespace Rle_bool

/-- Boolean comparison for ≤ on ℝ using explicit computation.
  This is computable if `x` and `y` are computable reals (e.g., floats).
  For computable reals, use a typeclass or structure that supports effective comparison. -/
@[irreducible, inline] def Rle_bool {α : Type*} [Ord α] (x y : α) : Bool :=
  match compare x y with
  | Ordering.lt | Ordering.eq => true
  | Ordering.gt => false

inductive Rle_bool_prop {α : Type*} [Ord α] [LE α] [LT α] (x y : α) : Bool → Prop
| true_  : x ≤ y → Rle_bool_prop x y true
| false_ : y < x → Rle_bool_prop x y false

theorem Rle_bool_spec {α : Type*} [Ord α] [LE α] [LT α] (x y : α) :
  Rle_bool_prop x y (Rle_bool x y) := by {
    unfold Rle_bool
--     unfold Rle_bool.
-- case Rcompare_spec ; constructor.
-- now apply Rlt_le.
-- rewrite H.
-- apply Rle_refl.
-- exact H.
-- Qed.
    sorry
  }

theorem Rle_bool_true {α : Type*} [Ord α] [LE α]
  [LT α] (x y : α) (h : x ≤ y) : Rle_bool x y = true := sorry
-- Proof.
-- intros x y Hxy.
-- case Rle_bool_spec ; intros H.
-- apply refl_equal.
-- elim (Rlt_irrefl x).
-- now apply Rle_lt_trans with y.
-- Qed.

theorem Rle_bool_false {α : Type*} [Ord α] [LE α] [LT α] (x y : α)
  (h : y < x) : Rle_bool x y = false := by sorry
-- Proof.
-- intros x y Hxy.
-- case Rle_bool_spec ; intros H.
-- elim (Rlt_irrefl x).
-- now apply Rle_lt_trans with y.
-- apply refl_equal.
-- Qed.

end Rle_bool

section Rlt_bool

open Ordering

/-- Boolean comparison for < on α using compare. -/
@[irreducible, inline] def Rlt_bool {α : Type*} [Ord α] (x y : α) : Bool :=
  match compare x y with
  | Ordering.lt => true
  | _ => false

inductive Rlt_bool_prop {α : Type*} [Ord α] [LE α] [LT α] (x y : α) : Bool → Prop
| true_  : x < y → Rlt_bool_prop x y true
| false_ : y ≤ x → Rlt_bool_prop x y false

theorem Rlt_bool_spec {α : Type*} [Ord α] [LE α] [LT α] (x y : α) :
  Rlt_bool_prop x y (Rlt_bool x y) := by sorry


end Rlt_bool
