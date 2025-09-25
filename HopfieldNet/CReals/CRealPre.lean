import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Ring
import Mathlib

--set_option maxHeartbeats 800000

/-!
# Foundational Definitions for Computable Real Numbers
-/

namespace Computable
open scoped Mathlib
/--
`CReal.Pre` is the pre-quotient representation of a computable real number.
It is a regular Cauchy sequence: |approx n - approx m| ≤ 1/2^n for n ≤ m.
(Bounds are derivable from regularity).
-/
structure CReal.Pre where
  approx : ℕ → ℚ
  is_regular : ∀ n m, n ≤ m → |approx n - approx m| ≤ (1 : ℚ) / (2 ^ n)

-- Helper for transitivity: existence of powers.
theorem exists_pow_gt {x : ℚ} (_ : 0 < x) : ∃ n : ℕ, x < (2 : ℚ) ^ n :=
  pow_unbounded_of_one_lt x rfl

lemma abs_add_four (a b c d : ℚ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  calc |a + b + c + d|
      = |(a + b) + (c + d)| := by simp [add_assoc]
  _ ≤ |a + b| + |c + d| := abs_add_le (a + b) (c + d)
  _ ≤ (|a| + |b|) + (|c| + |d|) := add_le_add (abs_add_le a b) (abs_add_le c d)
  _ = |a| + |b| + |c| + |d| := by simp [add_assoc]

namespace CReal.Pre

/-! ### Equivalence Relation -/

/--
Two pre-reals `x` and `y` are equivalent if |x.approx (n + 1) - y.approx (n + 1)| ≤ 1 / 2 ^ n.
-/
protected def Equiv (x y : CReal.Pre) : Prop :=
  ∀ n : ℕ, |x.approx (n + 1) - y.approx (n + 1)| ≤ (1 : ℚ) / 2 ^ n

infix:50 " ≈ " => CReal.Pre.Equiv

theorem equiv_refl (x : CReal.Pre) : x ≈ x := by
  intro n; simp

theorem equiv_symm {x y : CReal.Pre} (h : x ≈ y) : y ≈ x := by
  intro n; rw [abs_sub_comm]; exact h n

/--
Transitivity of the equivalence relation.
Uses the epsilon-delta approach (le_of_forall_pos_le_add).
-/
theorem equiv_trans {x y z : CReal.Pre} (hxy : x ≈ y) (hyz : y ≈ z) : x ≈ z := by
  intro k
  apply le_of_forall_pos_le_add
  intro ε hε
  -- we find m such that 1/2^m < ε.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 1 / ε < (2 : ℚ) ^ m := exists_pow_gt (one_div_pos.mpr hε)
  have h_eps_bound : (1:ℚ) / 2^m < ε := (one_div_lt (pow_pos (by norm_num) m) hε).mpr hm
  -- we choose m_idx ≥ k+1 and ≥ m+2.
  let m_idx := max (k + 1) (m + 2)
  have h_k_le_midx : k + 1 ≤ m_idx := le_max_left _ _
  have h_m_le_midx : m + 2 ≤ m_idx := le_max_right _ _
  have h_midx_ge_one : 1 ≤ m_idx := le_trans (by norm_num) h_k_le_midx
  -- we bound individual terms.
  have h₁ := x.is_regular (k+1) m_idx h_k_le_midx
  have h₄ : |z.approx m_idx - z.approx (k + 1)| ≤ (1 : ℚ) / 2 ^ (k + 1) := by
    rw [abs_sub_comm]; exact z.is_regular (k+1) m_idx h_k_le_midx
  have h₂ : |x.approx m_idx - y.approx m_idx| ≤ (1 : ℚ) / 2 ^ (m_idx - 1) := by
    simpa [Nat.sub_add_cancel h_midx_ge_one] using hxy (m_idx - 1)
  have h₃ : |y.approx m_idx - z.approx m_idx| ≤ (1 : ℚ) / 2 ^ (m_idx - 1) := by
    simpa [Nat.sub_add_cancel h_midx_ge_one] using hyz (m_idx - 1)
  -- we bound the error term 1/2^(m_idx-2) by ε.
  have h_error_bound : (1 : ℚ) / 2 ^ (m_idx - 2) ≤ (1 : ℚ) / 2 ^ m := by
    have h_le_m : m ≤ m_idx - 2 := Nat.le_sub_of_add_le h_m_le_midx
    rw [one_div_le_one_div (by positivity) (by positivity)]
    exact (pow_le_pow_iff_right₀ rfl).mpr h_le_m
  calc |x.approx (k + 1) - z.approx (k + 1)|
      ≤ |x.approx (k + 1) - x.approx m_idx|
        + |x.approx m_idx - y.approx m_idx|
        + |y.approx m_idx - z.approx m_idx|
        + |z.approx m_idx - z.approx (k + 1)| := by
          rw [show x.approx (k+1) - z.approx (k+1) = (x.approx (k+1) - x.approx m_idx) + (x.approx m_idx - y.approx m_idx) + (y.approx m_idx - z.approx m_idx) + (z.approx m_idx - z.approx (k+1)) by ring]
          exact abs_add_four _ _ _ _
    _ ≤ (1:ℚ) / 2^(k+1) + (1:ℚ) / 2^(m_idx-1) + (1:ℚ) / 2^(m_idx-1) + (1:ℚ) / 2^(k+1) := by
        gcongr
    _ = (1:ℚ) / 2^k + (1:ℚ) / 2^(m_idx-2) := by
        -- We need to show that
        -- (1/2^(k+1) + 1/2^(k+1)) + (1/2^(m_idx-1) + 1/2^(m_idx-1))
        -- = 1/2^k + 1/2^(m_idx-2)
        -- 1. First pair: 1/2^(k+1) + 1/2^(k+1) = 1/2^k
        have h₁ : (1:ℚ) / 2^(k+1) + (1:ℚ) / 2^(k+1) = (1:ℚ) / 2^k := by
          field_simp [pow_succ]
          ring
        -- 2. Second pair: 1/2^(m_idx-1) + 1/2^(m_idx-1) = 1/2^(m_idx-2)
        have h₂ : (1:ℚ) / 2^(m_idx-1) + (1:ℚ) / 2^(m_idx-1) = (1:ℚ) / 2^(m_idx-2) := by
          -- we combine fractions with same denominator
          have h : (1:ℚ) / 2^(m_idx-1) + (1:ℚ) / 2^(m_idx-1) = (2:ℚ) / 2^(m_idx-1) := by
            rw [← add_div]; rw [@one_add_one_eq_two]
          -- we simplify 2/2^(m_idx-1) to 1/2^(m_idx-2)
          rw [h]
          have h_midx_ge_two : 2 ≤ m_idx := le_trans (by norm_num) h_m_le_midx
          -- we relate the exponents: (m_idx-2)+1 = m_idx-1
          have h_exp : m_idx - 1 = (m_idx - 2) + 1 := by omega
          rw [h_exp, pow_succ]
          field_simp
        calc
          (1:ℚ) / 2^(k+1) + (1:ℚ) / 2^(m_idx-1) + (1:ℚ) / 2^(m_idx-1) + (1:ℚ) / 2^(k+1)
          = ((1:ℚ) / 2^(k+1) + (1:ℚ) / 2^(k+1)) + ((1:ℚ) / 2^(m_idx-1) + (1:ℚ) / 2^(m_idx-1)) := by
              ring_nf
          _ = (1:ℚ) / 2^k + (1:ℚ) / 2^(m_idx-2) := by
              rw [h₁, h₂]
    _ ≤ (1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ m := by gcongr;
    _ ≤ (1 : ℚ) / 2 ^ k + ε := by linarith [h_eps_bound]

instance setoid : Setoid CReal.Pre where
  r := CReal.Pre.Equiv
  iseqv := {
    refl  := equiv_refl
    symm  := equiv_symm
    trans := equiv_trans
  }

/-! ### Boundedness and Canonical Bounds -/

/--
Canonical Bound (cBound): `⌈|x₀|⌉ + 1`. Strictly positive and constructively defined.
-/
def cBound (x : CReal.Pre) : ℕ := Nat.ceil |x.approx 0| + 1

lemma cBound_pos (x : CReal.Pre) : 0 < x.cBound := Nat.succ_pos _

/-- Proof that `cBound` is a uniform bound. -/
lemma abs_approx_le_cBound (x : CReal.Pre) (n : ℕ) : |x.approx n| ≤ x.cBound := by
  dsimp [cBound]
  have h_reg : |x.approx n - x.approx 0| ≤ (1 : ℚ) := by
    simpa [abs_sub_comm, pow_zero, one_div] using x.is_regular 0 n (Nat.zero_le _)
  have h_ceil : |x.approx 0| ≤ (Nat.ceil |x.approx 0| : ℚ) := Nat.le_ceil _
  have h_triangle : |x.approx n| ≤ |x.approx n - x.approx 0| + |x.approx 0| :=
    calc |x.approx n|
      = |(x.approx n - x.approx 0) + x.approx 0| := by ring_nf
    _ ≤ |x.approx n - x.approx 0| + |x.approx 0| := abs_add_le (x.approx n - x.approx 0) (x.approx 0)
  calc
    |x.approx n| ≤ |x.approx n - x.approx 0| + |x.approx 0| := h_triangle
    _ ≤ 1 + |x.approx 0| := by linarith [h_reg]
    _ ≤ 1 + (Nat.ceil |x.approx 0| : ℚ) := by linarith [h_ceil]
    _ = (Nat.ceil |x.approx 0| : ℚ) + 1 := by rw [add_comm]
    _ = (↑(Nat.ceil |x.approx 0|) + 1 : ℚ) := by norm_cast
    _ = (↑(Nat.ceil |x.approx 0| + 1) : ℚ) := by norm_cast

end CReal.Pre

/--
The type of computable real numbers.
-/
abbrev CReal := Quotient (CReal.Pre.setoid)

namespace CReal

/-! ### Basic Arithmetic (Zero, Neg, Add) -/

/-- The `CReal.Pre` representation of `0`. -/
protected def Pre.zero : CReal.Pre where
  approx := fun _ ↦ 0
  is_regular := by intro n m _; simp

instance : Zero CReal := ⟨⟦CReal.Pre.zero⟧⟩

/-- Negation of a `CReal.Pre`. -/
protected def Pre.neg (x : CReal.Pre) : CReal.Pre where
  approx := fun n ↦ -x.approx n
  is_regular := by
    intro n m h_le; rw [neg_sub_neg, abs_sub_comm]; exact x.is_regular n m h_le

theorem neg_respects_equiv (x y : CReal.Pre) (h : CReal.Pre.Equiv x y) :
    CReal.Pre.Equiv (CReal.Pre.neg x) (CReal.Pre.neg y) := by
  intro n
  dsimp [CReal.Pre.neg, CReal.Pre.Equiv]
  simp only [neg_sub_neg, abs_sub_comm]
  exact h n

instance : Neg CReal := ⟨Quotient.map Pre.neg neg_respects_equiv⟩

/--
Addition of two `CReal.Pre`s. Shifted by 1 to maintain regularity.
-/
protected def Pre.add (x y : CReal.Pre) : CReal.Pre where
  approx := fun n ↦ x.approx (n + 1) + y.approx (n + 1)
  is_regular := by
    intro n m h_le
    have h_le_succ : n + 1 ≤ m + 1 := Nat.succ_le_succ h_le
    calc
      |(x.approx (n + 1) + y.approx (n + 1)) - (x.approx (m + 1) + y.approx (m + 1))|
        = |(x.approx (n + 1) - x.approx (m + 1)) + (y.approx (n + 1) - y.approx (m + 1))| := by ring_nf
      _ ≤ |x.approx (n + 1) - x.approx (m + 1)| + |y.approx (n + 1) - y.approx (m + 1)| :=
          abs_add_le (x.approx (n + 1) - x.approx (m + 1)) (y.approx (n + 1) - y.approx (m + 1))
      _ ≤ (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1) := by
        gcongr
        · exact x.is_regular (n + 1) (m + 1) h_le_succ
        · exact y.is_regular (n + 1) (m + 1) h_le_succ
      _ = (1 : ℚ) / 2 ^ n := by field_simp [pow_succ]; ring

theorem add_respects_equiv {x₁ x₂ y₁ y₂ : CReal.Pre} (h_x : CReal.Pre.Equiv x₁ x₂) (h_y : CReal.Pre.Equiv y₁ y₂) :
    CReal.Pre.Equiv (CReal.Pre.add x₁ y₁) (CReal.Pre.add x₂ y₂) := by
  intro n
  dsimp [CReal.Pre.add, CReal.Pre.Equiv]
  calc
    _ = |(x₁.approx (n + 2) - x₂.approx (n + 2)) + (y₁.approx (n + 2) - y₂.approx (n + 2))| := by ring_nf
    _ ≤ |x₁.approx (n + 2) - x₂.approx (n + 2)| + |y₁.approx (n + 2) - y₂.approx (n + 2)| :=
      abs_add_le (x₁.approx (n + 2) - x₂.approx (n + 2)) (y₁.approx (n + 2) - y₂.approx (n + 2))
    _ ≤ (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1) := by
        gcongr
        · exact h_x (n + 1)
        · exact h_y (n + 1)
    _ = (1 : ℚ) / 2 ^ n := by field_simp [pow_succ]; ring

/-- Addition on `CReal`. -/
instance : Add CReal := by
  refine ⟨Quotient.map₂ CReal.Pre.add ?_⟩
  intro a₁ a₂ h₁ b₁ b₂ h₂
  exact add_respects_equiv h₁ h₂

/-! ### Multiplication -/

-- Helper lemmas for bounding and logarithms.

/-- `B ≤ 2^(log₂ B + 1)` for B > 0. -/
lemma le_pow_log_succ (B : ℕ) (_ : 0 < B) :
    (B : ℚ) ≤ 2 ^ (Nat.log 2 B + 1) := by
  exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) B).le

/-- `2^a + 2^b ≤ 2^(max a b + 1)`. -/
lemma two_pow_add_le_pow_max_add_one (a b : ℕ) :
    (2 : ℚ) ^ a + 2 ^ b ≤ 2 ^ (max a b + 1) := by
  have h_max : (2:ℚ)^a ≤ (2:ℚ)^(max a b) := (pow_le_pow_iff_right₀ (by norm_num)).mpr (le_max_left a b)
  have h_max' : (2:ℚ)^b ≤ (2:ℚ)^(max a b) := (pow_le_pow_iff_right₀ (by norm_num)).mpr (le_max_right a b)
  calc
    _ ≤ (2:ℚ)^(max a b) + (2:ℚ)^(max a b) := add_le_add h_max h_max'
    _ = 2 ^ (max a b + 1) := by rw [pow_succ, ← two_mul]; exact Rat.mul_comm 2 (2 ^ max a b)

/-- Bounds Bx + By by a power of 2 based on their logs. -/
lemma add_bounds_le_power_of_two (Bx By : ℕ) (hBx : 0 < Bx) (hBy : 0 < By) :
    (Bx + By : ℚ) ≤ 2 ^ (max (Nat.log 2 Bx + 1) (Nat.log 2 By + 1) + 1) := by
  calc
    (Bx + By : ℚ) ≤ 2 ^ (Nat.log 2 Bx + 1) + 2 ^ (Nat.log 2 By + 1) :=
      add_le_add (le_pow_log_succ Bx hBx) (le_pow_log_succ By hBy)
    _ ≤ 2 ^ (max (Nat.log 2 Bx + 1) (Nat.log 2 By + 1) + 1) :=
      two_pow_add_le_pow_max_add_one _ _

/--
The precision shift S for multiplication. S = `max (log Bx + 1) (log By + 1) + 1`.
-/
def Pre.mulShift (x y : CReal.Pre) : ℕ :=
  let Bx := x.cBound
  let By := y.cBound
  max (Nat.log 2 Bx + 1) (Nat.log 2 By + 1) + 1

/-- Key property: Bx + By ≤ 2^S. -/
lemma Pre.sum_cBound_le_pow_mulShift (x y : CReal.Pre) :
    (x.cBound + y.cBound : ℚ) ≤ 2 ^ (x.mulShift y) := by
  dsimp [mulShift]
  apply add_bounds_le_power_of_two <;> apply CReal.Pre.cBound_pos

/--
**Core Product Estimate**.
`|xₙ yₙ - xₘ yₘ| ≤ (Bx + By) * (1 / 2 ^ n)` whenever
• `kₙ ≤ kₘ`
• `|xₙ| ≤ Bx` and `|yₘ| ≤ By`.
-/
lemma product_diff_bound
    (x y : CReal.Pre) {kₙ kₘ : ℕ} (h_le : kₙ ≤ kₘ)
    (Bx By : ℚ) (hxB : |x.approx kₙ| ≤ Bx) (hyB : |y.approx kₘ| ≤ By) :
    |x.approx kₙ * y.approx kₙ - x.approx kₘ * y.approx kₘ| ≤
      (Bx + By) * (1 / 2 ^ kₙ) := by
  -- Regularity (Cauchy) bounds for the two sequences.
  have h_xreg : |x.approx kₙ - x.approx kₘ| ≤ (1 : ℚ) / 2 ^ kₙ :=
    x.is_regular kₙ kₘ h_le
  have h_yreg : |y.approx kₙ - y.approx kₘ| ≤ (1 : ℚ) / 2 ^ kₙ :=
    y.is_regular kₙ kₘ h_le
  -- Non-negativity of the bounding constants.
  have hBx_nonneg : (0 : ℚ) ≤ Bx := le_trans (abs_nonneg _) hxB
  have hBy_nonneg : (0 : ℚ) ≤ By := le_trans (abs_nonneg _) hyB
  calc
    |x.approx kₙ * y.approx kₙ - x.approx kₘ * y.approx kₘ|
        = |x.approx kₙ * (y.approx kₙ - y.approx kₘ) +
            y.approx kₘ * (x.approx kₙ - x.approx kₘ)| := by
          ring_nf
    _ ≤ |x.approx kₙ * (y.approx kₙ - y.approx kₘ)| +
        |y.approx kₘ * (x.approx kₙ - x.approx kₘ)| := by
          exact abs_add_le _ _
    _ = |x.approx kₙ| * |y.approx kₙ - y.approx kₘ| +
        |y.approx kₘ| * |x.approx kₙ - x.approx kₘ| := by
          simp [abs_mul]
    _ ≤ Bx * (1 / 2 ^ kₙ) + By * (1 / 2 ^ kₙ) := by
      have h1 : |x.approx kₙ| * |y.approx kₙ - y.approx kₘ| ≤
          Bx * (1 / 2 ^ kₙ) := by
        have := mul_le_mul hxB h_yreg (abs_nonneg _) hBx_nonneg
        simpa using this
      have h2 : |y.approx kₘ| * |x.approx kₙ - x.approx kₘ| ≤
          By * (1 / 2 ^ kₙ) := by
        have := mul_le_mul hyB h_xreg (abs_nonneg _) hBy_nonneg
        simpa using this
      linarith
    _ = (Bx + By) * (1 / 2 ^ kₙ) := by ring

/--
The product of two `CReal.Pre`s. (x*y)_n := x_{n+S} * y_{n+S}.
-/
protected def Pre.mul (x y : CReal.Pre) : CReal.Pre where
  approx := fun n ↦
    let S := x.mulShift y
    x.approx (n + S) * y.approx (n + S)
  is_regular := by
    intro n m hnm
    let S := x.mulShift y
    let kₙ := n + S; let kₘ := m + S
    have hknm : kₙ ≤ kₘ := add_le_add_right hnm S
    let Bx := x.cBound; let By := y.cBound
    have h_core := product_diff_bound x y hknm (Bx:ℚ) (By:ℚ) (x.abs_approx_le_cBound kₙ) (y.abs_approx_le_cBound kₘ)
    have h_S := x.sum_cBound_le_pow_mulShift y
    calc
      _ ≤ (Bx + By : ℚ) * (1 / 2 ^ kₙ) := h_core
      _ ≤ (2 ^ S : ℚ) * (1 / 2 ^ kₙ) := mul_le_mul_of_nonneg_right h_S (by positivity)
      _ = (1 : ℚ) / 2 ^ n := by
        dsimp [kₙ]; rw [pow_add]; field_simp [pow_ne_zero]

/--
First half of the product estimate used in `mul_equiv_same_index`.
`|x₁ₖ|` is controlled by a bound `Bx₁`, while the difference
`|y₁ₖ − y₂ₖ|` is controlled by the `Equiv` relation.
-/
lemma prod_diff_bound_left
    {x₁ y₁ y₂ : CReal.Pre} {K : ℕ}
    (Bx₁ : ℚ) (h_x_bound : |x₁.approx K| ≤ Bx₁)
    (h_y_diff : |y₁.approx K - y₂.approx K| ≤ 1 / 2 ^ (K - 1)) :
    |x₁.approx K| * |y₁.approx K - y₂.approx K| ≤
      Bx₁ * (1 / 2 ^ (K - 1)) := by
  have hBx_nonneg : (0 : ℚ) ≤ Bx₁ := le_trans (abs_nonneg _) h_x_bound
  exact mul_le_mul h_x_bound h_y_diff (abs_nonneg _) hBx_nonneg

/--
Second half of the product estimate (roles of the factors swapped).
-/
lemma prod_diff_bound_right
    {y₂ x₁ x₂ : CReal.Pre} {K : ℕ}
    (By₂ : ℚ) (h_y_bound : |y₂.approx K| ≤ By₂)
    (h_x_diff : |x₁.approx K - x₂.approx K| ≤ 1 / 2 ^ (K - 1)) :
    |y₂.approx K| * |x₁.approx K - x₂.approx K| ≤
      By₂ * (1 / 2 ^ (K - 1)) := by
  have hBy_nonneg : (0 : ℚ) ≤ By₂ := le_trans (abs_nonneg _) h_y_bound
  exact mul_le_mul h_y_bound h_x_diff (abs_nonneg _) hBy_nonneg

/--
Add the two previous bounds and rewrite the right-hand side
into the convenient form `(Bx₁ + By₂)/2^(K-1)`.
-/
lemma prod_diff_sum_bound
    {x₁ x₂ y₁ y₂ : CReal.Pre} {K : ℕ}
    {Bx₁ By₂ : ℚ}
    (h₁ :
      |x₁.approx K| * |y₁.approx K - y₂.approx K| ≤
        Bx₁ * (1 / 2 ^ (K - 1)))
    (h₂ :
      |y₂.approx K| * |x₁.approx K - x₂.approx K| ≤
        By₂ * (1 / 2 ^ (K - 1))) :
    |x₁.approx K| * |y₁.approx K - y₂.approx K| +
      |y₂.approx K| * |x₁.approx K - x₂.approx K| ≤
      (Bx₁ + By₂) / 2 ^ (K - 1) := by
  have : (Bx₁ + By₂) / 2 ^ (K - 1) =
          Bx₁ * (1 / 2 ^ (K - 1)) +
          By₂ * (1 / 2 ^ (K - 1)) := by ring
  simpa [this] using add_le_add h₁ h₂

set_option maxHeartbeats 800000 in
lemma mul_equiv_same_index
    (x₁ x₂ y₁ y₂ : CReal.Pre) (K : ℕ) (hK : 0 < K)
    (h_x : CReal.Pre.Equiv x₁ x₂) (h_y : CReal.Pre.Equiv y₁ y₂) :
    |x₁.approx K * y₁.approx K - x₂.approx K * y₂.approx K| ≤
      (x₁.cBound + y₂.cBound : ℚ) / 2 ^ (K - 1) := by
  set Bx₁ : ℚ := (x₁.cBound : ℚ) with hBx₁
  set By₂ : ℚ := (y₂.cBound : ℚ) with hBy₂
  have hK_eq : K = (K - 1) + 1 := (Nat.succ_pred_eq_of_pos hK).symm
  have h_y_diff : |y₁.approx K - y₂.approx K| ≤ (1 : ℚ) / 2 ^ (K - 1) := by
    convert h_y (K - 1) using 2
    rw [hK_eq]; rw [Nat.add_succ_sub_one]
  have h_x_diff : |x₁.approx K - x₂.approx K| ≤ (1 : ℚ) / 2 ^ (K - 1) := by
    convert h_x (K - 1) using 2
    rw [hK_eq]; rw [Nat.add_succ_sub_one]
  have h_x_bound : |x₁.approx K| ≤ Bx₁ := by
    simpa [hBx₁] using x₁.abs_approx_le_cBound K
  have h_y_bound : |y₂.approx K| ≤ By₂ := by
    simpa [hBy₂] using y₂.abs_approx_le_cBound K
  have hBx_nonneg : (0 : ℚ) ≤ Bx₁ := by
    have : (0 : ℚ) ≤ (x₁.cBound : ℚ) := by exact_mod_cast (Nat.zero_le _)
    simp [hBx₁]
  have hBy_nonneg : (0 : ℚ) ≤ By₂ := by
    have : (0 : ℚ) ≤ (y₂.cBound : ℚ) := by exact_mod_cast (Nat.zero_le _)
    simp [hBy₂]
  have h_prod₁ := prod_diff_bound_left  Bx₁ h_x_bound h_y_diff
  have h_prod₂ := prod_diff_bound_right By₂ h_y_bound h_x_diff
  have := prod_diff_sum_bound (x₁:=x₁) (x₂:=x₂) (y₁:=y₁) (y₂:=y₂)
            h_prod₁ h_prod₂
  calc
    |x₁.approx K * y₁.approx K - x₂.approx K * y₂.approx K|
        = |x₁.approx K * (y₁.approx K - y₂.approx K) +
            y₂.approx K * (x₁.approx K - x₂.approx K)| := by ring_nf
    _ ≤ |x₁.approx K * (y₁.approx K - y₂.approx K)| +
        |y₂.approx K * (x₁.approx K - x₂.approx K)| :=
          abs_add_le _ _
    _ = |x₁.approx K| * |y₁.approx K - y₂.approx K| +
        |y₂.approx K| * |x₁.approx K - x₂.approx K| := by
          simp  [abs_mul]
    _ ≤ Bx₁ * (1 / 2 ^ (K - 1)) + By₂ * (1 / 2 ^ (K - 1)) := by
          linarith [h_prod₁, h_prod₂]
    _ = (Bx₁ + By₂) / 2 ^ (K - 1) := by
          rw [div_eq_mul_inv]; ring

lemma div_lt_iff {a b c : ℚ} (hb : 0 < b) : a / b < c ↔ a < c * b := by
  change a * b⁻¹ < c ↔ a < c * b
  rw [← mul_lt_mul_right hb]
  field_simp [hb.ne']

lemma div_le_div_of_le_of_nonneg {a _ c d : ℚ} (ha : 0 ≤ a) (hc : 0 < c) (_ : 0 < d) (h_le : c ≤ d) :
    a / d ≤ a / c := by
  gcongr

lemma lt_div_iff_mul_lt {a b c : ℚ} (hc : 0 < c) : a < b / c ↔ a * c < b := by
  rw [div_eq_mul_inv]
  exact lt_mul_inv_iff₀ hc

lemma div_lt_iff' {a b c : ℚ} (hc : 0 < c) : a / c < b ↔ a < b * c :=
  by exact div_lt_iff₀ hc

/-- Regularity bound :
for any indices `k_small ≤ k_big` we control
`|(x*y)ₖsmall  -  xₖbig * yₖbig|`. -/
lemma mul_regularity_bound
    (x y : CReal.Pre) {k_small k_big : ℕ} (h_le : k_small ≤ k_big) :
    |(x.mul y).approx k_small - (x.mul y).approx k_big|
      ≤ 1 / 2 ^ k_small := by
  dsimp [CReal.Pre.mul]
  set S := x.mulShift y
  let ks   := k_small + S
  let kbS  := k_big + S
  have h_le' : ks ≤ kbS := add_le_add_right h_le S
  have h_core :=
    product_diff_bound x y h_le' (x.cBound) (y.cBound)
      (x.abs_approx_le_cBound ks) (y.abs_approx_le_cBound kbS)
  have h_sum := x.sum_cBound_le_pow_mulShift y
  have : |x.approx ks * y.approx ks - x.approx kbS * y.approx kbS|
        ≤ (2 ^ S : ℚ) * (1 / 2 ^ ks) := by
    have h_pow_pos : 0 < (2 : ℚ) ^ ks := pow_pos (by norm_num) ks
    have h_nonneg : 0 ≤ (1 : ℚ) / 2 ^ ks := by
      have h1 : 0 ≤ (1 : ℚ) := by norm_num
      exact div_nonneg h1 (le_of_lt h_pow_pos)
    have h_mul : (x.cBound + y.cBound : ℚ) * (1 / 2 ^ ks)
             ≤ (2 ^ S : ℚ) * (1 / 2 ^ ks) :=
      mul_le_mul_of_nonneg_right h_sum h_nonneg
    exact h_core.trans h_mul
  simpa [ks, pow_add, mul_comm, mul_left_comm,
        mul_assoc, one_mul] using
    (calc
      |x.approx ks * y.approx ks - x.approx kbS * y.approx kbS|
          ≤ (2 ^ S : ℚ) * (1 / 2 ^ ks) := this
      _ = (1 : ℚ) / 2 ^ k_small := by
        dsimp [ks]; field_simp [pow_add]; ring)

/--  Equivalence (“middle”) bound at a *single* index `K`.  -/
alias mul_middle_bound := mul_equiv_same_index

/--  Given a positive ε, we can find an index `K` such that
`B / 2^(K-1) < ε`  -/
lemma mul_find_index
    {B ε : ℚ} (hB : 0 < B) (hε : 0 < ε) :
    ∃ K : ℕ, B / 2 ^ (K - 1) < ε := by
  -- we first find `K₀` with `B/ε < 2^K₀`.
  rcases exists_pow_gt (div_pos hB hε) with ⟨K₀, hK₀⟩
  have h_step : B / 2 ^ K₀ < ε := by
    have h1 : B < ε * 2 ^ K₀ := by
      have : B / ε < 2 ^ K₀ := hK₀
      have := (div_lt_iff hε).1 this
      simpa [mul_comm] using this
    have h_pow_pos : (0 : ℚ) < 2 ^ K₀ := pow_pos (by norm_num) _
    have : B / 2 ^ K₀ < ε := (div_lt_iff h_pow_pos).2 h1
    simpa using this
  refine ⟨K₀ + 1, ?_⟩
  simpa [Nat.add_sub_cancel] using h_step

lemma div_le_div_of_le {a b c : ℚ} (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr (le_of_lt hc))

lemma Nat.le_add_of_le_right {a b n : ℕ} (h : a ≤ b) : a ≤ b + n :=
  le_add_right h

lemma Nat.le_add_right_of_le {a b n : ℕ} (h : a ≤ b) : a ≤ b + n :=
  Nat.le_trans h (Nat.le_add_right _ _)

/--  If the numerator is non–negative and the denominators are
positive with `c ≤ d`, then `a / d ≤ a / c`. -/
lemma div_le_div_of_le_left
    {a c d : ℚ} (ha : 0 ≤ a) (hc : 0 < c) (h_le : c ≤ d) :
    a / d ≤ a / c := by
  have hd : 0 < d := lt_of_lt_of_le hc h_le
  -- `1/d ≤ 1/c`
  have h_inv : (1 : ℚ) / d ≤ 1 / c := by exact one_div_le_one_div_of_le hc h_le
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left h_inv ha

lemma div_le_div_of_le_right
    {a b c : ℚ} (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  simpa [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right h (inv_nonneg.mpr (le_of_lt hc))

lemma abs_approx_diff_le
    (x : CReal.Pre) (i j : ℕ) :
    |x.approx i - x.approx j| ≤ (1 : ℚ) / 2 ^ (min i j) := by
  cases le_total i j with
  | inl h_le =>
      simpa [min_eq_left h_le] using x.is_regular i j h_le
  | inr h_le' =>
      have h_le : j ≤ i := h_le'
      have := x.is_regular j i h_le
      simpa [abs_sub_comm, min_eq_right h_le] using this

/-- 1.  Triangle–inequality + Cauchy estimates:
gives the bound with the *minimum* index in the denominator. -/
lemma mul_approx_bound_min
    (x y : CReal.Pre) {ks kb : ℕ} :
    |x.approx ks * y.approx ks - x.approx kb * y.approx kb| ≤
      (x.cBound + y.cBound) * (1 / 2 ^ (min ks kb)) := by
  -- generic Cauchy bounds (always valid).
  have h_x : |x.approx ks - x.approx kb| ≤ (1 : ℚ) / 2 ^ (min ks kb) :=
    abs_approx_diff_le x _ _
  have h_y : |y.approx ks - y.approx kb| ≤ (1 : ℚ) / 2 ^ (min ks kb) :=
    abs_approx_diff_le y _ _
  have hxB : |x.approx kb| ≤ x.cBound := x.abs_approx_le_cBound kb
  have hyB : |y.approx ks| ≤ y.cBound := y.abs_approx_le_cBound ks
  calc
    |x.approx ks * y.approx ks - x.approx kb * y.approx kb|
      = |(x.approx ks - x.approx kb) * y.approx ks + x.approx kb * (y.approx ks - y.approx kb)| := by ring_nf
    _ ≤ |(x.approx ks - x.approx kb) * y.approx ks| + |x.approx kb * (y.approx ks - y.approx kb)| :=
      abs_add_le ((x.approx ks - x.approx kb) * y.approx ks) (x.approx kb * (y.approx ks - y.approx kb))
    _ = |x.approx ks - x.approx kb| * |y.approx ks| + |x.approx kb| * |y.approx ks - y.approx kb| := by simp [abs_mul]
    _ ≤ (1 / 2 ^ (min ks kb)) * |y.approx ks| + |x.approx kb| * (1 / 2 ^ (min ks kb)) := by
        gcongr
    _ ≤ (1 / 2 ^ (min ks kb)) * y.cBound + x.cBound * (1 / 2 ^ (min ks kb)) := by
        gcongr
    _ = (x.cBound + y.cBound) * (1 / 2 ^ (min ks kb)) := by ring

/-- 2.  Replace `1/2^{min ks kb}` by `1/2^{k_small}` when
      `k_small ≤ min ks kb`. -/
lemma one_div_pow_le_of_le_min
    {k_small ks kb : ℕ} (h : k_small ≤ min ks kb) :
    (1 : ℚ) / 2 ^ (min ks kb) ≤ 1 / 2 ^ k_small := by
  have : (2 : ℚ) ^ k_small ≤ 2 ^ (min ks kb) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : (1 : ℕ) ≤ 2) h
  have hp : 0 < (2 : ℚ) ^ k_small := pow_pos (by norm_num) _
  have hp' : 0 < (2 : ℚ) ^ (min ks kb) := pow_pos (by norm_num) _
  exact one_div_pow_le_one_div_pow_of_le rfl h-- (one_div_le_one_div hp hp').mpr this

/-- 3.  Final wrapper: bound at `k_small`, then widen the numerator
      with the harmless `+ 1`. -/
lemma mul_approx_bound_k_small
    (x y : CReal.Pre) {k_small ks kb : ℕ} (h₁ : k_small ≤ min ks kb) :
    |x.approx ks * y.approx ks - x.approx kb * y.approx kb| ≤
      (x.cBound + y.cBound) / 2 ^ k_small := by
  have h_core := mul_approx_bound_min x y (ks := ks) (kb := kb)
  -- we upgrade 1/2^(min ks kb) to 1/2^k_small
  have h_pow := one_div_pow_le_of_le_min h₁
  have h_nonneg : (0 : ℚ) ≤ x.cBound + y.cBound := by
    have : (0 : ℚ) ≤ (x.cBound : ℚ) := by exact_mod_cast Nat.zero_le _
    have : (0 : ℚ) ≤ (y.cBound : ℚ) := by exact_mod_cast Nat.zero_le _
    linarith
  have : (x.cBound + y.cBound : ℚ) * (1 / 2 ^ (min ks kb))
        ≤ (x.cBound + y.cBound) * (1 / 2 ^ k_small) :=
    mul_le_mul_of_nonneg_left h_pow h_nonneg
  simpa [div_eq_mul_inv] using h_core.trans this

/-! **Regularity of the product** -/
lemma mul_approx_regularity
    (x y : CReal.Pre) {k_small k_big : ℕ} (h_le : k_small ≤ k_big) :
    |(x.mul y).approx k_small - x.approx k_big * y.approx k_big| ≤
      (x.cBound + y.cBound + 1) / 2 ^ k_small := by
  dsimp [CReal.Pre.mul]
  let S  := x.mulShift y
  let ks := k_small + S
  let kb := k_big
  have h_min : k_small ≤ min ks kb := by
    have : k_small ≤ ks := by
      dsimp [ks]; exact Nat.le_add_right _ _
    have : k_small ≤ kb := by
      dsimp [kb]; exact h_le
    exact le_min ‹_› ‹_›
  have h_core :=
    mul_approx_bound_k_small x y h_min
  have h_num : (x.cBound + y.cBound : ℚ) ≤ x.cBound + y.cBound + 1 := by linarith
  have h_final : (x.cBound + y.cBound : ℚ) / 2 ^ k_small
               ≤ (x.cBound + y.cBound + 1) / 2 ^ k_small := by
    apply div_le_div_of_le_right
    · exact pow_pos (by norm_num) k_small
    · exact h_num
  exact h_core.trans h_final

lemma abs_add_three (a b c : ℚ) :
    |a + b + c| ≤ |a| + |b| + |c| := by
  calc
    |a + b + c| = |(a + b) + c| := by ring
    _ ≤ |a + b| + |c|           := abs_add_le (a + b) c
    _ ≤ |a| + |b| + |c|         := by
      have h₁ : |a + b| ≤ |a| + |b| := abs_add_le a b
      linarith

/-- Given a positive ε, we can find an index `K` such that `B / 2^(K-1) < ε`. -/
lemma mul_find_index'
    {B ε : ℚ} (hB : 0 < B) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ B / 2 ^ (K - 1) < ε := by
  rcases exists_pow_gt (div_pos hB hε) with ⟨K₀, hK₀⟩
  have h_step : B / 2 ^ K₀ < ε := by
    have h1 : B < ε * 2 ^ K₀ := by
      have := (div_lt_iff hε).1 hK₀
      simpa [mul_comm] using this
    have h_pow_pos : (0 : ℚ) < 2 ^ K₀ := pow_pos (by norm_num) K₀
    exact (div_lt_iff h_pow_pos).2 h1
  refine ⟨K₀ + 1, Nat.succ_pos _, ?_⟩
  simpa [Nat.add_sub_cancel] using h_step

open CReal.Pre

/--
Multiplication respects equivalence.
-/
theorem mul_respects_equiv {x₁ x₂ y₁ y₂ : CReal.Pre}
    (h_x : CReal.Pre.Equiv x₁ x₂) (h_y : CReal.Pre.Equiv y₁ y₂) :
    CReal.Pre.Equiv (x₁.mul y₁) (x₂.mul y₂) := by
  intro n
  apply le_of_forall_pos_le_add
  intro ε hε
  -- 1. Setup Bounds and Epsilon.
  let Bx₁ := (x₁.cBound : ℚ); let By₁ := (y₁.cBound : ℚ)
  let Bx₂ := (x₂.cBound : ℚ); let By₂ := (y₂.cBound : ℚ)
  -- Bounds for middle term and tail terms.
  let B_mid : ℚ := Bx₁ + By₂
  let B_tails : ℚ := max (Bx₁ + By₁) (Bx₂ + By₂)
  have hB_mid_pos : 0 < B_mid := by
    dsimp [B_mid, Bx₁, By₂]
    apply add_pos <;> (exact_mod_cast cBound_pos _)
  have hB_tails_pos : 0 < B_tails := by
    dsimp [B_tails, Bx₁, By₁, Bx₂, By₂]
    apply lt_max_of_lt_left
    apply add_pos <;> (exact_mod_cast cBound_pos _)
  have hε3 : 0 < ε / 3 := div_pos hε (by norm_num)
  -- 2. Find Indices K₁ (for middle term) and K₂ (for tails).
  -- K₁: B_mid / 2^(K₁-1) < ε/3.
  obtain ⟨K₁, hK₁_pos, hK₁_bound⟩ := mul_find_index' hB_mid_pos hε3
  -- K₂: B_tails / 2^K₂ < ε/3.
  obtain ⟨K₂, hK₂⟩ := exists_pow_gt (div_pos hB_tails_pos hε3)
  have hK₂_bound' : B_tails / (2^K₂) < ε/3 := by
    apply (div_lt_iff (pow_pos (by norm_num) _)).mpr
    rw [mul_comm]; exact (div_lt_iff' hε3).mp hK₂
  -- 3. Choose unified index K and target index k.
  let K := max K₁ K₂
  let k := n + 1
  -- 4. Define terms for Triangle Inequality.
  let A := (x₁.mul y₁).approx k          -- (x₁y₁)ₖ
  let D := (x₂.mul y₂).approx k          -- (x₂y₂)ₖ
  let B_bridge := x₁.approx K * y₁.approx K  -- x₁ₖy₁ₖ
  let C_bridge := x₂.approx K * y₂.approx K  -- x₂ₖy₂ₖ
  have h_tri : |A - D| ≤ |A - B_bridge| + |B_bridge - C_bridge| + |C_bridge - D| := by
    calc |A - D| = |(A - B_bridge) + (B_bridge - C_bridge) + (C_bridge - D)| := by ring_nf
               _ ≤ _ := abs_add_three _ _ _
  -- 5. Bound Term 2 (Middle).
  have h_term2 : |B_bridge - C_bridge| < ε / 3 := by
    have hK_pos : 0 < K := Nat.lt_of_lt_of_le hK₁_pos (le_max_left _ _)
    have h_mid := mul_equiv_same_index x₁ x₂ y₁ y₂ K hK_pos h_x h_y
    -- Use K₁ ≤ K to weaken the bound.
    have h_K_le : K₁ - 1 ≤ K - 1 := Nat.sub_le_sub_right (le_max_left K₁ K₂) 1
    have h_pow_le : (2:ℚ)^(K₁-1) ≤ (2:ℚ)^(K-1) := (pow_le_pow_iff_right₀ rfl).mpr h_K_le
    have h_bound_K : B_mid / 2^(K-1) ≤ B_mid / 2^(K₁-1) := by
      apply div_le_div_of_le_left (le_of_lt hB_mid_pos) (pow_pos (by norm_num) _) h_pow_le
    calc |B_bridge - C_bridge| ≤ B_mid / 2^(K-1) := h_mid
      _ ≤ B_mid / 2^(K₁-1) := h_bound_K
      _ < ε / 3 := hK₁_bound
  -- 6. Bound Term 1 (Nearness/Generalized Regularity).
  have h_term1 : |A - B_bridge| ≤ 1/2^k + ε/3 := by
    let S₁ := x₁.mulShift y₁
    let Bxy₁ := Bx₁ + By₁
    -- Apply mul_approx_bound_min (Nearness).
    have h_near : |A - B_bridge| ≤ Bxy₁ * (1 / 2^(min (k+S₁) K)) := by
      dsimp [A, B_bridge, CReal.Pre.mul]
      -- |x₁.approx (k+S₁) * y₁.approx (k+S₁) - x₁.approx K * y₁.approx K|
      -- ≤ (x₁.cBound + y₁.cBound) * (1 / 2^(min (k+S₁) K))
      simpa [Bxy₁, Bx₁, By₁] using
        (mul_approx_bound_min x₁ y₁ (ks := k + S₁) (kb := K))
    -- Case analysis on the minimum.
    cases le_or_gt (k+S₁) K with
    | inl h_le => -- Case 1: k+S₁ ≤ K. Precision k dominates.
      have h_min_eq : min (k+S₁) K = k+S₁ := min_eq_left h_le
      rw [h_min_eq] at h_near
      -- Use Bxy₁ ≤ 2^S₁.
      have h_S_bound : Bxy₁ ≤ 2^S₁ := x₁.sum_cBound_le_pow_mulShift y₁
      have h_case1 := calc |A - B_bridge| ≤ Bxy₁ * (1 / 2^(k+S₁)) := h_near
        _ ≤ 2^S₁ * (1 / 2^(k+S₁)) := mul_le_mul_of_nonneg_right h_S_bound (by positivity)
        _ = 1/2^k := by rw [pow_add]; field_simp [pow_ne_zero]
      -- Lift ≤ 1/2^k to ≤ 1/2^k + ε/3 using ε/3 ≥ 0
      have h_eps_nonneg : 0 ≤ ε / 3 := (le_of_lt hε3)
      have h_lift : (1 : ℚ) / 2 ^ k ≤ (1 : ℚ) / 2 ^ k + ε / 3 := by
        simpa [add_comm] using add_le_add_left h_eps_nonneg ((1 : ℚ) / 2 ^ k)
      exact le_trans h_case1 h_lift
    | inr h_lt => -- Case 2: K < k+S₁. Convergence index K dominates.
      have h_min_eq : min (k+S₁) K = K := min_eq_right (le_of_lt h_lt)
      rw [h_min_eq] at h_near
      -- We need Bxy₁ / 2^K < ε/3. Use Bxy₁ ≤ B_tails and K₂ ≤ K.
      have h_B_le : Bxy₁ ≤ B_tails := le_max_left _ _
      have h_K_le : K₂ ≤ K := le_max_right _ _
      have h_pow_le : (2:ℚ)^K₂ ≤ (2:ℚ)^K := (pow_le_pow_iff_right₀ rfl).mpr h_K_le
      have h_bound_K : B_tails / 2^K ≤ B_tails / 2^K₂ := by
        apply div_le_div_of_le_left (le_of_lt hB_tails_pos) (pow_pos (by norm_num) _) h_pow_le
      have h_case2 := calc |A - B_bridge| ≤ Bxy₁ / 2^K := by simpa using h_near
        _ ≤ B_tails / 2^K := div_le_div_of_le_right (pow_pos (by norm_num) _) h_B_le
        _ ≤ B_tails / 2^K₂ := h_bound_K
        _ < ε/3 := hK₂_bound'
      -- From |A - B_bridge| < ε/3 and 0 ≤ 1/2^k, get ≤ 1/2^k + ε/3
      have h_pos_div : 0 ≤ (1 : ℚ) / 2 ^ k := by
        have hpow : 0 < (2 : ℚ) ^ k := pow_pos (by norm_num) _
        exact div_nonneg (by norm_num) (le_of_lt hpow)
      have h_eps_mono : ε / 3 ≤ (1 : ℚ) / 2 ^ k + ε / 3 := by
        simp
      exact le_trans h_case2.le h_eps_mono
  -- 7. Bound Term 3 (Symmetric).
  have h_term3 : |C_bridge - D| ≤ 1/2^k + ε/3 := by
    rw [abs_sub_comm]
    -- (Logic identical to h_term1, applied to x₂, y₂)
    let S₂ := x₂.mulShift y₂
    let Bxy₂ := Bx₂ + By₂
    have h_near : |D - C_bridge| ≤ Bxy₂ * (1 / 2^(min (k+S₂) K)) := by
       dsimp [D, C_bridge, CReal.Pre.mul]
       -- |x₂.approx (k+S₂) * y₂.approx (k+S₂) - x₂.approx K * y₂.approx K|
       -- ≤ (x₂.cBound + y₂.cBound) * (1 / 2^(min (k+S₂) K))
       simpa [Bxy₂, Bx₂, By₂] using
         (mul_approx_bound_min x₂ y₂ (ks := k + S₂) (kb := K))
    cases le_or_gt (k+S₂) K with
    | inl h_le =>
      have h_min_eq : min (k+S₂) K = k+S₂ := min_eq_left h_le
      rw [h_min_eq] at h_near
      have h_S_bound : Bxy₂ ≤ 2^S₂ := x₂.sum_cBound_le_pow_mulShift y₂
      have h_case1 := calc |D - C_bridge| ≤ Bxy₂ * (1 / 2^(k+S₂)) := h_near
        _ ≤ 2^S₂ * (1 / 2^(k+S₂)) := mul_le_mul_of_nonneg_right h_S_bound (by positivity)
        _ = 1/2^k := by rw [pow_add]; field_simp [pow_ne_zero]
      have h_eps_nonneg : 0 ≤ ε / 3 := (le_of_lt hε3)
      have h_lift : (1 : ℚ) / 2 ^ k ≤ (1 : ℚ) / 2 ^ k + ε / 3 := by
        simpa [add_comm] using add_le_add_left h_eps_nonneg ((1 : ℚ) / 2 ^ k)
      exact le_trans h_case1 h_lift
    | inr h_lt =>
      have h_min_eq : min (k+S₂) K = K := min_eq_right (le_of_lt h_lt)
      rw [h_min_eq] at h_near
      have h_B_le : Bxy₂ ≤ B_tails := le_max_right _ _
      have h_K_le : K₂ ≤ K := le_max_right _ _
      have h_pow_le : (2:ℚ)^K₂ ≤ (2:ℚ)^K := (pow_le_pow_iff_right₀ rfl).mpr h_K_le
      have h_bound_K : B_tails / 2^K ≤ B_tails / 2^K₂ := by
        apply div_le_div_of_le_left (le_of_lt hB_tails_pos) (pow_pos (by norm_num) _) h_pow_le

      have h_case2 := calc |D - C_bridge| ≤ Bxy₂ / 2^K := by simpa using h_near
        _ ≤ B_tails / 2^K := div_le_div_of_le_right (pow_pos (by norm_num) _) h_B_le
        _ ≤ B_tails / 2^K₂ := h_bound_K
        _ < ε/3 := hK₂_bound'
      have h_pos_div : 0 ≤ (1 : ℚ) / 2 ^ k := by
        have hpow : 0 < (2 : ℚ) ^ k := pow_pos (by norm_num) _
        exact div_nonneg (by norm_num) (le_of_lt hpow)
      have h_eps_mono : ε / 3 ≤ (1 : ℚ) / 2 ^ k + ε / 3 := by
        simp
      exact le_trans h_case2.le h_eps_mono
  have h_final := calc |A - D| ≤ |A - B_bridge| + |B_bridge - C_bridge| + |C_bridge - D| := h_tri
    _ ≤ (1/2^k + ε/3) + ε/3 + (1/2^k + ε/3) := by linarith [h_term1, h_term2.le, h_term3]
    _ = 1/2^(k-1) + ε := by
      have h_eps : (ε/3) + ε/3 + ε/3 = ε := by ring_nf
      have h_pow : (1 : ℚ) / 2 ^ k + 1 / 2 ^ k = 1 / 2 ^ (k - 1) := by
        have h₁ : (1 : ℚ) / 2 ^ k + 1 / 2 ^ k = (2 : ℚ) / 2 ^ k := by
          field_simp; ring_nf
        have hk : 0 < k := by
          have : 1 ≤ k := by
            dsimp [k]; exact Nat.succ_le_succ (Nat.zero_le n)
          exact this
        have h₂ : (2 : ℚ) / 2 ^ k = 1 / 2 ^ (k - 1) := by
          have hk' : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_pos hk).symm
          field_simp [hk', pow_succ]
          exact Eq.symm (pow_succ' 2 n)
        simp_all only [lt_sup_iff, div_pos_iff_of_pos_left, Nat.ofNat_pos, one_div, lt_add_iff_pos_left, add_pos_iff,
          zero_lt_one, or_true, add_tsub_cancel_right, B_mid, Bx₁, By₂, B_tails, By₁, Bx₂, A, k, D, B_bridge, K,
          C_bridge]
      simp [add_comm, add_left_comm]; grind
    _ = 1/2^n + ε := by simp [k]

  exact h_final

/-- The product of two computable real numbers. -/
instance : Mul CReal := by
  refine ⟨Quotient.map₂ Pre.mul ?_⟩
  intro x₁ x₂ hx y₁ y₂ hy
  exact mul_respects_equiv hx hy

@[simp] theorem mul_def (x y : CReal.Pre) : (⟦x⟧ : CReal) * ⟦y⟧ = ⟦x.mul y⟧ := rfl

private lemma add_assoc_diff_rewrite
    (x y z : CReal.Pre) (n : ℕ) :
  |(x.approx (n + 3) + y.approx (n + 3) + z.approx (n + 2)) -
    (x.approx (n + 2) + y.approx (n + 3) + z.approx (n + 3))|
    =
  |(x.approx (n + 3) - x.approx (n + 2)) +
    (z.approx (n + 2) - z.approx (n + 3))| := by
  ring_nf

private lemma adjacent_reg (w : CReal.Pre) (n : ℕ) :
  |w.approx (n + 3) - w.approx (n + 2)| ≤ (1 : ℚ) / 2 ^ (n + 2) := by
  rw [abs_sub_comm]
  exact w.is_regular (n + 2) (n + 3) (Nat.le_succ _)

private lemma two_halves_to_succ (n : ℕ) :
  (1 : ℚ) / 2 ^ (n + 2) + (1 : ℚ) / 2 ^ (n + 2) = (1 : ℚ) / 2 ^ (n + 1) := by
  field_simp [pow_succ]
  ring

private lemma inv_pow_antitone_succ (n : ℕ) :
  (1 : ℚ) / 2 ^ (n + 1) ≤ (1 : ℚ) / 2 ^ n := by
  apply one_div_le_one_div_of_le
  · exact pow_pos (by norm_num) n
  · exact (pow_le_pow_iff_right₀ rfl).mpr (Nat.le_succ n)

private theorem add_assoc_pre (x y z : CReal.Pre) :
    CReal.Pre.Equiv ((x.add y).add z) (x.add (y.add z)) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.add]
  have h_rewrite := add_assoc_diff_rewrite x y z n
  have hx := adjacent_reg x n
  have hz := by
    rw [abs_sub_comm] at hx
    exact (adjacent_reg z n)
  calc
    |x.approx (n + 1 + 1 + 1) + y.approx (n + 1 + 1 + 1) + z.approx (n + 1 + 1) -
      (x.approx (n + 1 + 1) + (y.approx (n + 1 + 1 + 1) + z.approx (n + 1 + 1 + 1)))|
        = |(x.approx (n + 3) - x.approx (n + 2)) +
            (z.approx (n + 2) - z.approx (n + 3))| := by
          simp only [add_assoc]; ring_nf
    _ ≤ |x.approx (n + 3) - x.approx (n + 2)| +
        |z.approx (n + 2) - z.approx (n + 3)| := abs_add_le _ _
    _ ≤ (1 : ℚ) / 2 ^ (n + 2) + (1 : ℚ) / 2 ^ (n + 2) := add_le_add (adjacent_reg x n) (by
          simpa [abs_sub_comm] using (adjacent_reg z n))
    _ = (1 : ℚ) / 2 ^ (n + 1) := two_halves_to_succ n
    _ ≤ (1 : ℚ) / 2 ^ n := inv_pow_antitone_succ n

private theorem add_comm_pre (x y : CReal.Pre) : CReal.Pre.Equiv (x.add y) (y.add x) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.add]
  ring_nf; simp

private lemma adjacent_reg_succ (x : CReal.Pre) (n : ℕ) :
  |x.approx (n + 2) - x.approx (n + 1)| ≤ (1 : ℚ) / 2 ^ (n + 1) := by
  rw [abs_sub_comm]
  exact x.is_regular (n + 1) (n + 2) (Nat.le_succ _)

private theorem zero_add_pre (x : CReal.Pre) : CReal.Pre.Equiv (CReal.Pre.zero.add x) x := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.add, CReal.Pre.zero]
  simp only [zero_add]
  exact (adjacent_reg_succ x n).trans (inv_pow_antitone_succ n)

private theorem add_zero_pre (x : CReal.Pre) : CReal.Pre.Equiv (x.add CReal.Pre.zero) x := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.add, CReal.Pre.zero]
  simp only [add_zero]
  exact (adjacent_reg_succ x n).trans (inv_pow_antitone_succ n)

private theorem add_left_neg_pre (x : CReal.Pre) : CReal.Pre.Equiv (x.neg.add x) CReal.Pre.zero := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.add, CReal.Pre.neg, CReal.Pre.zero]
  simp only [neg_add_cancel, sub_zero, abs_zero]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  exact div_nonneg (by norm_num) (le_of_lt hpow)

open Rat

instance : AddCommGroup CReal where
  add := (· + ·)
  add_assoc := by
    intro a b c
    refine Quot.induction_on₃ a b c (fun x y z => ?_)
    simpa [add_def] using Quot.sound (add_assoc_pre x y z)
  zero := (0 : CReal)
  zero_add := by
    intro a
    refine Quot.induction_on a (fun x => ?_)
    simpa [add_def] using Quot.sound (zero_add_pre x)
  add_zero := by
    intro a
    refine Quot.induction_on a (fun x => ?_)
    simpa [add_def] using Quot.sound (add_zero_pre x)
  nsmul := nsmulRec
  nsmul_zero := by intros; rfl
  nsmul_succ := by intros; rfl
  neg := Neg.neg
  sub := fun a b => a + (-b)
  sub_eq_add_neg := by intros; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intros; rfl
  zsmul_succ' := by intros; rfl
  zsmul_neg' := by intros; rfl
  neg_add_cancel := by
    intro a
    refine Quot.induction_on a (fun x => ?_)
    simpa [add_def] using Quot.sound (add_left_neg_pre x)
  add_comm := by
    intro a b
    refine Quot.induction_on₂ a b (fun x y => ?_)
    simpa [add_def] using Quot.sound (add_comm_pre x y)

end CReal
end Computable
