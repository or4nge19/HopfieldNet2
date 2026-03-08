import HopfieldNet.CReals.Mobius.Basic

/-!
# Möbius ERA: soundness lemmas (corner propagation)

This file provides the real-analysis facts needed to justify corner-based bounds:

- affine inequalities on \([-1,1]\) propagate from endpoints,
- bilinear inequalities on \([-1,1]^2\) propagate from corners.

These are the basic tools for turning the *integer-only* corner oracle into a *real* semantic
containment statement about `Tensor.apply`.
-/

namespace Computable
namespace Mobius

open scoped BigOperators

lemma affine_nonneg_of_endpoints (M B : ℝ)
    (h1 : M * 1 + B ≥ 0) (hm1 : M * (-1) + B ≥ 0) :
    ∀ x : ℝ, -1 ≤ x → x ≤ 1 → M * x + B ≥ 0 := by
  intro x hx1 hx2
  rcases le_total 0 M with hM | hM
  · have : M * (-1) ≤ M * x := mul_le_mul_of_nonneg_left hx1 hM
    linarith
  · have : M * 1 ≤ M * x := mul_le_mul_of_nonpos_left hx2 hM
    linarith

lemma affine_nonpos_of_endpoints (M B : ℝ)
    (h1 : M * 1 + B ≤ 0) (hm1 : M * (-1) + B ≤ 0) :
    ∀ x : ℝ, -1 ≤ x → x ≤ 1 → M * x + B ≤ 0 := by
  intro x hx1 hx2
  rcases le_total 0 M with hM | hM
  · have : M * x ≤ M * 1 := mul_le_mul_of_nonneg_left hx2 hM
    linarith
  · have : M * x ≤ M * (-1) := mul_le_mul_of_nonpos_left hx1 hM
    linarith

lemma affine_pos_of_endpoints (M B : ℝ)
    (h1 : M * 1 + B > 0) (hm1 : M * (-1) + B > 0) :
    ∀ x : ℝ, -1 ≤ x → x ≤ 1 → M * x + B > 0 := by
  intro x hx1 hx2
  rcases le_total 0 M with hM | hM
  · have : M * (-1) ≤ M * x := mul_le_mul_of_nonneg_left hx1 hM
    linarith
  · have : M * 1 ≤ M * x := mul_le_mul_of_nonpos_left hx2 hM
    linarith

lemma affine_neg_of_endpoints (M B : ℝ)
    (h1 : M * 1 + B < 0) (hm1 : M * (-1) + B < 0) :
    ∀ x : ℝ, -1 ≤ x → x ≤ 1 → M * x + B < 0 := by
  intro x hx1 hx2
  rcases le_total 0 M with hM | hM
  · have : M * x ≤ M * 1 := mul_le_mul_of_nonneg_left hx2 hM
    linarith
  · have : M * x ≤ M * (-1) := mul_le_mul_of_nonpos_left hx1 hM
    linarith

lemma bilinear_nonpos_of_corners (A B C D : ℝ)
    (h11 : A*1*1 + B*1 + C*1 + D ≤ 0)
    (h1m : A*1*(-1) + B*1 + C*(-1) + D ≤ 0)
    (hm1 : A*(-1)*1 + B*(-1) + C*1 + D ≤ 0)
    (hmm : A*(-1)*(-1) + B*(-1) + C*(-1) + D ≤ 0) :
    ∀ x y : ℝ, -1 ≤ x → x ≤ 1 → -1 ≤ y → y ≤ 1 → A*x*y + B*x + C*y + D ≤ 0 := by
  intro x y hx1 hx2 hy1 hy2
  have hx1y : (A + C) * y + (B + D) ≤ 0 := by
    have h_y1 : (A + C) * 1 + (B + D) ≤ 0 := by linarith
    have h_ym1 : (A + C) * (-1) + (B + D) ≤ 0 := by linarith
    exact affine_nonpos_of_endpoints (A + C) (B + D) h_y1 h_ym1 y hy1 hy2
  have hxm1y : (C - A) * y + (D - B) ≤ 0 := by
    have h_y1 : (C - A) * 1 + (D - B) ≤ 0 := by linarith
    have h_ym1 : (C - A) * (-1) + (D - B) ≤ 0 := by linarith
    exact affine_nonpos_of_endpoints (C - A) (D - B) h_y1 h_ym1 y hy1 hy2
  have hx_end :
      ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (A * y + B) * x + (C * y + D) ≤ 0 := by
    have h_x1 : (A * y + B) * 1 + (C * y + D) ≤ 0 := by
      linarith [hx1y]
    have h_xm1 : (A * y + B) * (-1) + (C * y + D) ≤ 0 := by
      linarith [hxm1y]
    exact affine_nonpos_of_endpoints (A * y + B) (C * y + D) h_x1 h_xm1
  have := hx_end x hx1 hx2
  linarith

lemma bilinear_nonneg_of_corners (A B C D : ℝ)
    (h11 : A*1*1 + B*1 + C*1 + D ≥ 0)
    (h1m : A*1*(-1) + B*1 + C*(-1) + D ≥ 0)
    (hm1 : A*(-1)*1 + B*(-1) + C*1 + D ≥ 0)
    (hmm : A*(-1)*(-1) + B*(-1) + C*(-1) + D ≥ 0) :
    ∀ x y : ℝ, -1 ≤ x → x ≤ 1 → -1 ≤ y → y ≤ 1 → A*x*y + B*x + C*y + D ≥ 0 := by
  intro x y hx1 hx2 hy1 hy2
  have hx1y : (A + C) * y + (B + D) ≥ 0 := by
    have h_y1 : (A + C) * 1 + (B + D) ≥ 0 := by linarith
    have h_ym1 : (A + C) * (-1) + (B + D) ≥ 0 := by linarith
    exact affine_nonneg_of_endpoints (A + C) (B + D) h_y1 h_ym1 y hy1 hy2
  have hxm1y : (C - A) * y + (D - B) ≥ 0 := by
    have h_y1 : (C - A) * 1 + (D - B) ≥ 0 := by linarith
    have h_ym1 : (C - A) * (-1) + (D - B) ≥ 0 := by linarith
    exact affine_nonneg_of_endpoints (C - A) (D - B) h_y1 h_ym1 y hy1 hy2
  have hx_end :
      ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (A * y + B) * x + (C * y + D) ≥ 0 := by
    have h_x1 : (A * y + B) * 1 + (C * y + D) ≥ 0 := by linarith [hx1y]
    have h_xm1 : (A * y + B) * (-1) + (C * y + D) ≥ 0 := by linarith [hxm1y]
    exact affine_nonneg_of_endpoints (A * y + B) (C * y + D) h_x1 h_xm1
  have := hx_end x hx1 hx2
  linarith

lemma bilinear_pos_of_corners (A B C D : ℝ)
    (h11 : A*1*1 + B*1 + C*1 + D > 0)
    (h1m : A*1*(-1) + B*1 + C*(-1) + D > 0)
    (hm1 : A*(-1)*1 + B*(-1) + C*1 + D > 0)
    (hmm : A*(-1)*(-1) + B*(-1) + C*(-1) + D > 0) :
    ∀ x y : ℝ, -1 ≤ x → x ≤ 1 → -1 ≤ y → y ≤ 1 → A*x*y + B*x + C*y + D > 0 := by
  intro x y hx1 hx2 hy1 hy2
  have hx1y : (A + C) * y + (B + D) > 0 := by
    have h_y1 : (A + C) * 1 + (B + D) > 0 := by linarith
    have h_ym1 : (A + C) * (-1) + (B + D) > 0 := by linarith
    exact affine_pos_of_endpoints (A + C) (B + D) h_y1 h_ym1 y hy1 hy2
  have hxm1y : (C - A) * y + (D - B) > 0 := by
    have h_y1 : (C - A) * 1 + (D - B) > 0 := by linarith
    have h_ym1 : (C - A) * (-1) + (D - B) > 0 := by linarith
    exact affine_pos_of_endpoints (C - A) (D - B) h_y1 h_ym1 y hy1 hy2
  have hx_end :
      ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (A * y + B) * x + (C * y + D) > 0 := by
    have h_x1 : (A * y + B) * 1 + (C * y + D) > 0 := by linarith [hx1y]
    have h_xm1 : (A * y + B) * (-1) + (C * y + D) > 0 := by linarith [hxm1y]
    exact affine_pos_of_endpoints (A * y + B) (C * y + D) h_x1 h_xm1
  have := hx_end x hx1 hx2
  linarith

lemma bilinear_neg_of_corners (A B C D : ℝ)
    (h11 : A*1*1 + B*1 + C*1 + D < 0)
    (h1m : A*1*(-1) + B*1 + C*(-1) + D < 0)
    (hm1 : A*(-1)*1 + B*(-1) + C*1 + D < 0)
    (hmm : A*(-1)*(-1) + B*(-1) + C*(-1) + D < 0) :
    ∀ x y : ℝ, -1 ≤ x → x ≤ 1 → -1 ≤ y → y ≤ 1 → A*x*y + B*x + C*y + D < 0 := by
  intro x y hx1 hx2 hy1 hy2
  have hx1y : (A + C) * y + (B + D) < 0 := by
    have h_y1 : (A + C) * 1 + (B + D) < 0 := by linarith
    have h_ym1 : (A + C) * (-1) + (B + D) < 0 := by linarith
    exact affine_neg_of_endpoints (A + C) (B + D) h_y1 h_ym1 y hy1 hy2
  have hxm1y : (C - A) * y + (D - B) < 0 := by
    have h_y1 : (C - A) * 1 + (D - B) < 0 := by linarith
    have h_ym1 : (C - A) * (-1) + (D - B) < 0 := by linarith
    exact affine_neg_of_endpoints (C - A) (D - B) h_y1 h_ym1 y hy1 hy2
  have hx_end :
      ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (A * y + B) * x + (C * y + D) < 0 := by
    have h_x1 : (A * y + B) * 1 + (C * y + D) < 0 := by linarith [hx1y]
    have h_xm1 : (A * y + B) * (-1) + (C * y + D) < 0 := by linarith [hxm1y]
    exact affine_neg_of_endpoints (A * y + B) (C * y + D) h_x1 h_xm1
  have := hx_end x hx1 hx2
  linarith

end Mobius
end Computable
