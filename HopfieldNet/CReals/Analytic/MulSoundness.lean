import HopfieldNet.CReals.Analytic.CRealSemantics

namespace Computable
namespace CReal
namespace Analytic

open AnalyticReal

section

variable {V₁ V₂ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]

@[simp] theorem mul_out_init_zero (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) :
    (AnalyticReal.mul ar₁ ar₂).init (AnalyticReal.mul ar₁ ar₂).out = 0 := by
  rfl

@[simp] theorem mul_taylorCoeff_zero (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) :
    AnalyticReal.taylorCoeff (AnalyticReal.mul ar₁ ar₂) 0 = 0 := by
  simpa using AnalyticReal.taylorCoeff_zero (AnalyticReal.mul ar₁ ar₂)

end

section Const

private theorem const_lieIter_one_toMvPolynomialInt (q : ℤ) :
    (AnalyticReal.lieIter (AnalyticReal.const q) 1).toMvPolynomialInt = MvPolynomial.C q := by
  classical
  rw [AnalyticReal.lieIter, AnalyticReal.lieDeriv_toMvPolynomialInt]
  simp [AnalyticReal.const, AnalyticReal.lieIter, VPoly.toMvPolynomialInt]

private theorem const_lieIter_succ_succ_toMvPolynomialInt (q : ℤ) :
    ∀ n : ℕ, (AnalyticReal.lieIter (AnalyticReal.const q) (n + 2)).toMvPolynomialInt = 0
  | 0 => by
      rw [AnalyticReal.lieIter, AnalyticReal.lieDeriv_toMvPolynomialInt]
      rw [const_lieIter_one_toMvPolynomialInt]
      simp [AnalyticReal.const]
  | n + 1 => by
      rw [AnalyticReal.lieIter, AnalyticReal.lieDeriv_toMvPolynomialInt]
      rw [const_lieIter_succ_succ_toMvPolynomialInt q n]
      simp [AnalyticReal.const]

@[simp] theorem const_taylorCoeff_one (q : ℤ) :
    AnalyticReal.taylorCoeff (AnalyticReal.const q) 1 = q := by
  have hmain :
      (AnalyticReal.lieIter (AnalyticReal.const q) 1).eval (AnalyticReal.const q).init = q := by
    calc
      (AnalyticReal.lieIter (AnalyticReal.const q) 1).eval (AnalyticReal.const q).init
        =
          ((AnalyticReal.lieIter (AnalyticReal.const q) 1).toMvPolynomialInt).eval₂
            (Int.castRingHom ℚ) (AnalyticReal.const q).init := by
              symm
              exact VPoly.eval₂_toMvPolynomialInt
                (env := (AnalyticReal.const q).init)
                (p := AnalyticReal.lieIter (AnalyticReal.const q) 1)
      _ = (MvPolynomial.C q).eval₂ (Int.castRingHom ℚ) (AnalyticReal.const q).init := by
            rw [const_lieIter_one_toMvPolynomialInt]
      _ = q := by
            simpa using
              (MvPolynomial.eval₂_C (f := Int.castRingHom ℚ) (g := (AnalyticReal.const q).init) q)
  simpa [AnalyticReal.taylorCoeff] using hmain

@[simp] theorem const_taylorCoeff_succ_succ (q : ℤ) (n : ℕ) :
    AnalyticReal.taylorCoeff (AnalyticReal.const q) (n + 2) = 0 := by
  have hmain :
      (AnalyticReal.lieIter (AnalyticReal.const q) (n + 2)).eval (AnalyticReal.const q).init = 0 := by
    calc
      (AnalyticReal.lieIter (AnalyticReal.const q) (n + 2)).eval (AnalyticReal.const q).init
        =
          ((AnalyticReal.lieIter (AnalyticReal.const q) (n + 2)).toMvPolynomialInt).eval₂
            (Int.castRingHom ℚ) (AnalyticReal.const q).init := by
              symm
              exact VPoly.eval₂_toMvPolynomialInt
                (env := (AnalyticReal.const q).init)
                (p := AnalyticReal.lieIter (AnalyticReal.const q) (n + 2))
      _ = (0 : MvPolynomial Unit ℤ).eval₂ (Int.castRingHom ℚ) (AnalyticReal.const q).init := by
            rw [const_lieIter_succ_succ_toMvPolynomialInt]
      _ = 0 := by simp
  simpa [AnalyticReal.taylorCoeff, hmain]

@[simp] theorem const_taylorTerm_succ_succ (q : ℤ) (t : ℚ) (n : ℕ) :
    AnalyticReal.taylorTerm (AnalyticReal.const q) t (n + 2) = 0 := by
  simp [AnalyticReal.taylorTerm, const_taylorCoeff_succ_succ]

theorem approxSumAt_const_succ (q : ℤ) (t : ℚ) (n : ℕ) :
    AnalyticReal.approxSumAt (AnalyticReal.const q) t (n + 1) = q * t := by
  induction n with
  | zero =>
      rw [AnalyticReal.approxSumAt]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp [AnalyticReal.taylorTerm, const_taylorCoeff_one]
      ring_nf
  | succ n ih =>
      rw [AnalyticReal.approxSumAt, Finset.sum_range_succ]
      calc
        ∑ x ∈ Finset.range (n + 2), t ^ x * (AnalyticReal.const q).taylorCoeff x
            + t ^ (n + 2) * (AnalyticReal.const q).taylorCoeff (n + 2)
          =
            AnalyticReal.approxSumAt (AnalyticReal.const q) t (n + 1) + 0 := by
              simp [AnalyticReal.approxSumAt, AnalyticReal.taylorTerm, const_taylorCoeff_succ_succ]
        _ = q * t := by simpa [ih]

@[simp] theorem approxSum_const_succ (q : ℤ) (n : ℕ) :
    AnalyticReal.approxSum (AnalyticReal.const q) (n + 1) = q := by
  simpa [AnalyticReal.approxSum_eq_approxSumAt_one] using approxSumAt_const_succ q (1 : ℚ) n

namespace HasConstructiveTaylorLimit

noncomputable def const (q : ℤ) :
    HasConstructiveTaylorLimit (AnalyticReal.const q) := by
  let μ : ℕ → ℕ := fun _ => 1
  have hμ : Monotone μ := by
    intro a b hab
    simp [μ]
  refine mkHasConstructiveTaylorLimit (A := AnalyticReal.const q) μ hμ ?_
  intro k n m hn hm
  have hn1 : 1 ≤ n := by simpa [μ] using hn
  have hm1 : 1 ≤ m := by simpa [μ] using hm
  cases n with
  | zero =>
      cases hn1
  | succ n =>
      cases m with
      | zero =>
          cases hm1
      | succ m =>
          calc
            |AnalyticReal.approxSum (AnalyticReal.const q) (n + 1) -
                AnalyticReal.approxSum (AnalyticReal.const q) (m + 1)|
              = |(q : ℚ) - q| := by rw [approxSum_const_succ, approxSum_const_succ]
            _ = 0 := by simp
            _ ≤ (1 : ℚ) / 2 ^ (k + 1) := by positivity

end HasConstructiveTaylorLimit

end Const

end Analytic
end CReal
end Computable
