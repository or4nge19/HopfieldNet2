import HopfieldNet.CReals.Analytic.CRealSemantics
import Mathlib.Data.Fintype.BigOperators

namespace Computable
namespace CReal
namespace Analytic

open AnalyticReal
open scoped BigOperators

private def inlVar {V₁ V₂ : Type} : V₁ → Option (V₁ ⊕ V₂) := some ∘ Sum.inl
private def inrVar {V₁ V₂ : Type} : V₂ → Option (V₁ ⊕ V₂) := some ∘ Sum.inr

private theorem inlVar_injective {V₁ V₂ : Type} :
    Function.Injective (@inlVar V₁ V₂) := by
  intro x y h
  exact Sum.inl.inj (Option.some.inj h)

private theorem inrVar_injective {V₁ V₂ : Type} :
    Function.Injective (@inrVar V₁ V₂) := by
  intro x y h
  exact Sum.inr.inj (Option.some.inj h)

section

variable {V₁ V₂ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]

@[simp] theorem add_out_init_zero (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) :
    (AnalyticReal.add ar₁ ar₂).init (AnalyticReal.add ar₁ ar₂).out = 0 := by
  rfl

@[simp] theorem add_init_comp_inl (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) :
    (AnalyticReal.add ar₁ ar₂).init ∘ inlVar = ar₁.init := by
  funext x
  rfl

@[simp] theorem add_init_comp_inr (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) :
    (AnalyticReal.add ar₁ ar₂).init ∘ inrVar = ar₂.init := by
  funext y
  rfl

omit [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂] in
private theorem pderiv_none_rename_inl (P : MvPolynomial V₁ ℤ) :
    MvPolynomial.pderiv none (MvPolynomial.rename (@inlVar V₁ V₂) P) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hmem
  rcases MvPolynomial.mem_vars_rename (@inlVar V₁ V₂) P hmem with ⟨i, _, hi⟩
  cases hi

omit [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂] in
private theorem pderiv_inr_rename_inl (P : MvPolynomial V₁ ℤ) (y : V₂) :
    MvPolynomial.pderiv (some (Sum.inr y)) (MvPolynomial.rename (@inlVar V₁ V₂) P) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hmem
  rcases MvPolynomial.mem_vars_rename (@inlVar V₁ V₂) P hmem with ⟨i, _, hi⟩
  cases hi

omit [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂] in
private theorem pderiv_none_rename_inr (P : MvPolynomial V₂ ℤ) :
    MvPolynomial.pderiv none (MvPolynomial.rename (@inrVar V₁ V₂) P) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hmem
  rcases MvPolynomial.mem_vars_rename (@inrVar V₁ V₂) P hmem with ⟨i, _, hi⟩
  cases hi

omit [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂] in
private theorem pderiv_inl_rename_inr (P : MvPolynomial V₂ ℤ) (x : V₁) :
    MvPolynomial.pderiv (some (Sum.inl x)) (MvPolynomial.rename (@inrVar V₁ V₂) P) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hmem
  rcases MvPolynomial.mem_vars_rename (@inrVar V₁ V₂) P hmem with ⟨i, _, hi⟩
  cases hi

private theorem sum_inl_terms_rename_inl (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂)
    (P : MvPolynomial V₁ ℤ) :
    (∑ x : V₁,
        MvPolynomial.pderiv (some (Sum.inl x)) (MvPolynomial.rename (@inlVar V₁ V₂) P) *
          ((AnalyticReal.add ar₁ ar₂).deriv (some (Sum.inl x))).toMvPolynomialInt) =
      MvPolynomial.rename (@inlVar V₁ V₂)
        (∑ x : V₁, MvPolynomial.pderiv x P * (ar₁.deriv x).toMvPolynomialInt) := by
  calc
    (∑ x : V₁,
        MvPolynomial.pderiv (some (Sum.inl x)) (MvPolynomial.rename (@inlVar V₁ V₂) P) *
          ((AnalyticReal.add ar₁ ar₂).deriv (some (Sum.inl x))).toMvPolynomialInt)
      =
        ∑ x : V₁,
          MvPolynomial.rename (@inlVar V₁ V₂)
            (MvPolynomial.pderiv x P * (ar₁.deriv x).toMvPolynomialInt) := by
          apply Fintype.sum_congr
          intro x
          change MvPolynomial.pderiv (inlVar x) (MvPolynomial.rename (@inlVar V₁ V₂) P) *
              ((AnalyticReal.add ar₁ ar₂).deriv (some (Sum.inl x))).toMvPolynomialInt
            =
              MvPolynomial.rename (@inlVar V₁ V₂)
                (MvPolynomial.pderiv x P * (ar₁.deriv x).toMvPolynomialInt)
          rw [MvPolynomial.pderiv_rename (inlVar_injective (V₁ := V₁) (V₂ := V₂)) x]
          simp [AnalyticReal.add, VPoly.toMvPolynomialInt_rename, map_mul, inlVar]
    _ = MvPolynomial.rename (@inlVar V₁ V₂)
          (∑ x : V₁, MvPolynomial.pderiv x P * (ar₁.deriv x).toMvPolynomialInt) := by
          exact
            (map_sum (MvPolynomial.rename (@inlVar V₁ V₂))
              (fun x : V₁ => MvPolynomial.pderiv x P * (ar₁.deriv x).toMvPolynomialInt)
              Finset.univ).symm

private theorem sum_inr_terms_rename_inr (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂)
    (P : MvPolynomial V₂ ℤ) :
    (∑ y : V₂,
        MvPolynomial.pderiv (some (Sum.inr y)) (MvPolynomial.rename (@inrVar V₁ V₂) P) *
          ((AnalyticReal.add ar₁ ar₂).deriv (some (Sum.inr y))).toMvPolynomialInt) =
      MvPolynomial.rename (@inrVar V₁ V₂)
        (∑ y : V₂, MvPolynomial.pderiv y P * (ar₂.deriv y).toMvPolynomialInt) := by
  calc
    (∑ y : V₂,
        MvPolynomial.pderiv (some (Sum.inr y)) (MvPolynomial.rename (@inrVar V₁ V₂) P) *
          ((AnalyticReal.add ar₁ ar₂).deriv (some (Sum.inr y))).toMvPolynomialInt)
      =
        ∑ y : V₂,
          MvPolynomial.rename (@inrVar V₁ V₂)
            (MvPolynomial.pderiv y P * (ar₂.deriv y).toMvPolynomialInt) := by
          apply Fintype.sum_congr
          intro y
          change MvPolynomial.pderiv (inrVar y) (MvPolynomial.rename (@inrVar V₁ V₂) P) *
              ((AnalyticReal.add ar₁ ar₂).deriv (some (Sum.inr y))).toMvPolynomialInt
            =
              MvPolynomial.rename (@inrVar V₁ V₂)
                (MvPolynomial.pderiv y P * (ar₂.deriv y).toMvPolynomialInt)
          rw [MvPolynomial.pderiv_rename (inrVar_injective (V₁ := V₁) (V₂ := V₂)) y]
          simp [AnalyticReal.add, VPoly.toMvPolynomialInt_rename, map_mul, inrVar]
    _ = MvPolynomial.rename (@inrVar V₁ V₂)
          (∑ y : V₂, MvPolynomial.pderiv y P * (ar₂.deriv y).toMvPolynomialInt) := by
          exact
            (map_sum (MvPolynomial.rename (@inrVar V₁ V₂))
              (fun y : V₂ => MvPolynomial.pderiv y P * (ar₂.deriv y).toMvPolynomialInt)
              Finset.univ).symm

private theorem sum_inr_terms_zero (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂)
    (P : MvPolynomial V₁ ℤ) :
    (∑ y : V₂,
      MvPolynomial.pderiv (some (Sum.inr y)) (MvPolynomial.rename (@inlVar V₁ V₂) P) *
        ((AnalyticReal.add ar₁ ar₂).deriv (some (Sum.inr y))).toMvPolynomialInt)
      = (0 : MvPolynomial (Option (V₁ ⊕ V₂)) ℤ) := by
  classical
  simp [pderiv_inr_rename_inl, AnalyticReal.add]

private theorem sum_inl_terms_zero (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂)
    (P : MvPolynomial V₂ ℤ) :
    (∑ x : V₁,
      MvPolynomial.pderiv (some (Sum.inl x)) (MvPolynomial.rename (@inrVar V₁ V₂) P) *
        ((AnalyticReal.add ar₁ ar₂).deriv (some (Sum.inl x))).toMvPolynomialInt)
      = (0 : MvPolynomial (Option (V₁ ⊕ V₂)) ℤ) := by
  classical
  simp [pderiv_inl_rename_inr, AnalyticReal.add]

private theorem lieDeriv_add_rename_inl (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂)
    (P : MvPolynomial V₁ ℤ) :
    (∑ v : Option (V₁ ⊕ V₂),
        MvPolynomial.pderiv v (MvPolynomial.rename (@inlVar V₁ V₂) P) *
          ((AnalyticReal.add ar₁ ar₂).deriv v).toMvPolynomialInt) =
      MvPolynomial.rename (@inlVar V₁ V₂)
        (∑ x : V₁, MvPolynomial.pderiv x P * (ar₁.deriv x).toMvPolynomialInt) := by
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  rw [pderiv_none_rename_inl]
  rw [sum_inr_terms_zero, sum_inl_terms_rename_inl]
  simp [AnalyticReal.add]

private theorem lieDeriv_add_rename_inr (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂)
    (P : MvPolynomial V₂ ℤ) :
    (∑ v : Option (V₁ ⊕ V₂),
        MvPolynomial.pderiv v (MvPolynomial.rename (@inrVar V₁ V₂) P) *
          ((AnalyticReal.add ar₁ ar₂).deriv v).toMvPolynomialInt) =
      MvPolynomial.rename (@inrVar V₁ V₂)
        (∑ y : V₂, MvPolynomial.pderiv y P * (ar₂.deriv y).toMvPolynomialInt) := by
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  rw [pderiv_none_rename_inr]
  rw [sum_inl_terms_zero, sum_inr_terms_rename_inr]
  simp [AnalyticReal.add]

private theorem lieIter_one_toMvPolynomialInt {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) :
    (AnalyticReal.lieIter A 1).toMvPolynomialInt = (A.deriv A.out).toMvPolynomialInt := by
  classical
  rw [AnalyticReal.lieIter, AnalyticReal.lieDeriv_toMvPolynomialInt]
  rw [AnalyticReal.lieIter]
  rw [Finset.sum_eq_single A.out]
  · have hself : (MvPolynomial.pderiv A.out) (VPoly.X A.out).toMvPolynomialInt = 1 := by
      rw [VPoly.toMvPolynomialInt]
      exact MvPolynomial.pderiv_X_self (i := A.out)
    rw [hself]
    rw [one_mul]
  · intro x hx hne
    have hzero : (MvPolynomial.pderiv x) (VPoly.X A.out).toMvPolynomialInt = 0 := by
      simpa [VPoly.toMvPolynomialInt] using
        (MvPolynomial.pderiv_X_of_ne (i := x) (j := A.out) (by simpa [eq_comm] using hne))
    rw [hzero]
    rw [zero_mul]
  · intro hout
    exact (hout (Finset.mem_univ A.out)).elim

private theorem lieIter_add_succ_toMvPolynomialInt (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) :
    ∀ n : ℕ,
      (AnalyticReal.lieIter (AnalyticReal.add ar₁ ar₂) (n + 1)).toMvPolynomialInt =
        MvPolynomial.rename (@inlVar V₁ V₂)
          (AnalyticReal.lieIter ar₁ (n + 1)).toMvPolynomialInt +
        MvPolynomial.rename (@inrVar V₁ V₂)
          (AnalyticReal.lieIter ar₂ (n + 1)).toMvPolynomialInt
  | 0 => by
      classical
      calc
        (AnalyticReal.lieIter (AnalyticReal.add ar₁ ar₂) 1).toMvPolynomialInt
          =
            MvPolynomial.rename (@inlVar V₁ V₂) (ar₁.deriv ar₁.out).toMvPolynomialInt +
              MvPolynomial.rename (@inrVar V₁ V₂) (ar₂.deriv ar₂.out).toMvPolynomialInt := by
                rw [lieIter_one_toMvPolynomialInt]
                simp [AnalyticReal.add, inlVar, inrVar, VPoly.toMvPolynomialInt,
                  VPoly.toMvPolynomialInt_rename]
        _ =
            MvPolynomial.rename (@inlVar V₁ V₂)
                (AnalyticReal.lieIter ar₁ 1).toMvPolynomialInt +
              MvPolynomial.rename (@inrVar V₁ V₂)
                (AnalyticReal.lieIter ar₂ 1).toMvPolynomialInt := by
                  rw [lieIter_one_toMvPolynomialInt, lieIter_one_toMvPolynomialInt]
  | n + 1 => by
      rw [AnalyticReal.lieIter, AnalyticReal.lieDeriv_toMvPolynomialInt]
      rw [lieIter_add_succ_toMvPolynomialInt ar₁ ar₂ n]
      simp only [map_add, add_mul, Finset.sum_add_distrib]
      rw [lieDeriv_add_rename_inl (ar₁ := ar₁) (ar₂ := ar₂)
        (P := (AnalyticReal.lieIter ar₁ (n + 1)).toMvPolynomialInt)]
      rw [lieDeriv_add_rename_inr (ar₁ := ar₁) (ar₂ := ar₂)
        (P := (AnalyticReal.lieIter ar₂ (n + 1)).toMvPolynomialInt)]
      simp [AnalyticReal.lieIter, AnalyticReal.lieDeriv_toMvPolynomialInt]

theorem taylorCoeff_add (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) :
    ∀ k : ℕ,
      AnalyticReal.taylorCoeff (AnalyticReal.add ar₁ ar₂) k =
        AnalyticReal.taylorCoeff ar₁ k + AnalyticReal.taylorCoeff ar₂ k
  | 0 => by
      simp [AnalyticReal.taylorCoeff_zero]
  | k + 1 => by
      unfold AnalyticReal.taylorCoeff
      have hpoly := lieIter_add_succ_toMvPolynomialInt ar₁ ar₂ k
      have heval :=
        congrArg
          (fun q : MvPolynomial (Option (V₁ ⊕ V₂)) ℤ =>
            q.eval₂ (Int.castRingHom ℚ) (AnalyticReal.add ar₁ ar₂).init)
          hpoly
      have hleftEval :
          (MvPolynomial.rename (@inlVar V₁ V₂)
              (AnalyticReal.lieIter ar₁ (k + 1)).toMvPolynomialInt).eval₂
              (Int.castRingHom ℚ) (AnalyticReal.add ar₁ ar₂).init
            = (AnalyticReal.lieIter ar₁ (k + 1)).eval ar₁.init := by
        rw [MvPolynomial.eval₂_rename]
        simp [add_init_comp_inl]
      have hrightEval :
          (MvPolynomial.rename (@inrVar V₁ V₂)
              (AnalyticReal.lieIter ar₂ (k + 1)).toMvPolynomialInt).eval₂
              (Int.castRingHom ℚ) (AnalyticReal.add ar₁ ar₂).init
            = (AnalyticReal.lieIter ar₂ (k + 1)).eval ar₂.init := by
        rw [MvPolynomial.eval₂_rename]
        simp [add_init_comp_inr]
      have hmain :
          (AnalyticReal.lieIter (AnalyticReal.add ar₁ ar₂) (k + 1)).eval (AnalyticReal.add ar₁ ar₂).init =
            (AnalyticReal.lieIter ar₁ (k + 1)).eval ar₁.init +
              (AnalyticReal.lieIter ar₂ (k + 1)).eval ar₂.init := by
        calc
          (AnalyticReal.lieIter (AnalyticReal.add ar₁ ar₂) (k + 1)).eval (AnalyticReal.add ar₁ ar₂).init
            =
              ((AnalyticReal.lieIter (AnalyticReal.add ar₁ ar₂) (k + 1)).toMvPolynomialInt).eval₂
                (Int.castRingHom ℚ) (AnalyticReal.add ar₁ ar₂).init := by
                  symm
                  exact VPoly.eval₂_toMvPolynomialInt
                    (env := (AnalyticReal.add ar₁ ar₂).init)
                    (p := AnalyticReal.lieIter (AnalyticReal.add ar₁ ar₂) (k + 1))
          _ =
              (MvPolynomial.rename (@inlVar V₁ V₂)
                  (AnalyticReal.lieIter ar₁ (k + 1)).toMvPolynomialInt).eval₂
                  (Int.castRingHom ℚ) (AnalyticReal.add ar₁ ar₂).init
                +
              (MvPolynomial.rename (@inrVar V₁ V₂)
                  (AnalyticReal.lieIter ar₂ (k + 1)).toMvPolynomialInt).eval₂
                  (Int.castRingHom ℚ) (AnalyticReal.add ar₁ ar₂).init := by
                    simpa using heval
          _ = (AnalyticReal.lieIter ar₁ (k + 1)).eval ar₁.init +
                (AnalyticReal.lieIter ar₂ (k + 1)).eval ar₂.init := by
                  rw [hleftEval, hrightEval]
      calc
        (AnalyticReal.lieIter (AnalyticReal.add ar₁ ar₂) (k + 1)).eval (AnalyticReal.add ar₁ ar₂).init /
            (Nat.factorial (k + 1) : ℚ)
          =
            ((AnalyticReal.lieIter ar₁ (k + 1)).eval ar₁.init +
                (AnalyticReal.lieIter ar₂ (k + 1)).eval ar₂.init) /
              (Nat.factorial (k + 1) : ℚ) := by
                rw [hmain]
        _ =
            (AnalyticReal.lieIter ar₁ (k + 1)).eval ar₁.init / (Nat.factorial (k + 1) : ℚ) +
              (AnalyticReal.lieIter ar₂ (k + 1)).eval ar₂.init / (Nat.factorial (k + 1) : ℚ) := by
                rw [add_div]

theorem approxSumAt_add (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) (t : ℚ) (n : ℕ) :
    AnalyticReal.approxSumAt (AnalyticReal.add ar₁ ar₂) t n =
      AnalyticReal.approxSumAt ar₁ t n + AnalyticReal.approxSumAt ar₂ t n := by
  unfold AnalyticReal.approxSumAt AnalyticReal.taylorTerm
  calc
    Finset.sum (Finset.range (n + 1))
        (fun k => t ^ k * AnalyticReal.taylorCoeff (AnalyticReal.add ar₁ ar₂) k)
      =
        Finset.sum (Finset.range (n + 1))
          (fun k => t ^ k * AnalyticReal.taylorCoeff ar₁ k +
            t ^ k * AnalyticReal.taylorCoeff ar₂ k) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [taylorCoeff_add]
            ring
    _ =
        Finset.sum (Finset.range (n + 1))
          (fun k => t ^ k * AnalyticReal.taylorCoeff ar₁ k) +
          Finset.sum (Finset.range (n + 1))
            (fun k => t ^ k * AnalyticReal.taylorCoeff ar₂ k) := by
            rw [Finset.sum_add_distrib]

@[simp] theorem approxSum_add (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) (n : ℕ) :
    AnalyticReal.approxSum (AnalyticReal.add ar₁ ar₂) n =
      AnalyticReal.approxSum ar₁ n + AnalyticReal.approxSum ar₂ n := by
  simpa [AnalyticReal.approxSum_eq_approxSumAt_one] using approxSumAt_add ar₁ ar₂ (1 : ℚ) n

namespace HasConstructiveTaylorLimitAt

noncomputable def add {ar₁ : AnalyticReal V₁} {ar₂ : AnalyticReal V₂} {t : ℚ}
    (h₁ : HasConstructiveTaylorLimitAt ar₁ t)
    (h₂ : HasConstructiveTaylorLimitAt ar₂ t) :
    HasConstructiveTaylorLimitAt (AnalyticReal.add ar₁ ar₂) t := by
  let μ : ℕ → ℕ := fun k => max (h₁.sequence.μ (k + 1)) (h₂.sequence.μ (k + 1))
  have hμ : Monotone μ := by
    intro a b hab
    dsimp [μ]
    exact max_le_max
      (h₁.sequence.μ_mono (Nat.succ_le_succ hab))
      (h₂.sequence.μ_mono (Nat.succ_le_succ hab))
  refine mkHasConstructiveTaylorLimitAt (A := AnalyticReal.add ar₁ ar₂) (t := t) μ hμ ?_
  intro k n m hn hm
  have hn₁ : h₁.sequence.μ (k + 1) ≤ n := Nat.le_trans (le_max_left _ _) hn
  have hm₁ : h₁.sequence.μ (k + 1) ≤ m := Nat.le_trans (le_max_left _ _) hm
  have hn₂ : h₂.sequence.μ (k + 1) ≤ n := Nat.le_trans (le_max_right _ _) hn
  have hm₂ : h₂.sequence.μ (k + 1) ≤ m := Nat.le_trans (le_max_right _ _) hm
  have hc₁ :
      |AnalyticReal.approxSumAt ar₁ t n - AnalyticReal.approxSumAt ar₁ t m|
        ≤ (1 : ℚ) / 2 ^ (k + 2) := by
    simpa [sequence_pre_apply h₁ n, sequence_pre_apply h₁ m, Computable.CReal.Pre.ofRat] using
      h₁.sequence.is_cauchy (k + 1) n m hn₁ hm₁
  have hc₂ :
      |AnalyticReal.approxSumAt ar₂ t n - AnalyticReal.approxSumAt ar₂ t m|
        ≤ (1 : ℚ) / 2 ^ (k + 2) := by
    simpa [sequence_pre_apply h₂ n, sequence_pre_apply h₂ m, Computable.CReal.Pre.ofRat] using
      h₂.sequence.is_cauchy (k + 1) n m hn₂ hm₂
  calc
    |AnalyticReal.approxSumAt (AnalyticReal.add ar₁ ar₂) t n -
        AnalyticReal.approxSumAt (AnalyticReal.add ar₁ ar₂) t m|
      =
        |(AnalyticReal.approxSumAt ar₁ t n - AnalyticReal.approxSumAt ar₁ t m) +
          (AnalyticReal.approxSumAt ar₂ t n - AnalyticReal.approxSumAt ar₂ t m)| := by
            rw [approxSumAt_add, approxSumAt_add]
            ring_nf
    _ ≤
        |AnalyticReal.approxSumAt ar₁ t n - AnalyticReal.approxSumAt ar₁ t m| +
          |AnalyticReal.approxSumAt ar₂ t n - AnalyticReal.approxSumAt ar₂ t m| := by
            exact abs_add_le _ _
    _ ≤ (1 : ℚ) / 2 ^ (k + 2) + (1 : ℚ) / 2 ^ (k + 2) := add_le_add hc₁ hc₂
    _ = (1 : ℚ) / 2 ^ (k + 1) := by
          simpa [Nat.add_assoc] using (Computable.CReal.two_halves_to_pred (k + 1))

end HasConstructiveTaylorLimitAt

namespace HasConstructiveTaylorLimit

noncomputable def add {ar₁ : AnalyticReal V₁} {ar₂ : AnalyticReal V₂}
    (h₁ : HasConstructiveTaylorLimit ar₁)
    (h₂ : HasConstructiveTaylorLimit ar₂) :
    HasConstructiveTaylorLimit (AnalyticReal.add ar₁ ar₂) := by
  simpa [HasConstructiveTaylorLimit] using
    (HasConstructiveTaylorLimitAt.add (t := (1 : ℚ)) h₁ h₂)

end HasConstructiveTaylorLimit

end

end Analytic
end CReal
end Computable
