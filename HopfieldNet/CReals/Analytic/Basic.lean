import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename

namespace Computable
namespace CReal
namespace Analytic

open scoped BigOperators

inductive VPoly (V : Type)
  | C : ℤ → VPoly V
  | X : V → VPoly V
  | add : VPoly V → VPoly V → VPoly V
  | mul : VPoly V → VPoly V → VPoly V
  | neg : VPoly V → VPoly V

namespace VPoly

variable {V : Type}

instance : Zero (VPoly V) := ⟨C 0⟩
instance : Add (VPoly V) := ⟨add⟩
instance : Mul (VPoly V) := ⟨mul⟩
instance : Neg (VPoly V) := ⟨neg⟩
instance : Sub (VPoly V) := ⟨fun p q => p + (-q)⟩

def eval {R : Type} [CommRing R] (env : V → R) : VPoly V → R
  | C z => (z : R)
  | X v => env v
  | add p q => p.eval env + q.eval env
  | mul p q => p.eval env * q.eval env
  | neg p => -p.eval env

def pderiv [DecidableEq V] (v : V) : VPoly V → VPoly V
  | C _ => 0
  | X x => if x = v then C 1 else 0
  | add p q => p.pderiv v + q.pderiv v
  | mul p q => p.pderiv v * q + p * q.pderiv v
  | neg p => -(p.pderiv v)

def rename {W : Type} (f : V → W) : VPoly V → VPoly W
  | C z => C z
  | X v => X (f v)
  | add p q => p.rename f + q.rename f
  | mul p q => p.rename f * q.rename f
  | neg p => -(p.rename f)

noncomputable def toMvPolynomialInt : VPoly V → MvPolynomial V ℤ
  | C z => MvPolynomial.C z
  | X v => MvPolynomial.X v
  | add p q => p.toMvPolynomialInt + q.toMvPolynomialInt
  | mul p q => p.toMvPolynomialInt * q.toMvPolynomialInt
  | neg p => -p.toMvPolynomialInt

noncomputable def toMvPolynomial : VPoly V → MvPolynomial V ℚ :=
  fun p => MvPolynomial.map (Int.castRingHom ℚ) p.toMvPolynomialInt

@[simp]
theorem eval_add {R : Type} [CommRing R] (env : V → R) (p q : VPoly V) :
    (p + q).eval env = p.eval env + q.eval env := rfl

@[simp]
theorem eval_mul {R : Type} [CommRing R] (env : V → R) (p q : VPoly V) :
    (p * q).eval env = p.eval env * q.eval env := rfl

@[simp]
theorem eval_neg {R : Type} [CommRing R] (env : V → R) (p : VPoly V) :
    (-p).eval env = -p.eval env := rfl

@[simp]
theorem eval_rename {W R : Type} [CommRing R]
    (f : V → W) (env : W → R) (p : VPoly V) :
    (p.rename f).eval env = p.eval (env ∘ f) := by
  induction p with
  | C => rfl
  | X => rfl
  | add p q ihp ihq => simp [VPoly.eval, rename, ihp, ihq]
  | mul p q ihp ihq => simp [VPoly.eval, rename, ihp, ihq]
  | neg p ih => simp [VPoly.eval, rename, ih]

@[simp]
theorem toMvPolynomial_eq_map_intCast (p : VPoly V) :
    p.toMvPolynomial = MvPolynomial.map (Int.castRingHom ℚ) p.toMvPolynomialInt := rfl

@[simp]
theorem toMvPolynomialInt_rename {W : Type} (f : V → W) (p : VPoly V) :
    (p.rename f).toMvPolynomialInt = MvPolynomial.rename f p.toMvPolynomialInt := by
  induction p with
  | C => simp [rename, toMvPolynomialInt]
  | X => simp [rename, toMvPolynomialInt]
  | add p q ihp ihq => simp [rename, toMvPolynomialInt, ihp, ihq]
  | mul p q ihp ihq => simp [rename, toMvPolynomialInt, ihp, ihq]
  | neg p ih => simp [rename, toMvPolynomialInt, ih]

@[simp]
theorem toMvPolynomial_rename {W : Type} (f : V → W) (p : VPoly V) :
    (p.rename f).toMvPolynomial = MvPolynomial.rename f p.toMvPolynomial := by
  rw [toMvPolynomial_eq_map_intCast, toMvPolynomial_eq_map_intCast, toMvPolynomialInt_rename]
  simpa using (MvPolynomial.map_rename (Int.castRingHom ℚ) f p.toMvPolynomialInt)

@[simp]
theorem eval₂_toMvPolynomialInt {R : Type} [CommRing R] (env : V → R) (p : VPoly V) :
    p.toMvPolynomialInt.eval₂ (Int.castRingHom R) env = p.eval env := by
  induction p with
  | C z =>
      simpa [VPoly.eval, toMvPolynomialInt] using
        (MvPolynomial.eval₂_C (f := Int.castRingHom R) (g := env) z)
  | X v =>
      simp [VPoly.eval, toMvPolynomialInt]
  | add p q ihp ihq =>
      simpa [VPoly.eval, toMvPolynomialInt] using
        congrArg₂ HAdd.hAdd
          (show p.toMvPolynomialInt.eval₂ (Int.castRingHom R) env = p.eval env from ihp)
          (show q.toMvPolynomialInt.eval₂ (Int.castRingHom R) env = q.eval env from ihq)
  | mul p q ihp ihq =>
      simpa [VPoly.eval, toMvPolynomialInt, MvPolynomial.eval₂_mul] using
        congrArg₂ HMul.hMul
          (show p.toMvPolynomialInt.eval₂ (Int.castRingHom R) env = p.eval env from ihp)
          (show q.toMvPolynomialInt.eval₂ (Int.castRingHom R) env = q.eval env from ihq)
  | neg p ih =>
      change MvPolynomial.eval₂ (Int.castRingHom R) env (-p.toMvPolynomialInt) = -p.eval env
      simp [ih]

@[simp] theorem toMvPolynomialInt_pderiv [DecidableEq V] (v : V) (p : VPoly V) :
    (p.pderiv v).toMvPolynomialInt = MvPolynomial.pderiv v p.toMvPolynomialInt := by
  induction p with
  | C z =>
      simp [VPoly.pderiv, toMvPolynomialInt]
  | X x =>
      by_cases h : x = v
      · subst h
        simp [VPoly.pderiv, toMvPolynomialInt]
      · simp [VPoly.pderiv, toMvPolynomialInt, h]
  | add p q ihp ihq =>
      simp [VPoly.pderiv, toMvPolynomialInt, ihp, ihq]
  | mul p q ihp ihq =>
      simp [VPoly.pderiv, toMvPolynomialInt, ihp, ihq]
      ring
  | neg p ih =>
      simp [VPoly.pderiv, toMvPolynomialInt, ih]

@[simp] theorem toMvPolynomial_pderiv [DecidableEq V] (v : V) (p : VPoly V) :
    (p.pderiv v).toMvPolynomial = MvPolynomial.pderiv v p.toMvPolynomial := by
  rw [toMvPolynomial_eq_map_intCast, toMvPolynomial_eq_map_intCast]
  rw [toMvPolynomialInt_pderiv]
  simp [MvPolynomial.pderiv_map]

end VPoly

structure AnalyticReal (V : Type) [Fintype V] [DecidableEq V] where
  out : V
  init : V → ℚ
  deriv : V → VPoly V
  out_init_zero : init out = 0

namespace AnalyticReal

open VPoly

def const (q : ℤ) : AnalyticReal Unit where
  out := ()
  init := fun _ => 0
  deriv := fun _ => VPoly.C q
  out_init_zero := rfl

def invM1 {V : Type} [Fintype V] [DecidableEq V]
    (ar : AnalyticReal V) : AnalyticReal (Option V) where
  out := none
  init := fun v => match v with
    | none => 0
    | some x => ar.init x
  deriv := fun v => match v with
    | none =>
        let dx := VPoly.rename some (ar.deriv ar.out)
        let z := VPoly.X (none : Option V)
        let z1 := z + VPoly.C 1
        VPoly.neg (z1 * z1 * dx)
    | some x => VPoly.rename some (ar.deriv x)
  out_init_zero := rfl

variable {V₁ V₂ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]

def add (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) :
    AnalyticReal (Option (V₁ ⊕ V₂)) where
  out := none
  init := fun v => match v with
    | none => 0
    | some (Sum.inl x) => ar₁.init x
    | some (Sum.inr y) => ar₂.init y
  deriv := fun v => match v with
    | none =>
        VPoly.rename (some ∘ Sum.inl) (ar₁.deriv ar₁.out) +
        VPoly.rename (some ∘ Sum.inr) (ar₂.deriv ar₂.out)
    | some (Sum.inl x) => VPoly.rename (some ∘ Sum.inl) (ar₁.deriv x)
    | some (Sum.inr y) => VPoly.rename (some ∘ Sum.inr) (ar₂.deriv y)
  out_init_zero := rfl

def mul (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) :
    AnalyticReal (Option (V₁ ⊕ V₂)) where
  out := none
  init := fun v => match v with
    | none => 0
    | some (Sum.inl x) => ar₁.init x
    | some (Sum.inr y) => ar₂.init y
  deriv := fun v => match v with
    | none =>
        let dx := VPoly.rename (some ∘ Sum.inl) (ar₁.deriv ar₁.out)
        let dy := VPoly.rename (some ∘ Sum.inr) (ar₂.deriv ar₂.out)
        let xv := VPoly.X (some (Sum.inl ar₁.out))
        let yv := VPoly.X (some (Sum.inr ar₂.out))
        dx * yv + xv * dy
    | some (Sum.inl x) => VPoly.rename (some ∘ Sum.inl) (ar₁.deriv x)
    | some (Sum.inr y) => VPoly.rename (some ∘ Sum.inr) (ar₂.deriv y)
  out_init_zero := rfl

private noncomputable def lieTerms {V : Type} [Fintype V] [DecidableEq V]
    (dv : V → VPoly V) (F : VPoly V) : List (VPoly V) :=
  (Finset.univ : Finset V).toList.map (fun v => F.pderiv v * dv v)

private def sumPoly {V : Type} : List (VPoly V) → VPoly V
  | [] => 0
  | p :: ps => p + sumPoly ps

@[simp] theorem sumPoly_eval {V R : Type} [CommRing R]
    (env : V → R) : ∀ ps : List (VPoly V), (sumPoly ps).eval env = (ps.map fun p => p.eval env).sum
  | [] => by simp [sumPoly, VPoly.eval]
  | p :: ps => by
      simp [sumPoly, sumPoly_eval env ps]

@[simp] theorem sumPoly_toMvPolynomialInt {V : Type} :
    ∀ ps : List (VPoly V), (sumPoly ps).toMvPolynomialInt = (ps.map fun p => p.toMvPolynomialInt).sum
  | [] => by simp [sumPoly, toMvPolynomialInt]
  | p :: ps => by
      simp [sumPoly, sumPoly_toMvPolynomialInt ps, toMvPolynomialInt]

noncomputable def lieDeriv {V : Type} [Fintype V] [DecidableEq V]
    (dv : V → VPoly V) (F : VPoly V) : VPoly V :=
  sumPoly (lieTerms dv F)

@[simp] theorem lieDeriv_eval {V R : Type} [Fintype V] [DecidableEq V] [CommRing R]
    (dv : V → VPoly V) (F : VPoly V) (env : V → R) :
    (lieDeriv dv F).eval env = ∑ v, (F.pderiv v).eval env * (dv v).eval env := by
  classical
  unfold lieDeriv lieTerms
  rw [sumPoly_eval]
  rw [List.map_map]
  have hsum :
      (List.map ((fun p => p.eval env) ∘ fun v => F.pderiv v * dv v)
        ((Finset.univ : Finset V).toList)).sum
        =
      Finset.sum (((Finset.univ : Finset V).toList).toFinset)
        (fun v => ((fun p => p.eval env) ∘ fun v => F.pderiv v * dv v) v) := by
    exact
      (List.sum_toFinset
        (f := (fun p => p.eval env) ∘ fun v => F.pderiv v * dv v)
        (l := (Finset.univ : Finset V).toList)
        (Finset.nodup_toList (Finset.univ : Finset V))).symm
  rw [hsum]
  simp [Function.comp_apply, VPoly.eval_mul, Finset.toList_toFinset]

@[simp] theorem lieDeriv_toMvPolynomialInt {V : Type} [Fintype V] [DecidableEq V]
    (dv : V → VPoly V) (F : VPoly V) :
    (lieDeriv dv F).toMvPolynomialInt =
      ∑ v, MvPolynomial.pderiv v F.toMvPolynomialInt * (dv v).toMvPolynomialInt := by
  classical
  unfold lieDeriv lieTerms
  rw [sumPoly_toMvPolynomialInt]
  rw [List.map_map]
  have hsum :
      (List.map ((fun p => p.toMvPolynomialInt) ∘ fun v => F.pderiv v * dv v)
        ((Finset.univ : Finset V).toList)).sum
        =
      Finset.sum (((Finset.univ : Finset V).toList).toFinset)
        (fun v => ((fun p => p.toMvPolynomialInt) ∘ fun v => F.pderiv v * dv v) v) := by
    exact
      (List.sum_toFinset
        (f := (fun p => p.toMvPolynomialInt) ∘ fun v => F.pderiv v * dv v)
        (l := (Finset.univ : Finset V).toList)
        (Finset.nodup_toList (Finset.univ : Finset V))).symm
  rw [hsum]
  simp [Function.comp_apply, toMvPolynomialInt, toMvPolynomialInt_pderiv, Finset.toList_toFinset]

noncomputable def lieIter {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) : ℕ → VPoly V
  | 0 => VPoly.X A.out
  | n + 1 => lieDeriv A.deriv (lieIter A n)

noncomputable def taylorCoeff {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (k : ℕ) : ℚ :=
  (lieIter A k).eval A.init / (Nat.factorial k : ℚ)

noncomputable def taylorTerm {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (t : ℚ) (k : ℕ) : ℚ :=
  t ^ k * taylorCoeff A k

noncomputable def approxSumAt {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (t : ℚ) (n : ℕ) : ℚ :=
  Finset.sum (Finset.range (n + 1)) (fun k => taylorTerm A t k)

noncomputable def approxSum {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (n : ℕ) : ℚ :=
  approxSumAt A 1 n

@[simp] theorem taylorCoeff_zero {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) : taylorCoeff A 0 = 0 := by
  simp [taylorCoeff, lieIter, VPoly.eval, A.out_init_zero]

@[simp] theorem taylorTerm_zero {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (t : ℚ) : taylorTerm A t 0 = 0 := by
  simp [taylorTerm, taylorCoeff_zero]

@[simp] theorem approxSum_eq_approxSumAt_one {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (n : ℕ) : approxSum A n = approxSumAt A 1 n := rfl

@[simp] theorem approxSumAt_zero_index {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (t : ℚ) : approxSumAt A t 0 = 0 := by
  simp [approxSumAt]

@[simp] theorem approxSumAt_zero_time {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (n : ℕ) : approxSumAt A 0 n = 0 := by
  unfold approxSumAt
  refine Finset.sum_eq_zero ?_
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    simp [taylorTerm, taylorCoeff_zero]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    simp [taylorTerm, hk0]

end AnalyticReal

end Analytic
end CReal
end Computable
