import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv

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

noncomputable def toMvPolynomial : VPoly V → MvPolynomial V ℚ
  | C z => MvPolynomial.C (z : ℚ)
  | X v => MvPolynomial.X v
  | add p q => p.toMvPolynomial + q.toMvPolynomial
  | mul p q => p.toMvPolynomial * q.toMvPolynomial
  | neg p => -p.toMvPolynomial

@[simp] theorem eval_add {R : Type} [CommRing R] (env : V → R) (p q : VPoly V) :
    (p + q).eval env = p.eval env + q.eval env := rfl

@[simp] theorem eval_mul {R : Type} [CommRing R] (env : V → R) (p q : VPoly V) :
    (p * q).eval env = p.eval env * q.eval env := rfl

@[simp] theorem eval_neg {R : Type} [CommRing R] (env : V → R) (p : VPoly V) :
    (-p).eval env = -p.eval env := rfl

@[simp] theorem eval_rename {W R : Type} [CommRing R]
    (f : V → W) (env : W → R) (p : VPoly V) :
    (p.rename f).eval env = p.eval (env ∘ f) := by
  induction p with
  | C => rfl
  | X => rfl
  | add p q ihp ihq => simp [VPoly.eval, rename, ihp, ihq]
  | mul p q ihp ihq => simp [VPoly.eval, rename, ihp, ihq]
  | neg p ih => simp [VPoly.eval, rename, ih]

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

noncomputable def lieDeriv {V : Type} [Fintype V] [DecidableEq V]
    (dv : V → VPoly V) (F : VPoly V) : VPoly V :=
  sumPoly (lieTerms dv F)

noncomputable def lieIter {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) : ℕ → VPoly V
  | 0 => VPoly.X A.out
  | n + 1 => lieDeriv A.deriv (lieIter A n)

noncomputable def taylorCoeff {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (k : ℕ) : ℚ :=
  (lieIter A k).eval A.init / (Nat.factorial k : ℚ)

noncomputable def approxSum {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (n : ℕ) : ℚ :=
  Finset.sum (Finset.range (n + 1)) (fun k => taylorCoeff A k)

@[simp] theorem taylorCoeff_zero {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) : taylorCoeff A 0 = 0 := by
  simp [taylorCoeff, lieIter, VPoly.eval, A.out_init_zero]

end AnalyticReal

end Analytic
end CReal
end Computable
