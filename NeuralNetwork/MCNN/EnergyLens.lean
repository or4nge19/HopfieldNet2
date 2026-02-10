import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
## Energy-based learning: a principled `EnergyLens`

This module provides a small, **importable** core for energy-based models:

- an energy function `E : P → S → ℝ`
- a certified force/gradient field `∇E : P → S → (P × S)`

Crucially, we certify correctness using Mathlib’s `HasGradientAt`, so we can derive the
inner-product characterization against `fderiv` without any ad hoc “default derivative” tricks.
-/

namespace MCNN

open scoped Gradient

section

open scoped InnerProductSpace

/-- A bundled energy model on a Hilbert space `H`. -/
structure EnergyLens (H : Type*)
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  /-- Scalar energy / potential. -/
  energy : H → ℝ
  /-- Force vector field (a chosen gradient). -/
  force : H → H
  /-- Correctness certificate: `force x` is a gradient of `energy` at `x`. -/
  hasGrad : ∀ x, HasGradientAt energy (force x) x

namespace EnergyLens

/-- Inner-product characterization: \( \langle \nabla E(x), v \rangle = D E(x)\,v \). -/
lemma inner_force_eq_fderiv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (L : EnergyLens H) (x v : H) :
    ⟪L.force x, v⟫_ℝ = fderiv ℝ L.energy x v := by
  -- Mathlib gives `fderiv = ⟪grad,·⟫`; rewrite.
  -- `HasGradientAt.fderiv_apply` is stated as `fderiv ... = ⟪grad, v⟫`.
  simpa using (L.hasGrad x).fderiv_apply (y := v).symm

/-- Canonical construction from a globally differentiable energy. -/
noncomputable def ofDifferentiable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (energy : H → ℝ)
    (h : Differentiable ℝ energy) :
    EnergyLens H :=
{ energy := energy
  force := fun x => ∇ energy x
  hasGrad := by
    intro x
    exact (h.differentiableAt).hasGradientAt }

end EnergyLens

/-! ### Parameter–state specialization via `WithLp 2 (P × S)` -/

namespace EnergyLens

variable {P S : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]

/-- Canonical Hilbert space on `P × S` using the L2-product wrapper. -/
abbrev ParamState (P S : Type*) := WithLp 2 (P × S)

/-- Curry an energy `P → S → ℝ` into an energy on `WithLp 2 (P × S)`. -/
noncomputable def energyPS (E : P → S → ℝ) : ParamState P S → ℝ :=
  fun x => E (WithLp.ofLp x).1 (WithLp.ofLp x).2

/-- Build an `EnergyLens` on the canonical Hilbert space `WithLp 2 (P × S)` from a differentiable energy. -/
noncomputable def ofDifferentiablePS
    (E : P → S → ℝ)
    (h : Differentiable ℝ (energyPS (P:=P) (S:=S) E)) :
    EnergyLens (ParamState P S) :=
  EnergyLens.ofDifferentiable (energy := energyPS (P:=P) (S:=S) E) h

end EnergyLens

end

end MCNN
