import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.Comp
import Rebuild.Core.Specification
import Rebuild.Core.Dynamics

/-!
# Rebuild Specification Core

Neutral local-specification API for infinite-volume/statistical-mechanics semantics.

This file keeps the interface deliberately small:

- local kernels indexed by finite volumes,
- a consistency predicate,
- and a canonical bridge into indexed stochastic dynamics.
-/

set_option autoImplicit false

open ProbabilityTheory

namespace Rebuild.StatMech.Specification

open Rebuild.Core

abbrev StateSpace (Site Spin : Type*) := Configuration Site Spin

abbrev LocalSpecification (Site Spin : Type*) [DecidableEq Site] [MeasurableSpace Spin] :=
  Rebuild.Core.Specification Site Spin

variable {Site Spin : Type*} [DecidableEq Site] [MeasurableSpace Spin]

instance : CoeFun (LocalSpecification Site Spin)
    (fun _ => FiniteVolume Site → Kernel (StateSpace Site Spin) (StateSpace Site Spin)) where
  coe γ := γ.kernel

/-- A local specification is consistent if larger volumes absorb smaller-volume updates. -/
def IsConsistent (γ : LocalSpecification Site Spin) : Prop :=
  ∀ ⦃V W : FiniteVolume Site⦄,
    V.carrier ⊆ W.carrier →
      (γ V) ∘ₖ (γ W) = γ W

@[ext] theorem ext {γ₁ γ₂ : LocalSpecification Site Spin}
    (h : ∀ V, γ₁ V = γ₂ V) : γ₁ = γ₂ := by
  cases γ₁
  cases γ₂
  simp at h
  congr
  funext V
  exact h V

/-- The stochastic-dynamics view of a local specification. -/
noncomputable def toIndexedStochasticDynamics (γ : LocalSpecification Site Spin) :
    IndexedStochasticDynamics (FiniteVolume Site) PUnit (StateSpace Site Spin) where
  K := fun V _ => γ V

end Rebuild.StatMech.Specification
