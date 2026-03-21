import Mathlib
import Rebuild.Core.Energy

set_option autoImplicit false

open scoped BigOperators

namespace Rebuild.Core

noncomputable def boltzmannWeight {State : Type*} (β : ℝ) (E : Energy State) (σ : State) : ℝ :=
  Real.exp (-β * E σ)

noncomputable def partitionFunction {State : Type*} [Fintype State]
    (β : ℝ) (E : Energy State) : ℝ :=
  ∑ σ, boltzmannWeight β E σ

noncomputable def gibbsPMF {State : Type*} [Fintype State]
    (β : ℝ) (E : Energy State) (σ : State) : ℝ :=
  boltzmannWeight β E σ / partitionFunction β E

structure FiniteGibbsModel (State : Type*) [Fintype State] where
  energy : Energy State

end Rebuild.Core
