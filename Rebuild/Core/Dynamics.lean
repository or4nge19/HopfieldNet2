import Mathlib.Probability.Kernel.Basic
import Rebuild.Core.Configuration

set_option autoImplicit false

namespace Rebuild.Core

open ProbabilityTheory

structure DeterministicDynamics (Θ State : Type*) where
  step : Θ → State → State

structure StochasticDynamics (Θ State : Type*) [MeasurableSpace State] where
  step : Θ → Kernel State State

structure IndexedStochasticDynamics (Index Θ State : Type*) [MeasurableSpace State] where
  K : Index → Θ → Kernel State State

variable {Site Spin : Type*} [DecidableEq Site]

structure LocalDeterministicUpdate (Site Spin : Type*) [DecidableEq Site] where
  update : Site → Configuration Site Spin → Configuration Site Spin
  preserves_offsite : ∀ i σ j, j ≠ i → update i σ j = σ j

end Rebuild.Core
