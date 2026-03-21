import Rebuild.Learning.Boltzmann.Core

/-!
# Rebuild Vector Gibbs Learning

Vector-valued finite Gibbs statistics.
-/

set_option autoImplicit false

namespace Rebuild.Learning.Boltzmann

open Rebuild.Core

abbrev VectorStatistic (Index State : Type*) := State → Index → ℝ

noncomputable section

variable {Index State : Type*} [Fintype State] [Nonempty State] [MeasurableSpace State]
 [MeasurableSingletonClass State]

/-- Coordinate expectations of a vector-valued statistic. -/
noncomputable def vectorExpectation (μ : MeasureTheory.Measure State)
  (φ : VectorStatistic Index State) : Index → ℝ :=
 fun i => expectation μ (fun σ => φ σ i)

end

end Rebuild.Learning.Boltzmann
