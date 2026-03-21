import Rebuild.Core.Gibbs
import Rebuild.Core.TwoState
import Rebuild.StatMech.FiniteGibbs.Core
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Rebuild Boltzmann Learning Core

Small, typed learning interface built on explicit statistics and expectations.
-/

set_option autoImplicit false

open MeasureTheory

namespace Rebuild.Learning.Boltzmann

open Rebuild.Core
open Rebuild.StatMech.FiniteGibbs

abbrev Statistic (State : Type*) := State → ℝ

noncomputable section

variable {State : Type*} [Fintype State] [Nonempty State] [MeasurableSpace State]
 [MeasurableSingletonClass State]

/-- Expectation of a statistic under a measure. -/
noncomputable def expectation (μ : Measure State) (f : Statistic State) : ℝ :=
 ∫ σ, f σ ∂μ

/-- Expectation of a statistic under the Gibbs law of a finite model. -/
noncomputable def modelExpectation (β : ℝ) (model : FiniteGibbsModel State)
  (f : Statistic State) : ℝ :=
 expectation (gibbsMeasure β model) f

/-- A finite family of sufficient statistics, indexed by a parameter set. -/
structure StatisticFamily (Index State : Type*) where
 stat : Index → Statistic State

/-- A positive/negative phase pair for learning semantics. -/
structure PhasePair (State : Type*) [MeasurableSpace State] where
 positive : Measure State
 negative : Measure State

/-- Expectation gap between the positive and negative phases. -/
noncomputable def phaseGap (phases : PhasePair State) (f : Statistic State) : ℝ :=
 expectation phases.positive f - expectation phases.negative f

/-- Package a data distribution and a Gibbs model law as a learning phase pair. -/
noncomputable def modelPhasePair (data : Measure State) (β : ℝ)
  (model : FiniteGibbsModel State) : PhasePair State where
 positive := data
 negative := gibbsMeasure β model

@[simp]
lemma modelPhasePair_positive (data : Measure State) (β : ℝ)
  (model : FiniteGibbsModel State) :
  (modelPhasePair data β model).positive = data := rfl

@[simp]
lemma modelPhasePair_negative (data : Measure State) (β : ℝ)
  (model : FiniteGibbsModel State) :
  (modelPhasePair data β model).negative = gibbsMeasure β model := rfl

/-- Coordinate-wise phase gap for a family of sufficient statistics. -/
noncomputable def coordinatePhaseGap {Index : Type*}
  (phases : PhasePair State) (stats : StatisticFamily Index State) : Index → ℝ :=
 fun i => phaseGap phases (stats.stat i)

end

end Rebuild.Learning.Boltzmann
