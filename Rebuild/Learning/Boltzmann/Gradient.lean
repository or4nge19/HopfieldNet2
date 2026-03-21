import Rebuild.Learning.Boltzmann.Core

/-!
# Rebuild Boltzmann Learning Gradients

Expectation-difference learning-rule interface.
-/

set_option autoImplicit false

namespace Rebuild.Learning.Boltzmann

noncomputable section

variable {Index Θ State : Type*} [MeasurableSpace State]

/-- Canonical coordinate update induced by a sufficient-statistics family. -/
noncomputable def canonicalUpdate
  (phases : PhasePair State) (stats : StatisticFamily Index State) : Index → ℝ :=
 coordinatePhaseGap phases stats

/-- Coordinate-wise learning directions indexed by sufficient statistics. -/
structure LearningRule (Index Θ State : Type*) [MeasurableSpace State] where
 updateDir : PhasePair State → Θ
 coord : Θ → Index → ℝ
 stats : StatisticFamily Index State
 correct : ∀ phases : PhasePair State,
  ∀ i, coord (updateDir phases) i =
   expectation phases.positive (stats.stat i) - expectation phases.negative (stats.stat i)

/-- The canonical Boltzmann-learning rule whose coordinates are expectation gaps. -/
noncomputable def canonicalLearningRule (stats : StatisticFamily Index State) :
  LearningRule Index (Index → ℝ) State where
 updateDir phases := canonicalUpdate phases stats
 coord θ i := θ i
 stats := stats
 correct phases i := rfl

end

end Rebuild.Learning.Boltzmann
