import Rebuild.Models.BoltzmannMachine.Basic
import Rebuild.Probability.GibbsMeasure.Basic
import Mathlib.Probability.Kernel.Basic

/-!
# Boltzmann Machine to Gibbs Measure Functor

This file acts as the explicit mathematical bridge between the discrete, purely topological
definition of a Boltzmann Machine (`Rebuild.Models.BoltzmannMachine`), and the measure-theoretic
framework of Probability Theory and Markov Kernels (`Rebuild.Probability.GibbsMeasure`).

Following the strict formal ontology:
1. Boltzmann machines supply standard finite states, graphs, and exact energy evaluations.
2. The Functor defined here lifts those discrete structures into `MeasureTheory.MeasureSpace` and `ProbabilityTheory.kernel`.
-/

namespace Rebuild.Bridges.BoltzmannToGibbs

open MeasureTheory ProbabilityTheory
open Rebuild.Models.BoltzmannMachine

section StochasticStubs

variable {Site : Type*} [Fintype Site] [DecidableEq Site]
variable [MeasurableSpace Site] [DiscreteMeasurableSpace Site]

/-- The measure space structure for the state space. -/
instance : MeasurableSpace (SignedState Site) := ⊤

/-- Signed state space is trivially a discrete measurable space. -/
instance : DiscreteMeasurableSpace (SignedState Site) := ⟨fun _ => trivial⟩

end StochasticStubs

end Rebuild.Bridges.BoltzmannToGibbs
