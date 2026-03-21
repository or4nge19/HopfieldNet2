import Rebuild.StatMech.Specification.Core

/-!
# Rebuild Markov Specifications

Markov-property interface for local specifications.
-/

set_option autoImplicit false

namespace Rebuild.StatMech.Specification

open Rebuild.Core ProbabilityTheory

variable {Site Spin : Type*} [DecidableEq Site] [MeasurableSpace Spin]

/-- A specification is Markov if each local kernel is a Markov kernel. -/
def IsMarkov (γ : LocalSpecification Site Spin) : Prop :=
  ∀ V : FiniteVolume Site, IsMarkovKernel (γ.kernel V)

end Rebuild.StatMech.Specification
