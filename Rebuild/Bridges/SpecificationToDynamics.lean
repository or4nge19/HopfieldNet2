import Rebuild.StatMech.Specification.Core
import Rebuild.Core.Dynamics

/-!
# Rebuild Specification to Dynamics Bridge

Bridge local specifications into indexed stochastic dynamics.
-/

set_option autoImplicit false

namespace Rebuild.Bridges

open Rebuild.Core
open Rebuild.StatMech.Specification

variable {Site Spin : Type*} [DecidableEq Site] [MeasurableSpace Spin]

noncomputable abbrev specificationToDynamics (γ : LocalSpecification Site Spin) :=
  Rebuild.StatMech.Specification.toIndexedStochasticDynamics γ

@[simp] lemma specificationToDynamics_apply (γ : LocalSpecification Site Spin)
    (V : FiniteVolume Site) :
    (specificationToDynamics γ).K V PUnit.unit = γ V := rfl

end Rebuild.Bridges
