import Rebuild.Models.Hopfield.Patterns
import Rebuild.Core.Gibbs

set_option autoImplicit false

namespace Rebuild.Bridges

open Rebuild.Core
open Rebuild.Models.Hopfield

section Finite

variable {PatternIndex Site : Type*}
variable [Fintype PatternIndex] [Fintype Site] [DecidableEq Site]

/-- Canonical Hopfield parameters obtained from a family of stored patterns and an
optional external field. -/
noncomputable def hebbianParameters
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0) :
    Parameters Site :=
  parametersOfPatterns ξ externalField

/-- Canonical Hopfield energy induced by a stored-pattern family. -/
noncomputable def hebbianEnergy
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0) :=
  energy (hebbianParameters ξ externalField)

/-- Canonical asynchronous Hopfield update induced by a stored-pattern family. -/
noncomputable def hebbianUpdateAt
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0)
    (i : Site) (τ : State Site) : State Site :=
  updateAt (hebbianParameters ξ externalField) i τ

/-- Canonical finite Gibbs package induced by a stored-pattern family. -/
noncomputable def hebbianFiniteGibbsModel
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0) :=
  finiteGibbsModel (hebbianParameters ξ externalField)

@[simp] theorem hebbianParameters_coupling
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0) :
    (hebbianParameters ξ externalField).coupling = hebbianCoupling ξ :=
  rfl

@[simp] theorem hebbianParameters_externalField
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0) :
    (hebbianParameters ξ externalField).externalField = externalField :=
  rfl

@[simp] theorem hebbianFiniteGibbsModel_energy
    (ξ : PatternFamily PatternIndex Site) (externalField : Site → ℝ := fun _ => 0) :
    (hebbianFiniteGibbsModel ξ externalField).energy = hebbianEnergy ξ externalField :=
  rfl

end Finite

end Rebuild.Bridges
