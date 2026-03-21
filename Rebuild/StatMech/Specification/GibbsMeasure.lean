import Rebuild.StatMech.Specification.Core
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Rebuild Gibbs Measures

Neutral Gibbs-measure interface over local specifications.
-/

set_option autoImplicit false

open ProbabilityTheory MeasureTheory

namespace Rebuild.StatMech.Specification

open Rebuild.Core

variable {Site Spin : Type*} [DecidableEq Site] [MeasurableSpace Spin]

/-- A measure is Gibbs for a specification if it is invariant under every local kernel. -/
def IsGibbsMeasure (γ : LocalSpecification Site Spin)
    (μ : Measure (Configuration Site Spin)) : Prop :=
  ∀ V : FiniteVolume Site, μ.bind (γ V) = μ

lemma isGibbsMeasure_iff_forall_bind_eq {γ : LocalSpecification Site Spin}
    {μ : Measure (Configuration Site Spin)} :
    IsGibbsMeasure γ μ ↔ ∀ V : FiniteVolume Site, μ.bind (γ V) = μ := by
  rfl

end Rebuild.StatMech.Specification
