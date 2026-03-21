import Rebuild.StatMech.Specification.GibbsMeasure
import Rebuild.StatMech.Specification.Proper
import Rebuild.StatMech.Specification.Markov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.Order.Filter.CountableSeparatingOn
import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# Basic structure of the Gibbs state space `G(γ)` (Georgii, Ch. 7 — beginnings)

This file sets up *definitions* used in the structural analysis of Gibbs measures:
- `GP γ`: the set of Gibbs **probability measures** for a specification `γ`;
- `tailSigmaAlgebra`: the tail σ-algebra `𝓣` on the configuration space.
-/

open Set MeasureTheory

open scoped ENNReal

namespace Rebuild.StatMech.Specification

open Rebuild.Core

variable {Site Spin : Type*} [DecidableEq Site] [MeasurableSpace Spin]

/-! ### The Gibbs state space as a subset of `ProbabilityMeasure` -/

/-- The set of Gibbs **probability** measures for a specification `γ`. -/
def GP (γ : LocalSpecification Site Spin) : Set (ProbabilityMeasure (Configuration Site Spin)) :=
  {μ | IsGibbsMeasure γ (μ : Measure (Configuration Site Spin))}

/-! ### Convexity (binary convex combinations) -/

namespace ProbabilityMeasure

open unitInterval

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Binary convex combination of probability measures, with weight `p` on `μ` and `1-p` on `ν`. -/
noncomputable def convexCombo (p : I) (μ ν : ProbabilityMeasure Ω) : ProbabilityMeasure Ω :=
  ⟨toNNReal p • (μ : Measure Ω) + toNNReal (σ p) • (ν : Measure Ω), by infer_instance⟩

@[simp] lemma coe_convexCombo (p : I) (μ ν : ProbabilityMeasure Ω) :
    ((convexCombo (p := p) μ ν : ProbabilityMeasure Ω) : Measure Ω) =
      toNNReal p • (μ : Measure Ω) + toNNReal (σ p) • (ν : Measure Ω) := rfl

end ProbabilityMeasure

namespace Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma bind_add (μ ν : Measure α) (f : α → Measure β) (hf : Measurable f) :
    (μ + ν).bind f = μ.bind f + ν.bind f := by
  ext s hs
  simp [Measure.bind_apply hs hf.aemeasurable, lintegral_add_measure]

lemma bind_smul (c : NNReal) (μ : Measure α) (f : α → Measure β) (hf : Measurable f) :
    (c • μ).bind f = c • (μ.bind f) := by
  ext s hs
  simp [Measure.bind_apply hs hf.aemeasurable, lintegral_smul_measure]

end Measure

lemma convexCombo_mem_GP (γ : LocalSpecification Site Spin)
    (μ ν : ProbabilityMeasure (Configuration Site Spin)) (hμ : μ ∈ GP γ) (hν : ν ∈ GP γ) (p : unitInterval) :
    ProbabilityMeasure.convexCombo (p := p) μ ν ∈ GP γ := by
  have hμ' : ∀ V : FiniteVolume Site, (μ : Measure (Configuration Site Spin)).bind (γ V) = (μ : Measure (Configuration Site Spin)) := by
    have : IsGibbsMeasure γ (μ : Measure (Configuration Site Spin)) := hμ
    simpa [isGibbsMeasure_iff_forall_bind_eq] using this
  have hν' : ∀ V : FiniteVolume Site, (ν : Measure (Configuration Site Spin)).bind (γ V) = (ν : Measure (Configuration Site Spin)) := by
    have : IsGibbsMeasure γ (ν : Measure (Configuration Site Spin)) := hν
    simpa [isGibbsMeasure_iff_forall_bind_eq] using this
  have hfix : ∀ V : FiniteVolume Site,
        ((ProbabilityMeasure.convexCombo (Ω := (Configuration Site Spin)) (p := p) μ ν :
            ProbabilityMeasure (Configuration Site Spin)) : Measure (Configuration Site Spin)).bind (γ V)
        = ((ProbabilityMeasure.convexCombo (Ω := (Configuration Site Spin)) (p := p) μ ν :
            ProbabilityMeasure (Configuration Site Spin)) : Measure (Configuration Site Spin)) := by
    intro V
    have hmeas : Measurable (γ V) := ProbabilityTheory.Kernel.measurable (γ V)
    simp [ProbabilityMeasure.coe_convexCombo]
    rw [Measure.bind_add (μ := unitInterval.toNNReal p • (μ : Measure (Configuration Site Spin)))
      (ν := unitInterval.toNNReal (unitInterval.symm p) • (ν : Measure (Configuration Site Spin)))
      (f := γ V) hmeas]
    rw [Measure.bind_smul (c := unitInterval.toNNReal p) (μ := (μ : Measure (Configuration Site Spin))) (f := γ V) hmeas]
    rw [Measure.bind_smul (c := unitInterval.toNNReal (unitInterval.symm p)) (μ := (ν : Measure (Configuration Site Spin))) (f := γ V) hmeas]
    simp [hμ' V, hν' V]
  have : IsGibbsMeasure γ
      ((ProbabilityMeasure.convexCombo (Ω := (Configuration Site Spin)) (p := p) μ ν :
          ProbabilityMeasure (Configuration Site Spin)) : Measure (Configuration Site Spin)) := by
    haveI : IsFiniteMeasure ((ProbabilityMeasure.convexCombo (Ω := (Configuration Site Spin)) (p := p) μ ν : ProbabilityMeasure (Configuration Site Spin)) : Measure (Configuration Site Spin)) := by infer_instance
    simpa [isGibbsMeasure_iff_forall_bind_eq] using hfix
  exact this

/-! ### Tail σ-algebra -/

variable (Site Spin)
/-- The **tail σ-algebra** `𝓣`: information at infinity, defined as the infimum of the
σ-algebras `cylinderEvents (Vᶜ)` over finite volumes `V`. -/
def tailSigmaAlgebra : MeasurableSpace (Configuration Site Spin) :=
  ⨅ (V : FiniteVolume Site), MeasureTheory.cylinderEvents (X := fun _ : Site ↦ Spin) ((V.carrier : Set Site)ᶜ)
variable {Site Spin}

notation "𝓣" => tailSigmaAlgebra

/-- Tail-triviality: every tail event has probability `0` or `1`. -/
def IsTailTrivial (μ : ProbabilityMeasure (Configuration Site Spin)) : Prop :=
  ∀ A, MeasurableSet[@tailSigmaAlgebra Site Spin _ _] A →
    (μ : Measure (Configuration Site Spin)) A = 0 ∨ (μ : Measure (Configuration Site Spin)) A = 1

namespace IsTailTrivial

open Filter

variable {μ : ProbabilityMeasure (Configuration Site Spin)}

theorem ae_eq_const_of_measurable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablySeparated X]
    [Nonempty X] (hμ : IsTailTrivial (Site := Site) (Spin := Spin) μ) {f : Configuration Site Spin → X}
    (hf : Measurable[@tailSigmaAlgebra Site Spin _ _] f) :
    ∃ c : X, f =ᵐ[(μ : Measure (Configuration Site Spin))] fun _ => c := by
  classical
  letI : EmptyCollection (FiniteVolume Site) := ⟨⟨∅⟩⟩
  have hDich : ∀ U : Set X, MeasurableSet U →
        (∀ᵐ ω ∂(μ : Measure (Configuration Site Spin)), f ω ∈ U) ∨
          (∀ᵐ ω ∂(μ : Measure (Configuration Site Spin)), f ω ∉ U) := by
    intro U hU
    have hpre_tail : MeasurableSet[@tailSigmaAlgebra Site Spin _ _] (f ⁻¹' U) := hf hU
    have hpre_pi : MeasurableSet (f ⁻¹' U) := by
      have hle_tail_pi : (@tailSigmaAlgebra Site Spin _ _ : MeasurableSpace (Configuration Site Spin)) ≤ MeasurableSpace.pi := by
        refine le_trans (iInf_le (fun V : FiniteVolume Site => MeasureTheory.cylinderEvents (X := fun _ : Site ↦ Spin) ((V.carrier : Set Site)ᶜ)) (∅ : FiniteVolume Site)) ?_
        exact MeasureTheory.cylinderEvents_le_pi
      exact hle_tail_pi _ hpre_tail
    have hprob : (μ : Measure (Configuration Site Spin)) (f ⁻¹' U) = 0 ∨ (μ : Measure (Configuration Site Spin)) (f ⁻¹' U) = 1 := hμ (f ⁻¹' U) hpre_tail
    rcases hprob with h0 | h1
    · right
      have : (∀ᵐ ω ∂(μ : Measure (Configuration Site Spin)), ¬ f ω ∈ U) := by
        have : (μ : Measure (Configuration Site Spin)) {ω | ¬ (¬ f ω ∈ U)} = 0 := by simpa using h0
        simpa [ae_iff] using this
      exact this
    · left
      have hcompl0 : (μ : Measure (Configuration Site Spin)) (f ⁻¹' U)ᶜ = 0 :=
        (prob_compl_eq_zero_iff (μ := (μ : Measure (Configuration Site Spin))) hpre_pi).2 h1
      have : (∀ᵐ ω ∂(μ : Measure (Configuration Site Spin)), f ω ∈ U) := by
        have : (μ : Measure (Configuration Site Spin)) {ω | ¬ f ω ∈ U} = 0 := by simpa [Set.preimage, Set.compl_def] using hcompl0
        simpa [ae_iff] using this
      exact this
  have : ∃ c : X, f =ᶠ[ae (μ : Measure (Configuration Site Spin))] fun _ => c :=
    Filter.exists_eventuallyEq_const_of_forall_separating (l := ae (μ : Measure (Configuration Site Spin)))
      (f := f) (p := MeasurableSet) (β := X) (fun U hU => by simpa using (hDich U hU))
  rcases this with ⟨c, hc⟩
  exact ⟨c, hc⟩

theorem ae_eq_const_of_ae_eq_measurable {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablySeparated X] [Nonempty X]
    (hμ : IsTailTrivial (Site := Site) (Spin := Spin) μ) {f : Configuration Site Spin → X}
    (hf : ∃ g : (Configuration Site Spin) → X, Measurable[@tailSigmaAlgebra Site Spin _ _] g ∧
      f =ᵐ[(μ : Measure (Configuration Site Spin))] g) :
    ∃ c : X, f =ᵐ[(μ : Measure (Configuration Site Spin))] fun _ => c := by
  classical
  rcases hf with ⟨g, hg, hfg⟩
  rcases ae_eq_const_of_measurable (Site := Site) (Spin := Spin) (μ := μ) hμ (f := g) hg with ⟨c, hgc⟩
  refine ⟨c, hfg.trans ?_⟩
  simpa using hgc

end IsTailTrivial

end Rebuild.StatMech.Specification
