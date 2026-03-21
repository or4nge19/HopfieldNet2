import Rebuild.Models.BoltzmannMachine.Basic
import Rebuild.Bridges.TwoStateToBoltzmannLearning
import Rebuild.StatMech.FiniteGibbs.Core
import Rebuild.Learning.Boltzmann.Core
import Rebuild.Learning.Boltzmann.Gradient

/-!
# Rebuild Boltzmann Machine to Gibbs/Learning Bridge

Expose canonical Boltzmann-machine Gibbs semantics and learning interfaces through the
shared finite pairwise/two-state corridor.
-/

set_option autoImplicit false

namespace Rebuild.Bridges

open Rebuild.Core
open Rebuild.Models.BoltzmannMachine
open Rebuild.Learning.Boltzmann
open Rebuild.StatMech.FiniteGibbs

abbrev BoltzmannParameterIndex (Site : Type*) := ParameterIndex Site

section GeneralTwoState

variable {σ Site : Type*} [TwoState σ] [Fintype σ] [Fintype Site] [DecidableEq Site] [MeasurableSpace (State σ Site)] [MeasurableSingletonClass (State σ Site)]

noncomputable def boltzmannMachineFiniteGibbsModel (encoding : TwoStateEncoding σ)
    (p : Parameters Site) : FiniteGibbsModel (State σ Site) :=
  Rebuild.Models.BinarySpin.Pairwise.finiteGibbsModel encoding p

@[simp] theorem boltzmannMachineFiniteGibbsModel_energy (encoding : TwoStateEncoding σ)
    (p : Parameters Site) :
    (boltzmannMachineFiniteGibbsModel encoding p).energy = Rebuild.Models.BinarySpin.Pairwise.energy encoding p := rfl

noncomputable def boltzmannMachineGibbsProbability (encoding : TwoStateEncoding σ)
    (β : ℝ) (p : Parameters Site) (τ : State σ Site) : ℝ :=
  gibbsProbability β (boltzmannMachineFiniteGibbsModel encoding p) τ

noncomputable def boltzmannMachineGibbsMeasure (encoding : TwoStateEncoding σ)
    (β : ℝ) (p : Parameters Site)  :
    MeasureTheory.Measure (State σ Site) :=
  gibbsMeasure β (boltzmannMachineFiniteGibbsModel encoding p)

noncomputable def boltzmannMachineModelExpectation (encoding : TwoStateEncoding σ)
    (β : ℝ) (p : Parameters Site)  (f : State σ Site → ℝ) : ℝ :=
  modelExpectation β (boltzmannMachineFiniteGibbsModel encoding p) f

noncomputable def boltzmannMachineModelPhasePair (encoding : TwoStateEncoding σ)
    (data : MeasureTheory.Measure (State σ Site)) (β : ℝ) (p : Parameters Site)
     :
    PhasePair (State σ Site) :=
  modelPhasePair data β (boltzmannMachineFiniteGibbsModel encoding p)

noncomputable def boltzmannMachineCanonicalLearningRule (encoding : TwoStateEncoding σ) :
    LearningRule (BoltzmannParameterIndex Site) (BoltzmannParameterIndex Site → ℝ)
      (State σ Site) :=
  canonicalLearningRule (parameterStatisticFamily (Site := Site) encoding)

end GeneralTwoState

section BoolSigned

variable {Site : Type*} [Fintype Site] [DecidableEq Site]
    [MeasurableSpace (SignedState Site)] [MeasurableSingletonClass (SignedState Site)]

noncomputable abbrev signedBoltzmannMachineGibbsProbability (β : ℝ) (p : Parameters Site)
    (τ : SignedState Site) : ℝ :=
  boltzmannMachineGibbsProbability TwoStateEncoding.boolSigned β p τ

noncomputable abbrev signedBoltzmannMachineGibbsMeasure (β : ℝ) (p : Parameters Site) :
    MeasureTheory.Measure (SignedState Site) :=
  boltzmannMachineGibbsMeasure TwoStateEncoding.boolSigned β p

noncomputable abbrev signedBoltzmannMachineModelPhasePair
    (data : MeasureTheory.Measure (SignedState Site)) (β : ℝ) (p : Parameters Site) :
    PhasePair (SignedState Site) :=
  boltzmannMachineModelPhasePair TwoStateEncoding.boolSigned data β p

noncomputable abbrev signedBoltzmannMachineCanonicalLearningRule :
    LearningRule (BoltzmannParameterIndex Site) (BoltzmannParameterIndex Site → ℝ)
      (SignedState Site) :=
  boltzmannMachineCanonicalLearningRule TwoStateEncoding.boolSigned


noncomputable def signedSiteGibbsKernel (β : ℝ) (p : Parameters Site) (i : Site) :
    ProbabilityTheory.Kernel (SignedState Site) (SignedState Site) where
  toFun τ :=
    (ENNReal.ofReal (signedSiteConditionalProbability β p i τ true)) • MeasureTheory.Measure.dirac (Rebuild.Models.BinarySpin.Pairwise.overwrite τ i true) +
    (ENNReal.ofReal (signedSiteConditionalProbability β p i τ false)) • MeasureTheory.Measure.dirac (Rebuild.Models.BinarySpin.Pairwise.overwrite τ i false)
  measurable' := by
    haveI H : DiscreteMeasurableSpace (SignedState Site) :=
      ⟨by
        intro s
        have : s = ⋃ (x ∈ s), {x} := by ext x; simp
        rw [this]
        exact MeasurableSet.biUnion (Set.toFinite s).countable (fun _ _ => MeasurableSet.singleton _)
        ⟩
    measurability

lemma signedSiteGibbsKernel_apply_singleton
    (β : ℝ) (p : Parameters Site) (u : Site) (s s' : SignedState Site) :
    (signedSiteGibbsKernel β p u) s {s'} =
      if s' = Rebuild.Models.BinarySpin.Pairwise.overwrite s u true then ENNReal.ofReal (signedSiteConditionalProbability β p u s true)
      else if s' = Rebuild.Models.BinarySpin.Pairwise.overwrite s u false then ENNReal.ofReal (signedSiteConditionalProbability β p u s false)
      else 0 := by
  change ( (ENNReal.ofReal (signedSiteConditionalProbability β p u s true)) • MeasureTheory.Measure.dirac (Rebuild.Models.BinarySpin.Pairwise.overwrite s u true) + (ENNReal.ofReal (signedSiteConditionalProbability β p u s false)) • MeasureTheory.Measure.dirac (Rebuild.Models.BinarySpin.Pairwise.overwrite s u false) ) {s'} = _
  simp only [MeasureTheory.Measure.coe_add, Pi.add_apply, MeasureTheory.Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [MeasureTheory.Measure.dirac_apply' _ (MeasurableSet.singleton s')]
  rw [MeasureTheory.Measure.dirac_apply' _ (MeasurableSet.singleton s')]
  simp only [Set.mem_singleton_iff, Set.indicator_apply, Pi.one_apply]
  by_cases h1 : s' = Rebuild.Models.BinarySpin.Pairwise.overwrite s u true
  · have h1_rev : Rebuild.Models.BinarySpin.Pairwise.overwrite s u true = s' := h1.symm
    have h2 : Rebuild.Models.BinarySpin.Pairwise.overwrite s u false ≠ s' := by
      intro h
      have h3 : true = false := by
        have h_true := congrArg (fun x => x u) h1_rev
        have h_false := congrArg (fun x => x u) h
        simp [Rebuild.Models.BinarySpin.Pairwise.overwrite] at h_true h_false
        rw [← h_false, ← h_true]
      cases h3
    have h2_rev : s' ≠ Rebuild.Models.BinarySpin.Pairwise.overwrite s u false := fun h => h2 h.symm
    rw [if_pos h1, if_pos h1_rev, if_neg h2]
    simp only [mul_one, mul_zero, add_zero]
  · have h1_rev : Rebuild.Models.BinarySpin.Pairwise.overwrite s u true ≠ s' := fun h => h1 h.symm
    by_cases h2 : s' = Rebuild.Models.BinarySpin.Pairwise.overwrite s u false
    · have h2_rev : Rebuild.Models.BinarySpin.Pairwise.overwrite s u false = s' := h2.symm
      rw [if_neg h1, if_neg h1_rev, if_pos h2, if_pos h2_rev]
      simp only [mul_one, mul_zero, zero_add]
    · have h2_rev : Rebuild.Models.BinarySpin.Pairwise.overwrite s u false ≠ s' := fun h => h2 h.symm
      rw [if_neg h1, if_neg h1_rev, if_neg h2, if_neg h2_rev]
      simp only [mul_zero, add_zero]

end BoolSigned

end Rebuild.Bridges
