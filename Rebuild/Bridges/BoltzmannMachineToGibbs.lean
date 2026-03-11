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
  finiteGibbsModel encoding p

@[simp] theorem boltzmannMachineFiniteGibbsModel_energy (encoding : TwoStateEncoding σ)
    (p : Parameters Site) :
    (boltzmannMachineFiniteGibbsModel encoding p).energy = energy encoding p := rfl

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

end BoolSigned

end Rebuild.Bridges
