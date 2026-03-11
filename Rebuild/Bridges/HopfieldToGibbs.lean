import Rebuild.Models.Hopfield.Basic
import Rebuild.Core.Gibbs
import Rebuild.StatMech.FiniteGibbs.Core
import Rebuild.Learning.Boltzmann.Core

set_option autoImplicit false

namespace Rebuild.Bridges

open Rebuild.Core
open Rebuild.Models.Hopfield
open Rebuild.StatMech.FiniteGibbs
open Rebuild.Learning.Boltzmann

section Finite

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

noncomputable def hopfieldFiniteGibbsModel (p : Parameters Site) : FiniteGibbsModel (State Site) :=
  finiteGibbsModel p

@[simp] theorem hopfieldFiniteGibbsModel_energy (p : Parameters Site) :
    (hopfieldFiniteGibbsModel p).energy = energy p := rfl

noncomputable def hopfieldGibbsProbability (β : ℝ) (p : Parameters Site) (τ : State Site) : ℝ :=
  gibbsProbability β (hopfieldFiniteGibbsModel p) τ

noncomputable def hopfieldGibbsMeasure (β : ℝ) (p : Parameters Site)
    [MeasurableSpace (State Site)] : MeasureTheory.Measure (State Site) :=
  gibbsMeasure β (hopfieldFiniteGibbsModel p)

noncomputable def hopfieldModelExpectation (β : ℝ) (p : Parameters Site)
    [MeasurableSpace (State Site)] [MeasurableSingletonClass (State Site)]
    (f : State Site → ℝ) : ℝ :=
  modelExpectation β (hopfieldFiniteGibbsModel p) f

noncomputable def hopfieldModelPhasePair [MeasurableSpace (State Site)] [MeasurableSingletonClass (State Site)]
    (data : MeasureTheory.Measure (State Site)) (β : ℝ) (p : Parameters Site) :
    PhasePair (State Site) :=
  modelPhasePair data β (hopfieldFiniteGibbsModel p)

@[simp] theorem hopfieldGibbsProbability_eq (β : ℝ) (p : Parameters Site) (τ : State Site) :
    hopfieldGibbsProbability β p τ = gibbsProbability β (finiteGibbsModel p) τ := rfl

end Finite

end Rebuild.Bridges
