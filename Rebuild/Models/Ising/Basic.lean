import Rebuild.Models.BinarySpin.Pairwise

set_option autoImplicit false

namespace Rebuild.Models.Ising

abbrev Spin := Rebuild.Models.BinarySpin.Pairwise.Spin
abbrev State (Site : Type*) := Rebuild.Models.BinarySpin.Pairwise.SignedState Site
abbrev Parameters (Site : Type*) [Fintype Site] [DecidableEq Site] :=
  Rebuild.Models.BinarySpin.Pairwise.Parameters Site

noncomputable abbrev spinValue : Spin → ℝ :=
  Rebuild.Models.BinarySpin.Pairwise.signedSpinValue

noncomputable abbrev localField {Site : Type*} [Fintype Site] [DecidableEq Site]
    (p : Parameters Site) (τ : State Site) (i : Site) : ℝ :=
  Rebuild.Models.BinarySpin.Pairwise.signedLocalField p τ i

noncomputable abbrev energyFn {Site : Type*} [Fintype Site] [DecidableEq Site]
    (p : Parameters Site) (τ : State Site) : ℝ :=
  Rebuild.Models.BinarySpin.Pairwise.signedEnergyFn p τ

noncomputable abbrev energy {Site : Type*} [Fintype Site] [DecidableEq Site]
    (p : Parameters Site) : Rebuild.Core.Energy (State Site) :=
  Rebuild.Models.BinarySpin.Pairwise.signedEnergy p

noncomputable abbrev updateAt {Site : Type*} [Fintype Site] [DecidableEq Site]
    (p : Parameters Site) (i : Site) (τ : State Site) : State Site :=
  Rebuild.Models.BinarySpin.Pairwise.signedUpdateAt p i τ

noncomputable abbrev deterministicDynamics {Site : Type*} [Fintype Site] [DecidableEq Site]
    (p : Parameters Site) : Rebuild.Core.LocalDeterministicUpdate Site Spin :=
  Rebuild.Models.BinarySpin.Pairwise.signedDeterministicDynamics p

noncomputable abbrev finiteGibbsModel {Site : Type*} [Fintype Site] [DecidableEq Site]
    (p : Parameters Site) : Rebuild.Core.FiniteGibbsModel (State Site) :=
  Rebuild.Models.BinarySpin.Pairwise.signedFiniteGibbsModel p

end Rebuild.Models.Ising
