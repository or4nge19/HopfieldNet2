import Rebuild.Core.TwoState
import Rebuild.Models.BinarySpin.Pairwise

/-!
# Rebuild Boltzmann Machine Model (Topology & Energy)

Canonical home for Boltzmann-machine model data.
Critically, this file defines ONLY the structural topology (States, Energies, Update Rules).
It contains ZERO measure theory, Markov kernels, or probability definitions.
Stochastic dynamics and Gibbs limits are instantiated purely through explicit Functors in `Rebuild.Bridges`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Rebuild.Models.BoltzmannMachine

open Rebuild.Core

/-- Canonical Boltzmann-machine states are finite two-state configurations. -/
abbrev State (σ : Type*) (Site : Type*) := Rebuild.Models.BinarySpin.Pairwise.State σ Site
/-- Canonical Boltzmann-machine parameters are pairwise couplings plus fields. -/
abbrev Parameters (Site : Type*) [Fintype Site] [DecidableEq Site] :=
    Rebuild.Models.BinarySpin.Pairwise.Parameters Site

noncomputable abbrev spinValue {σ : Type*} [TwoState σ] (encoding : TwoStateEncoding σ) : σ → ℝ :=
    Rebuild.Models.BinarySpin.Pairwise.spinValue encoding

noncomputable abbrev localField {σ Site : Type*} [TwoState σ] [Fintype Site] [DecidableEq Site]
    (encoding : TwoStateEncoding σ) (p : Parameters Site) (τ : State σ Site) (i : Site) : ℝ :=
    Rebuild.Models.BinarySpin.Pairwise.localField encoding p τ i

noncomputable abbrev energyFn {σ Site : Type*} [TwoState σ] [Fintype Site] [DecidableEq Site]
    (encoding : TwoStateEncoding σ) (p : Parameters Site) (τ : State σ Site) : ℝ :=
    Rebuild.Models.BinarySpin.Pairwise.energyFn encoding p τ

noncomputable abbrev energy {σ Site : Type*} [TwoState σ] [Fintype Site] [DecidableEq Site]
    (encoding : TwoStateEncoding σ) (p : Parameters Site) : Rebuild.Core.Energy (State σ Site) :=
    Rebuild.Models.BinarySpin.Pairwise.energy encoding p

noncomputable abbrev updateAt {σ Site : Type*} [TwoState σ] [Fintype Site] [DecidableEq Site]
    (encoding : TwoStateEncoding σ) (p : Parameters Site) (i : Site) (τ : State σ Site) : State σ Site :=
    Rebuild.Models.BinarySpin.Pairwise.updateAt encoding p i τ

noncomputable abbrev zeroTempUpdateAt {σ Site : Type*} [TwoState σ] [Fintype Site] [DecidableEq Site]
    (encoding : TwoStateEncoding σ) (p : Parameters Site) (i : Site) (τ : State σ Site) : State σ Site :=
    updateAt encoding p i τ

section BoolSigned

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

abbrev Spin := Bool
abbrev SignedState (Site : Type*) := State Bool Site

noncomputable abbrev signedSpinValue : Spin → ℝ :=
    Rebuild.Models.BinarySpin.Pairwise.signedSpinValue

noncomputable abbrev signedLocalField (p : Parameters Site) (τ : SignedState Site) (i : Site) : ℝ :=
    localField TwoStateEncoding.boolSigned p τ i

noncomputable abbrev signedEnergyFn (p : Parameters Site) (τ : SignedState Site) : ℝ :=
    energyFn TwoStateEncoding.boolSigned p τ

noncomputable abbrev signedEnergy (p : Parameters Site) : Rebuild.Core.Energy (SignedState Site) :=
    energy TwoStateEncoding.boolSigned p

noncomputable abbrev signedUpdateAt (p : Parameters Site) (i : Site) (τ : SignedState Site) : SignedState Site :=
    updateAt TwoStateEncoding.boolSigned p i τ

noncomputable abbrev signedZeroTempUpdateAt (p : Parameters Site) (i : Site) (τ : SignedState Site) : SignedState Site :=
    zeroTempUpdateAt TwoStateEncoding.boolSigned p i τ

noncomputable def signedSiteConditionalWeight (β : ℝ) (p : Parameters Site)
        (i : Site) (τ : SignedState Site) (s : Spin) : ℝ :=
    Real.exp (-β * signedEnergyFn p (Rebuild.Models.BinarySpin.Pairwise.overwrite τ i s))

noncomputable def signedSitePartition (β : ℝ) (p : Parameters Site)
        (i : Site) (τ : SignedState Site) : ℝ :=
    signedSiteConditionalWeight β p i τ true + signedSiteConditionalWeight β p i τ false

lemma signedSitePartition_pos (β : ℝ) (p : Parameters Site)
        (i : Site) (τ : SignedState Site) :
        0 < signedSitePartition β p i τ := by
    unfold signedSitePartition signedSiteConditionalWeight
    exact add_pos (Real.exp_pos _) (Real.exp_pos _)

lemma signedSitePartition_ne_zero (β : ℝ) (p : Parameters Site)
        (i : Site) (τ : SignedState Site) :
        signedSitePartition β p i τ ≠ 0 :=
    (signedSitePartition_pos β p i τ).ne'

/--
Single-site heat-bath weight ratio (Not a defined probability measure)
-/
noncomputable def signedSiteConditionalProbability (β : ℝ) (p : Parameters Site)
        (i : Site) (τ : SignedState Site) (s : Spin) : ℝ :=
    signedSiteConditionalWeight β p i τ s / signedSitePartition β p i τ

lemma signedSiteConditionalProbability_nonneg (β : ℝ) (p : Parameters Site)
        (i : Site) (τ : SignedState Site) (s : Spin) :
        0 ≤ signedSiteConditionalProbability β p i τ s := by
    unfold signedSiteConditionalProbability signedSiteConditionalWeight
    exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (signedSitePartition_pos β p i τ))

lemma signedSiteConditionalProbability_sum (β : ℝ) (p : Parameters Site)
        (i : Site) (τ : SignedState Site) :
        signedSiteConditionalProbability β p i τ true + signedSiteConditionalProbability β p i τ false = 1 := by
    set a : ℝ := signedSiteConditionalWeight β p i τ true
    set b : ℝ := signedSiteConditionalWeight β p i τ false
    have h : a + b ≠ 0 := by
      simpa [a, b, signedSitePartition] using signedSitePartition_ne_zero β p i τ
    unfold signedSiteConditionalProbability signedSitePartition
    change a / (a + b) + b / (a + b) = 1
    rw [← add_div]
    exact div_self h

end BoolSigned

end Rebuild.Models.BoltzmannMachine
