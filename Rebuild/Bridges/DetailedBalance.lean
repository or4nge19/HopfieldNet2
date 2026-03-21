import Rebuild.Models.BoltzmannMachine.Basic
import Rebuild.Bridges.BoltzmannMachineToGibbs
import Mathlib.Probability.Kernel.Invariance
import NeuralNetwork.Mathematics.Probability.DetailedBalanceGen

open Rebuild.Models.BoltzmannMachine Rebuild.Core MeasureTheory ProbabilityTheory
open Rebuild.StatMech.FiniteGibbs Rebuild.Bridges
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

namespace Rebuild.Bridges

variable {Site : Type*} [Fintype Site] [DecidableEq Site]
    [MeasurableSpace (SignedState Site)] [MeasurableSingletonClass (SignedState Site)]

/-- States differ away from `u`. -/
def DiffAway (u : Site) (s s' : SignedState Site) : Prop :=
  ∃ v, v ≠ u ∧ s v ≠ s' v

lemma DiffAway.symm {u : Site} {s s' : SignedState Site} :
    DiffAway u s s' → DiffAway u s' s := by
  rintro ⟨v, hv, hvs⟩
  exact ⟨v, hv, hvs.symm⟩

lemma overwrite_eq_of_agree_offsite {u : Site} {s s' : SignedState Site}
    (h_off : ∀ v, v ≠ u → s v = s' v) :
    Models.BinarySpin.Pairwise.overwrite s u (s' u) = s' := by
  funext v
  by_cases hv : v = u
  · subst hv
    simp [Models.BinarySpin.Pairwise.overwrite]
  · simp [Models.BinarySpin.Pairwise.overwrite, hv, h_off v hv]

lemma overwrite_eq_overwrite_of_agree_offsite {u : Site} {s s' : SignedState Site}
    (h_off : ∀ v, v ≠ u → s v = s' v) (b : Spin) :
    Models.BinarySpin.Pairwise.overwrite s u b = Models.BinarySpin.Pairwise.overwrite s' u b := by
  funext v
  by_cases hv : v = u
  · subst hv
    simp [Models.BinarySpin.Pairwise.overwrite]
  · simp [Models.BinarySpin.Pairwise.overwrite, hv, h_off v hv]

lemma signedSitePartition_eq_of_agree_offsite
    (β : ℝ) (p : Parameters Site) {u : Site} {s s' : SignedState Site}
    (h_off : ∀ v, v ≠ u → s v = s' v) :
    signedSitePartition β p u s = signedSitePartition β p u s' := by
  have htrue : Models.BinarySpin.Pairwise.overwrite s u true = Models.BinarySpin.Pairwise.overwrite s' u true :=
    overwrite_eq_overwrite_of_agree_offsite h_off true
  have hfalse : Models.BinarySpin.Pairwise.overwrite s u false = Models.BinarySpin.Pairwise.overwrite s' u false :=
    overwrite_eq_overwrite_of_agree_offsite h_off false
  unfold signedSitePartition signedSiteConditionalWeight
  simp [htrue, hfalse]

lemma signedBoltzmannMachineGibbsMeasure_singleton
    (β : ℝ) (p : Parameters Site) (s : SignedState Site) :
    (signedBoltzmannMachineGibbsMeasure β p) {s} =
      ENNReal.ofReal (signedBoltzmannMachineGibbsProbability β p s) := by
  change Rebuild.StatMech.FiniteGibbs.gibbsMeasure β (boltzmannMachineFiniteGibbsModel TwoStateEncoding.boolSigned p) {s} =
    ENNReal.ofReal (Rebuild.StatMech.FiniteGibbs.gibbsProbability β (boltzmannMachineFiniteGibbsModel TwoStateEncoding.boolSigned p) s)
  exact Rebuild.StatMech.FiniteGibbs.gibbsMeasure_apply_singleton β (boltzmannMachineFiniteGibbsModel TwoStateEncoding.boolSigned p) s

lemma signedSiteGibbsKernel_zero_of_diffAway
    (β : ℝ) (p : Parameters Site) {u : Site} {s s' : SignedState Site}
    (h : DiffAway u s s') :
    (signedSiteGibbsKernel β p u) s {s'} = 0 := by
  rcases h with ⟨v, hv, hvs⟩
  have hne_true : s' ≠ Models.BinarySpin.Pairwise.overwrite s u true := by
    intro hs
    have hcoord := congrArg (fun τ : SignedState Site => τ v) hs
    simp [Models.BinarySpin.Pairwise.overwrite, hv] at hcoord
    exact hvs hcoord.symm
  have hne_false : s' ≠ Models.BinarySpin.Pairwise.overwrite s u false := by
    intro hs
    have hcoord := congrArg (fun τ : SignedState Site => τ v) hs
    simp [Models.BinarySpin.Pairwise.overwrite, hv] at hcoord
    exact hvs hcoord.symm
  rw [signedSiteGibbsKernel_apply_singleton]
  simp [hne_true, hne_false]

lemma signedSiteGibbsKernel_singleton_eval_of_agree_offsite
    (β : ℝ) (p : Parameters Site) {u : Site} {s s' : SignedState Site}
    (h_off : ∀ v, v ≠ u → s v = s' v) :
    (signedSiteGibbsKernel β p u) s {s'} =
      ENNReal.ofReal (signedSiteConditionalProbability β p u s (s' u)) := by
  have hs' : Models.BinarySpin.Pairwise.overwrite s u (s' u) = s' := overwrite_eq_of_agree_offsite h_off
  rw [signedSiteGibbsKernel_apply_singleton]
  cases hsu : s' u
  · have hfalse : s' = Models.BinarySpin.Pairwise.overwrite s u false := by
      simpa [hsu] using hs'.symm
    have hneq : Models.BinarySpin.Pairwise.overwrite s u false ≠ Models.BinarySpin.Pairwise.overwrite s u true := by
      intro h
      have hcoord := congrArg (fun τ : SignedState Site => τ u) h
      simp [Models.BinarySpin.Pairwise.overwrite] at hcoord
    simp [hfalse, hneq]
  · have htrue : s' = Models.BinarySpin.Pairwise.overwrite s u true := by
      simpa [hsu] using hs'.symm
    have hneq : Models.BinarySpin.Pairwise.overwrite s u true ≠ Models.BinarySpin.Pairwise.overwrite s u false := by
      intro h
      have hcoord := congrArg (fun τ : SignedState Site => τ u) h
      simp [Models.BinarySpin.Pairwise.overwrite] at hcoord
    simp [htrue, hneq]

lemma detailed_balance_single_site
    (β : ℝ) (p : Parameters Site) (u : Site) (s s' : SignedState Site)
    (h_off : ∀ v, v ≠ u → s v = s' v) :
    signedBoltzmannMachineGibbsProbability β p s * signedSiteConditionalProbability β p u s (s' u) =
      signedBoltzmannMachineGibbsProbability β p s' * signedSiteConditionalProbability β p u s' (s u) := by
  have hs' : Models.BinarySpin.Pairwise.overwrite s u (s' u) = s' := overwrite_eq_of_agree_offsite h_off
  have hs : Models.BinarySpin.Pairwise.overwrite s' u (s u) = s :=
    overwrite_eq_of_agree_offsite (fun v hv => (h_off v hv).symm)
  have hpart : signedSitePartition β p u s = signedSitePartition β p u s' :=
    signedSitePartition_eq_of_agree_offsite β p h_off
  simp only [Rebuild.Bridges.signedBoltzmannMachineGibbsProbability,
    Rebuild.Bridges.boltzmannMachineGibbsProbability,
    Rebuild.StatMech.FiniteGibbs.gibbsProbability,
    signedSiteConditionalProbability, signedSiteConditionalWeight]
  rw [hs', hs, hpart]
  simp [energy, signedEnergyFn, energyFn, Rebuild.Core.boltzmannWeight]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  simp [Models.BinarySpin.Pairwise.energy, mul_assoc, mul_left_comm, mul_comm]

lemma signedSiteGibbsKernel_pointwise_detailed_balance
    (β : ℝ) (p : Parameters Site) (u : Site) (s s' : SignedState Site) :
    (signedBoltzmannMachineGibbsMeasure β p) {s} * (signedSiteGibbsKernel β p u) s {s'} =
      (signedBoltzmannMachineGibbsMeasure β p) {s'} * (signedSiteGibbsKernel β p u) s' {s} := by
  by_cases h_diff : DiffAway u s s'
  · have hκss' : (signedSiteGibbsKernel β p u) s {s'} = 0 :=
      signedSiteGibbsKernel_zero_of_diffAway β p h_diff
    have hκs's : (signedSiteGibbsKernel β p u) s' {s} = 0 :=
      signedSiteGibbsKernel_zero_of_diffAway β p h_diff.symm
    rw [hκss', hκs's]
    rw [mul_zero, mul_zero]
  · have h_off : ∀ v, v ≠ u → s v = s' v := by
      intro v hv
      by_contra hne
      exact h_diff ⟨v, hv, hne⟩
    have h_off' : ∀ v, v ≠ u → s' v = s v := by
      intro v hv
      exact (h_off v hv).symm
    have hπs := signedBoltzmannMachineGibbsMeasure_singleton β p s
    have hπs' := signedBoltzmannMachineGibbsMeasure_singleton β p s'
    have hκss' := signedSiteGibbsKernel_singleton_eval_of_agree_offsite β p h_off
    have hκs's := signedSiteGibbsKernel_singleton_eval_of_agree_offsite β p h_off'
    have hreal := detailed_balance_single_site β p u s s' h_off
    rw [hπs, hπs', hκss', hκs's]
    calc
      ENNReal.ofReal (signedBoltzmannMachineGibbsProbability β p s) *
          ENNReal.ofReal (signedSiteConditionalProbability β p u s (s' u))
          = ENNReal.ofReal
              (signedBoltzmannMachineGibbsProbability β p s *
                signedSiteConditionalProbability β p u s (s' u)) := by
              symm
              exact ENNReal.ofReal_mul
                (Rebuild.StatMech.FiniteGibbs.gibbsProbability_nonneg β (boltzmannMachineFiniteGibbsModel TwoStateEncoding.boolSigned p) s)
      _ = ENNReal.ofReal
            (signedBoltzmannMachineGibbsProbability β p s' *
              signedSiteConditionalProbability β p u s' (s u)) := by
              exact congrArg ENNReal.ofReal hreal
      _ = ENNReal.ofReal (signedBoltzmannMachineGibbsProbability β p s') *
            ENNReal.ofReal (signedSiteConditionalProbability β p u s' (s u)) := by
              exact ENNReal.ofReal_mul
                (Rebuild.StatMech.FiniteGibbs.gibbsProbability_nonneg β (boltzmannMachineFiniteGibbsModel TwoStateEncoding.boolSigned p) s')

/-- Reversibility of the single-site kernel w.r.t. the Boltzmann measure. -/
lemma signedSiteGibbsKernel_reversible (β : ℝ) (p : Parameters Site) (u : Site) :
    Kernel.IsReversible (signedSiteGibbsKernel β p u) (signedBoltzmannMachineGibbsMeasure β p) := by
  refine Kernel.isReversible_of_pointwise_fintype
      (π := signedBoltzmannMachineGibbsMeasure β p)
      (κ := signedSiteGibbsKernel β p u) ?_
  intro s s'
  exact signedSiteGibbsKernel_pointwise_detailed_balance β p u s s'

end Rebuild.Bridges
