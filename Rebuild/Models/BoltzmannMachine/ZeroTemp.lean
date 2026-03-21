import Rebuild.Models.BoltzmannMachine.Basic
import Rebuild.StatMech.FiniteGibbs.ZeroTemp

/-!
# Zero-Temperature Limit for Boltzmann Machines

This file rescues the core convergence result demonstrating that stochastic
Gibbs updates smoothly transition into deterministic best-response limits as $\beta \to \infty$.
We reformulate the old `ZeroTemp.lean` results into the new type-safe parameterizations.
-/

set_option autoImplicit false

open Filter Topology
open Rebuild.Models.BoltzmannMachine
open Rebuild.StatMech.FiniteGibbs
open Rebuild.Models.BinarySpin.Pairwise (overwrite)

namespace Rebuild.Models.BoltzmannMachine

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- The conditional probability of picking `true` is exactly the logistic of the energy gap multiplied by β. -/
lemma signedSiteConditionalProbability_true_eq_logistic (β : ℝ) (p : Parameters Site)
    (i : Site) (τ : SignedState Site) :
    signedSiteConditionalProbability β p i τ true =
      logisticProb (β * (signedEnergyFn p (overwrite τ i false) - signedEnergyFn p (overwrite τ i true))) := by
  set E_T := signedEnergyFn p (overwrite τ i true)
  set E_F := signedEnergyFn p (overwrite τ i false)
  unfold signedSiteConditionalProbability signedSitePartition signedSiteConditionalWeight
  have h_denom : Real.exp (-β * E_T) + Real.exp (-β * E_F) =
      Real.exp (-β * E_T) * (1 + Real.exp ((-β * E_F) - (-β * E_T))) := by
    rw [mul_add, mul_one, ← Real.exp_add]
    congr 1
    ring_nf
  have h_denom' :
      Real.exp (-β * signedEnergyFn p (overwrite τ i true)) +
          Real.exp (-β * signedEnergyFn p (overwrite τ i false)) =
        Real.exp (-β * signedEnergyFn p (overwrite τ i true)) *
          (1 +
            Real.exp
              ((-β * signedEnergyFn p (overwrite τ i false)) -
                (-β * signedEnergyFn p (overwrite τ i true)))) := by
    simpa [E_T, E_F] using h_denom
  rw [h_denom', div_mul_eq_div_div, div_self (Real.exp_pos _).ne', one_div]
  have h_diff :
      (-β * signedEnergyFn p (overwrite τ i false)) -
          (-β * signedEnergyFn p (overwrite τ i true)) =
        -(β * (E_F - E_T)) := by
    simp [E_T, E_F]
    ring
  simp_rw [h_diff]
  unfold logisticProb
  ring_nf

/-- In the limit as β → ∞, the probability is determined by the local field's sign.
If E(false) > E(true), the probability of true approaches 1. -/
lemma tendsto_probability_true_of_lower_energy
    (p : Parameters Site) (i : Site) (τ : SignedState Site)
    (h_energy : signedEnergyFn p (overwrite τ i true) < signedEnergyFn p (overwrite τ i false)) :
    Tendsto (fun β => signedSiteConditionalProbability β p i τ true) atTop (𝓝 1) := by
  have h_gap : 0 < signedEnergyFn p (overwrite τ i false) - signedEnergyFn p (overwrite τ i true) :=
    sub_pos.2 h_energy
  have h_conv := tendsto_logistic_scaled_of_pos h_gap
  exact tendsto_congr (fun β => signedSiteConditionalProbability_true_eq_logistic β p i τ) |>.mpr h_conv

/-- If E(false) < E(true), the probability of true approaches 0. -/
lemma tendsto_probability_true_of_higher_energy
    (p : Parameters Site) (i : Site) (τ : SignedState Site)
    (h_energy : signedEnergyFn p (overwrite τ i false) < signedEnergyFn p (overwrite τ i true)) :
    Tendsto (fun β => signedSiteConditionalProbability β p i τ true) atTop (𝓝 0) := by
  have h_gap : signedEnergyFn p (overwrite τ i false) - signedEnergyFn p (overwrite τ i true) < 0 :=
    sub_neg.2 h_energy
  have h_conv := tendsto_logistic_scaled_of_neg h_gap
  exact tendsto_congr (fun β => signedSiteConditionalProbability_true_eq_logistic β p i τ) |>.mpr h_conv

/-- If E(false) = E(true), the probability of true remains 1/2. -/
lemma tendsto_probability_true_of_equal_energy
    (p : Parameters Site) (i : Site) (τ : SignedState Site)
    (h_energy : signedEnergyFn p (overwrite τ i false) = signedEnergyFn p (overwrite τ i true)) :
    Tendsto (fun β => signedSiteConditionalProbability β p i τ true) atTop (𝓝 (1 / 2)) := by
  have h_gap : signedEnergyFn p (overwrite τ i false) - signedEnergyFn p (overwrite τ i true) = 0 :=
    sub_eq_zero.2 h_energy
  have h_conv := tendsto_logistic_scaled_of_eq_zero h_gap
  exact tendsto_congr (fun β => signedSiteConditionalProbability_true_eq_logistic β p i τ) |>.mpr h_conv

end Rebuild.Models.BoltzmannMachine
