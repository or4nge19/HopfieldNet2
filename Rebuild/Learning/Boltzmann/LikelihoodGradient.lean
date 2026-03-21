import Rebuild.Statistics.LogPartition

/-!
# Boltzmann Machine Likelihood Gradients

This file turns the core identity `∇ (log Z)(θ) = - E_θ[stat]` into the
corresponding single-sample negative log-likelihood gradient formula:
`∇ (⟪stat x, θ⟫ + log Z(θ)) = stat x - E_θ[stat]`.
-/

namespace Rebuild.Learning.Boltzmann

open InnerProductSpace
open Rebuild.Statistics.ExponentialFamily

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]

/-- Single-sample negative log-likelihood for the exp-family `w_θ(x)=exp(-⟪stat x, θ⟫)`. -/
noncomputable def negLogLik (stat : X → Θ) (x : X) (θ : Θ) : ℝ :=
  inner ℝ (stat x) θ + Real.log (Z (X := X) (Θ := Θ) stat θ)

omit [DecidableEq X] in
/-- The negative log-likelihood gradient is `data_statistic - model_expectation`. -/
theorem hasGradientAt_negLogLik (stat : X → Θ) (x : X) (θ : Θ) :
    HasGradientAt (fun θ' : Θ => negLogLik (X := X) (Θ := Θ) stat x θ')
      (stat x - expectation (X := X) (Θ := Θ) stat θ) θ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun θ' : Θ => inner ℝ (stat x) θ') (toDual ℝ Θ (stat x)) θ := by
    simpa [InnerProductSpace.toDual_apply_apply] using (toDual ℝ Θ (stat x)).hasFDerivAt (x := θ)
  have h2 : HasFDerivAt (fun θ' : Θ => Real.log (Z (X := X) (Θ := Θ) stat θ'))
        (toDual ℝ Θ (-(expectation (X := X) (Θ := Θ) stat θ))) θ :=
    (hasGradientAt_logZ (X := X) (Θ := Θ) stat θ).hasFDerivAt
  have hsum := h1.add h2
  simpa [negLogLik, sub_eq_add_neg, map_add, map_neg] using hsum

end Rebuild.Learning.Boltzmann
