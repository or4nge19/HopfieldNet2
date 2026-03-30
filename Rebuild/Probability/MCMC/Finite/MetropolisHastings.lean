import MCMC.Finite.MetropolisHastings
import Rebuild.Probability.MCMC.Finite.KernelBridge

/-!
# Rebuild Finite Metropolis-Hastings

Rebuild-facing finite-state Metropolis-Hastings API.

This packages the mature finite Metropolis-Hastings development behind the canonical rebuild
namespace and makes explicit how the matrix semantics bridge to kernel semantics.

The additional reusable observation exposed here is that if a proposal kernel is already reversible
with respect to the target law, then Metropolis-Hastings accepts every proposal and leaves the
proposal matrix unchanged.
-/

set_option autoImplicit false

open ProbabilityTheory MeasureTheory

namespace Rebuild.Probability.MCMC.Finite

variable {State : Type*} [Fintype State]

/-- Acceptance probability for a finite-state Metropolis-Hastings step. -/
noncomputable abbrev acceptanceProbability (π : stdSimplex ℝ State)
    (Q : TransitionMatrix State) (x y : State) : ℝ :=
  _root_.MCMC.Finite.mh_acceptance_prob π Q x y

/-- The finite-state Metropolis-Hastings transition matrix. -/
noncomputable abbrev metropolisHastingsKernel [DecidableEq State]
    (π : stdSimplex ℝ State) (Q : TransitionMatrix State) : TransitionMatrix State :=
  _root_.MCMC.Finite.metropolisHastingsKernel π Q

variable {π : stdSimplex ℝ State} {Q : TransitionMatrix State}

lemma acceptanceProbability_bounds [DecidableEq State]
    (hQ_nonneg : ∀ i j, 0 ≤ Q i j) (x y : State) :
    0 ≤ acceptanceProbability π Q x y ∧ acceptanceProbability π Q x y ≤ 1 := by
  simpa [acceptanceProbability] using
    (_root_.MCMC.Finite.mh_acceptance_prob_bounds (π := π) (Q := Q) hQ_nonneg x y)

theorem metropolisHastings_is_stochastic [DecidableEq State] (hQ_stoch : IsStochastic Q) :
    IsStochastic (metropolisHastingsKernel π Q) := by
  simpa [metropolisHastingsKernel] using
    (_root_.MCMC.Finite.metropolisHastings_is_stochastic (π := π) (Q := Q) hQ_stoch)

theorem metropolisHastings_is_reversible [DecidableEq State] (hQ_nonneg : ∀ i j, 0 ≤ Q i j) :
    IsReversible (metropolisHastingsKernel π Q) π := by
  simpa [metropolisHastingsKernel, IsReversible] using
    (_root_.MCMC.Finite.metropolisHastings_is_reversible (π := π) (Q := Q) hQ_nonneg)

theorem metropolisHastings_is_stationary [DecidableEq State] (hQ_stoch : IsStochastic Q) :
    IsStationary (metropolisHastingsKernel π Q) π := by
  simpa [metropolisHastingsKernel] using
    (_root_.MCMC.Finite.metropolisHastings_is_stationary (π := π) (Q := Q) hQ_stoch)

/-- Bundle a finite Metropolis-Hastings chain once irreducibility and primitivity are known. -/
noncomputable def metropolisHastingsChain [DecidableEq State] [Nonempty State]
    (hQ_stoch : IsStochastic Q)
    (hP_irred : Matrix.IsIrreducible (metropolisHastingsKernel π Q))
    (hP_prim : Matrix.IsPrimitive (metropolisHastingsKernel π Q)) :
    FiniteChain State where
  transition := metropolisHastingsKernel π Q
  invariant := π
  stochastic := metropolisHastings_is_stochastic (π := π) (Q := Q) hQ_stoch
  stationary := metropolisHastings_is_stationary (π := π) (Q := Q) hQ_stoch
  irreducible := hP_irred
  primitive := hP_prim

theorem acceptanceProbability_eq_one_of_reversibleProposal [DecidableEq State]
    (hQ_rev : IsReversible Q π) (x y : State) :
    acceptanceProbability π Q x y = 1 := by
  set num : ℝ := π.val y * Q y x
  set den : ℝ := π.val x * Q x y
  have hrev : den = num := by
    dsimp [den, num]
    simpa [IsReversible] using hQ_rev x y
  by_cases hden : den = 0
  · simp [acceptanceProbability, _root_.MCMC.Finite.mh_acceptance_prob, den, hden]
  · have hratio : num / den = 1 := by
      rw [← hrev, div_self hden]
    simp [acceptanceProbability, _root_.MCMC.Finite.mh_acceptance_prob, num, den, hden, hratio]

theorem metropolisHastings_eq_of_reversibleProposal [DecidableEq State]
    (hQ_stoch : IsStochastic Q) (hQ_rev : IsReversible Q π) :
    metropolisHastingsKernel π Q = Q := by
  have hA : ∀ x y, _root_.MCMC.Finite.mh_acceptance_prob π Q x y = 1 := by
    intro x y
    simpa [acceptanceProbability] using
      (acceptanceProbability_eq_one_of_reversibleProposal (π := π) (Q := Q) hQ_rev x y)
  ext x y
  by_cases hxy : x = y
  · subst hxy
    change _root_.MCMC.Finite.metropolisHastingsKernel π Q x x = Q x x
    unfold _root_.MCMC.Finite.metropolisHastingsKernel
    simp [hA, hQ_stoch.2 x]
  · change _root_.MCMC.Finite.metropolisHastingsKernel π Q x y = Q x y
    unfold _root_.MCMC.Finite.metropolisHastingsKernel
    simp [hxy, hA]

section MeasureBridge

variable [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State]

theorem metropolisHastings_invariant (hQ_stoch : IsStochastic Q) :
    Kernel.Invariant
      (matrixToKernel (metropolisHastingsKernel π Q)
        (metropolisHastings_is_stochastic (π := π) (Q := Q) hQ_stoch))
      (vecToMeasure π) := by
  let hP : IsStochastic (metropolisHastingsKernel π Q) :=
    metropolisHastings_is_stochastic (π := π) (Q := Q) hQ_stoch
  exact (isStationary_iff_invariant (P := metropolisHastingsKernel π Q) (π := π) hP).mp
    (metropolisHastings_is_stationary (π := π) (Q := Q) hQ_stoch)

theorem metropolisHastings_kernel_reversible (hQ_stoch : IsStochastic Q) :
    Kernel.IsReversible
      (matrixToKernel (metropolisHastingsKernel π Q)
        (metropolisHastings_is_stochastic (π := π) (Q := Q) hQ_stoch))
      (vecToMeasure π) := by
  let hP : IsStochastic (metropolisHastingsKernel π Q) :=
    metropolisHastings_is_stochastic (π := π) (Q := Q) hQ_stoch
  exact (isReversible_iff_kernel_reversible (P := metropolisHastingsKernel π Q) (π := π) hP).mp
    (metropolisHastings_is_reversible (π := π) (Q := Q) hQ_stoch.1)

end MeasureBridge

end Rebuild.Probability.MCMC.Finite
