import MCMC.Finite.Core

/-!
# Rebuild Finite MCMC Core

Canonical finite-state MCMC semantics for the rebuild.

This file does not re-prove the whole Perron–Frobenius theory. Instead it packages the already
audited finite-MCMC corridor behind rebuild-facing names and a small bundled chain structure.
-/

set_option autoImplicit false

open Matrix Finset

namespace Rebuild.Probability.MCMC.Finite

/-- Transition matrices for a finite-state Markov chain. -/
abbrev TransitionMatrix (State : Type*) := Matrix State State ℝ

/-- Re-export row-stochasticity under the rebuild namespace. -/
def IsStochastic {State : Type*} [Fintype State]
  (P : TransitionMatrix State) : Prop := _root_.MCMC.Finite.IsStochastic P

/-- Re-export stationarity on the simplex under the rebuild namespace. -/
def IsStationary {State : Type*} [Fintype State]
  (P : TransitionMatrix State) (π : stdSimplex ℝ State) : Prop :=
  _root_.MCMC.Finite.IsStationary P π

/-- Detailed balance for a finite transition matrix with respect to a target distribution. -/
def IsReversible {State : Type*} [Fintype State]
  (P : TransitionMatrix State) (π : stdSimplex ℝ State) : Prop :=
  ∀ i j, π.val i * P i j = π.val j * P j i

theorem IsReversible.isStationary {State : Type*} [Fintype State]
    {P : TransitionMatrix State} {π : stdSimplex ℝ State}
    (hP : IsStochastic P) (h_rev : IsReversible P π) :
    IsStationary P π := by
  ext i
  dsimp [IsStationary, transpose_apply]
  calc
    ∑ j, P j i * π.val j = ∑ j, π.val i * P i j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [mul_comm, h_rev j i, mul_comm]
    _ = π.val i * ∑ j, P i j := by
      rw [Finset.mul_sum]
    _ = π.val i := by
      rw [hP.2 i, mul_one]

/-- A bundled finite verified Markov chain. -/
structure FiniteChain (State : Type*) [Fintype State] [DecidableEq State] [Nonempty State] where
  transition : TransitionMatrix State
  invariant : stdSimplex ℝ State
  stochastic : IsStochastic transition
  stationary : IsStationary transition invariant
  irreducible : Matrix.IsIrreducible transition
  primitive : IsPrimitive transition

instance {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]
    (chain : FiniteChain State) : _root_.MCMC.Finite.IsMCMC chain.transition chain.invariant where
  stochastic := chain.stochastic
  stationary := chain.stationary
  irreducible := chain.irreducible
  primitive := chain.primitive

noncomputable def stationaryDistribution {State : Type*} [Fintype State] [DecidableEq State]
    [Nonempty State] (P : TransitionMatrix State) (h_irred : Matrix.IsIrreducible P)
    (h_stoch : IsStochastic P) : stdSimplex ℝ State :=
  _root_.MCMC.Finite.stationaryDistribution P h_irred h_stoch

lemma stationaryDistribution_is_stationary {State : Type*} [Fintype State] [DecidableEq State]
    [Nonempty State] (P : TransitionMatrix State) (h_irred : Matrix.IsIrreducible P)
    (h_stoch : IsStochastic P) :
    IsStationary P (stationaryDistribution P h_irred h_stoch) :=
  _root_.MCMC.Finite.stationaryDistribution_is_stationary P h_irred h_stoch

theorem exists_unique_stationary_distribution_of_irreducible
    {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]
    {P : TransitionMatrix State} (h_stoch : IsStochastic P) (h_irred : Matrix.IsIrreducible P) :
    ∃! (π : stdSimplex ℝ State), IsStationary P π :=
  _root_.MCMC.Finite.exists_unique_stationary_distribution_of_irreducible h_stoch h_irred

noncomputable def ofProperties {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]
    (P : TransitionMatrix State) (h_stoch : IsStochastic P) (h_irred : Matrix.IsIrreducible P)
    (h_prim : IsPrimitive P) : FiniteChain State where
  transition := P
  invariant := stationaryDistribution P h_irred h_stoch
  stochastic := h_stoch
  stationary := stationaryDistribution_is_stationary P h_irred h_stoch
  irreducible := h_irred
  primitive := h_prim

lemma FiniteChain.aperiodic {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]
    (chain : FiniteChain State) : Matrix.IsAperiodic chain.transition :=
  _root_.MCMC.Finite.IsMCMC.aperiodic (P := chain.transition) (π := chain.invariant)
    (h := inferInstance)

end Rebuild.Probability.MCMC.Finite
