import MCMC.Finite.toKernel
import Rebuild.Probability.MCMC.Finite.Core

/-!
# Rebuild Finite MCMC Kernel Bridge

Bridge finite transition-matrix semantics to kernel-based Markov semantics on finite measurable
spaces.
-/

set_option autoImplicit false

open ProbabilityTheory MeasureTheory

namespace Rebuild.Probability.MCMC.Finite

noncomputable abbrev matrixToKernel {State : Type*} [Fintype State] [DecidableEq State]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (P : TransitionMatrix State) (hP : IsStochastic P) : Kernel State State :=
  _root_.MCMC.Finite.matrixToKernel P hP

noncomputable abbrev vecToMeasure {State : Type*} [Fintype State] [DecidableEq State]
    [MeasurableSpace State] [MeasurableSingletonClass State] :
    stdSimplex ℝ State → Measure State :=
  _root_.MCMC.Finite.vecToMeasure

theorem isStationary_iff_invariant {State : Type*} [Fintype State] [DecidableEq State]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (P : TransitionMatrix State) (π : stdSimplex ℝ State) (hP : IsStochastic P) :
    IsStationary P π ↔ Kernel.Invariant (matrixToKernel P hP) (vecToMeasure π) :=
  _root_.MCMC.Finite.isStationary_iff_invariant P π hP

theorem exists_unique_invariant_measure_of_irreducible
    {State : Type*} [Fintype State] [DecidableEq State] [MeasurableSpace State]
    [MeasurableSingletonClass State] [Nonempty State]
    {P : TransitionMatrix State} (hP : IsStochastic P) (h_irred : Matrix.IsIrreducible P) :
    ∃! (π : stdSimplex ℝ State),
      Kernel.Invariant (matrixToKernel P hP) (vecToMeasure π) :=
  _root_.MCMC.Finite.exists_unique_invariant_measure_of_irreducible hP h_irred

lemma FiniteChain.invariant_kernel {State : Type*} [Fintype State] [DecidableEq State]
    [MeasurableSpace State] [MeasurableSingletonClass State] [Nonempty State]
    (chain : FiniteChain State) :
    Kernel.Invariant (matrixToKernel chain.transition chain.stochastic) (vecToMeasure chain.invariant) := by
  exact (isStationary_iff_invariant chain.transition chain.invariant chain.stochastic).mp
    chain.stationary

end Rebuild.Probability.MCMC.Finite
