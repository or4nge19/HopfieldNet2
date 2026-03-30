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

lemma matrixToKernel_apply_singleton {State : Type*} [Fintype State] [DecidableEq State]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    {P : TransitionMatrix State} (hP : IsStochastic P) (i j : State) :
    (matrixToKernel P hP) i {j} = ENNReal.ofReal (P i j) := by
  simpa [matrixToKernel] using
    (_root_.MCMC.Finite.matrixToKernel_apply_singleton (n := State) (P := P) hP i j)

lemma vecToMeasure_apply_singleton {State : Type*} [Fintype State] [DecidableEq State]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (π : stdSimplex ℝ State) (i : State) :
    vecToMeasure π {i} = ENNReal.ofReal (π.val i) := by
  change ((∑ j : State, ENNReal.ofReal (π.val j) • Measure.dirac j) : Measure State) {i} = _
  rw [Measure.finset_sum_apply]
  · rw [Finset.sum_eq_single i]
    · rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton i)]
      simp [smul_eq_mul]
    · intro j _ hj
      rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton i)]
      simp [hj, smul_eq_mul]
    · simp

theorem isStationary_iff_invariant {State : Type*} [Fintype State] [DecidableEq State]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (P : TransitionMatrix State) (π : stdSimplex ℝ State) (hP : IsStochastic P) :
    IsStationary P π ↔ Kernel.Invariant (matrixToKernel P hP) (vecToMeasure π) :=
  _root_.MCMC.Finite.isStationary_iff_invariant P π hP

theorem isReversible_iff_kernel_reversible {State : Type*} [Fintype State] [DecidableEq State]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (P : TransitionMatrix State) (π : stdSimplex ℝ State) (hP : IsStochastic P) :
    IsReversible P π ↔ Kernel.IsReversible (matrixToKernel P hP) (vecToMeasure π) := by
  simpa [IsReversible] using
    (_root_.MCMC.Finite.isReversible_iff_kernel_reversible (n := State) P π hP)

instance matrixToKernel_isMarkov {State : Type*} [Fintype State] [DecidableEq State]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (P : TransitionMatrix State) (hP : IsStochastic P) :
    IsMarkovKernel (matrixToKernel P hP) := by
  simpa [matrixToKernel] using
    (_root_.MCMC.Finite.matrixToKernel_isMarkov (n := State) P hP)

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
