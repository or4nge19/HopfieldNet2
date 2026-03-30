import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Rebuild.Probability.MCMC.Finite.KernelBridge

/-!
# Rebuild Finite MCMC PMF Bridge

Bridge finite Markov semantics among `PMF`, `Kernel`, and transition-matrix presentations.
-/

set_option autoImplicit false

open ProbabilityTheory MeasureTheory
open scoped BigOperators ENNReal

namespace Rebuild.Probability.MCMC.Finite

variable {State : Type*} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Turn a `PMF`-valued step rule into a finite-state Markov kernel. -/
noncomputable def pmfToKernel (κ : State → PMF State) : Kernel State State :=
  Kernel.ofFunOfCountable (fun i => (κ i).toMeasure)

instance pmfToKernel_isMarkov (κ : State → PMF State) :
    IsMarkovKernel (pmfToKernel κ) where
  isProbabilityMeasure i := by
    change IsProbabilityMeasure ((κ i).toMeasure)
    infer_instance

omit [DecidableEq State] in
lemma pmfToKernel_apply_singleton (κ : State → PMF State) (i j : State) :
    pmfToKernel κ i {j} = κ i j := by
  change (κ i).toMeasure {j} = κ i j
  exact PMF.toMeasure_apply_singleton (κ i) j (measurableSet_singleton j)

/-- Read a finite Markov kernel row as a `PMF`. -/
noncomputable def kernelToPMF (κ : Kernel State State) [IsMarkovKernel κ] :
    State → PMF State :=
  fun i => (κ i).toPMF

omit [DecidableEq State] in
lemma kernelToPMF_apply (κ : Kernel State State) [IsMarkovKernel κ] (i j : State) :
    kernelToPMF κ i j = κ i {j} := by
  simp [kernelToPMF, Measure.toPMF_apply]

omit [DecidableEq State] in
theorem pmfToKernel_kernelToPMF (κ : Kernel State State) [IsMarkovKernel κ] :
    pmfToKernel (kernelToPMF κ) = κ := by
  rw [Kernel.ext_iff]
  intro i
  change ((κ i).toPMF).toMeasure = κ i
  exact Measure.toPMF_toMeasure (μ := κ i)

omit [DecidableEq State] in
theorem kernelToPMF_pmfToKernel (κ : State → PMF State) :
    kernelToPMF (pmfToKernel κ) = κ := by
  funext i
  change ((κ i).toMeasure).toPMF = κ i
  exact PMF.toMeasure_toPMF (p := κ i)

/-- Convert a `PMF`-valued step rule into its row-stochastic matrix. -/
noncomputable def pmfToMatrix (κ : State → PMF State) : TransitionMatrix State :=
  fun i j => (κ i j).toReal

omit [Fintype State] [DecidableEq State] [MeasurableSpace State]
  [MeasurableSingletonClass State] in
lemma pmfToMatrix_nonneg (κ : State → PMF State) (i j : State) :
    0 ≤ pmfToMatrix κ i j := by
  simp [pmfToMatrix]

omit [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State] in
lemma pmfToMatrix_row_sum (κ : State → PMF State) (i : State) :
    ∑ j : State, pmfToMatrix κ i j = 1 := by
  have h_ne_top : ∀ j : State, κ i j ≠ ∞ := fun j => (κ i).apply_ne_top j
  have h_toReal :
      ENNReal.toReal ((Finset.univ : Finset State).sum (fun j => κ i j)) =
        (Finset.univ : Finset State).sum (fun j => (κ i j).toReal) :=
    ENNReal.toReal_sum (s := (Finset.univ : Finset State))
      (f := fun j : State => κ i j) (by
        intro j _
        exact h_ne_top j)
  have hsum :
      ((Finset.univ : Finset State).sum (fun j => κ i j)) = (1 : ℝ≥0∞) := by
    simpa [tsum_fintype] using (PMF.tsum_coe (κ i))
  have hsum_toReal :
      ENNReal.toReal ((Finset.univ : Finset State).sum (fun j => κ i j)) = 1 := by
    simp [hsum]
  have hrow : (Finset.univ : Finset State).sum (fun j => (κ i j).toReal) = 1 := by
    simpa [h_toReal] using hsum_toReal
  simpa [pmfToMatrix] using hrow

omit [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State] in
theorem pmfToMatrix_isStochastic (κ : State → PMF State) :
    IsStochastic (pmfToMatrix κ) := by
  constructor
  · intro i j
    exact pmfToMatrix_nonneg κ i j
  · intro i
    simpa using pmfToMatrix_row_sum κ i

theorem matrixToKernel_pmfToMatrix (κ : State → PMF State) :
    matrixToKernel (pmfToMatrix κ) (pmfToMatrix_isStochastic κ) = pmfToKernel κ := by
  rw [Kernel.ext_iff]
  intro i
  rw [MeasureTheory.Measure.ext_iff_singleton]
  intro j
  rw [matrixToKernel_apply_singleton, pmfToKernel_apply_singleton]
  simpa [pmfToMatrix] using ENNReal.ofReal_toReal ((κ i).apply_ne_top j)

/-- Convert a finite Markov kernel into its transition matrix by singleton masses. -/
noncomputable def kernelToMatrix (κ : Kernel State State) [IsMarkovKernel κ] :
    TransitionMatrix State :=
  pmfToMatrix (kernelToPMF κ)

omit [DecidableEq State] in
lemma kernelToMatrix_apply (κ : Kernel State State) [IsMarkovKernel κ] (i j : State) :
    kernelToMatrix κ i j = (κ i {j}).toReal := by
  simp [kernelToMatrix, pmfToMatrix, kernelToPMF, Measure.toPMF_apply]

omit [DecidableEq State] in
theorem kernelToMatrix_isStochastic (κ : Kernel State State) [IsMarkovKernel κ] :
    IsStochastic (kernelToMatrix κ) := by
  simpa [kernelToMatrix] using pmfToMatrix_isStochastic (kernelToPMF κ)

theorem kernelToMatrix_matrixToKernel
    {P : TransitionMatrix State} (hP : IsStochastic P) :
    kernelToMatrix (matrixToKernel P hP) = P := by
  ext i j
  rw [kernelToMatrix_apply, matrixToKernel_apply_singleton]
  exact ENNReal.toReal_ofReal (hP.1 i j)

theorem matrixToKernel_kernelToMatrix (κ : Kernel State State) [IsMarkovKernel κ] :
    matrixToKernel (kernelToMatrix κ) (kernelToMatrix_isStochastic κ) = κ := by
  rw [Kernel.ext_iff]
  intro i
  rw [MeasureTheory.Measure.ext_iff_singleton]
  intro j
  rw [matrixToKernel_apply_singleton, kernelToMatrix_apply]
  exact ENNReal.ofReal_toReal (measure_ne_top (κ i) {j})

end Rebuild.Probability.MCMC.Finite
