
import HopfieldNet.Stochastic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.Defs

/-!
# Markov Chain Framework

The framework aims to provide:

1. Transition kernels for Gibbs sampling and Metropolis-Hastings algorithms
2. Detailed balance conditions that ensure convergence to stationary distributions (TODO)
3. Ergodicity properties for Markov chains (TODO)
4. Convergence rates and mixing time analysis (TODO)
5. Direct connection to the Boltzmann distribution as stationary distribution (TODO)

## Main definitions

* `stochasticHopfieldMarkovProcess`: A Markov process on Hopfield network states
* `gibbsTransitionKernel`: The transition kernel for Gibbs sampling
* `DetailedBalance`: The detailed balance condition for reversible Markov chains (TODO)
* `mixingTime`: The time needed to approach the stationary distribution (TODO)

## Implementation notes

TODO

-/

open MeasureTheory ProbabilityTheory ENNReal Finset Function ProbabilityTheory.Kernel

namespace MarkovChain

instance (R U : Type) [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] :
    MeasurableSpace ((HopfieldNetwork R U).State) :=
{
  MeasurableSet' := fun _ => True,
  measurableSet_empty := trivial,
  measurableSet_compl := fun _ _ => trivial,
  measurableSet_iUnion := fun _ _ => trivial }

/-!
### Core Markov Chain Definitions
-/

/--
A `StationaryDistribution` for a transition kernel is a measure that remains
invariant under the action of the kernel.
-/
structure StationaryDistribution {α : Type*} [MeasurableSpace α] (K : Kernel α α) where
  /-- The probability measure that is stationary with respect to the kernel K. -/
  measure : Measure α
  /-- Proof that the measure is a probability measure (sums to 1). -/
  isProbability : IsProbabilityMeasure measure
  /-- Proof that the measure is invariant under the kernel K. -/
  isStationary : ∀ s, MeasurableSet s → (measure.bind K) s = measure s
/--
The detailed balance condition for a Markov kernel with respect to a measure.
This condition is crucial for proving convergence to the stationary distribution.

`μ(dx) K(x,dy) = μ(dy) K(y,dx)` for all measurable sets
-/
def DetailedBalance {α : Type*} [MeasurableSpace α] (μ : Measure α) (K : Kernel α α) : Prop :=
  ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
    ∫⁻ x in A, (K x B) ∂μ = ∫⁻ y in B, (K y A) ∂μ

/-- When detailed balance holds, the measure is stationary -/
def stationaryOfDetailedBalance {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {K : Kernel α α} [IsMarkovKernel K]
    (h : DetailedBalance μ K) : StationaryDistribution K where
  measure := μ
  isProbability := inferInstance
  isStationary := by
    intro s hs
    have bind_def : (μ.bind K) s = ∫⁻ x, (K x s) ∂μ := by
      apply Measure.bind_apply
      exact hs
      exact measurable K
    have h_balance := h Set.univ s MeasurableSet.univ hs
    rw [bind_def]
    have h_univ : ∫⁻ x, K x s ∂μ = ∫⁻ x in Set.univ, K x s ∂μ := by
      simp only [Measure.restrict_univ]
    rw [h_univ, h_balance]
    have univ_one : ∀ y ∈ s, K y Set.univ = 1 := by
      intro y _
      have h_prob : IsProbabilityMeasure (K y) := inferInstance
      exact isProbabilityMeasure_iff.mp h_prob
    have h_one : ∫⁻ y in s, K y Set.univ ∂μ = ∫⁻ y in s, 1 ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae (ae_of_all μ univ_one)] with y hy
      exact measure_univ
    rw [h_one, MeasureTheory.lintegral_const]; rw [@Measure.restrict_apply_univ]
    exact one_mul (μ s)

/-!
### Markov Chain on Hopfield Networks
-/

section HopfieldMarkovChain

variable {R U : Type} [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]

instance : Nonempty ((HopfieldNetwork R U).State) := by
  -- We construct a default state where all neurons have activation -1
  let defaultState : (HopfieldNetwork R U).State := {
    act := fun _ => -1,
    hp := fun _ => Or.inr rfl
  }
  exact ⟨defaultState⟩

noncomputable instance [Fintype (U → R)] : Fintype ((HopfieldNetwork R U).State) := by
  apply Fintype.ofInjective
    (fun s => s.act)
    (fun s1 s2 h => by
      cases s1; cases s2
      simp only at h
      subst h
      rfl)


/--
The Gibbs transition kernel for Hopfield networks. This defines the probability transition
from one state to another using Gibbs sampling at temperature T.
-/
noncomputable def gibbsTransitionKernel [Countable ENNReal] (wθ : Params (HopfieldNetwork R U)) (T : ℝ) :
    Kernel ((HopfieldNetwork R U).State) ((HopfieldNetwork R U).State) := {
      toFun := fun state => (NN.State.gibbsSamplingStep wθ T state).toMeasure,
      measurable' := by
        apply Measure.measurable_of_measurable_coe
        intro s hs
        apply measurable_to_countable
        intro x
        exact hs
    }

/--
The stochastic Hopfield Markov process, which models the evolution of Hopfield network states
over discrete time steps using Gibbs sampling at fixed temperature.
In this simplified model, the transition kernel is time-homogeneous (same for all steps).
-/
noncomputable def stochasticHopfieldMarkovProcess [Countable ENNReal] (wθ : Params (HopfieldNetwork R U)) (T : ℝ) :
    ℕ → Kernel ((HopfieldNetwork R U).State) ((HopfieldNetwork R U).State) :=
  fun _ => gibbsTransitionKernel wθ T

/--
The n-step transition probability, which gives the probability of moving from
state x to state y in exactly n steps.
-/
noncomputable def nStepTransition [Countable ENNReal] (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (n : ℕ) :
    ((HopfieldNetwork R U).State) → ((HopfieldNetwork R U).State) → ENNReal :=
  match n with
  | 0 => fun x y => if x = y then 1 else 0
  | n+1 => fun x y => ∫⁻ z, nStepTransition wθ T n z y ∂(gibbsTransitionKernel wθ T x)

/--
The total variation distance between two probability measures on Hopfield network states.
Defined as half the supremum of |μ(A) - ν(A)| over all measurable sets A.
-/
noncomputable def totalVariation [AddGroup ENNReal]  (μ ν : Measure ((HopfieldNetwork R U).State)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : ℝ :=
  (1/2) * ENNReal.toReal (
    ⨆ (A : Set ((HopfieldNetwork R U).State)) (hA : MeasurableSet A),
      |μ A - ν A|
  )

/--
A state is aperiodic if there's a positive probability of returning to it in a single step.
-/
def IsAperiodic [Countable ENNReal] (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s : (HopfieldNetwork R U).State) : Prop :=
  (gibbsTransitionKernel wθ T s) {s} > 0

/--
A Markov chain is irreducible if it's possible to get from any state to any other state
with positive probability in some finite number of steps.
-/
def IsIrreducibl [Countable ENNReal] (wθ : Params (HopfieldNetwork R U)) (T : ℝ) : Prop :=
  ∀ x y, ∃ n, nStepTransition wθ T n x y > 0

/--
The Boltzmann distribution over Hopfield network states at temperature T.
-/
noncomputable def boltzmannDistribution (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (hT : T > 0) :
    Measure ((HopfieldNetwork R U).State) :=
  let hnet := HopfieldNetwork R U
  let densityFn : hnet.State → ENNReal := fun s =>
    let energy : R := NeuralNetwork.State.E wθ s
    let r : ℝ := Real.exp (-(Coe.coe energy : ℝ) / T)
    have h : 0 ≤ r := Real.exp_nonneg _
    ENNReal.ofReal (max r 0)
  let partitionFn : ENNReal := ∑ s : hnet.State, densityFn s
  let countMeasure : Measure (hnet.State) := MeasureTheory.Measure.count
  Measure.withDensity countMeasure (fun s => densityFn s / partitionFn)

/-- The unnormalized Boltzmann density function -/
noncomputable def boltzmannDensityFn (wθ : Params (HopfieldNetwork R U)) (T : ℝ)
    (s : (HopfieldNetwork R U).State) : ENNReal :=
  ENNReal.ofReal (Real.exp (-(Coe.coe (NeuralNetwork.State.E wθ s) : ℝ) / T))

/-- The Boltzmann partition function (normalizing constant) -/
noncomputable def boltzmannPartitionFn (wθ : Params (HopfieldNetwork R U)) (T : ℝ) : ENNReal :=
  ∑ s, boltzmannDensityFn wθ T s

/-- The Boltzmann distribution measure of the universe equals the integral of density/partition -/
lemma boltzmannDistribution_measure_univ (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (hT : T > 0) :
  boltzmannDistribution wθ T hT Set.univ =
  ∫⁻ s in Set.univ, (boltzmannDensityFn wθ T s) / (boltzmannPartitionFn wθ T) ∂Measure.count := by
  unfold boltzmannDistribution
  rw [withDensity_apply _ MeasurableSet.univ]
  apply lintegral_congr
  intro s
  simp only [boltzmannDensityFn, Set.mem_univ, forall_const]
  have h_exp_pos : Real.exp (-Coe.coe (NeuralNetwork.State.E wθ s) / T) ≥ 0 := Real.exp_nonneg _
  have h_max : Real.exp (-Coe.coe (NeuralNetwork.State.E wθ s) / T) ⊔ 0 = Real.exp (-Coe.coe (NeuralNetwork.State.E wθ s) / T) := by
    exact max_eq_left h_exp_pos
  congr
  · ext x
    simp only [boltzmannDensityFn]
    have h_exp_pos_x : Real.exp (-Coe.coe (NeuralNetwork.State.E wθ x) / T) ≥ 0 := Real.exp_nonneg _
    have h_max_x : Real.exp (-Coe.coe (NeuralNetwork.State.E wθ x) / T) ⊔ 0 = Real.exp (-Coe.coe (NeuralNetwork.State.E wθ x) / T) := by
      exact max_eq_left h_exp_pos_x
    exact congrArg ENNReal.ofReal h_max_x

/-- The Boltzmann partition function is positive -/
lemma boltzmannPartitionFn_pos [IsOrderedCancelAddMonoid ENNReal] (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (hT : T > 0) :
  boltzmannPartitionFn wθ T > 0 := by
  simp only [boltzmannPartitionFn]
  apply Finset.sum_pos
  · intro s _
    simp only [boltzmannDensityFn]
    exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  · exact Finset.univ_nonempty

/-- The integral over the universe equals the sum over all states -/
lemma boltzmannDistribution_integral_eq_sum (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (hT : T > 0) :
  ∫⁻ s in Set.univ, (boltzmannDensityFn wθ T s) / (boltzmannPartitionFn wθ T) ∂Measure.count =
  ∑ s, (boltzmannDensityFn wθ T s) / (boltzmannPartitionFn wθ T) := by
  rw [Measure.restrict_univ, MeasureTheory.lintegral_count]
  exact tsum_fintype (fun s => boltzmannDensityFn wθ T s / boltzmannPartitionFn wθ T)

/-- Division can be distributed over the sum in the Boltzmann distribution -/
lemma boltzmannDistribution_div_sum [IsOrderedCancelAddMonoid ENNReal] [IsOrderedCancelAddMonoid ENNReal] (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (hT : T > 0) :
  ∑ s, (boltzmannDensityFn wθ T s) / (boltzmannPartitionFn wθ T) =
  (∑ s, boltzmannDensityFn wθ T s) / (boltzmannPartitionFn wθ T) := by
  have h_pos := boltzmannPartitionFn_pos wθ T hT
  have h_nonzero : boltzmannPartitionFn wθ T ≠ 0 := ne_of_gt h_pos
  have h_rewrite : ∀ x, boltzmannDensityFn wθ T x / boltzmannPartitionFn wθ T =
                        boltzmannDensityFn wθ T x * (1 / boltzmannPartitionFn wθ T) := by
    intro x
    simp only [one_div]
    exact rfl
  simp_rw [h_rewrite]
  have h_factor : ∑ x, boltzmannDensityFn wθ T x * (1 / boltzmannPartitionFn wθ T) =
                  (1 / boltzmannPartitionFn wθ T) * ∑ x, boltzmannDensityFn wθ T x := by
    rw [← Finset.sum_mul]
    exact CommMonoid.mul_comm (∑ i, boltzmannDensityFn wθ T i) (1 / boltzmannPartitionFn wθ T)
  rw [h_factor]
  simp only [one_div]
  exact Eq.symm ENNReal.div_eq_inv_mul

/-- The sum of Boltzmann probabilities equals 1 -/
lemma boltzmannDistribution_sum_one [IsOrderedCancelAddMonoid ENNReal] (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (hT : T > 0) :
  (∑ s, boltzmannDensityFn wθ T s) / (boltzmannPartitionFn wθ T) = 1 := by
  unfold boltzmannPartitionFn
  have h_pos := boltzmannPartitionFn_pos wθ T hT
  have h_nonzero : (∑ s, boltzmannDensityFn wθ T s) ≠ 0 := ne_of_gt h_pos

  have h_fin : (∑ s, boltzmannDensityFn wθ T s) ≠ ∞ := by
    refine sum_ne_top.mpr ?_
    intro s _
    exact Ne.symm (ne_of_beq_false rfl)

  exact ENNReal.div_self h_nonzero h_fin

/--
Proves that the Boltzmann distribution for a Hopfield network forms a valid probability measure.
-/
theorem boltzmannDistribution_isProbability [IsOrderedCancelAddMonoid ENNReal] {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  [DivisionSemiring ((HopfieldNetwork R U).State → ENNReal)]
  [IsOrderedCancelAddMonoid ENNReal] [DivisionSemiring ENNReal]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (hT : T > 0) :
  IsProbabilityMeasure (boltzmannDistribution wθ T hT) := by
  apply IsProbabilityMeasure.mk
  rw [boltzmannDistribution_measure_univ wθ T hT]
  rw [boltzmannDistribution_integral_eq_sum wθ T hT]
  rw [boltzmannDistribution_div_sum wθ T hT]
  exact boltzmannDistribution_sum_one wθ T hT
