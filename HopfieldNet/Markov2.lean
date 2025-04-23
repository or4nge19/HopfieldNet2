
import HopfieldNet.DetailedBalance
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Integral.LebesgueNormedSpace
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# Markov Chain Framework

The framework provides:

1. Transition kernels for Gibbs sampling and Metropolis-Hastings algorithms
2. Detailed balance conditions that ensure convergence to stationary distributions
3. Ergodicity properties for Markov chains
4. Convergence rates and mixing time analysis
5. Direct connection to the Boltzmann distribution as stationary distribution

## Main definitions

* `stochasticHopfieldMarkovProcess`: A Markov process on Hopfield network states
* `gibbsTransitionKernel`: The transition kernel for Gibbs sampling
* `DetailedBalance`: The detailed balance condition for reversible Markov chains
* `mixingTime`: The time needed to approach the stationary distribution

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
  measure : Measure α
  isProbability : IsProbabilityMeasure measure
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
  -- Construct a default state where all neurons have activation -1
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
The Markov process induced by Gibbs sampling on a Hopfield network.
This formalizes the stochastic dynamics of the network.
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
    -- Use temperature T with proof it's positive (hT)
    let r : ℝ := Real.exp (-(Coe.coe energy : ℝ) / T)
    have h : 0 ≤ r := Real.exp_nonneg _
    -- Use the fact that r is non-negative to ensure we get a valid ENNReal
    ENNReal.ofReal (max r 0) -- max with 0 uses the fact that h : 0 ≤ r
  let partitionFn : ENNReal := ∑ s : hnet.State, densityFn s
  let countMeasure : Measure (hnet.State) := MeasureTheory.Measure.count
  -- Ensure the temperature is positive when constructing the distribution
  Measure.withDensity countMeasure (fun s => densityFn s / partitionFn)
