/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import HopfieldNet.Asym
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Vector.Basic

set_option linter.unusedVariables false

open Finset Matrix NeuralNetwork State

/-- Extensionality lemma for neural network states --/
@[ext]
lemma State.ext {R U : Type} [Zero R] {NN : NeuralNetwork R U}
    {s₁ s₂ : NN.State} : (∀ u, s₁.act u = s₂.act u) → s₁ = s₂ := by
  intro h
  cases s₁
  cases s₂
  simp only [NeuralNetwork.State.mk.injEq]
  apply funext
  exact h

instance decidableEqState {R U : Type} [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] :
  DecidableEq ((HopfieldNetwork R U).State) := by
  intro s₁ s₂
  apply decidable_of_iff (∀ u, s₁.act u = s₂.act u)
  · exact ⟨fun h ↦ State.ext h, fun h u ↦ by rw [h]⟩

/-- Decompose energy into weight component and bias component --/
@[simp]
lemma energy_decomposition {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) :
  s.E wθ = s.Ew wθ + s.Eθ wθ := by
  -- By definition of E
  -- Show that probs true is positive since it's constructed from exp of a real
  rw [← @add_neg_eq_iff_eq_add]
  exact add_neg_eq_of_eq_add rfl



/-- Weight matrix is symmetric in a Hopfield network --/
@[simp]
lemma weight_symmetry {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (v1 v2 : U) :
  wθ.w v1 v2 = wθ.w v2 v1 :=
  (congrFun (congrFun (id (wθ.hw').symm) v1) v2)

/-- Energy sum can be split into terms with u and terms without u --/
@[simp]
lemma energy_sum_split {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U):
  ∑ v : U, ∑ v2 ∈ {v2 | v2 ≠ v}, wθ.w v v2 * s.act v * s.act v2 =
    (∑ v2 ∈ {v2 | v2 ≠ u}, wθ.w u v2 * s.act u * s.act v2) +
    (∑ v ∈ univ.erase u, ∑ v2 ∈ {v2 | v2 ≠ v}, wθ.w v v2 * s.act v * s.act v2) := by
  rw [← sum_erase_add _ _ (mem_univ u)]
  simp only [ne_eq, mem_univ, sum_erase_eq_sub, sub_add_cancel, add_sub_cancel]

instance updateNeuronDecEq {R U : Type} [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U]
    (s : (HopfieldNetwork R U).State) (u : U) (val : R) (hval : (HopfieldNetwork R U).pact val) :
    DecidableEq ((HopfieldNetwork R U).State) := by
  intro s₁ s₂
  apply decidable_of_iff (∀ u, s₁.act u = s₂.act u)
  · exact ⟨fun h ↦ State.ext h, fun h u ↦ by rw [h]⟩

section Stochastic
set_option linter.unusedVariables false

open Finset Matrix NeuralNetwork State

/-- Probability Mass Function over Neural Network States --/
def NeuralNetwork.StatePMF {R U : Type} [Zero R] (NN : NeuralNetwork R U) := PMF (NN.State)

/-- Temperature-parameterized stochastic dynamics for neural networks --/
def NeuralNetwork.StochasticDynamics {R U : Type} [Zero R] (NN : NeuralNetwork R U) :=
  ∀ (T : ℝ), NN.State → NeuralNetwork.StatePMF NN

/-- Metropolis acceptance decision as a probability mass function over Boolean outcomes --/
def NN.State.metropolisDecision
  {R U : Type} [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (p : ℝ) : PMF Bool :=
  PMF.bernoulli (ENNReal.ofReal (min p 1)) (by
    exact_mod_cast min_le_right p 1)

/-- Gibbs sampler update for a single neuron in a Hopfield network --/
noncomputable def NN.State.gibbsUpdateNeuron
  {R U : Type} [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s : (HopfieldNetwork R U).State) (u : U)
  : PMF ((HopfieldNetwork R U).State) :=
  -- Calculate local field and energy difference for flipping
  let h_u := s.net wθ u
  let ΔE := 2 * h_u * s.act u  -- Energy difference if neuron flips

  -- Metropolis-Hastings acceptance probability
  let p_flip := ENNReal.ofReal (Real.exp (-(↑ΔE) / T)) / (1 + ENNReal.ofReal (Real.exp (-(↑ΔE) / T)))

  -- Return distribution over possible states after update
  let p_flip_le_one : p_flip ≤ 1 := by
    -- Since p_flip = a/(1+a) where a is non-negative,
    -- and a/(1+a) ≤ 1 for all a ≥ 0
    simp [p_flip]
    let a := ENNReal.ofReal (Real.exp (-(↑ΔE) / T))

    have h_a_nonneg : 0 ≤ a := by exact zero_le a

    have h_denom_ne_zero : 1 + a ≠ 0 := by
      intro h
      have h1 : 0 ≤ 1 + a := by exact zero_le (1 + a)
      have h2 : 1 + a = 0 := h
      simp_all only [zero_le, add_eq_zero, one_ne_zero, ENNReal.ofReal_eq_zero, false_and, a, ΔE, h_u, p_flip]

    have h_sum_ne_top : (1 + a) ≠ ⊤ := by
      apply ENNReal.add_ne_top.2
      constructor
      · exact ENNReal.one_ne_top
      · apply ENNReal.ofReal_ne_top

    rw [ENNReal.div_le_iff h_denom_ne_zero h_sum_ne_top]
    simp
    exact le_add_self

  PMF.bind (PMF.bernoulli p_flip p_flip_le_one) $ λ should_flip =>
    PMF.pure $ if should_flip then s.Up wθ u else s

/-- Function to set a specific neuron state --/
def NN.State.updateNeuron {R U : Type} [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U]
  (s : (HopfieldNetwork R U).State) (u : U) (val : R) (hval : (HopfieldNetwork R U).pact val) : (HopfieldNetwork R U).State :=
{ act := fun u' => if u' = u then val else s.act u',
  hp := by
    intro u'
    by_cases h : u' = u
    · simp [h]
      exact hval
    · simp [h]
      exact s.hp u' }

/-- Update a single neuron according to Gibbs sampling rule --/
noncomputable def NN.State.gibbsUpdateSingleNeuron
  {R U : Type} [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s : (HopfieldNetwork R U).State) (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (u : U)
  : PMF ((HopfieldNetwork R U).State) :=
  -- Calculate local field for the neuron
  let local_field := s.net wθ u

  -- Calculate probabilities based on Boltzmann distribution
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))

  -- Create PMF with normalized probabilities
  let total : ENNReal := probs true + probs false
  let norm_probs : Bool → ENNReal := λ b => probs b / total

  -- Convert Bool to State
  (PMF.map (λ b => if b then
              NN.State.updateNeuron s u 1 (by exact mul_self_eq_mul_self_iff.mp rfl)
            else
              NN.State.updateNeuron s u (-1) (by exact AffineMap.lineMap_eq_lineMap_iff.mp rfl))
    (PMF.ofFintype norm_probs (by
      have h_total : total ≠ 0 := by {
        simp [probs]
        refine ENNReal.inv_ne_top.mp ?_
        have h_exp_pos := Real.exp_pos (local_field * 1 / T)
        have h := ENNReal.ofReal_pos.mpr h_exp_pos
        simp_all only [mul_one, ENNReal.ofReal_pos, mul_ite, mul_neg, ↓reduceIte, Bool.false_eq_true, ne_eq,
          ENNReal.inv_eq_top, add_eq_zero, ENNReal.ofReal_eq_zero, not_and, not_le, isEmpty_Prop, IsEmpty.forall_iff,
          local_field, total, probs]
      }
      have h_total_ne_top : total ≠ ⊤ := by {
        simp [probs, total]
      }
      have h_sum : Finset.sum Finset.univ norm_probs = 1 := by
        calc Finset.sum Finset.univ norm_probs
          = (probs true)/total + (probs false)/total := by exact Fintype.sum_bool fun b ↦ probs b / total
        _ = (probs true + probs false)/total := ENNReal.div_add_div_same
        _ = total/total := by rfl
        _ = 1 := ENNReal.div_self h_total h_total_ne_top
      exact h_sum)))

@[inherit_doc]
scoped[ENNReal] notation "ℝ≥0∞" => ENNReal

/-- Given a Hopfield Network's parameters, temperature, and current state, performs a single step
of Gibbs sampling by:
1. Uniformly selecting a random neuron
2. Updating that neuron's state according to the Gibbs distribution
-/
noncomputable def NN.State.gibbsSamplingStep
  {R U : Type} [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s : (HopfieldNetwork R U).State)
  : PMF ((HopfieldNetwork R U).State) :=
  -- Uniform random selection of neuron
  let neuron_pmf : PMF U :=
    PMF.ofFintype (λ _ => (1 : ENNReal) / (Fintype.card U : ENNReal))
      (by
        rw [Finset.sum_const, Finset.card_univ]
        rw [ENNReal.div_eq_inv_mul]
        simp only [mul_one]
        have h : (Fintype.card U : ENNReal) ≠ 0 := by
          simp [Fintype.card_pos_iff.mpr inferInstance]
        have h_top : (Fintype.card U : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
        rw [← ENNReal.mul_inv_cancel h h_top]
        simp_all only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true, ENNReal.natCast_ne_top,
          nsmul_eq_mul])
  -- Bind neuron selection with conditional update
  PMF.bind neuron_pmf $ λ u => NN.State.gibbsUpdateSingleNeuron s wθ T u

instance : Coe ℝ ℝ := ⟨id⟩

lemma Array.mkArray_size {α : Type} (n : ℕ) (a : α) :
  (Array.mkArray n a).size = n := by exact size_mkArray n a

lemma Array.mkArray_get {α : Type} (n : ℕ) (a : α) (i : Nat) (h : i < n) :
  (Array.mkArray n a)[i]'(by rw [Array.mkArray_size]; exact h) = a :=
  Array.getElem_mkArray _ _ _

/--
Proves that `Array.mkArray` creates valid parameters for a Hopfield network.

Given a vertex `u` in a Hopfield network with `n` nodes, this lemma establishes that:
1. The array `σ_u` has size equal to `κ1 u`
2. The array `θ_u` has size equal to `κ2 u`
3. All elements in `σ_u` are initialized to 0
4. All elements in `θ_u` are initialized to 0

where `κ1` and `κ2` are dimension functions defined in the `HopfieldNetwork` structure.
-/
lemma Array.mkArray_creates_valid_hopfield_params {n : ℕ} [Nonempty (Fin n)] :
  ∀ (u : Fin n),
    let σ_u := Array.mkArray ((HopfieldNetwork ℝ (Fin n)).κ1 u) 0
    let θ_u := Array.mkArray ((HopfieldNetwork ℝ (Fin n)).κ2 u) 0
    σ_u.size = (HopfieldNetwork ℝ (Fin n)).κ1 u ∧
    θ_u.size = (HopfieldNetwork ℝ (Fin n)).κ2 u ∧
    (∀ i : Nat, ∀ h : i < σ_u.size, σ_u[i]'(by { simp only [σ_u]; rw [Array.mkArray_size]; exact h }) = 0) ∧
    (∀ i : Nat, ∀ h : i < θ_u.size, θ_u[i]'(by { simp only [θ_u]; rw [Array.mkArray_size]; exact h }) = 0) := by
      intro u
      let σ_u := Array.mkArray ((HopfieldNetwork ℝ (Fin n)).κ1 u) 0
      let θ_u := Array.mkArray ((HopfieldNetwork ℝ (Fin n)).κ2 u) 0
      simp only [σ_u, θ_u] -- Unfold lets
      refine ⟨Array.size_mkArray .., Array.size_mkArray .., ?_, ?_⟩
      · intro i h; exact Array.getElem_mkArray .. -- Simplified using .. notation
      · intro i h; exact Array.getElem_mkArray ..
-- Note: The exact structure of κ1, κ2 might influence the `by { ... }` proofs for the indices.
-- Assuming κ1 u = n and κ2 u = 1 (typical for basic Hopfield), the proofs might simplify.

/--
In a Hopfield network, two neurons are adjacent if and only if they are different.
This formalizes the fully connected nature of Hopfield networks.
--/
lemma HopfieldNetwork.all_nodes_adjacent {R U : Type} [LinearOrderedField R] [DecidableEq U]
    [Nonempty U] [Fintype U] (u v : U) :
    ¬(HopfieldNetwork R U).Adj u v → u = v := by
  intro h
  unfold HopfieldNetwork at h
  simp only [ne_eq] at h
  simp_all only [Decidable.not_not]

/-- Perform a stochastic update on a Pattern representation -/
noncomputable def patternStochasticUpdate
  {n : ℕ} [Nonempty (Fin n)] (weights : Fin n → Fin n → ℝ) (h_diag_zero : ∀ i : Fin n, weights i i = 0)
  (h_sym : ∀ i j : Fin n, weights i j = weights j i) (T : ℝ)
  (pattern : NeuralNetwork.State (HopfieldNetwork ℝ (Fin n))) (i : Fin n) :
  PMF (NeuralNetwork.State (HopfieldNetwork ℝ (Fin n))) :=
  let wθ : Params (HopfieldNetwork ℝ (Fin n)) := {
    w := weights,
    hw := fun u v h => by
      -- For Hopfield networks, w(u,u) = 0 is always true
      -- since self-connections are disallowed in a standard Hopfield network
      -- Check if u = v (self-connection)
      if h_eq : u = v then
        -- For a self-connection, weights should be 0
        rw [h_eq]
        exact h_diag_zero v
      else
        -- For distinct neurons, we need to show weights u v = 0 when not adjacent
        -- In a Hopfield network, all distinct neurons are adjacent
        -- This is a contradiction since h proves they're not adjacent
        have h_adj : (HopfieldNetwork ℝ (Fin n)).Adj u v := by
          simp only [HopfieldNetwork]; simp only [ne_eq]
          exact h_eq
        -- We have h: ¬Adj u v and h_adj: Adj u v, contradiction
        contradiction
    hw' := by
      -- For Hopfield networks, we need to prove weight symmetry
      unfold NeuralNetwork.pw
      -- Apply the symmetry hypothesis directly
      exact IsSymm.ext_iff.mpr fun i j ↦ h_sym j i
    σ := fun u => Vector.mk (Array.mkArray ((HopfieldNetwork ℝ (Fin n)).κ1 u) (0 : ℝ)) (by simp [Array.mkArray_size]),
    θ := fun u => Vector.mk (Array.mkArray ((HopfieldNetwork ℝ (Fin n)).κ2 u) (0 : ℝ)) (by simp [Array.mkArray_size])
  }
  NN.State.gibbsUpdateSingleNeuron pattern wθ T i

noncomputable def NN.State.gibbsSamplingSteps
  {R U : Type} [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (steps : ℕ)
  (s : (HopfieldNetwork R U).State) : PMF ((HopfieldNetwork R U).State) :=
  match steps with
  | 0 => PMF.pure s
  | steps+1 => PMF.bind (gibbsSamplingSteps wθ T steps s) $ λ s' =>
                NN.State.gibbsSamplingStep wθ T s'

/-- `NN.State.simulatedAnnealing` implements the simulated annealing optimization algorithm for a Hopfield Network.
This function performs simulated annealing by starting from an initial state and gradually reducing
the temperature according to an exponential cooling schedule, allowing the system to explore the
state space and eventually settle into a low-energy configuration.
-/
noncomputable def NN.State.simulatedAnnealing
  {R U : Type} [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U))
  (initial_temp : ℝ) (cooling_rate : ℝ) (steps : ℕ)
  (initial_state : (HopfieldNetwork R U).State) : PMF ((HopfieldNetwork R U).State) :=
  -- Temperature schedule definition
  let temp_schedule : ℕ → ℝ := λ step => initial_temp * Real.exp (-cooling_rate * step)

  -- Recursive implementation with termination proof
  let rec apply_steps (step : ℕ) (state : (HopfieldNetwork R U).State) :
    PMF ((HopfieldNetwork R U).State) :=
    if h : step ≥ steps then
      PMF.pure state
    else
      PMF.bind (NN.State.gibbsSamplingStep wθ (temp_schedule step) state) (apply_steps (step+1))
  termination_by steps - step
  decreasing_by {
    have : step < steps := by exact not_le.mp h
    have : steps - (step + 1) < steps - step := by
      rw [Nat.sub_succ]
      simp_all only [ge_iff_le, not_le, Nat.pred_eq_sub_one, tsub_lt_self_iff, tsub_pos_iff_lt, Nat.lt_one_iff,
        pos_of_gt, and_self]
    exact this
  }

  apply_steps 0 initial_state

/-- Given a HopfieldNetwork with parameters `wθ` and temperature `T`, computes the acceptance probability
for transitioning from a `current` state to a `proposed` state according to the Metropolis-Hastings algorithm.

* If the energy difference (ΔE) is negative or zero, returns 1.0 (always accepts the transition)
* If the energy difference is positive, returns exp(-ΔE/T) following the Boltzmann distribution
-/
noncomputable def NN.State.acceptanceProbability
  {R U : Type} [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ)
  (current : (HopfieldNetwork R U).State) (proposed : (HopfieldNetwork R U).State) : ℝ :=
  let energy_diff := proposed.E wθ - current.E wθ
  if energy_diff ≤ 0 then
    1.0  -- Always accept if energy decreases
  else
    Real.exp (-energy_diff / T)  -- Accept with probability e^(-ΔE/T) if energy increases

/-- The partition function for a Hopfield network, defined as the sum over all possible states
of the Boltzmann factor `exp(-E/T)`.
-/
noncomputable def NN.State.partitionFunction
  {R U : Type} [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) : ℝ :=
  ∑ s : (HopfieldNetwork R U).State, Real.exp (-s.E wθ / T)

/-- Metropolis-Hastings single step for Hopfield networks --/
noncomputable def NN.State.metropolisHastingsStep
  {R U : Type} [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s : (HopfieldNetwork R U).State)
  : PMF ((HopfieldNetwork R U).State) :=
  -- Uniform random selection of neuron
  let neuron_pmf : PMF U :=
    PMF.ofFintype (λ _ => (1 : ENNReal) / (Fintype.card U : ENNReal))
      (by
        rw [Finset.sum_const, Finset.card_univ]
        rw [ENNReal.div_eq_inv_mul]
        simp only [mul_one]
        have h : (Fintype.card U : ENNReal) ≠ 0 := by
          simp [Fintype.card_pos_iff.mpr inferInstance]
        have h_top : (Fintype.card U : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
        rw [← ENNReal.mul_inv_cancel h h_top]
        simp_all only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true, ENNReal.natCast_ne_top,
          nsmul_eq_mul])

  -- Create proposed state by flipping a randomly selected neuron
  let propose : U → PMF ((HopfieldNetwork R U).State) := λ u =>
    let flipped_state :=
      if s.act u = 1 then  -- Assuming 1 and -1 as valid activation values
        NN.State.updateNeuron s u (-1) (by exact Or.inr rfl)
      else
        NN.State.updateNeuron s u 1 (by exact Or.inl rfl)

    let p := NN.State.acceptanceProbability wθ T s flipped_state

    -- Make acceptance decision
    PMF.bind (NN.State.metropolisDecision (R := R) (U := U) p) (λ accept =>
      if accept then PMF.pure flipped_state else PMF.pure s)

  -- Combine neuron selection with state proposal
  PMF.bind neuron_pmf propose

/-- Multiple steps of Metropolis-Hastings algorithm for Hopfield networks --/
noncomputable def NN.State.metropolisHastingsSteps
  {R U : Type} [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (steps : ℕ) (s : (HopfieldNetwork R U).State)
  : PMF ((HopfieldNetwork R U).State) :=
  match steps with
  | 0 => PMF.pure s
  | steps+1 => PMF.bind (metropolisHastingsSteps wθ T steps s) $ λ s' =>
                NN.State.metropolisHastingsStep wθ T s'

/-- The Boltzmann (Gibbs) distribution over neural network states --/
noncomputable def boltzmannDistribution {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) : ((HopfieldNetwork R U).State → ℝ) :=
  λ s => Real.exp (-s.E wθ / T) / NN.State.partitionFunction wθ T

/-- The transition probability matrix for Gibbs sampling --/
noncomputable def gibbsTransitionProb {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s s' : (HopfieldNetwork R U).State) : ℝ :=
  ENNReal.toReal ((NN.State.gibbsSamplingStep wθ T s) s')

/-- The transition probability matrix for Metropolis-Hastings --/
noncomputable def metropolisTransitionProb {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s s' : (HopfieldNetwork R U).State) : ℝ :=
  ENNReal.toReal ((NN.State.metropolisHastingsStep wθ T s) s')

/-- Total variation distance between probability distributions --/
noncomputable def total_variation_distance {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (μ ν : (HopfieldNetwork R U).State → ℝ) : ℝ :=
  (1/2) * ∑ s : (HopfieldNetwork R U).State, |μ s - ν s|

/-- When states differ at exactly one site, we can identify that site --/
@[simp]
lemma single_site_difference {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s s' : (HopfieldNetwork R U).State)
  (h : s ≠ s' ∧ ∃ u : U, ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∃! u : U, s.act u ≠ s'.act u := by
  -- Decompose the hypothesis into non-equality and the existence statement
  obtain ⟨s_neq, hu_all⟩ := h
  obtain ⟨u, hu⟩ := hu_all

  -- Show that states must differ at u
  have diff_at_u : s.act u ≠ s'.act u := by {
    by_contra h_eq
    -- If s.act u = s'.act u then for every v we have equality
    have all_same : ∀ v, s.act v = s'.act v := by {
      intro v
      by_cases hv : v = u
      { rw [hv, h_eq]}
      { exact hu v hv }
    }
    -- This implies s = s', which contradicts s ≠ s'
    have s_eq : s = s' := State.ext all_same
    exact s_neq s_eq
  }
  use u
  constructor
  { exact diff_at_u }
  { intros v h_diff
    by_contra h_v
    -- If v is not the unique differing site then s.act v = s'.act v by the same argument
    have eq_v : s.act v = s'.act v := by {
      by_cases hv : v = u
      { rw [hv]; exact hu u fun a ↦ h_diff (hu v h_v) }
      { exact hu v hv }
    }
    exact h_diff eq_v }

/-- States that are equal at all sites are equal --/
@[simp]
lemma state_equality_from_sites {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s s' : (HopfieldNetwork R U).State)
  (h : ∀ u : U, s.act u = s'.act u) : s = s' := by
  apply State.ext
  exact h

/-- The updateNeuron function only changes the specified neuron, leaving others unchanged --/
@[simp]
lemma updateNeuron_preserves {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U]
  (s : (HopfieldNetwork R U).State) (v w : U) (val : R) (hval : (HopfieldNetwork R U).pact val) :
  w ≠ v → (NN.State.updateNeuron s v val hval).act w = s.act w := by
  intro h_neq
  unfold NN.State.updateNeuron
  exact if_neg h_neq

/-- For Gibbs updates, given the normalization and probabilities, the sum of normalized probabilities equals 1 --/
@[simp]
lemma gibbs_probs_sum_one {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s : (HopfieldNetwork R U).State) (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (v : U) :
  let local_field := s.net wθ v
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  let norm_probs := λ b => probs b / total

  ∑ b : Bool, norm_probs b = 1 := by
  intro local_field probs total norm_probs

  have h_sum : ∑ b : Bool, probs b / total = (probs true + probs false) / total := by
    simp only [Fintype.sum_bool]
    exact ENNReal.div_add_div_same

  rw [h_sum]

  have h_total_ne_zero : total ≠ 0 := by
    simp only [total, probs, ne_eq]
    intro h_zero
    have h1 : ENNReal.ofReal (Real.exp (local_field * 1 / T)) > 0 := by
      apply ENNReal.ofReal_pos.mpr
      apply Real.exp_pos
    have h2 : ENNReal.ofReal (Real.exp (local_field * (-1) / T)) > 0 := by
      apply ENNReal.ofReal_pos.mpr
      apply Real.exp_pos
    have h_sum_zero : ENNReal.ofReal (Real.exp (local_field * 1 / T)) +
                     ENNReal.ofReal (Real.exp (local_field * (-1) / T)) = 0 := h_zero
    exact h1.ne' (add_eq_zero.mp h_sum_zero).1

  have h_total_ne_top : total ≠ ⊤ := by
    simp [total, probs]

  exact ENNReal.div_self h_total_ne_zero h_total_ne_top

/-- The function that maps boolean values to states in Gibbs sampling --/
def gibbs_bool_to_state_map {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U]
  (s : (HopfieldNetwork R U).State) (v : U) : Bool → (HopfieldNetwork R U).State :=
  λ b => if b then
    NN.State.updateNeuron s v 1 (by exact mul_self_eq_mul_self_iff.mp rfl)
  else
    NN.State.updateNeuron s v (-1) (by exact AffineMap.lineMap_eq_lineMap_iff.mp rfl)

/-- The total normalization constant for Gibbs sampling is positive --/
@[simp]
lemma gibbs_total_positive {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))

  probs true + probs false ≠ 0 := by
  intro probs
  simp only [ne_eq]
  intro h_zero

  have h1 : ENNReal.ofReal (Real.exp (local_field * 1 / T)) > 0 := by
    apply ENNReal.ofReal_pos.mpr
    apply Real.exp_pos

  have h2 : ENNReal.ofReal (Real.exp (local_field * (-1) / T)) > 0 := by
    apply ENNReal.ofReal_pos.mpr
    apply Real.exp_pos

  have h_sum_zero : ENNReal.ofReal (Real.exp (local_field * 1 / T)) +
                   ENNReal.ofReal (Real.exp (local_field * (-1) / T)) = 0 := h_zero

  have h_both_zero : ENNReal.ofReal (Real.exp (local_field * 1 / T)) = 0 ∧
                    ENNReal.ofReal (Real.exp (local_field * (-1) / T)) = 0 :=
    add_eq_zero.mp h_sum_zero

  exact h1.ne' h_both_zero.1

/-- The total normalization constant for Gibbs sampling is not infinity --/
@[simp]
lemma gibbs_total_not_top {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))

  probs true + probs false ≠ ⊤ := by
  intro probs
  simp [probs]

/-- For a positive PMF.map application, there exists a preimage with positive probability --/
lemma pmf_map_pos_implies_preimage {α β : Type} [Fintype α] [DecidableEq β]
  {p : α → ENNReal} (h_pmf : ∑ a, p a = 1) (f : α → β) (y : β) :
  (PMF.map f (PMF.ofFintype p h_pmf)) y > 0 →
  ∃ x : α, p x > 0 ∧ f x = y := by
  intro h_pos
  simp only [PMF.map_apply] at h_pos

  have h_eqn : (∑' (a : α), if y = f a then (PMF.ofFintype p h_pmf) a else 0) =
               ∑ a ∈ filter (fun a ↦ f a = y) univ, p a := by
    -- First handle the if-then-else structure
    have h1 : (∑' (a : α), if y = f a then (PMF.ofFintype p h_pmf) a else 0) =
              (∑' (a : α), if f a = y then (PMF.ofFintype p h_pmf) a else 0) := by
      apply tsum_congr
      intro a
      by_cases h : f a = y
      · simp [h]
      · simp [h, Ne.symm h]

    -- Now apply the filter sum lemma
    rw [h1]

    -- For finite types, tsum can be converted to a sum over the universe
    have h2 : (∑' (a : α), if f a = y then (PMF.ofFintype p h_pmf) a else 0) =
              ∑ a ∈ filter (fun a ↦ f a = y) univ, (PMF.ofFintype p h_pmf) a := by
      -- For finite types, tsum equals sum over univ
      have tsum_eq_sum : (∑' (a : α), if f a = y then (PMF.ofFintype p h_pmf) a else 0) =
                         (∑ a ∈ univ, if f a = y then (PMF.ofFintype p h_pmf) a else 0) := by
        exact tsum_fintype fun b ↦ if f b = y then (PMF.ofFintype p h_pmf) b else 0

      -- Then use a sum_filter property
      rw [tsum_eq_sum]
      exact Eq.symm (sum_filter (fun a ↦ f a = y) ⇑(PMF.ofFintype p h_pmf))

    rw [h2]

    -- Convert PMF.ofFintype back to p
    apply Finset.sum_congr rfl
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    simp [PMF.ofFintype_apply]

  simp_all only [PMF.ofFintype_apply, tsum_eq_filter_sum, gt_iff_lt, filter_sum_pos_iff_exists_pos,
    pmf_map_pos_iff_exists_pos]

/-- For states with positive Gibbs update probability, there exists a boolean variable that
    determines whether the state has activation 1 or -1 at the updated neuron --/
lemma gibbsUpdate_exists_bool {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s : (HopfieldNetwork R U).State) (v : U)
  (s_next : (HopfieldNetwork R U).State) :
  (NN.State.gibbsUpdateSingleNeuron s wθ T v) s_next > 0 →
  ∃ b : Bool, s_next = gibbs_bool_to_state_map s v b := by
  intro h_prob_pos

  let local_field := s.net wθ v
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  let norm_probs := λ b => probs b / total

  -- Extract mapping structure from PMF.map
  unfold NN.State.gibbsUpdateSingleNeuron at h_prob_pos

  -- Use our helper lemmas
  have h_total_ne_zero := @gibbs_total_positive R U _ _ _ _ _ local_field T
  have h_total_ne_top := @gibbs_total_not_top R U _ _ _ _ _ local_field T
  have h_sum_one := @gibbs_probs_sum_one R U _ _ _ _ _ s wθ T v

  -- Apply the preimage lemma
  unfold gibbs_bool_to_state_map

  -- Apply pmf_map_pos_implies_preimage to get the preimage
  have ⟨b, h_prob_b, h_map_b⟩ := pmf_map_pos_implies_preimage h_sum_one
    (λ b => if b then
      NN.State.updateNeuron s v 1 (by exact mul_self_eq_mul_self_iff.mp rfl)
    else
      NN.State.updateNeuron s v (-1) (by exact AffineMap.lineMap_eq_lineMap_iff.mp rfl))
    s_next h_prob_pos

  -- Use the preimage to construct our result
  use b
  exact id (Eq.symm h_map_b)

/-- For states with positive probability under gibbsUpdateSingleNeuron,
    they must be one of exactly two possible states (with neuron v set to 1 or -1) --/
@[simp]
lemma gibbsUpdate_possible_states {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s : (HopfieldNetwork R U).State) (v : U)
  (s_next : (HopfieldNetwork R U).State) :
  (NN.State.gibbsUpdateSingleNeuron s wθ T v) s_next > 0 →
  s_next = NN.State.updateNeuron s v 1 (by exact mul_self_eq_mul_self_iff.mp rfl) ∨
  s_next = NN.State.updateNeuron s v (-1) (by exact AffineMap.lineMap_eq_lineMap_iff.mp rfl) := by
  intro h_prob_pos

  -- Use the helper lemma to get the boolean
  obtain ⟨b, h_eq⟩ := gibbsUpdate_exists_bool wθ T s v s_next h_prob_pos

  -- Do case analysis on the boolean to determine which state we have
  cases b with
  | false =>
    right
    unfold gibbs_bool_to_state_map at h_eq
    rw [@Std.Tactic.BVDecide.Normalize.if_eq_cond] at h_eq
    exact h_eq
  | true =>
    left
    unfold gibbs_bool_to_state_map at h_eq
    rw [@Std.Tactic.BVDecide.Normalize.if_eq_cond] at h_eq
    exact h_eq

/-- Gibbs update preserves states at non-updated sites --/
@[simp]
lemma gibbsUpdate_preserves_other_neurons {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s : (HopfieldNetwork R U).State)
  (v w : U) (h_neq : w ≠ v) :
  ∀ s_next, (NN.State.gibbsUpdateSingleNeuron s wθ T v) s_next > 0 →
    s_next.act w = s.act w := by
  intro s_next h_prob_pos

  -- Use the helper lemma to determine the structure of s_next
  have h_structure := gibbsUpdate_possible_states wθ T s v s_next h_prob_pos

  -- Handle both possible cases
  cases h_structure with
  | inl h_pos =>
    -- If s_next has v = 1, then all other neurons remain unchanged
    rw [h_pos]
    exact updateNeuron_preserves s v w 1 (by exact mul_self_eq_mul_self_iff.mp rfl) h_neq
  | inr h_neg =>
    -- If s_next has v = -1, then all other neurons remain unchanged
    rw [h_neg]
    exact updateNeuron_preserves s v w (-1) (by exact AffineMap.lineMap_eq_lineMap_iff.mp rfl) h_neq


/-- For states differing at only one site, that site must be u --/
@[simp]
lemma single_site_difference_unique {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) (h_diff : s ≠ s') :
  ∃! v : U, s.act v ≠ s'.act v := by
  use u
  constructor
  · by_contra h_eq
    have all_equal : ∀ v, s.act v = s'.act v := by
      intro v
      by_cases hv : v = u
      · rw [hv]
        exact h_eq
      · exact h v hv
    exact h_diff (State.ext all_equal)
  · intro v hv
    by_contra h_neq
    have v_diff_u : v ≠ u := by
      by_contra h_eq
      rw [h_eq] at hv
      contradiction
    exact hv (h v v_diff_u)

/-- Given a single-site difference, the destination state is an update of the source state --/
@[simp]
lemma single_site_is_update {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s s' : (HopfieldNetwork R U).State) (u : U)
  (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) := by
  apply State.ext
  intro v
  by_cases hv : v = u
  · rw [hv]
    unfold NN.State.updateNeuron
    exact Eq.symm (if_pos rfl)
  · unfold NN.State.updateNeuron
    rw [← h v hv]
    exact Eq.symm (if_neg hv)

/-- The probability mass function for a binary choice (true/false) has sum 1 when properly normalized --/
@[simp]
lemma pmf_binary_norm_sum_one
  (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  let norm_probs := λ b => probs b / total

  ∑ b : Bool, norm_probs b = 1 := by
  intro probs total norm_probs
  -- Convert sum over normalized probabilities
  have h_sum : ∑ b : Bool, probs b / total = (probs true + probs false) / total := by
    simp only [Fintype.sum_bool]
    exact ENNReal.div_add_div_same

  -- Show the sum equals 1
  rw [h_sum]

  -- Show total is positive (not zero)
  have h_total_ne_zero : total ≠ 0 := by
    simp only [total, probs, ne_eq]
    intro h_zero
    have h1 : ENNReal.ofReal (Real.exp (local_field * 1 / T)) > 0 := by
      apply ENNReal.ofReal_pos.mpr
      apply Real.exp_pos
    have h2 : ENNReal.ofReal (Real.exp (local_field * (-1) / T)) > 0 := by
      apply ENNReal.ofReal_pos.mpr
      apply Real.exp_pos
    have h_sum_zero : ENNReal.ofReal (Real.exp (local_field * 1 / T)) +
                      ENNReal.ofReal (Real.exp (local_field * (-1) / T)) = 0 := h_zero
    have h_both_zero : ENNReal.ofReal (Real.exp (local_field * 1 / T)) = 0 ∧
                      ENNReal.ofReal (Real.exp (local_field * (-1) / T)) = 0 := by
      exact add_eq_zero.mp h_sum_zero
    exact h1.ne' h_both_zero.1

  -- Show total is not top
  have h_total_ne_top : total ≠ ⊤ := by
    simp [total, probs]

  -- Division by self is 1
  exact ENNReal.div_self h_total_ne_zero h_total_ne_top

/-- When updating a neuron with a value that equals one of the standard values (1 or -1),
    the result equals the standard update --/
@[simp]
lemma update_neuron_equiv {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U]
  (s : (HopfieldNetwork R U).State) (u : U) (val : R)
  (hval : (HopfieldNetwork R U).pact val) :
  val = 1 → NN.State.updateNeuron s u val hval =
    NN.State.updateNeuron s u 1 (by exact Or.inl rfl) := by
  intro h_val
  apply State.ext
  intro v
  unfold NN.State.updateNeuron
  by_cases h_v : v = u
  · exact ite_congr rfl (fun a ↦ h_val) (congrFun rfl)
  · exact ite_congr rfl (fun a ↦ h_val) (congrFun rfl)

/-- Updates with different activation values produce different states --/
@[simp]
lemma different_activation_different_state {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U]
  (s : (HopfieldNetwork R U).State) (u : U) :
  NN.State.updateNeuron s u 1 (by exact Or.inl rfl) ≠
  NN.State.updateNeuron s u (-1) (by exact Or.inr rfl) := by
  intro h_contra
  have h_values :
    (NN.State.updateNeuron s u 1 (by exact Or.inl rfl)).act u =
    (NN.State.updateNeuron s u (-1) (by exact Or.inr rfl)).act u := by
    congr

  unfold NN.State.updateNeuron at h_values
  simp at h_values
  have : (1 : R) ≠ -1 := by
    simp only [ne_eq]
    norm_num
  exact this h_values

/-- Two neuron updates at the same site are equal if and only if their new values are equal --/
@[simp]
lemma update_neuron_eq_iff {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U]
  (s : (HopfieldNetwork R U).State) (u : U) (val₁ val₂ : R)
  (hval₁ : (HopfieldNetwork R U).pact val₁) (hval₂ : (HopfieldNetwork R U).pact val₂) :
  NN.State.updateNeuron s u val₁ hval₁ = NN.State.updateNeuron s u val₂ hval₂ ↔ val₁ = val₂ := by
  constructor
  · intro h
    -- If states are equal, their activations at u must be equal
    have h_act : (NN.State.updateNeuron s u val₁ hval₁).act u = (NN.State.updateNeuron s u val₂ hval₂).act u := by
      rw [h]
    -- Simplify to get val₁ = val₂
    unfold NN.State.updateNeuron at h_act
    simp at h_act
    exact h_act
  · intro h_val
    -- If val₁ = val₂, the resulting states must be equal
    subst h_val
    apply State.ext
    intro v
    by_cases hv : v = u
    · subst hv; unfold NN.State.updateNeuron; exact rfl
    · unfold NN.State.updateNeuron; exact rfl

/-- Determines when a boolean-indexed update equals a specific update --/
@[simp]
lemma bool_update_eq_iff {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U]
  (s : (HopfieldNetwork R U).State) (u : U) (b : Bool) (val : R)
  (hval : (HopfieldNetwork R U).pact val) :
  (if b then NN.State.updateNeuron s u 1 (by exact Or.inl rfl)
   else NN.State.updateNeuron s u (-1) (by exact Or.inr rfl)) =
  NN.State.updateNeuron s u val hval ↔
  (b = true ∧ val = 1) ∨ (b = false ∧ val = -1) := by
  cases b
  · -- Case: b = false
    simp only [Bool.false_eq_true, ↓reduceIte, update_neuron_eq_iff, false_and, true_and, false_or]
    constructor
    · intro h
      -- Apply update_neuron_eq_iff to get -1 = val
      have h_val_eq := (update_neuron_eq_iff s u (-1) val (by exact Or.inr rfl) hval).mpr h
      exact id (Eq.symm h)
    · intro h_cases
      cases h_cases
      trivial
      -- This is an impossible case since b = false can't satisfy b = true ∧ val = 1

  · -- Case: b = true
    simp only [↓reduceIte, update_neuron_eq_iff, true_and, Bool.true_eq_false, false_and, or_false]
    constructor
    · intro h
      -- Apply update_neuron_eq_iff to get 1 = val
      have h_val_eq := (update_neuron_eq_iff s u 1 val (by exact Or.inl rfl) hval).mpr h
      -- Now we need to construct (b = true ∧ val = 1) as the left side of an Or
      exact id (Eq.symm h)
    · intro h_cases
      cases h_cases
      · -- Case: b = true ∧ val = 1
        exact rfl


/-- When filtering a PMF with binary support to states matching a given state's update,
    the result reduces to a singleton if the update site matches --/
@[simp]
lemma pmf_filter_update_neuron {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U]
  (s : (HopfieldNetwork R U).State) (u : U) (val : R)
  (hval : (HopfieldNetwork R U).pact val) :
  let f : Bool → (HopfieldNetwork R U).State := λ b =>
    if b then NN.State.updateNeuron s u 1 (by exact Or.inl rfl)
    else NN.State.updateNeuron s u (-1) (by exact Or.inr rfl)

  filter (fun b => f b = NN.State.updateNeuron s u val hval) univ =
    if val = 1 then {true} else
    if val = -1 then {false} else ∅ := by
  intro f

  -- Apply our boolean matching lemma to the filter condition
  -- First establish the filter condition for all booleans
  have filter_cond : ∀ b, f b = NN.State.updateNeuron s u val hval ↔
    (b = true ∧ val = 1) ∨ (b = false ∧ val = -1) := by
    intro b
    exact bool_update_eq_iff s u b val hval

  -- Now use cases on the possible values
  by_cases h1 : val = 1
  · -- Case val = 1
    simp only [h1]
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_singleton]

    -- Directly apply the bool_update_eq_iff lemma
    rw [@bool_update_eq_iff]
    simp [h1]
    cases b
    · -- b = false
      simp [Bool.false_eq_true]
      norm_num
    · -- b = true
      simp
  · by_cases h2 : val = -1
    · -- Case val = -1
      simp only [h1, h2]
      ext b
      simp only [mem_filter, mem_univ, true_and, mem_singleton]

      -- Directly apply the bool_update_eq_iff lemma
      rw [@bool_update_eq_iff]
      simp [h1, h2]
      cases b
      · -- b = false
        simp [Bool.false_eq_true]
        -- When val = -1, the if-statement simplifies to {false}
        norm_num
      · -- b = true
        simp only [true_and, Bool.true_eq_false, or_false]
        have one_ne_neg_one : (1 : R) ≠ (-1 : R) := by norm_num
        norm_num
    · -- Case neither val = 1 nor val = -1
      simp only [h1, h2]
      ext b
      simp only [mem_filter, mem_univ, true_and]

      -- Apply bool_update_eq_iff to reduce the filter condition
      rw [@bool_update_eq_iff]
      simp [h1, h2]


/-- The normalization factor in Gibbs sampling is the sum of Boltzmann factors for both possible states --/
@[simp]
lemma gibbs_normalization_factor {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false

  total = ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T)) := by
  intro probs total
  simp only [probs, total]
  simp [mul_one_div, one_div_neg_one_eq_neg_one]


/-- The probability mass assigned to true when using Gibbs sampling --/
@[simp]
lemma gibbs_prob_true {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  let norm_probs := λ b => probs b / total

  norm_probs true = ENNReal.ofReal (Real.exp (local_field / T)) /
    (ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))) := by
  intro probs total norm_probs
  simp only [norm_probs, probs]
  have h_total : total = ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T)) := by
    simp [total, probs]
  rw [h_total]
  congr
  simp [mul_one_div]

/-- The probability mass assigned to false when using Gibbs sampling --/
@[simp]
lemma gibbs_prob_false {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  let norm_probs := λ b => probs b / total

  norm_probs false = ENNReal.ofReal (Real.exp (-local_field / T)) /
    (ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))) := by
  intro probs total norm_probs
  simp only [norm_probs, probs]
  have h_total : total = ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T)) := by
    simp [total, probs]
  rw [h_total]
  congr
  simp [one_div_neg_one_eq_neg_one]

/-- For a PMF over binary values mapped to states, the probability of a specific state
    equals the probability of its corresponding binary value --/
@[simp]
lemma pmf_map_binary_state {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s : (HopfieldNetwork R U).State) (u : U) (b : Bool) (p : Bool → ENNReal) (h_sum : ∑ b, p b = 1) :
  let f : Bool → (HopfieldNetwork R U).State := λ b =>
    if b then NN.State.updateNeuron s u 1 (by exact Or.inl rfl)
    else NN.State.updateNeuron s u (-1) (by exact Or.inr rfl)

  PMF.map f (PMF.ofFintype p h_sum) (f b) = p b := by
  intro f
  simp only [PMF.map_apply]

  -- Show that f is injective (maps false and true to different states)
  have h_inj : ∀ b₁ b₂ : Bool, b₁ ≠ b₂ → f b₁ ≠ f b₂ := by
    intro b₁ b₂ hneq
    unfold f
    cases b₁ <;> cases b₂
    · contradiction
    · -- Case: b₁ = false, b₂ = true
      simp [Bool.false_eq_true]  -- Simplify the if-then-else expressions
      -- Now we're proving: NN.State.updateNeuron s u (-1) ... ≠ NN.State.updateNeuron s u 1 ...
      apply Ne.symm
      -- Show states with different activation values are different using update_neuron_eq_iff
      have h_values_diff : (1 : R) ≠ (-1 : R) := by
        simp only [ne_eq]
        norm_num
      exact h_values_diff
    · -- Case: b₁ = true, b₂ = false
      dsimp only [↓dreduceIte, Bool.false_eq_true, ne_eq]  -- Simplify the if-then-else expressions
      -- Show states with different activation values are different using update_neuron_eq_iff
      have h_values_diff : (1 : R) ≠ (-1 : R) := by
        simp only [ne_eq]
        norm_num
      exact (update_neuron_eq_iff s u 1 (-1) (by exact Or.inl rfl) (by exact Or.inr rfl)).not.mpr h_values_diff
    · contradiction

  -- For a filtered sum over Bool, there's only one element that maps to f b, and that's b itself
  have h_unique : ∀ b' : Bool, f b' = f b ↔ b' = b := by
    intro b'
    by_cases h : b' = b
    · -- Case: b' = b
      constructor
      · -- Direction: f b' = f b → b' = b
        intro _
        exact h
      · -- Direction: b' = b → f b' = f b
        intro _
        rw [h]
    · -- Case: b' ≠ b
      have : f b' ≠ f b := h_inj b' b h
      constructor
      · -- Direction: f b' = f b → b' = b
        intro h_eq
        contradiction
      · -- Direction: b' = b → f b' = f b
        intro h_eq
        contradiction

  -- Convert tsum to a sum over elements satisfying the filter condition
  have h_filter : (∑' (b' : Bool), if f b = f b' then (PMF.ofFintype p h_sum) b' else 0) =
                 (PMF.ofFintype p h_sum) b := by
    -- Convert tsum to a finite sum over Bool
    rw [tsum_fintype]

    -- We'll use the fact that f is injective, so f b = f b' iff b = b'
    have h_iff : ∀ b' : Bool, f b = f b' ↔ b = b' := by
      intro b'
      constructor
      · -- Direction: f b = f b' → b = b'
        intro h_eq
        by_contra h_neq
        have h_different : f b ≠ f b' := by
          apply h_inj
          exact h_neq
        contradiction
      · -- Direction: b = b' → f b = f b'
        intro h_eq
        rw [h_eq]

    -- Using this characterization, we can simplify the sum
    have h_eq : ∑ b' : Bool, ite (f b = f b') ((PMF.ofFintype p h_sum) b') 0 =
                ∑ b' : Bool, ite (b = b') ((PMF.ofFintype p h_sum) b') 0 := by
      apply Finset.sum_congr rfl
      intro b' _
      -- Check if the conditions are equivalent
      have hcond : (f b = f b') ↔ (b = b') := h_iff b'
      simp only [hcond]

    -- Apply the equality
    rw [h_eq]

    -- Sum with if condition based on equality is just the value at the equal element
    simp [h_eq, Finset.sum_ite_eq]

  -- Apply our filtered sum result
  rw [@tsum_bool]

  -- PMF.ofFintype applies p to each element
  simp only [PMF.ofFintype_apply]

  -- Case analysis on b
  cases b
  · -- Case: b = false
    have h_false_eq : f false = f false := rfl
    have h_true_neq : f false ≠ f true := by
      apply h_inj
      simp only [ne_eq, Bool.false_eq_true, not_false_eq_true]

    simp only [h_false_eq, h_true_neq, if_true, if_false, add_zero]
  · -- Case: b = true
    have h_true_eq : f true = f true := rfl
    have h_false_neq : f true ≠ f false := by
      apply h_inj
      simp only [ne_eq, Bool.true_eq_false, not_false_eq_true]

    simp only [h_true_eq, h_false_neq, if_true, if_false, zero_add]

/-- A specialized version of the previous lemma for the case where the state is an update with new_val = 1 --/
@[simp]
lemma pmf_map_update_one {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s : (HopfieldNetwork R U).State) (u : U) (p : Bool → ENNReal) (h_sum : ∑ b, p b = 1) :
  let f : Bool → (HopfieldNetwork R U).State := λ b =>
    if b then NN.State.updateNeuron s u 1 (by exact Or.inl rfl)
    else NN.State.updateNeuron s u (-1) (by exact Or.inr rfl)

  PMF.map f (PMF.ofFintype p h_sum) (NN.State.updateNeuron s u 1 (by exact Or.inl rfl)) = p true := by
  intro f
  apply pmf_map_binary_state s u true p h_sum

/-- A specialized version for the case where the state is an update with new_val = -1 --/
@[simp]
lemma pmf_map_update_neg_one {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s : (HopfieldNetwork R U).State) (u : U) (p : Bool → ENNReal) (h_sum : ∑ b, p b = 1) :
  let f : Bool → (HopfieldNetwork R U).State := λ b =>
    if b then NN.State.updateNeuron s u 1 (by exact Or.inl rfl)
    else NN.State.updateNeuron s u (-1) (by exact Or.inr rfl)

  PMF.map f (PMF.ofFintype p h_sum) (NN.State.updateNeuron s u (-1) (by exact Or.inr rfl)) = p false := by
  intro f
  apply pmf_map_binary_state s u false p h_sum

/-- When dividing ENNReal values that come from real numbers, the result equals
    the ENNReal value of the division of the original real numbers.
--/
@[simp]
lemma ENNReal.div_eq_ofReal_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
  ENNReal.ofReal a / ENNReal.ofReal b = ENNReal.ofReal (a / b) := by
  -- The ENNReal.ofReal function preserves ordering and arithmetic operations
  -- when dealing with finite, non-negative real numbers

  -- b > 0 ensures division is well-defined in both domains
  have hb_ne_zero : ENNReal.ofReal b ≠ 0 := by
    simp only [ne_eq, ofReal_eq_zero, not_le]
    exact hb

  -- b > 0 ensures ENNReal.ofReal b ≠ ∞
  have hb_ne_top : ENNReal.ofReal b ≠ ⊤ := ENNReal.ofReal_ne_top

  -- Apply the division definition for ENNReal
  have h_div : ENNReal.toReal (ENNReal.ofReal a / ENNReal.ofReal b) =
               ENNReal.toReal (ENNReal.ofReal a) / ENNReal.toReal (ENNReal.ofReal b) := by
    exact toReal_div (ENNReal.ofReal a) (ENNReal.ofReal b)

  rw [ofReal_div_of_pos hb]

/-- Expresses a ratio of exponentials in terms of the sigmoid function format.
--/
@[simp]
lemma exp_ratio_to_sigmoid (x : ℝ) :
  Real.exp x / (Real.exp x + Real.exp (-x)) = 1 / (1 + Real.exp (-2 * x)) := by
  -- Divide both numerator and denominator by exp(x)
  have h_denom : Real.exp x + Real.exp (-x) = Real.exp x * (1 + Real.exp (-2 * x)) := by
    -- Expand the right-hand side first
    have rhs_expanded : Real.exp x * (1 + Real.exp (-2 * x)) = Real.exp x + Real.exp x * Real.exp (-2 * x) := by
      rw [mul_add, mul_one]

    -- Show that Real.exp x * Real.exp (-2 * x) = Real.exp (-x)
    have exp_identity : Real.exp x * Real.exp (-2 * x) = Real.exp (-x) := by
      rw [← Real.exp_add]
      congr
      ring

    -- Combine the results
    rw [rhs_expanded, exp_identity]

  -- Substitute and simplify
  rw [h_denom, div_mul_eq_div_div]
  have h_exp_ne_zero : Real.exp x ≠ 0 := by exact ne_of_gt (Real.exp_pos x)
  field_simp

/-- Local field is the weighted sum of incoming activations --/
@[simp]
lemma local_field_eq_weighted_sum {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) :
  s.net wθ u = ∑ v ∈ univ.erase u, wθ.w u v * s.act v := by
  -- Unfold the definition of net
  unfold NeuralNetwork.State.net

  -- Use properties of HopfieldNetwork fnet
  have h_not_adj_self : ¬(HopfieldNetwork R U).Adj u u := by simp [HopfieldNetwork]

  -- For Hopfield networks, fnet is defined as sum over v ≠ u
  -- Unfold the definition of fnet for Hopfield networks
  unfold NeuralNetwork.fnet HopfieldNetwork

  -- Use the definition of adjacency in Hopfield networks: v ≠ u
  simp only [ne_eq]

  -- Show that the filtered sum is equal to sum over univ.erase u
  have sum_filter_eq : ∑ v ∈ filter (fun v => v ≠ u) univ, wθ.w u v * s.act v =
                       ∑ v ∈ univ.erase u, wθ.w u v * s.act v := by
    apply Finset.sum_congr
    · -- Show sets are equal
      ext v
      simp only [mem_filter, mem_erase, mem_univ, true_and, and_true]
    · -- Functions are equal on the sets
      intro v _
      rw [@OrderedCommSemiring.mul_comm]

  exact sum_filter_eq

/-- Converts the ratio of Boltzmann factors to ENNReal sigmoid form.
--/
@[simp]
lemma ENNReal_exp_ratio_to_sigmoid (x : ℝ) :
  ENNReal.ofReal (Real.exp x) /
  (ENNReal.ofReal (Real.exp x) + ENNReal.ofReal (Real.exp (-x))) =
  ENNReal.ofReal (1 / (1 + Real.exp (-2 * x))) := by
  -- We need to ensure the division is well-defined in both ENNReal and ℝ
  have num_pos : 0 ≤ Real.exp x := le_of_lt (Real.exp_pos x)
  have denom_pos : 0 < Real.exp x + Real.exp (-x) := by
    apply add_pos
    · exact Real.exp_pos x
    · exact Real.exp_pos (-x)

  -- First convert the ENNReal division to ofReal of a real division
  have h1 : ENNReal.ofReal (Real.exp x) /
            (ENNReal.ofReal (Real.exp x) + ENNReal.ofReal (Real.exp (-x))) =
            ENNReal.ofReal (Real.exp x / (Real.exp x + Real.exp (-x))) := by
    -- Division of ENNReal values needs to consider denominator properties
    have denom_ne_zero : ENNReal.ofReal (Real.exp x) + ENNReal.ofReal (Real.exp (-x)) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      intro h
      have h1 : ENNReal.ofReal (Real.exp x) = 0 ∧ ENNReal.ofReal (Real.exp (-x)) = 0 := by
        exact add_eq_zero.mp h
      have h_exp_pos : Real.exp x > 0 := Real.exp_pos x
      have h_ofreal_pos : ENNReal.ofReal (Real.exp x) ≠ 0 := by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact h_exp_pos
      exact h_ofreal_pos h1.1

    have denom_ne_top : ENNReal.ofReal (Real.exp x) + ENNReal.ofReal (Real.exp (-x)) ≠ ⊤ := by
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩

    -- First combine the sum in denominator using ofReal_add
    have h_sum : ENNReal.ofReal (Real.exp x) + ENNReal.ofReal (Real.exp (-x)) =
                 ENNReal.ofReal (Real.exp x + Real.exp (-x)) := by
      -- Both exponentials are non-negative
      have exp_neg_pos : 0 ≤ Real.exp (-x) := le_of_lt (Real.exp_pos (-x))
      exact Eq.symm (ENNReal.ofReal_add num_pos exp_neg_pos)

    rw [h_sum]

    -- Now we can apply ENNReal.div_eq_ofReal_div
    apply ENNReal.div_eq_ofReal_div
    · exact num_pos
    · exact denom_pos

  -- Now use the real-valued identity for the ratio of exponentials
  have h2 : Real.exp x / (Real.exp x + Real.exp (-x)) = 1 / (1 + Real.exp (-2 * x)) := by
    -- Normalize the denominator
    have h_denom : Real.exp x + Real.exp (-x) = Real.exp x * (1 + Real.exp (-2 * x)) := by
      -- Expand and verify the algebraic identity
      have h_exp_diff : Real.exp (-x) = Real.exp x * Real.exp (-2 * x) := by
        rw [← Real.exp_add]
        congr
        ring
      calc Real.exp x + Real.exp (-x)
          = Real.exp x + Real.exp x * Real.exp (-2 * x) := by rw [h_exp_diff]
        _ = Real.exp x * (1 + Real.exp (-2 * x)) := by rw [mul_add, mul_one]

    -- Substitute the normalized denominator and simplify
    rw [h_denom, div_mul_eq_div_div]
    have h_exp_ne_zero : Real.exp x ≠ 0 := by exact ne_of_gt (Real.exp_pos x)
    field_simp

  -- Combine the two results
  rw [h1, h2]

@[simp]
lemma ENNReal.div_ne_top {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ 0) :
  a / b ≠ ⊤ := by
  intro h_top
  -- Using the characterization of division equaling ⊤, we have two cases.
  rw [ENNReal.div_eq_top] at h_top
  rcases h_top with (⟨_, h_right⟩ | ⟨h_left, _⟩);
  -- In either case, one of the assumptions (hb or ha) is contradicted.
  exact hb h_right; exact ha h_left

@[simp]
lemma gibbs_prob_positive {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false

  ENNReal.ofReal (Real.exp (local_field / T)) / total =
    ENNReal.ofReal (1 / (1 + Real.exp (-2 * local_field / T))) := by
  intro probs total

  -- First show that total equals the sum of exponentials
  have h_total : total = ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T)) := by
    simp [total, probs]

  -- Rewrite using this equality
  rw [h_total]

  -- Handle temperature scaling explicitly
  have h_temp : ∀ x, Real.exp (x / T) = Real.exp (x * (1/T)) := by
    intro x
    congr
    field_simp

  rw [h_temp local_field, h_temp (-local_field)]

  -- Now apply the sigmoid transformation with properly scaled argument
  -- Apply the sigmoid transformation directly and handle the format differences
  have h_direct :
    ENNReal.ofReal (Real.exp (local_field * (1 / T))) /
    (ENNReal.ofReal (Real.exp (local_field * (1 / T))) + ENNReal.ofReal (Real.exp (-local_field * (1 / T)))) =
    ENNReal.ofReal (1 / (1 + Real.exp (-2 * local_field / T))) := by
    -- Start with the standard sigmoid transformation
    have h := ENNReal_exp_ratio_to_sigmoid (local_field * (1 / T))

    -- Show that the right-hand side expressions are equivalent
    have h_rhs : -2 * (local_field * (1 / T)) = -2 * local_field / T := by
      field_simp

    -- Rewrite the right-hand side to match our goal format
    rw [h_rhs] at h

    -- Show that the negation inside exp is equivalent
    have neg_equiv : ENNReal.ofReal (Real.exp (-(local_field * (1 / T)))) =
                    ENNReal.ofReal (Real.exp (-local_field * (1 / T))) := by
      congr; ring

    -- Rewrite the left side of h to match our goal format
    rw [neg_equiv] at h
    exact h

  -- Apply the direct proof
  exact h_direct

/-- The probability of setting a neuron to -1 under Gibbs sampling --/
@[simp]
lemma gibbs_prob_negative {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false

  ENNReal.ofReal (Real.exp (-local_field / T)) / total =
  ENNReal.ofReal (1 / (1 + Real.exp (2 * local_field / T))) := by
  intro probs total

  -- First show that total equals the sum of exponentials
  have h_total : total = ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T)) := by
    simp [total, probs]

  -- Rewrite using this equality
  rw [h_total]

  -- We need to directly prove the desired result
  -- First express our goal in terms of the basic sigmoid formula
  have h_basic := ENNReal_exp_ratio_to_sigmoid (-local_field / T)

  -- Simplify the expressions in h_basic
  have h_neg2_neg : -2 * (-local_field / T) = 2 * local_field / T := by ring
  have h_neg_neg : -(-local_field / T) = local_field / T := by ring

  -- Rewrite the components of h_basic with our simplifications
  have h_ratio_final : ENNReal.ofReal (Real.exp (-local_field / T)) /
                       (ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))) =
                       ENNReal.ofReal (1 / (1 + Real.exp (2 * local_field / T))) := by
    -- Start with the basic transformation
    have h := ENNReal_exp_ratio_to_sigmoid (-local_field / T)

    -- Match the desired forms in the numerator and denominator
    have h_exp_neg_neg : ENNReal.ofReal (Real.exp (-(-local_field / T))) =
                         ENNReal.ofReal (Real.exp (local_field / T)) := by congr

    -- Rewrite h to use the correct term
    rw [h_exp_neg_neg] at h

    -- Switch the order of terms in the denominator to match our goal
    have h_comm : ENNReal.ofReal (Real.exp (-local_field / T)) + ENNReal.ofReal (Real.exp (local_field / T)) =
                  ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T)) := by
      rw [add_comm]

    -- Update the right side to use 2*local_field/T
    rw [h_neg2_neg] at h

    -- Apply the commutativity of addition to match exactly
    rw [h_comm] at h
    exact h

  -- Apply our final result
  exact h_ratio_final

-- First, define a lemma about mapping Boolean values to updated states
@[simp]
lemma gibbs_bool_to_state_map_positive {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s : (HopfieldNetwork R U).State) (u : U) (val : R) (hval : (HopfieldNetwork R U).pact val) :
  val = 1 → NN.State.updateNeuron s u val hval =
    NN.State.updateNeuron s u 1 (by exact Or.inl rfl) := by
  intro h_val
  apply State.ext
  intro v
  unfold NN.State.updateNeuron
  by_cases h_v : v = u
  · rw [h_v]
    exact ite_congr rfl (fun a ↦ h_val) (congrFun rfl)
  · simp only [h_v, if_neg]
    rfl

-- Similar lemma for negative case
lemma gibbs_bool_to_state_map_negative {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s : (HopfieldNetwork R U).State) (u : U) (val : R) (hval : (HopfieldNetwork R U).pact val) :
  val = -1 → NN.State.updateNeuron s u val hval =
    NN.State.updateNeuron s u (-1) (by exact Or.inr rfl) := by
  intro h_val
  apply State.ext
  intro v
  unfold NN.State.updateNeuron
  by_cases h_v : v = u
  · -- Case v = u
    rw [h_v]
    dsimp [h_val]; exact congrFun (congrArg (ite (u = u)) h_val) (s.act u)
  · -- Case v ≠ u
    dsimp [h_v]; exact congrFun (congrArg (ite (v = u)) h_val) (s.act v)

-- Lemma for the probability calculation in the positive case
lemma gibbs_prob_positive_case {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s : (HopfieldNetwork R U).State) (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (u : U) :
  let local_field := s.net wθ u
  let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
  let norm_probs := λ b => if b then
                             ENNReal.ofReal (Real.exp (local_field / T)) / Z
                           else
                             ENNReal.ofReal (Real.exp (-local_field / T)) / Z

  (PMF.map (gibbs_bool_to_state_map s u) (PMF.ofFintype norm_probs (by
    -- Prove that the probability mass sums to 1
    have h_sum : ∑ b : Bool, norm_probs b = norm_probs true + norm_probs false := by
      exact Fintype.sum_bool (λ b => norm_probs b)
    rw [h_sum]
    simp only [norm_probs]

    -- Express sum of normalized probabilities in terms of Z
    have h_ratio_sum : ENNReal.ofReal (Real.exp (local_field / T)) / Z +
                       ENNReal.ofReal (Real.exp (-local_field / T)) / Z =
                       (ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))) / Z := by
      exact ENNReal.div_add_div_same

    -- Simplify the if expressions in the sum first
    simp only [Bool.false_eq_true]

    -- Simplify the if-then-else expressions first
    have h_if_true : (if True then ENNReal.ofReal (Real.exp (local_field / T)) / Z
                      else ENNReal.ofReal (Real.exp (-local_field / T)) / Z) =
                     ENNReal.ofReal (Real.exp (local_field / T)) / Z := by simp

    have h_if_false : (if False then ENNReal.ofReal (Real.exp (local_field / T)) / Z
                       else ENNReal.ofReal (Real.exp (-local_field / T)) / Z) =
                      ENNReal.ofReal (Real.exp (-local_field / T)) / Z := by simp

    rw [h_if_true, h_if_false]

    -- Now we can rewrite using our ratio sum lemma
    rw [h_ratio_sum]

    -- Z divided by itself equals 1
    have h_Z_ne_zero : Z ≠ 0 := by
      simp [Z]
      intro h
      have h_exp_pos : ENNReal.ofReal (Real.exp (local_field / T)) > 0 := by
        apply ENNReal.ofReal_pos.mpr
        apply Real.exp_pos
      exact Real.exp_pos (-Coe.coe local_field / T)

    have h_Z_ne_top : Z ≠ ⊤ := by simp [Z]

    exact ENNReal.div_self h_Z_ne_zero h_Z_ne_top
  ))) (NN.State.updateNeuron s u 1 (by exact Or.inl rfl)) = norm_probs true := by
  intro
  -- Use pmf_map_update_one lemma which directly gives us the result
  apply pmf_map_update_one

-- Lemma for the probability calculation in the negative case
lemma gibbs_prob_negative_case {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (s : (HopfieldNetwork R U).State) (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (u : U) :
  let local_field := s.net wθ u
  let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
  let norm_probs := λ b => if b then
                             ENNReal.ofReal (Real.exp (local_field / T)) / Z
                           else
                             ENNReal.ofReal (Real.exp (-local_field / T)) / Z

  (PMF.map (gibbs_bool_to_state_map s u) (PMF.ofFintype norm_probs (by
    -- Prove that the probability mass sums to 1
    have h_sum : ∑ b : Bool, norm_probs b = norm_probs true + norm_probs false := by
      exact Fintype.sum_bool (λ b => norm_probs b)
    rw [h_sum]
    simp only [norm_probs]

    -- Express sum of normalized probabilities in terms of Z
    have h_ratio_sum : ENNReal.ofReal (Real.exp (local_field / T)) / Z +
                       ENNReal.ofReal (Real.exp (-local_field / T)) / Z =
                       (ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))) / Z := by
      exact ENNReal.div_add_div_same

    -- Simplify the if expressions in the sum first
    simp only [Bool.false_eq_true]

    -- Simplify the if-then-else expressions first
    simp [ite_true, ite_false]

    -- Now we can rewrite using our ratio sum lemma
    rw [h_ratio_sum]

    -- Z divided by itself equals 1
    have h_Z_ne_zero : Z ≠ 0 := by
      simp only [Z, ne_eq, add_eq_zero]
      intro h
      have h_exp_pos : ENNReal.ofReal (Real.exp (local_field / T)) > 0 := by
        apply ENNReal.ofReal_pos.mpr
        apply Real.exp_pos
      have h_exp_neg_pos : ENNReal.ofReal (Real.exp (-local_field / T)) > 0 := by
        apply ENNReal.ofReal_pos.mpr
        apply Real.exp_pos
      exact (not_and_or.mpr (Or.inl h_exp_pos.ne')) h

    have h_Z_ne_top : Z ≠ ⊤ := by
      simp [Z]

    exact ENNReal.div_self h_Z_ne_zero h_Z_ne_top
  )))
    (NN.State.updateNeuron s u (-1) (by exact Or.inr rfl)) = norm_probs false := by
  intro
  -- Use pmf_map_update_neg_one lemma which directly gives us the result
  apply pmf_map_update_neg_one

/-- Computes the probability of updating a neuron to a specific value using Gibbs sampling.

This lemma expresses the probability as a ratio of Boltzmann factors, showing that:
- If new_val = 1: probability = exp(local_field/T)/Z
- If new_val = -1: probability = exp(-local_field/T)/Z
where Z is the normalization constant (partition function).
--/
lemma gibbs_update_single_neuron_prob {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s : (HopfieldNetwork R U).State)
  (u : U) (new_val : R) (hval : (HopfieldNetwork R U).pact new_val) :
  let local_field := s.net wθ u
  let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))

  (NN.State.gibbsUpdateSingleNeuron s wθ T u) (NN.State.updateNeuron s u new_val hval) =
    if new_val = 1 then
      ENNReal.ofReal (Real.exp (local_field / T)) / Z
    else
      ENNReal.ofReal (Real.exp (-local_field / T)) / Z := by
    sorry

/-- Multi-site transitions have zero probability --/
lemma gibbs_multi_site_transition {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s s' : (HopfieldNetwork R U).State) :
  (¬∃ u : U, ∀ v : U, v ≠ u → s.act v = s'.act v) →
  gibbsTransitionProb wθ T s s' = 0 := by
  sorry
