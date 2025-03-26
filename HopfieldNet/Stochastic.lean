/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import HopfieldNet.HN
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Vector.Basic

set_option linter.unusedVariables false

section aux

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

/-- Convert telescope sum to filtered sum --/
@[simp]
lemma tsum_to_filter {α : Type} [Finite α] [Fintype α] {p : α → ENNReal} {y : β} (f : α → β) :
  (∑' (a : α), if y = f a then p a else 0) = ∑ a ∈ filter (fun a ↦ f a = y) univ, p a := by
  -- First show that filter condition is equivalent
  have h_eq_cond : ∀ a, (y = f a) ↔ (f a = y) := by
    intro a
    exact eq_comm

  -- Connect tsum with filter sum
  have : (∑' (a : α), if f a = y then p a else 0) = ∑ a ∈ filter (fun a ↦ f a = y) univ, p a := by
    -- For finite types, tsum equals sum
    rw [tsum_fintype]
    -- Convert conditional sum to filtered sum
    exact Eq.symm (sum_filter (fun a ↦ f a = y) p)

  exact this

/-- If filtered sum is positive, there exists a positive element satisfying filter condition --/
@[simp]
lemma filter_sum_pos_exists {α β : Type} [Finite α] [Fintype α] [DecidableEq β] {p : α → ENNReal} {f : α → β} {y : β} :
  ∑ a ∈ filter (fun a ↦ f a = y) univ, p a > 0 →
  ∃ x : α, p x > 0 ∧ f x = y := by
  intro sum_pos
  -- If sum is positive, at least one term must be positive
  have exists_pos : ∃ a ∈ filter (fun a ↦ f a = y) univ, p a > 0 := by
    by_contra h
    -- If no element is positive, then all must be ≤ 0 (actually = 0 since p returns ENNReal)
    have all_zero : ∀ a ∈ filter (fun a ↦ f a = y) univ, p a = 0 := by
      intro a ha
      apply le_antisymm
      · push_neg at h
        exact h a ha
      · simp_all only [gt_iff_lt, mem_filter, mem_univ, true_and, not_exists, not_and, not_lt, nonpos_iff_eq_zero,
        le_refl]
    -- But then the sum would be 0
    have sum_zero : ∑ a ∈ filter (fun a ↦ f a = y) univ, p a = 0 := by
      apply Finset.sum_eq_zero
      exact all_zero
    -- Contradiction with sum_pos
    simp_all only [sum_const_zero, gt_iff_lt, lt_self_iff_false]

  -- Extract that element
  rcases exists_pos with ⟨x, h_mem, h_p_pos⟩
  -- Membership in filter means f x = y
  simp only [filter_subset, mem_filter, mem_univ, true_and] at h_mem
  subst h_mem
  simp_all only [gt_iff_lt]
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl
    }
    · simp_all only


/-- Any element in finset contributes to supremum over filtered sums --/
@[simp]
lemma ENNReal.le_iSup_finset {α : Type} {s : Finset α} {f : α → ENNReal} :
    ∑ a ∈ s, f a ≤ ⨆ (t : Finset α), ∑ a ∈ t, f a := by
  -- Use s as witness for supremum bound
  exact le_iSup_iff.mpr fun b a ↦ a s

/-- If there exists an element with positive value, then the telescope sum is positive --/
@[simp]
lemma ENNReal.tsum_pos_of_exists {α : Type} {f : α → ENNReal} (h : ∃ a : α, f a > 0) :
  (∑' a, f a) > 0 := by
  -- Extract the element with positive value
  rcases h with ⟨a₀, h_pos⟩

  -- Show that sum is at least as large as the term f a₀
  have h_le : f a₀ ≤ ∑' a, f a := by
    apply ENNReal.le_tsum

  -- Since f a₀ > 0 and sum ≥ f a₀, the sum must be positive
  exact lt_of_lt_of_le h_pos h_le

/-- If there exists a positive element satisfying filter condition, filtered sum is positive --/
@[simp]
lemma exists_pos_filter_sum_pos {α β : Type} [Finite α] [Fintype α] [DecidableEq β] [DecidableEq β] {p : α → ENNReal} {f : α → β} {y : β} :
  (∃ x : α, p x > 0 ∧ f x = y) →
  ∑ a ∈ filter (fun a ↦ f a = y) univ, p a > 0 := by
  rintro ⟨x, h_p_pos, h_fx_eq_y⟩
  -- x is in the filtered set
  have x_in_filter : x ∈ filter (fun a ↦ f a = y) univ := by
    simp only [filter_subset, mem_filter, mem_univ, true_and, h_fx_eq_y]

  -- Sum includes term for x
  have sum_ge_x : ∑ a ∈ filter (fun a ↦ f a = y) univ, p a ≥ p x := by
    exact CanonicallyOrderedAddCommMonoid.single_le_sum x_in_filter

  -- Since p x > 0, sum is positive
  exact lt_of_lt_of_le h_p_pos sum_ge_x

/-- Decompose energy into weight component and bias component --/
@[simp]
lemma energy_decomposition {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) :
  s.E wθ = s.Ew wθ + s.Eθ wθ := by
  -- By definition of E
  rfl

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
      rfl

  exact sum_filter_eq

/-- Weight matrix is symmetric in a Hopfield network --/
@[simp]
lemma weight_symmetry {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (v1 v2 : U) :
  wθ.w v1 v2 = wθ.w v2 v1 :=
  (congrFun (congrFun (id (wθ.hw').symm) v1) v2)

/-- Filter of non-equal elements is equivalent to erase operation --/
@[simp]
lemma filter_erase_equiv {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] (u : U) :
  filter (fun v => v ≠ u) univ = univ.erase u := by
  ext v
  simp only [mem_filter, mem_erase, mem_univ, true_and]
  exact Iff.symm (and_iff_left_of_imp fun a ↦ trivial)

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

end aux

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
  PMF.map (λ b => if b then
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
      exact h_sum))

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
    (∀ i : ℕ, ∀ h : i < σ_u.size, σ_u[i]'(by simp [σ_u, Array.mkArray_size]; exact Nat.not_succ_le_zero i h) = 0) ∧
    (∀ i : ℕ, ∀ h : i < θ_u.size, θ_u[i]'(by simp [θ_u, Array.mkArray_size]; exact Nat.lt_one_iff.mp h) = 0) := by
      intro u
      let σ_u := Array.mkArray ((HopfieldNetwork ℝ (Fin n)).κ1 u) 0
      let θ_u := Array.mkArray ((HopfieldNetwork ℝ (Fin n)).κ2 u) 0

      simp [Array.mkArray_size]

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
  simp [h_neq]

/-- Main aux lemma:
    For a mapped PMF, the probability of a state is positive if and only if
    there exists a preimage with positive probability --/
--/
@[simp]
lemma pmf_map_pos_iff_exists_pos {α β : Type} [Finite α] [Fintype α] [DecidableEq β]
    {p : α → ENNReal} (h_pmf : ∑ a, p a = 1) (f : α → β) (y : β) :
    PMF.map f (PMF.ofFintype p h_pmf) y > 0 ↔
    ∃ x : α, p x > 0 ∧ f x = y := by
  constructor
  · -- Forward direction
    intro h_pos
    simp only [PMF.map_apply] at h_pos

    -- First, convert tsum to filtered sum
    have h_filtered : (∑' (a : α), if y = f a then (PMF.ofFintype p h_pmf) a else 0) =
                     ∑ a ∈ filter (fun a ↦ f a = y) univ, (PMF.ofFintype p h_pmf) a := by
      rw [tsum_fintype]
      simp only [sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      simp only [eq_comm]

    -- Connect PMF.ofFintype back to original p
    have h_pmf_eq : ∀ a, (PMF.ofFintype p h_pmf) a = p a := by
      intro a
      simp only [PMF.ofFintype_apply]

    -- Use the filtered sum and rewrite with h_pos
    have h_pos_filter : ∑ a ∈ filter (fun a ↦ f a = y) univ, (PMF.ofFintype p h_pmf) a > 0 := by
      rw [←h_filtered]
      simp_all only [gt_iff_lt, PMF.ofFintype_apply, implies_true]

    -- Replace PMF.ofFintype with p in the sum
    have h_sum_p : ∑ a ∈ filter (fun a ↦ f a = y) univ, (PMF.ofFintype p h_pmf) a =
                  ∑ a ∈ filter (fun a ↦ f a = y) univ, p a := by
      apply Finset.sum_congr rfl
      intro a _
      exact h_pmf_eq a

    -- Use the rewritten sum with h_pos_filter
    have h_pos_p : ∑ a ∈ filter (fun a ↦ f a = y) univ, p a > 0 := by
      rw [←h_sum_p]
      exact h_pos_filter

    -- Now use filter_sum_pos_exists with the correctly formed sum
    exact filter_sum_pos_exists h_pos_p

  · -- Reverse direction
    intro h_exists
    simp only [PMF.map_apply]

    -- Convert directly to filtered sum
    rw [@ENNReal.tsum_eq_iSup_sum]

    -- Replace p with PMF.ofFintype
    have h_pmf_eq : ∀ a, p a = (PMF.ofFintype p h_pmf) a := by
      intro a
      simp only [PMF.ofFintype_apply]

    have h_sum_pmf : ∑ a ∈ filter (fun a ↦ f a = y) univ, p a =
                    ∑ a ∈ filter (fun a ↦ f a = y) univ, (PMF.ofFintype p h_pmf) a := by
      apply Finset.sum_congr rfl
      intro a _
      exact h_pmf_eq a

    have h_pos : ∑ a ∈ filter (fun a => f a = y) univ, p a > 0 := by
      exact exists_pos_filter_sum_pos h_exists

    -- Connect the filtered sum back to the telescoping sum
    have h_filtered : (∑' (a : α), if y = f a then (PMF.ofFintype p h_pmf) a else 0) =
                     ∑ a ∈ filter (fun a ↦ f a = y) univ, (PMF.ofFintype p h_pmf) a := by
      -- For finite types, tsum equals sum over filtered elements
      simp only [PMF.ofFintype_apply]
      rw [tsum_fintype]
      rw [sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      simp only [eq_comm]

    -- The filtered sum is positive
    have h_filter_pos : ∑ a ∈ filter (fun a ↦ f a = y) univ, (PMF.ofFintype p h_pmf) a > 0 := by
      rw [←h_sum_pmf]
      exact h_pos

    -- Use the equivalence to show the telescoping sum is positive
    have h_pos_sup : (⨆ s, ∑ x ∈ s, if y = f x then p x else 0) > 0 := by
      -- Show the supremum is at least as large as our positive filtered sum
      apply lt_of_lt_of_le h_filter_pos

      -- Connect filtered sum to supremum
      have h_filtered_pmf : (∑' (a : α), if y = f a then (PMF.ofFintype p h_pmf) a else 0) =
                          ∑ a ∈ filter (fun a ↦ f a = y) univ, (PMF.ofFintype p h_pmf) a := by
        rw [tsum_fintype]
        simp only [sum_filter]
        apply Finset.sum_congr rfl
        intro x _
        simp only [eq_comm]

      -- Use the fact that telescope sum equals supremum
      rw [←h_filtered_pmf]
      rw [ENNReal.tsum_eq_iSup_sum]
      -- The filter set contributes to the supremum
      exact Preorder.le_refl (⨆ s, ∑ a ∈ s, if y = f a then (PMF.ofFintype p h_pmf) a else 0)

    simp [<-h_filtered]
    exact h_pos_sup

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

  -- Define local components for clarity
  let local_field := s.net wθ v
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total : ENNReal := probs true + probs false
  let norm_probs : Bool → ENNReal := λ b => probs b / total

  -- Extract mapping structure from PMF.map
  simp [PMF.map_apply] at h_prob_pos

  -- Define local components
  let local_field := net wθ s v
  let probs := fun b =>
    let new_act_val := if b = true then 1 else -1
    ENNReal.ofReal (Real.exp (Coe.coe local_field * new_act_val / T))
  let total := probs true + probs false
  let norm_probs := fun b => probs b / total

  -- If probability is positive, there must be a preimage
  have h_exists : ∃ b : Bool, norm_probs b > 0 ∧ s_next = (if b then
      NN.State.updateNeuron s v 1 (by exact mul_self_eq_mul_self_iff.mp rfl)
    else
      NN.State.updateNeuron s v (-1) (by exact AffineMap.lineMap_eq_lineMap_iff.mp rfl)) := by
    -- Calculate the sum of normalized probabilities
    have h_sum_one : ∑ b : Bool, norm_probs b = 1 := by
      -- Convert sum of normalized probabilities
      have h_sum : ∑ b : Bool, probs b / total = (probs true + probs false) / total := by
        rw [Fintype.sum_bool]
        exact ENNReal.div_add_div_same
      -- Show that (p₁ + p₂)/total = 1 when total = p₁ + p₂
      rw [h_sum]
      have h_total_ne_zero : total ≠ 0 := by
        simp [total, probs]
        intro h_zero
        have h1 : ENNReal.ofReal (Real.exp (local_field * 1 / T)) > 0 := by
          apply ENNReal.ofReal_pos.mpr
          apply Real.exp_pos
        have h2 : ENNReal.ofReal (Real.exp (local_field * (-1) / T)) > 0 := by
          apply ENNReal.ofReal_pos.mpr
          apply Real.exp_pos
        have h_sum : ENNReal.ofReal (Real.exp (local_field * 1 / T)) +
                    ENNReal.ofReal (Real.exp (local_field * (-1) / T)) = 0 := by
                      simp_all only [Fintype.univ_bool, mul_ite, mul_one, mul_neg, ↓reduceIte, Bool.false_eq_true,
                        mem_singleton, Bool.true_eq_false, not_false_eq_true, sum_insert, sum_singleton, gt_iff_lt,
                        ENNReal.ofReal_pos, add_eq_zero, ENNReal.ofReal_eq_zero, true_and, probs, total, local_field]
                      exact le_imp_le_of_lt_imp_lt (fun a ↦ h1) h_zero
        have h_both_zero : ENNReal.ofReal (Real.exp (local_field * 1 / T)) = 0 ∧
                           ENNReal.ofReal (Real.exp (local_field * (-1) / T)) = 0 := by
          exact add_eq_zero.mp h_sum
        exact Real.exp_pos (-Coe.coe local_field / T)
      have h_total_ne_top : total ≠ ⊤ := by
        simp [total, probs]
      rw [ENNReal.div_self h_total_ne_zero h_total_ne_top]

    -- Define the function that maps Bool to the next state
    let f := λ (b : Bool) => if b then
        NN.State.updateNeuron s v 1 (by exact mul_self_eq_mul_self_iff.mp rfl)
      else
        NN.State.updateNeuron s v (-1) (by exact AffineMap.lineMap_eq_lineMap_iff.mp rfl)

    have h_exists_f : ∃ b : Bool, norm_probs b > 0 ∧ f b = s_next := by
      -- First show that the PMF map applied to s_next is > 0
      have h_pmf_pos : (PMF.map f (PMF.ofFintype norm_probs h_sum_one)) s_next > 0 := by
        -- This is what the lemma pmf_map_pos_iff_exists_pos expects
        unfold NN.State.gibbsUpdateSingleNeuron at h_prob_pos
        -- We can directly use h_prob_pos, but we need to make sure the types match
        exact h_prob_pos

      -- Now use the lemma with the correctly typed hypothesis
      apply (pmf_map_pos_iff_exists_pos h_sum_one f s_next).mp
      exact h_pmf_pos

    -- Rewrite to the desired form
    obtain ⟨b, h_norm_pos, h_eq⟩ := h_exists_f
    use b
    constructor
    { exact h_norm_pos }
    { rw [←h_eq];  }

  -- Extract the Boolean value and the equality
  obtain ⟨b, _, h_eq⟩ := h_exists

  -- Provide the disjunction based on the value of b
  cases b
  · right; exact h_eq  -- b = false
  · left; exact h_eq   -- b = true

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
    simp [hv]
  · unfold NN.State.updateNeuron
    simp [hv]
    simp_all only [ne_eq, not_false_eq_true]

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
  · simp [h_v, h_val]
  · simp [h_v]

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
