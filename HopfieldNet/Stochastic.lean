import HopfieldNet.HN
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Vector.Basic

set_option linter.unusedVariables false


open Finset Matrix NeuralNetwork State

/-- Probability Mass Function over Neural Network States --/
def NeuralNetwork.StatePMF {R U : Type} [Zero R] (NN : NeuralNetwork R U) := PMF (NN.State)

/-- Temperature-parameterized stochastic dynamics for neural networks --/
def NeuralNetwork.StochasticDynamics {R U : Type} [Zero R] (NN : NeuralNetwork R U) :=
  ∀ (T : ℝ), NN.State → NeuralNetwork.StatePMF NN

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
        aesop
      }
      have h_total_ne_top : total ≠ ⊤ := by {
        simp [probs, total]
      }
      have h_sum : Finset.sum Finset.univ norm_probs = 1 := by
        calc Finset.sum Finset.univ norm_probs
          = (probs true)/total + (probs false)/total := by exact Fintype.sum_bool fun b ↦ probs b / total
          _ = (probs true + probs false)/total := ENNReal.div_add_div_same
          _ = total/total := rfl
          _ = 1 := ENNReal.div_self h_total h_total_ne_top
      exact h_sum))

@[inherit_doc]
scoped[ENNReal] notation "ℝ≥0∞" => ENNReal

/-- Complete Gibbs sampling step for Hopfield network --/
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

theorem Array.mkArray_creates_valid_hopfield_params {n : ℕ} [Nonempty (Fin n)] :
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
This lemma proves that if two neurons are not adjacent, they must be the same neuron.
This formalizes the fully connected nature of Hopfield networks.
--/
lemma HopfieldNetwork.all_nodes_adjacent {R U : Type} [LinearOrderedField R] [DecidableEq U]
    [Nonempty U] [Fintype U] (u v : U) :
    ¬(HopfieldNetwork R U).Adj u v → u = v := by
  intro h
  unfold HopfieldNetwork at h
  simp only [ne_eq] at h
  simp_all only [Decidable.not_not]
