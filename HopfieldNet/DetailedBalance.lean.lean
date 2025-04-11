import HopfieldNet.Stochastic
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Topology.Metrizable.CompletelyMetrizable


open Finset Matrix NeuralNetwork State

lemma sum_univ_eq_tsum_uniform {U : Type} [Fintype U] [DecidableEq U]
  [Nonempty U] :
  Summable (fun (_ : U) => (1 : ℝ) / ↑(Fintype.card U)) ∧
  ∑' (_ : U), (1 : ℝ) / ↑(Fintype.card U) = Finset.sum Finset.univ (fun (_ : U) => (1 : ℝ) / ↑(Fintype.card U)) :=
by
  have h_nonzero : (1 : ℝ) / ↑(Fintype.card U) ≠ 0 :=
    by { apply div_ne_zero; norm_num; simp_all only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]}
  have h_support : (Function.support (fun (u : U) => (1 : ℝ) / ↑(Fintype.card U))).Finite := by
    rw [Function.support_const]
    exact Set.finite_univ
    exact h_nonzero
  have h_summable : Summable (fun (u : U) => (1 : ℝ) / ↑(Fintype.card U)) := by
    apply summable_of_finite_support
    · rw [Function.support_const]
      exact Set.finite_univ
      exact h_nonzero
  have h_tsum_eq_sum : ∑' (u : U), (1 : ℝ) / ↑(Fintype.card U) = ∑ (u : U), (1 : ℝ) / ↑(Fintype.card U) := by
    simp_all only [one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
      Function.support_inv, tsum_const, Nat.card_eq_fintype_card, nsmul_eq_mul, mul_inv_cancel₀, sum_const, card_univ]
  exact ⟨h_summable, h_tsum_eq_sum⟩

lemma mul_div_cancel_of_ne_zero {α : Type*} [Field α] (a b : α) (h : b ≠ 0) : a * b / b = a := by
  rw [div_eq_mul_inv]
  rw [propext (mul_inv_eq_iff_eq_mul₀ h)]

/-- In a tsum over all neurons, only the neuron where s and s' differ contributes --/
lemma gibbs_single_site_tsum {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [HDiv ℕ ℕ ℝ]
  [Nonempty U] [Coe R ℝ] [Inv ℕ] [CommGroup ℕ] [Field ℕ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h_diff_at_u : s.act u ≠ s'.act u)
  (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑' (a : U),
    (PMF.ofFintype (fun x => 1 / ↑(Fintype.card U)) (by exact uniform_neuron_selection_prob_valid)) a
    * (NN.State.gibbsUpdateSingleNeuron s wθ T a) s' =
  1 / ↑(Fintype.card U) * (NN.State.gibbsUpdateSingleNeuron s wθ T u)
    (NN.State.updateNeuron s u (s'.act u) (s'.hp u)) := by
  have h_s'_as_update : s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) := by
    apply single_site_difference_as_update s s' u h_diff_at_u h_same_elsewhere
  have h_card_nonzero : (Fintype.card U : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (@Fintype.card_ne_zero U _ ‹Nonempty U›)
  have h_calc : ((Fintype.card U : ℝ)) * (1 / ↑(Fintype.card U)) = 1 := by
    exact mul_one_div_cancel h_card_nonzero
  have h_s'_as_update : s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) := by
    apply single_site_difference_as_update s s' u h_diff_at_u h_same_elsewhere

  have h_tsum_to_sum : ∑' (a : U), (PMF.ofFintype (fun x => 1 / ↑(Fintype.card U)) (by exact uniform_neuron_selection_prob_valid)) a *
                      (NN.State.gibbsUpdateSingleNeuron s wθ T a) s' =
                      ∑ a ∈ Finset.univ, (PMF.ofFintype (fun x => 1 / ↑(Fintype.card U)) (by exact uniform_neuron_selection_prob_valid)) a *
                      (NN.State.gibbsUpdateSingleNeuron s wθ T a) s' := by
    apply tsum_eq_sum
    · intro a ha
      simp only [Finset.mem_univ] at ha
      contradiction
  rw [h_tsum_to_sum]
  rw [h_s'_as_update]
  have h_zero_other_sites : ∀ a ∈ Finset.univ, a ≠ u →
                           (NN.State.gibbsUpdateSingleNeuron s wθ T a) s' = 0 := by
    intro a _ ha
    exact gibbs_update_zero_other_sites wθ T s s' u a h_same_elsewhere h_diff_at_u ha
  rw [Finset.sum_eq_single u]
  · simp only [uniform_neuron_selection_prob]
    have h_update_eq : (NN.State.gibbsUpdateSingleNeuron s wθ T u) s' =
                      (NN.State.gibbsUpdateSingleNeuron s wθ T u)
                      (NN.State.updateNeuron s u (s'.act u) (s'.hp u)) := by
      rw [h_s'_as_update]
      congr
    congr
  · intro a h_in h_ne
    have h_eq : s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) := h_s'_as_update
    rw [h_eq] at h_zero_other_sites
    exact mul_eq_zero_of_right _ (h_zero_other_sites a h_in h_ne)
  · intro h_not_in
    absurd (Finset.mem_univ u)
    exact h_not_in

  /-- Main lemma for Gibbs transition probability with single site update :
    For a state transition involving change at exactly one site u, the Gibbs transition
    probability is the product of the probability of selecting u and the probability
    of updating u to the new value --/--/
lemma gibbs_single_site_transition_prob {R U : Type}
  [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Field ℕ] [CommGroup ℕ] [Coe R ℝ] [HDiv ℕ ℕ ℝ] [Inv ℕ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h_diff_at_u : s.act u ≠ s'.act u)
  (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  gibbsTransitionProb wθ T s s' =
  ENNReal.toReal (((1 : ENNReal) / (Fintype.card U : ENNReal)) *
  (NN.State.gibbsUpdateSingleNeuron s wθ T u) (NN.State.updateNeuron s u (s'.act u) (s'.hp u))) := by
  -- Unfold the definition and apply bind_apply
  unfold gibbsTransitionProb
  rw [NN.State.gibbsSamplingStep]
  rw [PMF.bind_apply]
  -- Use the gibbs_single_site_tsum lemma to simplify the sum
  have h_eq := gibbs_single_site_tsum wθ T s s' u h_diff_at_u h_same_elsewhere
  -- Apply ENNReal.toReal to both sides
  exact congrArg ENNReal.toReal h_eq
