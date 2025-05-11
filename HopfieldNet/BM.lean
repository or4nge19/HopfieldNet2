import HopfieldNet.NN -- For NeuralNetwork, State, etc.
import HopfieldNet.HN -- For HopfieldNetwork, HNfnet, HNfact
import HopfieldNet.Stochastic -- For NN.State.updateNeuron
import Mathlib

open Finset Matrix NeuralNetwork State ENNReal Real PMF

variable {R U : Type} [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U]

lemma HNfact_is_one_or_neg_one_for_BM_pact (θ val : R) :
  (fun act : R => act = 1 ∨ act = -1) (HNfact θ val) := by
  unfold HNfact
  split_ifs
  · left; rfl
  · right; rfl

variable [Coe R ℝ]

abbrev BoltzmannMachine (R U : Type) [LinearOrderedField R] [DecidableEq U]
  [Nonempty U] [Fintype U] : NeuralNetwork R U :=
{ (HopfieldNetwork R U) with
  Adj := fun u v => u ≠ v,
  Ui := Set.univ, Uo := Set.univ, Uh := ∅,
  hU := by simp only [Set.univ, Set.union_self, Set.union_empty],
  hUi := Ne.symm Set.empty_ne_univ, hUo := Ne.symm Set.empty_ne_univ,
  hhio := Set.empty_inter (Set.univ ∪ Set.univ),
  pw := fun w => w.IsSymm ∧ ∀ u, w u u = 0,
  κ1 := fun _ => 0, κ2 := fun _ => 1,
  fnet := fun u w_u pred _ => HNfnet u w_u pred,
  fact := fun u input θ_vec => HNfact (θ_vec.get 0) input,
  fout := fun _ act => act,
  pact := fun act => act = (1 : R) ∨ act = (-1 : R), -- This is the pact for BoltzmannMachine
  hpact := fun _ _ _ _ _ _ _ _ => HNfact_is_one_or_neg_one_for_BM_pact _ _
}

structure ParamsBM (R U : Type) [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] where
  w : Matrix U U R
  hpw : (BoltzmannMachine R U).pw w
  θ : U → R
  T : R
  hT_pos : T > 0

abbrev StateBM (R U : Type) [LinearOrderedField R] [DecidableEq U] [Fintype U] [Nonempty U] [Coe R ℝ] :=
  (BoltzmannMachine R U).State

namespace BoltzmannMachine

def energy (p : ParamsBM R U) (s : StateBM R U) : R :=
  - (1 / (2 : R)) * (∑ u, ∑ v ∈ Finset.univ.filter (fun v' => v' ≠ u), p.w u v * s.act u * s.act v)
  - (∑ u, p.θ u * s.act u)

def localField (p : ParamsBM R U) (s : StateBM R U) (u : U) : R :=
  (∑ v ∈ Finset.univ.filter (fun v' => v' ≠ u), p.w u v * s.act v) + p.θ u

noncomputable def probNeuronIsOne (p : ParamsBM R U)
  (s : StateBM R U) (u : U) : ℝ :=
  let L_u : ℝ := ↑(localField p s u) -- Explicit coercion
  let T_R : ℝ := ↑(p.T)             -- Explicit coercion
  (1 : ℝ) / (1 + Real.exp (- (2 * L_u / T_R)))

lemma probNeuronIsOne_nonneg (p : ParamsBM R U)
  (s : StateBM R U) (u : U) : probNeuronIsOne p s u ≥ 0 := by
  simp only [probNeuronIsOne, div_nonneg_iff]
  left
  constructor
  · norm_num -- 1 ≥ 0
  · positivity -- 1 + exp(..) > 0

lemma probNeuronIsOne_le_one (p : ParamsBM R U)
  (s : StateBM R U) (u : U) : probNeuronIsOne p s u ≤ 1 := by
  unfold probNeuronIsOne
  apply div_le_one_of_le₀
  · have h : 0 < Real.exp (-(2 * ↑(localField p s u) / ↑p.T)) := Real.exp_pos _
    linarith
  · have h1 : 0 < 1 := by norm_num
    have h2 : 0 < Real.exp (-(2 * ↑(localField p s u) / ↑p.T)) := Real.exp_pos _
    linarith

noncomputable def gibbsUpdateSingleNeuron (p : ParamsBM R U)
  (s : StateBM R U) (u : U) : PMF (StateBM R U) :=
  let prob_one_R : ℝ := probNeuronIsOne p s u
  let prob_one_ennreal := ENNReal.ofReal prob_one_R
  have h_prob_ennreal_le_one : prob_one_ennreal ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (probNeuronIsOne_le_one p s u)
  PMF.bernoulli prob_one_ennreal h_prob_ennreal_le_one >>= fun takes_value_one =>
    let new_val : R := if takes_value_one then (1 : R) else (-1 : R)
    PMF.pure
      { act := fun v => if v = u then new_val else s.act v
      , hp := fun v => by
          by_cases hv : v = u
          · subst hv
            dsimp [new_val]
            split_ifs with h
            · exact Or.inl rfl
            · exact Or.inr rfl
            exact False.elim (h rfl)
          · dsimp only; simp [if_neg hv]; exact s.hp v }

noncomputable def gibbsSamplingStep [LinearOrderedField ℕ] [LinearOrderedField ℤ] (p : ParamsBM R U)
  (s : StateBM R U) : PMF (StateBM R U) :=
  let neuron_pmf : PMF U := PMF.uniformOfFintype U
  neuron_pmf >>= fun u => gibbsUpdateSingleNeuron p s u

end BoltzmannMachine
