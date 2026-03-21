import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Rebuild.Core.Gibbs

/-!
# Rebuild Finite Gibbs Core

Canonical finite-volume Gibbs semantics for a finite state space.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace Rebuild.StatMech.FiniteGibbs

open Rebuild.Core

noncomputable section

variable {State : Type*} [Fintype State] [Nonempty State]

lemma partitionFunction_pos (β : ℝ) (model : FiniteGibbsModel State) :
    0 < Rebuild.Core.partitionFunction β model.energy := by
  classical
  unfold Rebuild.Core.partitionFunction Rebuild.Core.boltzmannWeight
  refine Finset.sum_pos ?_ Finset.univ_nonempty
  intro σ _
  exact Real.exp_pos _

lemma partitionFunction_ne_zero (β : ℝ) (model : FiniteGibbsModel State) :
    Rebuild.Core.partitionFunction β model.energy ≠ 0 :=
  (partitionFunction_pos β model).ne'

/-- The normalized Gibbs probability of a state in a finite Gibbs model. -/
def gibbsProbability (β : ℝ) (model : FiniteGibbsModel State) (σ : State) : ℝ :=
  Rebuild.Core.boltzmannWeight β model.energy σ /
    Rebuild.Core.partitionFunction β model.energy

lemma gibbsProbability_nonneg (β : ℝ) (model : FiniteGibbsModel State) (σ : State) :
    0 ≤ gibbsProbability β model σ := by
  unfold gibbsProbability Rebuild.Core.boltzmannWeight
  exact div_nonneg (Real.exp_nonneg _) (le_of_lt (partitionFunction_pos β model))

lemma sum_gibbsProbability (β : ℝ) (model : FiniteGibbsModel State) :
    (∑ σ, gibbsProbability β model σ) = 1 := by
  classical
  let Z := Rebuild.Core.partitionFunction β model.energy
  have hZ : Z ≠ 0 := partitionFunction_ne_zero β model
  calc
    ∑ σ, gibbsProbability β model σ
        = ∑ σ, Rebuild.Core.boltzmannWeight β model.energy σ * Z⁻¹ := by
            simp [gibbsProbability, Z, div_eq_mul_inv]
    _ = (∑ σ, Rebuild.Core.boltzmannWeight β model.energy σ) * Z⁻¹ := by
          symm
          simpa using
            (Finset.sum_mul
              (s := (Finset.univ : Finset State))
              (f := fun σ => Rebuild.Core.boltzmannWeight β model.energy σ)
              (a := Z⁻¹))
    _ = Z * Z⁻¹ := by rfl
    _ = 1 := by simp [hZ]

/-- Gibbs probability packaged as a nonnegative real. -/
def gibbsProbabilityNNReal (β : ℝ) (model : FiniteGibbsModel State)
    (σ : State) : ℝ≥0 :=
  ⟨gibbsProbability β model σ, gibbsProbability_nonneg β model σ⟩

@[simp] lemma gibbsProbabilityNNReal_coe (β : ℝ) (model : FiniteGibbsModel State)
    (σ : State) :
    (gibbsProbabilityNNReal β model σ : ℝ) = gibbsProbability β model σ := rfl

@[simp] lemma gibbsProbabilityNNReal_coe_ennreal (β : ℝ) (model : FiniteGibbsModel State)
    (σ : State) :
    (gibbsProbabilityNNReal β model σ : ℝ≥0∞) = ENNReal.ofReal (gibbsProbability β model σ) := by
  symm
  exact ENNReal.ofReal_eq_coe_nnreal (gibbsProbability_nonneg β model σ)

variable [MeasurableSpace State]

/-- The finite Gibbs law as an atomic probability measure on the state space. -/
def gibbsMeasure (β : ℝ) (model : FiniteGibbsModel State) : Measure State :=
  (Finset.univ : Finset State).sum fun σ =>
    ((gibbsProbabilityNNReal β model σ : ℝ≥0∞) • Measure.dirac σ)

lemma gibbsMeasure_apply_singleton (β : ℝ) (model : FiniteGibbsModel State)
    [MeasurableSingletonClass State] (σ : State) :
    gibbsMeasure β model {σ} = ENNReal.ofReal (gibbsProbability β model σ) := by
  classical
  have hs : MeasurableSet ({σ} : Set State) := measurableSet_singleton σ
  change ((∑ τ : State, (gibbsProbabilityNNReal β model τ : ℝ≥0∞) • Measure.dirac τ) : Measure State)
      {σ} = _
  rw [Measure.finset_sum_apply]
  · rw [Finset.sum_eq_single σ]
    · rw [Measure.smul_apply, Measure.dirac_apply' _ hs]
      simp [gibbsProbabilityNNReal_coe_ennreal, smul_eq_mul]
    · intro b _ hb
      rw [Measure.smul_apply, Measure.dirac_apply' _ hs]
      simp [hb, gibbsProbabilityNNReal_coe_ennreal, smul_eq_mul]
    · simp

lemma gibbsMeasure_univ (β : ℝ) (model : FiniteGibbsModel State) :
    gibbsMeasure β model Set.univ = 1 := by
  have h_univ :
      gibbsMeasure β model Set.univ =
        ∑ σ : State, (gibbsProbabilityNNReal β model σ : ℝ≥0∞) := by
    simp [gibbsMeasure]
  have h_sum :
      (∑ σ : State, (gibbsProbabilityNNReal β model σ : ℝ≥0∞)) = (1 : ℝ≥0∞) := by
    calc
      (∑ σ : State, (gibbsProbabilityNNReal β model σ : ℝ≥0∞))
          = ∑ σ : State, ENNReal.ofReal (gibbsProbability β model σ) := by
              simp [gibbsProbabilityNNReal_coe_ennreal]
      _ = ENNReal.ofReal (∑ σ : State, gibbsProbability β model σ) := by
            symm
            refine ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset State))
              (f := fun σ => gibbsProbability β model σ) ?_
            intro σ _
            exact gibbsProbability_nonneg β model σ
      _ = 1 := by simp [sum_gibbsProbability]
  simpa [h_univ] using h_sum

instance (β : ℝ) (model : FiniteGibbsModel State) : IsProbabilityMeasure (gibbsMeasure β model) :=
  ⟨gibbsMeasure_univ β model⟩

lemma integral_gibbsMeasure (β : ℝ) (model : FiniteGibbsModel State) (f : State → ℝ)
    [MeasurableSingletonClass State] :
    (∫ σ, f σ ∂gibbsMeasure β model) = ∑ σ : State, gibbsProbability β model σ * f σ := by
  let μatom : State → Measure State :=
    fun σ => ((gibbsProbabilityNNReal β model σ : ℝ≥0∞) • Measure.dirac σ)
  have h_integrable :
      ∀ σ ∈ (Finset.univ : Finset State), Integrable f (μatom σ) := by
    intro σ _
    exact (MeasureTheory.integrable_dirac (a := σ) (f := f) (by simp)).smul_measure (by simp)
  have hsum :=
    MeasureTheory.integral_finset_sum_measure
      (f := f) (μ := μatom) (s := (Finset.univ : Finset State)) h_integrable
  simpa [gibbsMeasure, μatom, gibbsProbabilityNNReal, gibbsProbability,
    mul_comm, mul_left_comm, mul_assoc] using hsum

end

end Rebuild.StatMech.FiniteGibbs
