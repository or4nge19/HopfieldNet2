import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.Complex.Trigonometric

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace Rebuild.StatMech.MeanField

/-- Standard Gaussian measure on `ℝ^M` (as `Fin M → ℝ`) with independent `N(0,1)` coordinates. -/
noncomputable def stdGaussianMeasure (M : ℕ) : Measure (Fin M → ℝ) :=
  Measure.infinitePi (fun _ : Fin M => (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)))

instance (M : ℕ) : IsProbabilityMeasure (stdGaussianMeasure M) := by
  dsimp [stdGaussianMeasure]
  infer_instance

private lemma mgf_eval_stdGaussian (M : ℕ) (k : Fin M) :
    ProbabilityTheory.mgf (fun z : Fin M → ℝ => z k) (stdGaussianMeasure M)
      = ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)) := by
  have hmap :
      (stdGaussianMeasure M).map (fun z : Fin M → ℝ => z k)
        = ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0) := by
    simpa [stdGaussianMeasure] using
      (measurePreserving_eval_infinitePi (μ := fun _ : Fin M =>
        (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0))) k).map_eq
  have hm :
      ProbabilityTheory.mgf id ((stdGaussianMeasure M).map (fun z : Fin M → ℝ => z k))
        = ProbabilityTheory.mgf (fun z : Fin M → ℝ => z k) (stdGaussianMeasure M) := by
    have hmeas : AEMeasurable (fun z : Fin M → ℝ => z k) (stdGaussianMeasure M) := by
      exact (measurable_pi_apply k).aemeasurable
    simpa using (ProbabilityTheory.mgf_id_map (μ := stdGaussianMeasure M)
      (X := fun z : Fin M → ℝ => z k) hmeas)
  simpa [hmap] using hm.symm

/--
Hubbard–Stratonovich / Gaussian linearization identity on `ℝ^M` with product standard Gaussian.
-/
theorem hubbardStratonovich_stdGaussian (M : ℕ) (c : ℝ) (hc : 0 ≤ c) (m : Fin M → ℝ) :
    (∫ z : Fin M → ℝ, Real.exp ((Real.sqrt c) * (∑ k : Fin M, m k * z k))
        ∂(stdGaussianMeasure M))
      =
      Real.exp ((c / 2) * ∑ k : Fin M, (m k) ^ 2) := by
  let μ : Measure (Fin M → ℝ) := stdGaussianMeasure M
  let X : Fin M → (Fin M → ℝ) → ℝ := fun k z => m k * z k
  have h_indep : ProbabilityTheory.iIndepFun (fun k z => z k) μ := by
    simpa [μ, stdGaussianMeasure] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun _ : Fin M => (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)))
        (X := fun _ : Fin M => id) (by fun_prop))
  have h_indep' : ProbabilityTheory.iIndepFun X μ :=
    (ProbabilityTheory.iIndepFun.comp h_indep (fun k x => m k * x) (fun _ => by fun_prop))
  have hX_meas : ∀ k, Measurable (X k) := by fun_prop
  have hL :
      (∫ z : Fin M → ℝ, Real.exp ((Real.sqrt c) * (∑ k : Fin M, m k * z k)) ∂μ)
        =
        ProbabilityTheory.mgf ((Finset.univ : Finset (Fin M)).sum fun k => X k) μ (Real.sqrt c) := by
    simp [ProbabilityTheory.mgf, X, μ, Finset.mul_sum, mul_assoc, mul_comm]
  have hmgf_sum :
      ProbabilityTheory.mgf ((Finset.univ : Finset (Fin M)).sum fun k => X k) μ (Real.sqrt c)
        = ∏ k : Fin M, ProbabilityTheory.mgf (X k) μ (Real.sqrt c) := by
    simpa using (h_indep'.mgf_sum (μ := μ) (t := Real.sqrt c) hX_meas (Finset.univ : Finset (Fin M)))
  have hmgf_one (k : Fin M) :
      ProbabilityTheory.mgf (X k) μ (Real.sqrt c) =
        Real.exp (((Real.sqrt c) * m k) ^ 2 / 2) := by
    have hmap_val :
        ProbabilityTheory.mgf (fun z : Fin M → ℝ => z k) μ ((m k) * (Real.sqrt c))
          =
          ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0))
            ((m k) * (Real.sqrt c)) := by
      simpa [μ, stdGaussianMeasure] using
        congrArg (fun F : ℝ → ℝ => F ((m k) * (Real.sqrt c))) (mgf_eval_stdGaussian (M := M) k)
    have hscale :
        ProbabilityTheory.mgf (X k) μ (Real.sqrt c)
          = ProbabilityTheory.mgf (fun z : Fin M → ℝ => z k) μ ((m k) * (Real.sqrt c)) := by
      simpa [X, mul_assoc, mul_left_comm, mul_comm] using
        (ProbabilityTheory.mgf_const_mul (μ := μ) (X := fun z : Fin M → ℝ => z k) (α := m k)
          (t := Real.sqrt c))
    have hgauss :
        ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)) ((m k) * (Real.sqrt c))
          = Real.exp ((((m k) * (Real.sqrt c)) ^ 2) / 2) := by
      simpa using congrArg (fun F => F ((m k) * (Real.sqrt c)))
        (ProbabilityTheory.mgf_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
    calc
      ProbabilityTheory.mgf (X k) μ (Real.sqrt c)
          = ProbabilityTheory.mgf (fun z : Fin M → ℝ => z k) μ ((m k) * (Real.sqrt c)) := hscale
      _ = ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)) ((m k) * (Real.sqrt c)) := hmap_val
      _ = Real.exp (((m k) * (Real.sqrt c)) ^ 2 / 2) := hgauss
      _ = Real.exp (((Real.sqrt c) * m k) ^ 2 / 2) := by ring_nf
  have :
      (∏ k : Fin M, ProbabilityTheory.mgf (X k) μ (Real.sqrt c))
        = Real.exp ((c / 2) * ∑ k : Fin M, (m k) ^ 2) := by
    have hsqrt_sq : (Real.sqrt c) ^ 2 = c := by
      simpa using (Real.sq_sqrt hc)
    calc
      (∏ k : Fin M, ProbabilityTheory.mgf (X k) μ (Real.sqrt c))
          = ∏ k : Fin M, Real.exp (((Real.sqrt c) * m k) ^ 2 / 2) := by
              simp [hmgf_one]
      _ = Real.exp (∑ k : Fin M, (((Real.sqrt c) * m k) ^ 2 / 2)) := by
            simpa using (Real.exp_sum (s := (Finset.univ : Finset (Fin M)))
              (f := fun k : Fin M => (((Real.sqrt c) * m k) ^ 2 / 2))).symm
      _ = Real.exp ((c / 2) * ∑ k : Fin M, (m k) ^ 2) := by
            have : (∑ k : Fin M, (((Real.sqrt c) * m k) ^ 2 / 2))
                = (c / 2) * ∑ k : Fin M, (m k) ^ 2 := by
              have hs : (Real.sqrt c) * (Real.sqrt c) = c := by
                simpa [pow_two] using hsqrt_sq
              calc
                (∑ k : Fin M, (((Real.sqrt c) * m k) ^ 2 / 2))
                    = ∑ k : Fin M, (c / 2) * (m k) ^ 2 := by
                        refine Finset.sum_congr rfl (fun k _hk => ?_)
                        simp [pow_two, hs, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
                    _ = (c / 2) * ∑ k : Fin M, (m k) ^ 2 := by
                      simp [Finset.mul_sum]
            simp [this]
  calc
    (∫ z : Fin M → ℝ, Real.exp ((Real.sqrt c) * (∑ k : Fin M, m k * z k)) ∂μ)
        = ProbabilityTheory.mgf ((Finset.univ : Finset (Fin M)).sum fun k => X k) μ (Real.sqrt c) := hL
    _ = ∏ k : Fin M, ProbabilityTheory.mgf (X k) μ (Real.sqrt c) := hmgf_sum
    _ = Real.exp ((c / 2) * ∑ k : Fin M, (m k) ^ 2) := this

/-- The variance parameter `v = (β * N)⁻¹` used by Talagrand’s Hopfield analysis. -/
noncomputable def talagrandGaussianVar (N : ℕ) (β : ℝ) (hβ : 0 ≤ β) : ℝ≥0 :=
  ⟨(β * (N : ℝ))⁻¹, inv_nonneg.mpr (mul_nonneg hβ (by exact_mod_cast (Nat.zero_le N)))⟩

/-- Talagrand’s auxiliary Gaussian measure `γ` on `ℝ^M`, realized as a product of `N(0,(βN)⁻¹)`. -/
noncomputable def talagrandGaussianMeasure (N M : ℕ) (β : ℝ) (hβ : 0 ≤ β) : Measure (Fin M → ℝ) :=
  Measure.infinitePi (fun _ : Fin M =>
    ProbabilityTheory.gaussianReal 0 (talagrandGaussianVar (N := N) β hβ))

instance (N M : ℕ) (β : ℝ) (hβ : 0 ≤ β) : IsProbabilityMeasure (talagrandGaussianMeasure N M β hβ) := by
  dsimp [talagrandGaussianMeasure]
  infer_instance

