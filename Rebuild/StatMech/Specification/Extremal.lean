import Rebuild.StatMech.Specification.Structure
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Extremality and tail events (Georgii, Ch. 7 — first step)

This file starts the route to Georgii Thm. 7.7 (extreme points ↔ tail triviality) by proving the
easy direction: if a Gibbs measure is **not** tail-trivial, then it admits a nontrivial convex
decomposition into two Gibbs measures obtained by conditioning on a tail event.

We keep the formalization purely measure-theoretic, using only the fixed-point characterization
`μ.bind (γ.kernel Λ) = μ` and the properness of `γ` to show stability under restriction to tail events.
-/

open Set
open scoped ENNReal

open MeasureTheory

namespace Rebuild.StatMech.Specification



variable {Site Spin : Type*} [DecidableEq Site] [MeasurableSpace Spin]

open Rebuild.Core

/-! ### Tail events are boundary events for every finite volume -/

lemma measurableSet_cylinderEvents_compl_of_measurableSet_tail
    (Λ : FiniteVolume Site) {A : Set (Configuration Site Spin)} (hA : MeasurableSet[@tailSigmaAlgebra Site Spin _ _] A) :
    MeasurableSet[cylinderEvents (X := fun _ : Site ↦ Spin) ((Λ : Set Site)ᶜ)] A := by
  -- `tailSigmaAlgebra = ⨅ Λ, cylinderEvents (Λᶜ)`, hence it is smaller than each `cylinderEvents (Λᶜ)`.
  have hle :
      (@tailSigmaAlgebra Site Spin _ _ : MeasurableSpace (Configuration Site Spin)) ≤
        cylinderEvents (X := fun _ : Site ↦ Spin) ((Λ : Set Site)ᶜ) :=
    iInf_le (fun Λ : FiniteVolume Site => cylinderEvents (X := fun _ : Site ↦ Spin) ((Λ : Set Site)ᶜ)) Λ
  exact hle _ hA

/-! ### Restricting a Gibbs measure to a tail event gives another Gibbs measure -/

section Restrict

variable (γ : LocalSpecification Site Spin) (hMarkov : IsMarkov γ)

lemma bind_restrict_eq_of_measurableSet_boundary (hγ : IsProper γ) (Λ : FiniteVolume Site)
    {A : Set (Configuration Site Spin)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : Site ↦ Spin) ((Λ : Set Site)ᶜ)] A)
    (μ : Measure (Configuration Site Spin)) :
    (μ.restrict A).bind (γ.kernel Λ) = (μ.bind (γ.kernel Λ)).restrict A := by
  classical
  ext s hs
  have hA_pi :
      MeasurableSet A :=
    (cylinderEvents_le_pi (X := fun _ : Site ↦ Spin) (Δ := ((Λ : Set Site)ᶜ))) _ hA
  -- Kernel measurability with respect to the product sigma-algebra.
  have hker_meas : Measurable (γ.kernel Λ) :=
    ProbabilityTheory.Kernel.measurable (γ.kernel Λ)
  have hker_ae : AEMeasurable (γ.kernel Λ) μ := hker_meas.aemeasurable
  have hker_ae_restrict : AEMeasurable (γ.kernel Λ) (μ.restrict A) := hker_meas.aemeasurable
  -- Properness identity for the tail event `A`.
  have hproper :
      ∀ x : Configuration Site Spin, γ.kernel Λ x (s ∩ A) = A.indicator 1 x * γ.kernel Λ x s := by
    intro x
    -- Use properness of the specification (in the `inter_eq_indicator_mul` form).
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      (IsProper.inter_eq_indicator_mul hγ Λ hs hA x)
  -- Compute both sides using `bind_apply`, and rewrite the restricted integral via `lintegral_restrict`.
  calc
    ((μ.restrict A).bind (γ.kernel Λ)) s
        = ∫⁻ x, (γ.kernel Λ x) s ∂(μ.restrict A) := by
          simp [Measure.bind_apply hs hker_ae_restrict]
    _ = ∫⁻ x in A, (γ.kernel Λ x) s ∂μ := by
          -- This is just the definition of the set integral.
          rfl
    _ = ∫⁻ x, A.indicator (fun x => (γ.kernel Λ x) s) x ∂μ := by
          -- Convert the set integral to an integral with an indicator.
          simpa using (lintegral_indicator (μ := μ) hA_pi (f := fun x => (γ.kernel Λ x) s)).symm
    _ = ∫⁻ x, A.indicator 1 x * (γ.kernel Λ x) s ∂μ := by
          -- Turn the indicator into a multiplicative mask.
          -- Pointwise: `A.indicator g x = A.indicator (fun _ => 1) x * g x`.
          have hind :
              (fun x : Configuration Site Spin => A.indicator (fun x => (γ.kernel Λ x) s) x)
                =
              (fun x : Configuration Site Spin => A.indicator 1 x * (γ.kernel Λ x) s) := by
            funext x
            -- Rewrite `A.indicator g x` as `A.indicator (fun _ => 1 * g _) x` and apply
            -- `Set.indicator_mul_left`.
            simpa [mul_assoc] using
              (Set.indicator_mul_left (s := A)
                (f := (1 : (Configuration Site Spin) → ℝ≥0∞))
                (g := fun x : Configuration Site Spin => (γ.kernel Λ x) s) (i := x))
          simp [hind]
    _ = ∫⁻ x, (γ.kernel Λ x) (s ∩ A) ∂μ := by
          -- Apply the properness identity pointwise.
          simp [hproper]
    _ = (μ.bind (γ.kernel Λ)) (s ∩ A) := by
          simp [Measure.bind_apply (hs.inter hA_pi) hker_ae]
    _ = ((μ.bind (γ.kernel Λ)).restrict A) s := by
          simp [Measure.restrict_apply, hs, hA_pi, Set.inter_comm]

lemma bind_restrict_eq_of_measurableSet_tail (hγ : IsProper γ) (Λ : FiniteVolume Site)
    {A : Set (Configuration Site Spin)} (hA : MeasurableSet[@tailSigmaAlgebra Site Spin _ _] A)
    (μ : Measure (Configuration Site Spin)) :
    (μ.restrict A).bind (γ.kernel Λ) = (μ.bind (γ.kernel Λ)).restrict A := by
  exact bind_restrict_eq_of_measurableSet_boundary (γ := γ) (hγ := hγ) (Λ := Λ)
    (hA := measurableSet_cylinderEvents_compl_of_measurableSet_tail  Λ hA) μ

/-- If `μ` is Gibbs for `γ`, then the restriction of `μ` to a tail event is also Gibbs. -/
lemma isGibbsMeasure_restrict_of_measurableSet_tail
    (hγ : IsProper γ) {μ : Measure (Configuration Site Spin)} [IsFiniteMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    {A : Set (Configuration Site Spin)} (hA : MeasurableSet[@tailSigmaAlgebra Site Spin _ _] A) :
    IsGibbsMeasure γ (μ.restrict A) := by
  -- Use the fixed-point characterization of Gibbs measures.
  have hfix : ∀ Λ : FiniteVolume Site, μ.bind (γ.kernel Λ) = μ := by
    simpa [isGibbsMeasure_iff_forall_bind_eq (γ := γ)] using hμ
  have hfix_restrict : ∀ Λ : FiniteVolume Site, (μ.restrict A).bind (γ.kernel Λ) = μ.restrict A := by
    intro Λ
    calc
      (μ.restrict A).bind (γ.kernel Λ)
          = (μ.bind (γ.kernel Λ)).restrict A :=
            bind_restrict_eq_of_measurableSet_tail (γ := γ) (hγ := hγ) (Λ := Λ) (hA := hA) μ
      _ = μ.restrict A := by simp [hfix Λ]
  haveI : IsFiniteMeasure (μ.restrict A) := by infer_instance
  -- Convert back to the Gibbs property.
  simpa [isGibbsMeasure_iff_forall_bind_eq (γ := γ)] using hfix_restrict

end Restrict

/-! ### From non-tail-triviality to non-extremality (Georgii Thm. 7.7, easy direction) -/

section ExtremePoints

open scoped Convex

variable (γ : LocalSpecification Site Spin)

/-- The set `G(γ)` of Gibbs **probability** measures, viewed as a subset of `Measure (Configuration Site Spin)` so that
we can use Mathlib's `Set.extremePoints`. -/
def G : Set (Measure (Configuration Site Spin)) :=
  {μ | IsProbabilityMeasure μ ∧ IsGibbsMeasure γ μ}

namespace G

variable {γ}

@[simp] lemma mem_iff (μ : Measure (Configuration Site Spin)) :
    μ ∈ G (γ := γ) ↔
      IsProbabilityMeasure μ ∧ IsGibbsMeasure γ μ :=
  Iff.rfl

end G

section

variable {γ}
variable (hMarkov : IsMarkov γ)

local notation3 "Ω" => (Configuration Site Spin)

lemma measurableSet_of_measurableSet_tail {A : Set Ω}
    (hA : MeasurableSet[@tailSigmaAlgebra Site Spin _ _] A) : MeasurableSet A := by
  -- `tailSigmaAlgebra ≤ cylinderEvents univ ≤ MeasurableSpace.pi`.
  have hle_tail_pi :
      (@tailSigmaAlgebra Site Spin _ _ : MeasurableSpace Ω) ≤ MeasurableSpace.pi := by
    -- use the `Λ = ∅` term in the infimum definition of `tailSigmaAlgebra`.
    refine le_trans
      (iInf_le (fun Λ : FiniteVolume Site =>
          cylinderEvents (X := fun _ : Site ↦ Spin) ((Λ : Set Site)ᶜ)) { carrier := ∅ }) ?_
    exact MeasureTheory.cylinderEvents_le_pi
  exact hle_tail_pi _ hA

lemma bind_smul (c : ENNReal) (μ : Measure Ω) (κ : Ω → Measure Ω) (hκ : Measurable κ) :
    (c • μ).bind κ = c • (μ.bind κ) := by
  ext s hs
  simp [Measure.bind_apply hs hκ.aemeasurable, lintegral_smul_measure]

lemma bind_add (μ ν : Measure Ω) (κ : Ω → Measure Ω) (hκ : Measurable κ) :
    (μ + ν).bind κ = μ.bind κ + ν.bind κ := by
  ext s hs
  simp [Measure.bind_apply hs hκ.aemeasurable, lintegral_add_measure]

/-! ### Proper kernels commute with `withDensity` for boundary-measurable densities -/

lemma withDensity_bind_eq_bind_withDensity (Λ : FiniteVolume Site) (hγ : IsProper γ)
    (μ : Measure[cylinderEvents (X := fun _ : Site ↦ Spin) ((Λ : Set Site)ᶜ)] Ω)
    (f : Ω → ℝ≥0∞) (hf : Measurable[cylinderEvents (X := fun _ : Site ↦ Spin) ((Λ : Set Site)ᶜ)] f) :
    (μ.bind (γ.kernel Λ)).withDensity f = (μ.withDensity f).bind (γ.kernel Λ) := by
  classical
  -- We prove equality on measurable sets.
  ext A hA
  -- Upgrade measurability of `f` to the full product σ-algebra to use `withDensity_apply`.
  have hf_pi : Measurable f :=
    (hf.mono MeasureTheory.cylinderEvents_le_pi le_rfl)
  -- The integrand used in `Measure.lintegral_bind` is `A.indicator f`.
  have hAem : AEMeasurable (γ.kernel Λ) μ := (ProbabilityTheory.Kernel.measurable (γ.kernel Λ)).mono MeasureTheory.cylinderEvents_le_pi le_rfl |>.aemeasurable (μ := μ)
  have hAem' : AEMeasurable (fun x : Ω => A.indicator f x) (μ.bind (γ.kernel Λ)) :=
    (hf_pi.indicator hA).aemeasurable
  -- Expand both sides and use properness to identify the inner integral.
  -- LHS: set-lintegral of `f` against `μ.bind (γ.kernel Λ)`.
  have hLHS :
      (∫⁻ x, A.indicator f x ∂(μ.bind (γ.kernel Λ)))
        = ∫⁻ η, f η * (γ.kernel Λ η) A ∂μ := by
    -- Apply Fubini/Tonelli for `bind`.
    have hbind :=
      (Measure.lintegral_bind (m := μ) (μ := (γ.kernel Λ)) (f := fun x : Ω => A.indicator f x)
        hAem hAem')
    -- Identify the inner integral using properness of `γ`.
    -- `A.indicator f = fun x => f x * A.indicator 1 x`.
    have hind :
        (fun x : Ω => A.indicator f x) = fun x => f x * A.indicator (1 : Ω → ℝ≥0∞) x := by
      funext x
      by_cases hx : x ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
    -- Evaluate the inner integral.
    have hinner :
        (fun η : Ω => ∫⁻ x, A.indicator f x ∂(γ.kernel Λ η))
          = fun η : Ω => f η * (γ.kernel Λ η) A := by
      funext η
      -- Rewrite using `hind`, then apply the properness `lintegral_mul`.
      have hmul :
          (∫⁻ x, f x * A.indicator (1 : Ω → ℝ≥0∞) x ∂(γ.kernel Λ η))
            =
            f η * ∫⁻ x, A.indicator (1 : Ω → ℝ≥0∞) x ∂(γ.kernel Λ η) :=
        LocalSpecification.IsProper.lintegral_mul (γ := γ) (hγ := hγ) (Λ := Λ)
          (η₀ := η)
          (f := fun x : Ω => A.indicator (1 : Ω → ℝ≥0∞) x)
          (g := f)
          (hf := (measurable_one.indicator hA))
          (hg := hf)
      -- Evaluate the indicator integral.
      have hind1 : (∫⁻ x, A.indicator (1 : Ω → ℝ≥0∞) x ∂(γ.kernel Λ η)) = (γ.kernel Λ η) A := by
        simpa using (lintegral_indicator_one (μ := (γ.kernel Λ η)) hA)
      -- Finish.
      simp [hind, hmul, hind1]
    -- Finish.
    simp [hinner] at hbind
    simpa using hbind
  -- Now compare LHS/RHS using `withDensity_apply` and `bind_apply`.
  calc
    ((μ.bind (γ.kernel Λ)).withDensity f) A
        = ∫⁻ x in A, f x ∂(μ.bind (γ.kernel Λ)) := by
            simpa using (withDensity_apply f (μ := μ.bind (γ.kernel Λ)) hA)
    _ = ∫⁻ x, A.indicator f x ∂(μ.bind (γ.kernel Λ)) := by
          simpa using (lintegral_indicator (μ := (μ.bind (γ.kernel Λ))) hA (f := f)).symm
    _ = ∫⁻ η, f η * (γ.kernel Λ η) A ∂μ := hLHS
    _ = ∫⁻ η, (γ.kernel Λ η) A ∂(μ.withDensity f) := by
          -- Move `f` into the measure using `withDensity`.
          have hkerA :
              Measurable[cylinderEvents (X := fun _ : Site ↦ Spin) ((Λ : Set Site)ᶜ)]
                (fun η : Ω => (γ.kernel Λ η) A) :=
            (ProbabilityTheory.Kernel.measurable_coe (γ.kernel Λ) hA)
          simpa [Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc] using
            (lintegral_withDensity_eq_lintegral_mul (μ := μ) (f := f) hf (g := fun η : Ω => (γ.kernel Λ η) A)
              hkerA).symm
    _ = ((μ.withDensity f).bind (γ.kernel Λ)) A := by
          simp [Measure.bind_apply hA (ProbabilityTheory.Kernel.measurable (γ.kernel Λ)).aemeasurable]

/-- Normalized restriction of a probability measure to an event `A` (as a measure). -/
noncomputable def normRestrict (μ : Measure Ω) (A : Set Ω) : Measure Ω :=
  (μ A)⁻¹ • μ.restrict A

lemma normRestrict_apply (μ : Measure Ω) (A s : Set Ω) :
    normRestrict (μ := μ) A s = (μ A)⁻¹ * (μ.restrict A) s := by
  simp [normRestrict, Measure.smul_apply, smul_eq_mul]

lemma isProbabilityMeasure_normRestrict
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A : Set Ω} (hA0 : μ A ≠ 0) :
    IsProbabilityMeasure (normRestrict (μ := μ) A) := by
  -- Use the standard normalization instance `isProbabilityMeasureSMul` on `μ.restrict A`.
  haveI : IsFiniteMeasure (μ.restrict A) := by infer_instance
  have hne : μ.restrict A ≠ 0 := by
    intro h
    have : (μ.restrict A) Set.univ = 0 := by simp [h]
    -- `(μ.restrict A) univ = μ A`
    have : μ A = 0 := by simpa [Measure.restrict_apply] using this
    exact hA0 this
  haveI : NeZero (μ.restrict A) := ⟨hne⟩
  -- Now the generic instance gives probability measure after scaling by `(μ.restrict A univ)⁻¹`.
  haveI : IsProbabilityMeasure (((μ.restrict A) Set.univ)⁻¹ • (μ.restrict A)) := by infer_instance
  -- Rewrite `((μ.restrict A) univ)` as `μ A`.
  simpa [normRestrict, Measure.restrict_apply, smul_smul, smul_eq_mul] using
    (inferInstance : IsProbabilityMeasure (((μ.restrict A) Set.univ)⁻¹ • (μ.restrict A)))

lemma isGibbsMeasure_normRestrict_of_tail (hγ : IsProper γ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    {A : Set Ω} (hA_tail : MeasurableSet[@tailSigmaAlgebra Site Spin _ _] A) (hA0 : μ A ≠ 0) :
    IsGibbsMeasure γ (normRestrict (μ := μ) A) := by
  -- Use the fixed-point characterization `μ.bind (γ.kernel Λ) = μ`.
  have hfix : ∀ Λ : FiniteVolume Site, μ.bind (γ.kernel Λ) = μ := by
    haveI : IsFiniteMeasure μ := by infer_instance
    exact (isGibbsMeasure_iff_forall_bind_eq (γ := γ) hγ).1 hμ
  -- First show the restricted measure is also a fixed point for every `Λ`.
  have hfix_restrict : ∀ Λ : FiniteVolume Site, (μ.restrict A).bind (γ.kernel Λ) = μ.restrict A := by
    intro Λ
    calc
      (μ.restrict A).bind (γ.kernel Λ)
          = (μ.bind (γ.kernel Λ)).restrict A := by
              -- Tail events are boundary events, so restriction commutes with `bind`.
              simpa using
                (bind_restrict_eq_of_measurableSet_tail (γ := γ) (hγ := hγ) (Λ := Λ) (hA := hA_tail) μ)
      _ = μ.restrict A := by simp [hfix Λ]
  -- Scale the fixed-point equation.
  have hfix_norm : ∀ Λ : FiniteVolume Site,
      (normRestrict (μ := μ) A).bind (γ.kernel Λ) = normRestrict (μ := μ) A := by
    intro Λ
    have hκ : Measurable (γ.kernel Λ) :=
      (ProbabilityTheory.Kernel.measurable (γ.kernel Λ)).mono
        (MeasureTheory.cylinderEvents_le_pi (X := fun _ : Site ↦ Spin) (Δ := ((Λ : Set Site)ᶜ))) le_rfl
    calc
      (normRestrict (μ := μ) A).bind (γ.kernel Λ)
          = ((μ A)⁻¹ • (μ.restrict A)).bind (γ.kernel Λ) := rfl
      _ = (μ A)⁻¹ • ((μ.restrict A).bind (γ.kernel Λ)) := by
            simpa [normRestrict] using (bind_smul (c := (μ A)⁻¹) (μ := μ.restrict A) (κ := γ.kernel Λ) hκ)
      _ = (μ A)⁻¹ • (μ.restrict A) := by simp [hfix_restrict Λ]
      _ = normRestrict (μ := μ) A := rfl
  -- Convert fixed-point back to Gibbs property.
  haveI : IsFiniteMeasure (normRestrict (μ := μ) A) := by
    -- it's a probability measure by the previous lemma
    haveI : IsProbabilityMeasure (normRestrict (μ := μ) A) := isProbabilityMeasure_normRestrict (μ := μ) (A := A) hA0
    infer_instance
  haveI : IsProbabilityMeasure (normRestrict (μ := μ) A) :=
    isProbabilityMeasure_normRestrict (μ := μ) (A := A) hA0
  -- use the equivalence again
  -- use the equivalence again
  exact (isGibbsMeasure_iff_forall_bind_eq (γ := γ) hγ).2 hfix_norm

/-! #### Conditioning a Gibbs probability measure on a tail event stays Gibbs -/

namespace ProbabilityMeasure

/-- Normalize the restriction of a probability measure to an event with positive mass. -/
noncomputable def normRestrict (μ : ProbabilityMeasure Ω) (A : Set Ω) (hA0 : (μ : Measure Ω) A ≠ 0) :
    ProbabilityMeasure Ω :=
  ⟨MeasureTheory.GibbsMeasure.normRestrict (μ := (μ : Measure Ω)) A, by
    -- `MeasureTheory.GibbsMeasure.normRestrict` is a probability measure once we know `μ A ≠ 0`.
    haveI : IsProbabilityMeasure (μ : Measure Ω) := by infer_instance
    exact isProbabilityMeasure_normRestrict (μ := (μ : Measure Ω)) (A := A) hA0⟩

@[simp] lemma coe_normRestrict (μ : ProbabilityMeasure Ω) (A : Set Ω) (hA0 : (μ : Measure Ω) A ≠ 0) :
    ((normRestrict (μ := μ) A hA0 : ProbabilityMeasure Ω) : Measure Ω)
      =
      MeasureTheory.GibbsMeasure.normRestrict (μ := (μ : Measure Ω)) A :=
  rfl

lemma mem_GP_normRestrict_of_tail (hγ : IsProper γ) {μ : ProbabilityMeasure Ω}
    (hμ : μ ∈ GP  γ)
    {A : Set Ω} (hA_tail : MeasurableSet[@tailSigmaAlgebra Site Spin _ _] A) (hA0 : (μ : Measure Ω) A ≠ 0) :
    normRestrict (μ := μ) A hA0 ∈ GP  γ := by
  -- Unpack `μ ∈ GP γ` to a Gibbs property for the underlying measure.
  have hμ_gibbs : IsGibbsMeasure γ (μ : Measure Ω) := hμ
  -- Apply the measure-level conditioning lemma.
  have hcond_gibbs :
      IsGibbsMeasure γ
        (MeasureTheory.GibbsMeasure.normRestrict (μ := (μ : Measure Ω)) A) :=
    isGibbsMeasure_normRestrict_of_tail (γ := γ) (hγ := hγ) (μ := (μ : Measure Ω)) hμ_gibbs
      (A := A) hA_tail hA0
  -- Convert back to membership in `GP`.
  exact hcond_gibbs

end ProbabilityMeasure

/-- If a Gibbs probability measure assigns a tail event probability strictly between `0` and `1`,
then it is **not** an extreme point of `G(γ)`. -/
theorem not_mem_extremePoints_G_of_tail_prob
    (hγ : IsProper γ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    {A : Set Ω} (hA_tail : MeasurableSet[@tailSigmaAlgebra Site Spin _ _] A)
    (hA0 : 0 < μ A) (hA1 : μ A < 1) :
    μ ∉ (G (γ := γ)).extremePoints ENNReal := by
  classical
  -- Define the two conditional measures.
  let μA : Measure Ω := normRestrict (μ := μ) A
  let μAc : Measure Ω := normRestrict (μ := μ) Aᶜ
  have hA0' : μ A ≠ 0 := ne_of_gt hA0
  have hAc0' : μ Aᶜ ≠ 0 := by
    -- `μ Aᶜ = 0 ↔ μ A = 1`, contradicting `μ A < 1`.
    have hA_meas : MeasurableSet A := measurableSet_of_measurableSet_tail  hA_tail
    intro hAcompl0
    have hμA_le : μ A ≤ 1 := by
      have : μ A ≤ μ (Set.univ : Set Ω) := measure_mono (subset_univ A)
      simpa [IsProbabilityMeasure.measure_univ (μ := μ)] using this
    -- From `μ Aᶜ = 0`, get `μ A = 1` using `μ Aᶜ = 1 - μ A`.
    have hμA : μ A = 1 := by
      have hcompl : μ Aᶜ = 1 - μ A := prob_compl_eq_one_sub (μ := μ) hA_meas
      have : 1 - μ A = 0 := by simpa [hcompl] using hAcompl0
      -- `1 - μ A = 0` implies `1 ≤ μ A`; combined with `μ A ≤ 1` gives `μ A = 1`.
      have hge : 1 ≤ μ A := (tsub_eq_zero_iff_le).1 this
      exact le_antisymm hμA_le hge
    exact (ne_of_lt hA1) hμA
  -- Show `μA`, `μAc` are in `G(γ)`.
  have hμA_prob : IsProbabilityMeasure μA := isProbabilityMeasure_normRestrict (μ := μ) (A := A) hA0'
  have hμAc_prob : IsProbabilityMeasure μAc := isProbabilityMeasure_normRestrict (μ := μ) (A := Aᶜ) hAc0'
  have hμA_gibbs : IsGibbsMeasure γ μA :=
    isGibbsMeasure_normRestrict_of_tail (γ := γ) (hγ := hγ) (μ := μ) hμ (A := A) hA_tail hA0'
  have hμAc_gibbs : IsGibbsMeasure γ μAc := by
    -- `Aᶜ` is also tail-measurable.
    have hA_tail' : MeasurableSet[@tailSigmaAlgebra Site Spin _ _] Aᶜ := by
      simpa using (MeasurableSet.compl hA_tail)
    exact isGibbsMeasure_normRestrict_of_tail (γ := γ) (hγ := hγ) (μ := μ) hμ (A := Aᶜ) hA_tail' hAc0'
  have hμA_mem : μA ∈ G (γ := γ) := ⟨hμA_prob, hμA_gibbs⟩
  have hμAc_mem : μAc ∈ G (γ := γ) := ⟨hμAc_prob, hμAc_gibbs⟩
  have hμ_mem : μ ∈ G (γ := γ) := ⟨inferInstance, hμ⟩
  -- Show `μ ∈ openSegment μA μAc`.
  have hA_meas : MeasurableSet A := measurableSet_of_measurableSet_tail  hA_tail
  have hsum : μ A + μ Aᶜ = 1 := prob_add_prob_compl (μ := μ) hA_meas
  have hseg : μ ∈ openSegment ENNReal μA μAc := by
    refine ⟨μ A, μ Aᶜ, hA0, ?_, hsum, ?_⟩
    · -- positivity of `μ Aᶜ`
      have : μ Aᶜ ≠ 0 := hAc0'
      exact pos_iff_ne_zero.2 this
    · -- the convex combination equals `μ`
      -- First simplify `μ A • μA = μ.restrict A`.
      have hA_ne_top : μ A ≠ ∞ := by
        -- `μ A ≤ 1`, so `μ A` is finite.
        have : μ A ≤ 1 := by simpa [measure_univ] using (prob_le_one)
        exact ne_top_of_le_ne_top (by simp) this
      have hAc_ne_top : μ Aᶜ ≠ ∞ := by
        have : μ Aᶜ ≤ 1 := by simpa [measure_univ] using (prob_le_one)
        exact ne_top_of_le_ne_top (by simp) this
      have hmulA : (μ A) • μA = μ.restrict A := by
        -- `a • (a⁻¹ • μ.restrict A) = μ.restrict A`.
        have : (μ A) * (μ A)⁻¹ = (1 : ENNReal) := by
          simpa [mul_comm] using ENNReal.inv_mul_cancel hA0' hA_ne_top
        simp [μA, normRestrict, smul_smul, this]
      have hmulAc : (μ Aᶜ) • μAc = μ.restrict Aᶜ := by
        have : (μ Aᶜ) * (μ Aᶜ)⁻¹ = (1 : ENNReal) := by
          simpa [mul_comm] using ENNReal.inv_mul_cancel hAc0' hAc_ne_top
        simp [μAc, normRestrict, smul_smul, this]
      -- Now combine the restricted measures.
      have : (μ A) • μA + (μ Aᶜ) • μAc = μ := by
        simp [hmulA, hmulAc, Measure.restrict_add_restrict_compl hA_meas]
      simp [this]
  -- Use the definition of extreme points.
  intro hext
  rcases (mem_extremePoints_iff_left (𝕜 := ENNReal) (A := G (γ := γ)) (x := μ)).1 hext with ⟨_hμ_in, hleft⟩
  have hEq : μA = μ := hleft μA hμA_mem μAc hμAc_mem hseg
  -- Contradict by evaluating the event `A`.
  have hμA_A : μA A = 1 := by
    -- `μA` is the normalized restriction to `A`.
    have hA_ne_top : μ A ≠ ∞ := by
      have : μ A ≤ 1 := by simpa using (prob_le_one)
      exact ne_top_of_le_ne_top (by simp) this
    calc
      μA A = (μ A)⁻¹ * (μ.restrict A) A := by
        simp [μA, normRestrict, Measure.smul_apply, smul_eq_mul]
      _ = (μ A)⁻¹ * μ A := by simp [Measure.restrict_apply hA_meas, Set.inter_self]
      _ = 1 := ENNReal.inv_mul_cancel hA0' hA_ne_top
  -- But `μ A < 1`.
  have : μ A = 1 := by simpa [hEq] using hμA_A
  exact (ne_of_lt hA1) this

/-- **Extreme** Gibbs probability measures are **tail-trivial** (Georgii Thm. 7.7, direction
`extreme → tail-trivial`). -/
theorem tailTrivial_of_mem_extremePoints_G
    (hγ : IsProper γ) {μ : Measure Ω}
    (hμext : μ ∈ (G (γ := γ)).extremePoints ENNReal) :
    ∀ A, MeasurableSet[@tailSigmaAlgebra Site Spin _ _] A → μ A = 0 ∨ μ A = 1 := by
  intro A hA_tail
  -- `μ ∈ G(γ)` and `μ` is Gibbs + probability.
  rcases (mem_extremePoints (𝕜 := ENNReal) (A := G (γ := γ)) (x := μ)).1 hμext with ⟨hμG, _hleft⟩
  rcases hμG with ⟨hμ_prob, hμ_gibbs⟩
  haveI : IsProbabilityMeasure μ := hμ_prob
  -- If `μ A` is neither `0` nor `1`, we contradict extremality using the previous theorem.
  by_contra h
  have hne0 : μ A ≠ 0 := by
    intro h0
    exact h (Or.inl h0)
  have hne1 : μ A ≠ 1 := by
    intro h1
    exact h (Or.inr h1)
  have hpos : 0 < μ A := pos_iff_ne_zero.2 hne0
  have hle : μ A ≤ 1 := by
    -- `μ A ≤ μ univ = 1`.
    have : μ A ≤ μ (Set.univ : Set Ω) := measure_mono (subset_univ A)
    simpa [IsProbabilityMeasure.measure_univ (μ := μ)] using this
  have hlt : μ A < 1 := lt_of_le_of_ne hle hne1
  exact (not_mem_extremePoints_G_of_tail_prob (γ := γ) (hγ := hγ) (μ := μ) hμ_gibbs
      (hA_tail := hA_tail) hpos hlt) hμext

/-- Probability-measure version of `tailTrivial_of_mem_extremePoints_G`. -/
theorem isTailTrivial_of_mem_extremePoints_G
    (hγ : IsProper γ) (μ : ProbabilityMeasure Ω)
    (hμext : (μ : Measure Ω) ∈ (G (γ := γ)).extremePoints ENNReal) :
    IsTailTrivial μ := by
  intro A hA
  -- unfold `IsTailTrivial` and reuse the measure-level lemma
  simpa using
    tailTrivial_of_mem_extremePoints_G (γ := γ) (hγ := hγ) (μ := (μ : Measure Ω)) hμext A hA

/-! ### Tail-triviality implies extremality (Georgii Thm. 7.7, hard direction) -/

section TailTrivialImpliesExtreme

open Filter

variable [Countable Site]

omit [MeasurableSpace Spin] [Countable Site] in
lemma measurable_iInf_iff {ι : Sort*} (m : ι → MeasurableSpace Ω) {X : Type*}
    [MeasurableSpace X] {f : Ω → X} :
    Measurable[iInf m] f ↔ ∀ i, Measurable[m i] f := by
  constructor
  · intro hf i
    exact hf.mono (iInf_le m i) le_rfl
  · intro hf s hs
    -- `MeasurableSet` for the infimum σ-algebra is exactly measurability in each component.
    exact (MeasurableSpace.measurableSet_iInf (m := m) (s := f ⁻¹' s)).2 (fun i => (hf i) hs)

lemma iInf_eq_iInf_ge_of_antitone {α : Type*} [CompleteLattice α] (h : ℕ → α)
    (hh : Antitone h) (N : ℕ) :
    (⨅ n : ℕ, h n) = (⨅ n : {n // N ≤ n}, h n.1) := by
  refine le_antisymm ?_ ?_
  · refine le_iInf ?_
    intro n
    exact iInf_le (fun k : ℕ => h k) n.1
  · refine le_iInf ?_
    intro n
    by_cases hn : N ≤ n
    · simpa using (iInf_le (fun k : {k // N ≤ k} => h k.1) ⟨n, hn⟩)
    · have hNle : (⨅ k : {k // N ≤ k}, h k.1) ≤ h N := by
        simpa using (iInf_le (fun k : {k // N ≤ k} => h k.1) ⟨N, le_rfl⟩)
      have hn' : n ≤ N := le_of_not_ge hn
      have hhn : h N ≤ h n := hh hn'
      exact hNle.trans hhn

lemma antitone_iSup_ge {α : Type*} [CompleteLattice α] (g : ℕ → α) :
    Antitone (fun n : ℕ => (⨆ i : ℕ, ⨆ (_ : i ≥ n), g i)) := by
  intro a b hab
  refine iSup_le ?_
  intro i
  refine iSup_le ?_
  intro hib
  exact le_iSup_of_le i (le_iSup_of_le (le_trans hab hib) le_rfl)

omit [MeasurableSpace Spin] [Countable Site] in
lemma measurable_limsup_of_antitone_measurableSpace
    (m : ℕ → MeasurableSpace Ω) (hm : Antitone m)
    (g : ℕ → Ω → ℝ≥0∞) (hg : ∀ n, Measurable[m n] (g n)) :
    Measurable[iInf m] (fun ω : Ω => Filter.limsup (fun n => g n ω) atTop) := by
  -- It suffices to show measurability w.r.t. each `m N`.
  have himp : Measurable[iInf m] (fun ω : Ω => Filter.limsup (fun n => g n ω) atTop) ↔
      ∀ N : ℕ, Measurable[m N] (fun ω : Ω => Filter.limsup (fun n => g n ω) atTop) :=
    measurable_iInf_iff (m := m)
  refine (himp).2 ?_
  intro N
  -- Rewrite `limsup` as `iInf iSup`, then drop the finite prefix of the `iInf` using antitonicity.
  have h_limsup :
      (fun ω : Ω => Filter.limsup (fun n => g n ω) atTop) =
        fun ω : Ω => (⨅ n : ℕ, ⨆ i : ℕ, ⨆ (_ : i ≥ n), g i ω) := by
    funext ω
    simpa using (Filter.limsup_eq_iInf_iSup_of_nat (u := fun n => g n ω))
  -- Define the antitone sequence `h n = sup_{i ≥ n} g i`.
  let h : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨆ i : ℕ, ⨆ (_ : i ≥ n), g i ω
  -- Drop the finite prefix: `⨅ n, h n = ⨅ n ≥ N, h n`.
  have h_drop :
      (fun ω : Ω => (⨅ n : ℕ, h n ω)) =
        fun ω : Ω => (⨅ n : {n // N ≤ n}, h n.1 ω) := by
    funext ω
    have hhω : Antitone (fun n : ℕ => h n ω) := by
      intro a b hab
      exact antitone_iSup_ge (g := fun i => g i ω) hab
    exact iInf_eq_iInf_ge_of_antitone (h := fun n => h n ω) (hh := hhω) N
  -- Now show measurability in `m N`.
  -- For `n ≥ N`, each `g i` with `i ≥ n` is measurable w.r.t `m N` since `m i ≤ m N`.
  have h_meas_h :
      ∀ n : {n // N ≤ n}, Measurable[m N] (h n.1) := by
    intro n
    -- `h n.1` is an `iSup` over the countable subtype `{i // i ≥ n.1}`.
    have h_meas_each :
        ∀ i : {i // i ≥ n.1}, Measurable[m N] (g i.1) := by
      intro i
      -- `N ≤ n.1 ≤ i.1`, so `m i.1 ≤ m N` by antitonicity.
      have hNi : N ≤ i.1 := le_trans n.2 i.2
      have hmi : m i.1 ≤ m N := hm hNi
      exact (hg i.1).mono hmi le_rfl
    -- Form the supremum.
    have :
        Measurable[m N] (fun ω : Ω => ⨆ i : {i // i ≥ n.1}, g i.1 ω) :=
      Measurable.iSup (f := fun i : {i // i ≥ n.1} => g i.1) h_meas_each
    -- The nested `iSup` over proofs is definitional equal to the subtype supremum.
    -- We just rewrite `h` accordingly.
    simpa [h, iSup_subtype] using this
  -- Finally, `⨅ n ≥ N, h n` is measurable as an infimum over a countable type.
  have h_meas_drop :
      Measurable[m N] (fun ω : Ω => (⨅ n : {n // N ≤ n}, h n.1 ω)) :=
    Measurable.iInf (f := fun n : {n // N ≤ n} => h n.1) h_meas_h
  -- Combine rewrites.
  -- `limsup` = `⨅ n, h n` = dropped infimum.
  have :
      Measurable[m N] (fun ω : Ω => Filter.limsup (fun n => g n ω) atTop) := by
    -- `Measurable` is stable under definitional rewriting.
    -- We thread the rewrites via `simp`.
    simpa [h_limsup, h_drop, h] using h_meas_drop
  exact this

noncomputable def exhaustionVolumes : ℕ → FiniteVolume Site := by
  classical
  by_cases hS : Nonempty Site
  · exact fun n => (Finset.range n).image (Classical.choose (exists_surjective_nat Site))
  · exact fun _ => ∅

lemma exhaustionVolumes_monotone :
    Monotone (exhaustionVolumes (Site := Site) : ℕ → FiniteVolume Site) := by
  classical
  by_cases hS : Nonempty Site
  · -- unfold the definition in the nonempty case
    simp [exhaustionVolumes, hS]
    intro a b hab
    -- `range a ⊆ range b` when `a ≤ b`.
    exact Finset.image_subset_image (Finset.range_mono hab)
  ·
    -- empty `Site`: the exhaustion is constantly `∅`
    intro a b hab
    simp [exhaustionVolumes, hS]

lemma exhaustionVolumes_cofinal (Λ : FiniteVolume Site) :
    ∃ n : ℕ, Λ ⊆ exhaustionVolumes (Site := Site) n := by
  classical
  by_cases hS : Nonempty Site
  · -- Use a surjective enumeration of `Site`.
    let f : ℕ → Site := Classical.choose (exists_surjective_nat Site)
    have hf : Function.Surjective f := Classical.choose_spec (exists_surjective_nat Site)
    have hexh : (exhaustionVolumes (Site := Site) : ℕ → FiniteVolume Site) = fun n => (Finset.range n).image f := by
      simp [exhaustionVolumes, hS, f]
    -- For each `x ∈ Λ`, pick an index `n_x` with `f n_x = x`.
    classical
    have : ∀ x : Site, x ∈ Λ → ∃ n, f n = x := by
      intro x hx
      exact ⟨Classical.choose (hf x), Classical.choose_spec (hf x)⟩
    -- Take `n` large enough to contain all chosen indices.
    classical
    let ns : Finset ℕ := Λ.attach.image fun x => Classical.choose (hf x.1)
    have hns : ∀ x : Site, x ∈ Λ → Classical.choose (hf x) ∈ ns := by
      intro x hx
      -- `x` appears in `Λ.attach` as `⟨x, hx⟩`.
      have : (⟨x, hx⟩ : {y // y ∈ Λ}) ∈ Λ.attach := by
        simp
      -- Now membership in the image.
      exact Finset.mem_image_of_mem _ this
    let n0 : ℕ := ns.sup id + 1
    refine ⟨n0, ?_⟩
    intro x hx
    -- Show `x ∈ (range n0).image f`.
    have hx_idx : Classical.choose (hf x) < n0 := by
      -- `choose (hf x) ≤ sup id ns` and `< sup + 1`.
      have hle : Classical.choose (hf x) ≤ ns.sup id := by
        exact Finset.le_sup (f := id) (hns x hx)
      exact lt_of_le_of_lt hle (Nat.lt_succ_self _)
    -- Conclude via membership in `range`.
    have hx_mem_range : Classical.choose (hf x) ∈ Finset.range n0 := by
      simpa [Finset.mem_range] using hx_idx
    -- Finally, use `hf` to rewrite `f (choose _) = x`.
    have hfx : f (Classical.choose (hf x)) = x := Classical.choose_spec (hf x)
    -- `x` is in the image.
    -- Re-express the goal using `hexh`.
    have : x ∈ (Finset.range n0).image f := by
      refine Finset.mem_image.2 ?_
      refine ⟨Classical.choose (hf x), hx_mem_range, ?_⟩
      simp [hfx]
    simpa [hexh] using this
  · -- If `Site` is empty, every finite set is empty.
    have : Λ = ∅ := by
      classical
      simpa using (Finset.eq_empty_of_forall_notMem (s := Λ) (by
        intro x hx
        exact (hS ⟨x⟩)))
    subst this
    refine ⟨0, by simp [exhaustionVolumes, hS]⟩

lemma tailSigmaAlgebra_eq_iInf_exhaustion :
    (@tailSigmaAlgebra Site Spin _ _ : MeasurableSpace Ω)
      =
      ⨅ n : ℕ,
        cylinderEvents (X := fun _ : Site ↦ Spin) (((exhaustionVolumes (Site := Site) n : FiniteVolume Site) : Set Site)ᶜ) := by
  classical
  -- Let `m Λ = cylinderEvents (Λᶜ)`.
  let m : FiniteVolume Site → MeasurableSpace Ω :=
    fun Λ => cylinderEvents (X := fun _ : Site ↦ Spin) ((Λ : Set Site)ᶜ)
  -- `≤`: inf over all finsets is below the inf over the subsequence.
  have hle :
      (⨅ Λ : FiniteVolume Site, m Λ) ≤
        (⨅ n : ℕ, m (exhaustionVolumes (Site := Site) n)) := by
    refine le_iInf ?_
    intro n
    exact iInf_le (fun Λ : FiniteVolume Site => m Λ) (exhaustionVolumes (Site := Site) n)
  -- `≥`: use cofinality of the exhaustion.
  have hge :
      (⨅ n : ℕ, m (exhaustionVolumes (Site := Site) n)) ≤
        (⨅ Λ : FiniteVolume Site, m Λ) := by
    refine le_iInf ?_
    intro Λ
    rcases exhaustionVolumes_cofinal (Site := Site) (Λ := Λ) with ⟨n, hn⟩
    -- From `Λ ⊆ Λn` we get `Λnᶜ ⊆ Λᶜ` and hence `m (Λn) ≤ m Λ`.
    have hcompl : (((exhaustionVolumes (Site := Site) n : FiniteVolume Site) : Set Site)ᶜ) ⊆ ((Λ : Set Site)ᶜ) := by
      intro x hx
      intro hxΛ
      exact hx (hn hxΛ)
    have hmmono : m (exhaustionVolumes (Site := Site) n) ≤ m Λ :=
      MeasureTheory.cylinderEvents_mono (X := fun _ : Site ↦ Spin) (h := hcompl)
    exact (iInf_le (fun n : ℕ => m (exhaustionVolumes (Site := Site) n)) n).trans hmmono
  -- Unfold `tailSigmaAlgebra` and `m`.
  simpa [tailSigmaAlgebra, m] using le_antisymm hle hge

omit (hMarkov : IsMarkov γ) [Countable Site] in
lemma bind_eq_bind_trim (Λ : FiniteVolume Site) (μ : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) :
    (μ.trim (MeasureTheory.cylinderEvents_le_pi (X := fun _ : Site ↦ Spin) (Δ := ((Λ : Set Site)ᶜ)))).bind (γ.kernel Λ) A
      =
    μ.bind (γ.kernel Λ) A := by
  -- The integrand `η ↦ (γ.kernel Λ η) A` is measurable w.r.t. `cylinderEvents (Λᶜ)`, so trimming does not
  -- change the bind integral.
  have hkerA :
      Measurable[cylinderEvents (X := fun _ : Site ↦ Spin) ((Λ : Set Site)ᶜ)] (fun η : Ω => (γ.kernel Λ η) A) :=
    (ProbabilityTheory.Kernel.measurable_coe (γ.kernel Λ) hA)
  have hkerA_pi : Measurable (fun η : Ω => (γ.kernel Λ η) A) :=
    hkerA.mono (MeasureTheory.cylinderEvents_le_pi (X := fun _ : Site ↦ Spin) (Δ := ((Λ : Set Site)ᶜ))) le_rfl
  -- `bind_apply` + `lintegral_trim`.
  have hAEM : AEMeasurable (γ.kernel Λ) μ :=
    ((ProbabilityTheory.Kernel.measurable (γ.kernel Λ)).mono
        (MeasureTheory.cylinderEvents_le_pi (X := fun _ : Site ↦ Spin) (Δ := ((Λ : Set Site)ᶜ))) le_rfl).aemeasurable
  have hAEM_trim : AEMeasurable (γ.kernel Λ) (μ.trim (MeasureTheory.cylinderEvents_le_pi (X := fun _ : Site ↦ Spin) (Δ := ((Λ : Set Site)ᶜ)))) :=
    (ProbabilityTheory.Kernel.measurable (γ.kernel Λ)).aemeasurable
  -- Evaluate both binds and use `lintegral_trim`.
  simp [Measure.bind_apply hA hAEM, Measure.bind_apply hA hAEM_trim,
    MeasureTheory.lintegral_trim (hm := MeasureTheory.cylinderEvents_le_pi (X := fun _ : Site ↦ Spin) (Δ := ((Λ : Set Site)ᶜ)))
      (f := fun η : Ω => (γ.kernel Λ η) A) hkerA]

omit [Countable Site] in
lemma exists_withDensity_of_absolutelyContinuous_gibbs
    (hγ : IsProper γ)
    {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : IsGibbsMeasure γ μ)
    (hν : IsGibbsMeasure γ ν)
    (hνμ : ν ≪ μ) (Λ : FiniteVolume Site) :
    ∃ g : Ω → ℝ≥0∞,
      Measurable[cylinderEvents (X := fun _ : Site ↦ Spin) ((Λ : Set Site)ᶜ)] g ∧
      μ.withDensity g = ν := by
  classical
  -- Work on the boundary σ-algebra `cylinderEvents (Λᶜ)`.
  let hm := MeasureTheory.cylinderEvents_le_pi (X := fun _ : Site ↦ Spin) (Δ := ((Λ : Set Site)ᶜ))
  let μb : Measure[cylinderEvents (X := fun _ : Site ↦ Spin) ((Λ : Set Site)ᶜ)] Ω := μ.trim hm
  let νb : Measure[cylinderEvents (X := fun _ : Site ↦ Spin) ((Λ : Set Site)ᶜ)] Ω := ν.trim hm
  have hνbμb : νb ≪ μb := (Measure.AbsolutelyContinuous.trim (hμν := hνμ) hm)
  -- Define the boundary RN density.
  let g : Ω → ℝ≥0∞ := (νb.rnDeriv μb)
  have hg : Measurable[cylinderEvents (X := fun _ : Site ↦ Spin) ((Λ : Set Site)ᶜ)] g :=
    Measure.measurable_rnDeriv νb μb
  -- `μb.withDensity g = νb`.
  haveI : IsFiniteMeasure μb := by infer_instance
  haveI : IsFiniteMeasure νb := by infer_instance
  haveI : SigmaFinite μb := by infer_instance
  haveI : SFinite νb := by infer_instance
  haveI : νb.HaveLebesgueDecomposition μb := Measure.haveLebesgueDecomposition_of_sigmaFinite νb μb
  have hμb : μb.withDensity g = νb := by
    -- `withDensity_rnDeriv_eq` expects `νb ≪ μb`.
    simpa [g] using (Measure.withDensity_rnDeriv_eq (μ := νb) (ν := μb) hνbμb)
  -- Use Gibbs fixed-point equations to lift from boundary density to the full measure.
  have hbindμ : μ.bind (γ.kernel Λ) = μ := by
    -- fixed-point characterization
    have := (isGibbsMeasure_iff_forall_bind_eq  (γ := γ) hγ).1 hμ
    simpa using this Λ
  have hbindν : ν.bind (γ.kernel Λ) = ν := by
    have := (isGibbsMeasure_iff_forall_bind_eq  (γ := γ) hγ).1 hν
    simpa using this Λ
  -- Show `μb.bind (γ.kernel Λ) = μ` and `νb.bind (γ.kernel Λ) = ν` by trimming-invariance of the bind integral.
  have hμb_bind : μb.bind (γ.kernel Λ) = μ := by
    ext A hA
    -- `μb.bind` equals `μ.bind` on measurable sets, and `μ.bind = μ`.
    have := bind_eq_bind_trim (γ := γ) (Λ := Λ) (μ := μ) (A := A) hA
    simpa [μb, hbindμ] using this
  have hνb_bind : νb.bind (γ.kernel Λ) = ν := by
    ext A hA
    have := bind_eq_bind_trim (γ := γ) (Λ := Λ) (μ := ν) (A := A) hA
    simpa [νb, hbindν] using this
  -- Commute `withDensity` through `bind` (properness), then conclude.
  have hcomm :
      (μb.bind (γ.kernel Λ)).withDensity g = (μb.withDensity g).bind (γ.kernel Λ) :=
    withDensity_bind_eq_bind_withDensity (γ := γ) (Λ := Λ) hγ μb g hg
  refine ⟨g, hg, ?_⟩
  -- Substitute the computed binds.
  calc
    μ.withDensity g = (μb.bind (γ.kernel Λ)).withDensity g := by simp [hμb_bind]
    _ = (μb.withDensity g).bind (γ.kernel Λ) := hcomm
    _ = (νb).bind (γ.kernel Λ) := by simp [hμb, μb] -- `μb.withDensity g = νb`
    _ = ν := hνb_bind

lemma ae_eq_tailMeasurable_of_forall_boundary
    (hγ : IsProper γ)
    {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : IsGibbsMeasure γ μ)
    (hν : IsGibbsMeasure γ ν)
    (hνμ : ν ≪ μ) :
    ∃ g : Ω → ℝ≥0∞,
      Measurable[@tailSigmaAlgebra Site Spin _ _] g ∧
      (ν.rnDeriv μ) =ᵐ[μ] g := by
  classical
  -- Build the cofinal exhaustion `Λn` of finite volumes.
  let Λn : ℕ → FiniteVolume Site := exhaustionVolumes (Site := Site)
  have hmonoΛ : Monotone Λn := exhaustionVolumes_monotone (Site := Site)
  -- The corresponding boundary σ-algebras decrease.
  let m : ℕ → MeasurableSpace Ω :=
    fun n => cylinderEvents (X := fun _ : Site ↦ Spin) (((Λn n : FiniteVolume Site) : Set Site)ᶜ)
  have hm_antitone : Antitone m := by
    intro a b hab
    -- `Λn a ⊆ Λn b` ⇒ complements reverse ⇒ cylinderEvents monotone.
    have hsub : (Λn a : Set Site) ⊆ (Λn b : Set Site) := by
      intro x hx
      exact hmonoΛ hab hx
    have hcompl : ((Λn b : Set Site)ᶜ) ⊆ ((Λn a : Set Site)ᶜ) := by
      intro x hx
      intro hxa
      exact hx (hsub hxa)
    exact MeasureTheory.cylinderEvents_mono (X := fun _ : Site ↦ Spin) (h := hcompl)
  -- For each `n`, build a boundary-measurable density `g_n` such that `μ.withDensity g_n = ν`.
  choose g hgmeas hμg using
    fun n =>
      exists_withDensity_of_absolutelyContinuous_gibbs  (γ := γ) hγ
        (hμ := hμ) (hν := hν) (hνμ := hνμ) (Λ := Λn n)
  -- Then `ν.rnDeriv μ = g n` a.e. for each `n`.
  have hfg : ∀ n, (ν.rnDeriv μ) =ᵐ[μ] g n := by
    intro n
    haveI : SigmaFinite μ := by
      haveI : IsFiniteMeasure μ := by infer_instance
      infer_instance
    -- Use `rnDeriv_withDensity` with `ν := μ` and `f := g n`.
    -- First rewrite `ν` as `μ.withDensity (g n)`.
    have hνeq : ν = μ.withDensity (g n) := (hμg n).symm
    -- `rnDeriv_withDensity` gives `(μ.withDensity (g n)).rnDeriv μ =ᵐ[μ] g n`.
    have hg_pi : Measurable (g n) :=
      (hgmeas n).mono
        (MeasureTheory.cylinderEvents_le_pi (X := fun _ : Site ↦ Spin) (Δ := ((Λn n : Set Site)ᶜ))) le_rfl
    simpa [hνeq] using (Measure.rnDeriv_withDensity (ν := μ) (f := g n) hg_pi)
  -- Define the candidate tail-measurable version as a limsup of the `g n`.
  let gtail : Ω → ℝ≥0∞ := fun ω => Filter.limsup (fun n => g n ω) atTop
  have hgtail_meas : Measurable[iInf m] gtail := by
    -- Apply the generic measurability lemma for limsups over an antitone family of σ-algebras.
    have hg' : ∀ n, Measurable[m n] (g n) := hgmeas
    exact measurable_limsup_of_antitone_measurableSpace (m := m) hm_antitone (g := g) hg'
  -- Identify `iInf m` with the tail σ-algebra (cofinality of the exhaustion).
  have htail_eq : (@tailSigmaAlgebra Site Spin _ _ : MeasurableSpace Ω) = iInf m := by
    simpa [m, Λn] using (tailSigmaAlgebra_eq_iInf_exhaustion)
  have hgtail_tail : Measurable[@tailSigmaAlgebra Site Spin _ _] gtail := by
    -- rewrite using `htail_eq`
    simpa [htail_eq] using hgtail_meas
  -- Finally, show `ν.rnDeriv μ = gtail` a.e.: since `ν.rnDeriv μ = g n` a.e. for all `n`,
  -- the sequence `g n ω` is eventually constant a.e., hence its limsup equals `ν.rnDeriv μ`.
  have hpoint :
      ∀ᵐ ω ∂μ, (∀ n, g n ω = (ν.rnDeriv μ) ω) := by
    -- Countable intersection of full-measure sets.
    have h_event : ∀ n, ∀ᵐ ω ∂μ, g n ω = (ν.rnDeriv μ) ω := by
      intro n
      simpa [Filter.EventuallyEq] using (hfg n).symm
    -- Use `ae_all_iff` (countable index).
    exact (ae_all_iff).2 (fun n => h_event n)
  have hlimsup :
      (ν.rnDeriv μ) =ᵐ[μ] gtail := by
    filter_upwards [hpoint] with ω hω
    -- On this ω, the sequence is constant, so limsup is that constant.
    have : (fun n => g n ω) = fun _ : ℕ => (ν.rnDeriv μ) ω := by
      funext n; simpa using (hω n)
    simp [gtail, this]
  exact ⟨gtail, hgtail_tail, hlimsup⟩

/-- If `μ` is Gibbs and tail-trivial, then any absolutely continuous Gibbs measure equals `μ`.

This is the key analytic step in Georgii Thm. 7.7, direction `tail-trivial → extreme`. -/
theorem eq_of_absolutelyContinuous_of_isTailTrivial
    (hγ : IsProper γ)
    {μ ν : Measure Ω}
    (hμG : IsGibbsMeasure γ μ)
    (hνG : IsGibbsMeasure γ ν)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμtail : IsTailTrivial (⟨μ, ‹IsProbabilityMeasure μ›⟩ : ProbabilityMeasure Ω))
    (hνμ : ν ≪ μ) :
    ν = μ := by
  classical
  -- Get a tail-measurable version of the RN derivative.
  obtain ⟨g, hg_tail, hfg⟩ :=
    ae_eq_tailMeasurable_of_forall_boundary  (γ := γ) hγ hμG hνG hνμ
  -- Tail-triviality forces `g` to be a.e. constant.
  haveI : MeasurableSpace.CountablySeparated ℝ≥0∞ := by infer_instance
  haveI : Nonempty ℝ≥0∞ := by infer_instance
  obtain ⟨c, hgc⟩ :=
    IsTailTrivial.ae_eq_const_of_measurable
      (μ := (⟨μ, ‹IsProbabilityMeasure μ›⟩ : ProbabilityMeasure Ω)) hμtail (f := g) hg_tail
  -- Hence `ν.rnDeriv μ` is a.e. equal to the constant `c`.
  have hfc : (ν.rnDeriv μ) =ᵐ[μ] fun _ => c := hfg.trans hgc
  -- Conclude `ν = c • μ`, then use mass `1` to get `c = 1`.
  haveI : SigmaFinite μ := by
    haveI : IsFiniteMeasure μ := by infer_instance
    infer_instance
  haveI : μ.HaveLebesgueDecomposition ν := Measure.haveLebesgueDecomposition_of_sigmaFinite μ ν
  -- `ν = μ.withDensity (ν.rnDeriv μ)`.
  have hν_repr : μ.withDensity (ν.rnDeriv μ) = ν := by
    simpa using (Measure.withDensity_rnDeriv_eq (μ := ν) (ν := μ) hνμ)
  -- Replace the density by the constant.
  have hν_const : μ.withDensity (fun _ => c) = ν := by
    -- use congruence under a.e. equality of densities
    have : μ.withDensity (ν.rnDeriv μ) = μ.withDensity (fun _ => c) :=
      withDensity_congr_ae (μ := μ) (h := hfc)
    simpa [hν_repr] using this.symm
  -- Convert to a scalar multiple and compare total masses.
  have hν_smul : ν = c • μ := by
    simpa [withDensity_const (μ := μ)] using hν_const.symm
  -- Evaluate on `univ` to get `c = 1`.
  have hmass : c = 1 := by
    have hμ1 : μ (Set.univ : Set Ω) = 1 := by simp
    have hν1 : ν (Set.univ : Set Ω) = 1 := by simp
    -- `ν univ = c * μ univ`
    have : ν (Set.univ : Set Ω) = c * μ (Set.univ : Set Ω) := by
      simp [hν_smul, Measure.smul_apply, smul_eq_mul]
    -- Simplify to get `c = 1`.
    simpa [hμ1, hν1] using this.symm
  -- Finish.
  simp [hmass, hν_smul]

/-- **Tail-trivial** Gibbs probability measures are **extreme** (Georgii Thm. 7.7, direction
`tail-trivial → extreme`). -/
theorem mem_extremePoints_G_of_isTailTrivial
    (hγ : IsProper γ)
    {μ : Measure Ω}
    (hμG : μ ∈ G (γ := γ))
    (hμtail : IsTailTrivial (⟨μ, hμG.1⟩ : ProbabilityMeasure Ω)) :
    μ ∈ (G (γ := γ)).extremePoints ENNReal := by
  classical
  -- Use the `mem_extremePoints_iff_left` characterization.
  rw [mem_extremePoints_iff_left]
  refine ⟨hμG, ?_⟩
  rintro ν₁ hν₁ ν₂ hν₂ ⟨a, b, ha, hb, hab, hμeq⟩
  -- Show `ν₁ ≪ μ`, then apply the absolute continuity lemma.
  have hμ_prob : IsProbabilityMeasure μ := hμG.1
  haveI : IsProbabilityMeasure μ := hμ_prob
  haveI : IsProbabilityMeasure ν₁ := hν₁.1
  haveI : IsProbabilityMeasure ν₂ := hν₂.1
  have hν₁μ : ν₁ ≪ μ := by
    -- Use the defining property: `μ s = 0 → ν₁ s = 0`.
    intro s hsμ
    have ha0 : a ≠ 0 := ne_of_gt ha
    -- Evaluate the convex combination on `s`.
    have hμs : μ s = a * ν₁ s + b * ν₂ s := by
      have := congrArg (fun m : Measure Ω => m s) hμeq.symm
      simpa [Measure.add_apply, Measure.smul_apply, smul_eq_mul, add_assoc, add_comm, add_left_comm] using this
    have hsum0 : a * ν₁ s + b * ν₂ s = 0 := by simpa [hμs] using hsμ
    have hterm0 : a * ν₁ s = 0 := (add_eq_zero.1 hsum0).1
    rcases (mul_eq_zero.1 hterm0) with ha0' | hν₁0
    · exact (ha0 ha0').elim
    · exact hν₁0
  -- Apply the tail-trivial absolute continuity lemma to conclude `ν₁ = μ`.
  have hμ_gibbs : IsGibbsMeasure γ μ := hμG.2
  have hν₁_gibbs : IsGibbsMeasure γ ν₁ := hν₁.2
  have hEq : ν₁ = μ :=
    eq_of_absolutelyContinuous_of_isTailTrivial  (γ := γ) (hγ := hγ)
      (μ := μ) (ν := ν₁) hμ_gibbs hν₁_gibbs (hμtail := hμtail) hν₁μ
  simp [hEq]

end TailTrivialImpliesExtreme

end

end ExtremePoints



end Rebuild.StatMech.Specification
