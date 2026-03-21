import Rebuild.StatMech.Specification.Core
import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# Rebuild Proper Specifications

Boundary-condition/properness interface for local specifications.
-/

set_option autoImplicit false

namespace Rebuild.StatMech.Specification

open Rebuild.Core ProbabilityTheory MeasureTheory ENNReal Set

variable {Site Spin : Type*} [DecidableEq Site] [MeasurableSpace Spin]

/-- A local kernel is proper if it leaves configurations unchanged off its index volume. -/
def KernelIsProperOn (V : FiniteVolume Site)
    (κ : ProbabilityTheory.Kernel (Configuration Site Spin) (Configuration Site Spin)) : Prop :=
  ∀ σ,
    ∀ᵐ τ ∂κ σ, ∀ i, i ∉ V.carrier → τ i = σ i

/-- A local specification is proper if every local kernel only updates inside its volume. -/
def IsProper (γ : LocalSpecification Site Spin) : Prop :=
  ∀ V : FiniteVolume Site,
    KernelIsProperOn V (γ.kernel V)

lemma cylinder_eq_of_agree {Δ : Set Site} {B : Set (Configuration Site Spin)}
    (hB : MeasurableSet[cylinderEvents (X := fun _ : Site ↦ Spin) Δ] B) {σ τ : Configuration Site Spin}
    (h: ∀ i ∈ Δ, σ i = τ i) : σ ∈ B ↔ τ ∈ B := by
  have hd : cylinderEvents (X := fun _ : Site ↦ Spin) Δ ≤
      { MeasurableSet' := fun S => (∀ x y : Configuration Site Spin, (∀ i ∈ Δ, x i = y i) → (x ∈ S ↔ y ∈ S))
        measurableSet_empty := by simp
        measurableSet_compl := fun S hS x y hxy => not_congr (hS x y hxy)
        measurableSet_iUnion := fun f (hf : ∀ i, ∀ x y : Configuration Site Spin, (∀ i ∈ Δ, x i = y i) → (x ∈ f i ↔ y ∈ f i)) =>
          fun x y hxy => by simp [Set.mem_iUnion]; exact exists_congr (fun i => hf i x y hxy) } := by
    apply iSup_le
    intro i
    apply iSup_le
    intro hi
    rintro S ⟨S', _, rfl⟩
    intro x y hxy
    dsimp [Set.preimage]
    rw [hxy i hi]
  exact hd B hB σ τ h

lemma KernelIsProperOn.inter_eq_indicator_mul {V : FiniteVolume Site}
    {κ : ProbabilityTheory.Kernel (Configuration Site Spin) (Configuration Site Spin)}
    (h_prop : KernelIsProperOn V κ) {A B : Set (Configuration Site Spin)}
    (hA : MeasurableSet A) (hB : MeasurableSet[cylinderEvents (X := fun _ : Site ↦ Spin) ((V : Set Site)ᶜ)] B) (σ : Configuration Site Spin) :
    κ σ (A ∩ B) = B.indicator 1 σ * κ σ A := by
  by_cases h : σ ∈ B
  · rw [Set.indicator_of_mem h]
    simp only [Pi.one_apply, one_mul]
    apply measure_congr
    have h_ae : ∀ᵐ τ ∂(κ σ), τ ∈ B := by
      filter_upwards [h_prop σ] with τ hτ
      have heq : ∀ i ∈ ((V : Set Site)ᶜ), σ i = τ i := fun i hi => (hτ i hi).symm
      exact (cylinder_eq_of_agree hB heq).mp h
    filter_upwards [h_ae] with τ hτ
    exact propext (and_iff_left hτ)
  · have h0 : B.indicator 1 σ = (0 : ENNReal) := Set.indicator_apply_eq_zero.mpr (fun h_in => (h h_in).elim)
    rw [h0]
    simp only [zero_mul]
    have ht : κ σ (A ∩ B) = κ σ ∅ := by
      apply measure_congr
      have h_ae : ∀ᵐ τ ∂(κ σ), τ ∉ B := by
        filter_upwards [h_prop σ] with τ hτ
        have heq : ∀ i ∈ ((V : Set Site)ᶜ), σ i = τ i := fun i hi => (hτ i hi).symm
        intro h_in
        exact h ((cylinder_eq_of_agree hB heq).mpr h_in)
      filter_upwards [h_ae] with τ hτ
      exact propext (iff_false_intro (fun h_in : τ ∈ A ∩ B => hτ h_in.2))
    rw [ht, measure_empty]

lemma cylinder_fun_eq_of_agree {Δ : Set Site} {g : Configuration Site Spin → ℝ≥0∞}
    (hg : Measurable[cylinderEvents (X := fun _ : Site ↦ Spin) Δ] g) {σ τ : Configuration Site Spin}
    (h: ∀ i ∈ Δ, σ i = τ i) : g σ = g τ := by
  by_contra hneq
  have hB : MeasurableSet[cylinderEvents (X := fun _ : Site ↦ Spin) Δ] (g ⁻¹' {g σ}) :=
    hg (measurableSet_singleton (g σ))
  have h_eq : σ ∈ g ⁻¹' {g σ} ↔ τ ∈ g ⁻¹' {g σ} := cylinder_eq_of_agree hB h
  have h_in : σ ∈ g ⁻¹' {g σ} := rfl
  have h_out : τ ∉ g ⁻¹' {g σ} := fun hc => hneq hc.symm
  exact h_out (h_eq.mp h_in)

lemma KernelIsProperOn.lintegral_mul {V : FiniteVolume Site}
    {κ : ProbabilityTheory.Kernel (Configuration Site Spin) (Configuration Site Spin)}
    (h_prop : KernelIsProperOn V κ) {f g : Configuration Site Spin → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable[cylinderEvents (X := fun _ : Site ↦ Spin) ((V : Set Site)ᶜ)] g) (σ : Configuration Site Spin) :
    ∫⁻ τ, g τ * f τ ∂(κ σ) = g σ * ∫⁻ τ, f τ ∂(κ σ) := by
  have h_ae : ∀ᵐ τ ∂(κ σ), g τ * f τ = g σ * f τ := by
    filter_upwards [h_prop σ] with τ hτ
    have heq : ∀ i ∈ ((V : Set Site)ᶜ), σ i = τ i := fun i hi => (hτ i hi).symm
    rw [cylinder_fun_eq_of_agree hg heq]
  have hl : ∫⁻ τ, g τ * f τ ∂(κ σ) = ∫⁻ τ, g σ * f τ ∂(κ σ) := lintegral_congr_ae h_ae
  rw [hl]
  exact lintegral_const_mul _ hf

lemma IsProper.inter_eq_indicator_mul {γ : LocalSpecification Site Spin}
    (hγ : IsProper γ) (V : FiniteVolume Site) {A B : Set (Configuration Site Spin)}
    (hA : MeasurableSet A) (hB : MeasurableSet[cylinderEvents (X := fun _ : Site ↦ Spin) ((V : Set Site)ᶜ)] B) (σ : Configuration Site Spin) :
    γ.kernel V σ (A ∩ B) = B.indicator 1 σ * γ.kernel V σ A :=
  (hγ V).inter_eq_indicator_mul hA hB σ

lemma IsProper.lintegral_mul {γ : LocalSpecification Site Spin}
    (hγ : IsProper γ) (V : FiniteVolume Site) {f g : Configuration Site Spin → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable[cylinderEvents (X := fun _ : Site ↦ Spin) ((V : Set Site)ᶜ)] g) (σ : Configuration Site Spin) :
    ∫⁻ τ, g τ * f τ ∂(γ.kernel V σ) = g σ * ∫⁻ τ, f τ ∂(γ.kernel V σ) :=
  (hγ V).lintegral_mul hf hg σ

end Rebuild.StatMech.Specification
