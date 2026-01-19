import GibbsMeasure.Potential
import GibbsMeasure.Specification
import GibbsMeasure.Prereqs.Filtration.Consistent
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
## Hopfield model as a Georgii potential / Gibbs specification (non-orthogonal patterns)

This file starts the **Georgii-side** Hopfield pipeline, in direct analogy with
`GibbsMeasure/SpinGlass.lean`.

Key design choice (Talagrand / mean-field Hopfield):
- spins take values in `{±1}` (we use `Int` for the configuration space, like the SK example),
- the interaction is pairwise with couplings

\[
J_{ij} := \frac{1}{|V|} \sum_{\mu=1}^m \xi_i^\mu \xi_j^\mu,
\]

with **no orthogonality assumption** on the patterns `ξ`. The resulting crosstalk/interference is
encoded in the couplings, and later analysis can reuse the “signal + interference” algebra already
formalized on the HopfieldNet side.

The potential is the standard pair interaction:
\[
\Phi_{\{i,j\}}(\sigma) = - J_{ij} \, \sigma_i \sigma_j
\]
and zero on all other finite supports.
-/

open ENNReal MeasureTheory

namespace GibbsMeasure.Examples.Hopfield

variable {V : Type*} [DecidableEq V] [Fintype V]

-- Make `Int` measurable (trivial σ-algebra), matching the SpinGlass example.
instance : MeasurableSpace Int := ⊤

open scoped BigOperators

/-! ### Hebbian couplings from patterns (no orthogonality assumptions) -/

variable {m : ℕ}

/-- Hopfield patterns: `m` stored patterns, each a configuration in `{±1}^V`. -/
abbrev Patterns (V : Type*) (m : ℕ) := Fin m → V → Int

/-- The (mean-field normalized) Hopfield coupling \(J_{ij}\) induced by patterns `ξ`. -/
noncomputable def hopfieldJ (ξ : Patterns V m) (i j : V) : ℝ :=
  (1 / (Fintype.card V : ℝ)) *
    ∑ μ : Fin m, (ξ μ i : ℝ) * (ξ μ j : ℝ)

/-! ### Potential and specification -/

/-- Pairwise Hopfield potential on `{±1}^V` with couplings from patterns `ξ`. -/
noncomputable def hopfieldPotential (ξ : Patterns V m) : Potential V Int :=
  fun Δ σ ↦
    if h : ∃ i j, i ≠ j ∧ Δ = {i, j} then
      by
        classical
        -- We use classical choice to extract a witness from the Prop `∃ i j, ...`.
        let i : V := Classical.choose h
        let hj : ∃ j : V, i ≠ j ∧ Δ = {i, j} := Classical.choose_spec h
        let j : V := Classical.choose hj
        -- Standard pair interaction (note the SK sign convention).
        exact - hopfieldJ (V := V) (m := m) ξ i j * (σ i : ℝ) * (σ j : ℝ)
    else
      0

instance (ξ : Patterns V m) : Potential.IsFinitary (hopfieldPotential (V := V) (m := m) ξ) where
  finite_support := by
    classical
    -- Same finitary support argument as the SK example: only 2-site interactions can be non-zero.
    let s : Finset (Finset V) :=
      Finset.univ.biUnion fun i ↦ Finset.univ.image (fun j ↦ ({i, j} : Finset V))
    apply Set.Finite.subset (s := (s : Set (Finset V)))
    · exact Finset.finite_toSet s
    · intro Δ hΔ
      -- If `hopfieldPotential ξ Δ ≠ 0`, then the pair-support condition must hold.
      by_cases h : ∃ i j, i ≠ j ∧ Δ = {i, j}
      · obtain ⟨i, j, hij, rfl⟩ := h
        simp [s]
      · -- Otherwise the potential is definitionally 0, contradiction.
        have hzero : hopfieldPotential (V := V) (m := m) ξ Δ = 0 := by
          funext σ
          simp [hopfieldPotential, h]
        exact (hΔ hzero).elim

instance (ξ : Patterns V m) : Potential.IsPotential (hopfieldPotential (V := V) (m := m) ξ) where
  measurable Δ := by
    classical
    by_cases h : ∃ i j, i ≠ j ∧ Δ = {i, j}
    · -- In this branch `Φ Δ` is a product of two cylinder-coordinate functions.
      -- Use the chosen witnesses `i,j` for the (fixed) support `Δ`.
      let i : V := Classical.choose h
      let hj : ∃ j : V, i ≠ j ∧ Δ = {i, j} := Classical.choose_spec h
      let j : V := Classical.choose hj
      have hΔ : Δ = ({i, j} : Finset V) := (Classical.choose_spec hj).2
      have hi : i ∈ (Δ : Set V) := by simp [hΔ]
      have hj' : j ∈ (Δ : Set V) := by
        have : j ∈ ({i, j} : Finset V) := by simp
        simpa [hΔ] using this
      -- Now build measurability.
      -- (With the trivial measurable space on `Int`, these projections are `measurable_from_top`.)
      have mi : Measurable[cylinderEvents (X := fun _ : V ↦ Int) (Δ : Set V)]
          (fun σ : V → Int => (σ i : ℝ)) :=
        (measurable_from_top.comp
          (measurable_cylinderEvent_apply (i := i) (X := fun _ : V ↦ Int) (by simpa using hi)))
      have mj : Measurable[cylinderEvents (X := fun _ : V ↦ Int) (Δ : Set V)]
          (fun σ : V → Int => (σ j : ℝ)) :=
        (measurable_from_top.comp
          (measurable_cylinderEvent_apply (i := j) (X := fun _ : V ↦ Int) (by simpa using hj')))
      -- Rewrite `hopfieldPotential` at `Δ` under `h` to expose the product form.
      have hform :
          (hopfieldPotential (V := V) (m := m) ξ) Δ =
            fun σ : V → Int => - hopfieldJ (V := V) (m := m) ξ i j * (σ i : ℝ) * (σ j : ℝ) := by
        funext σ
        simp [hopfieldPotential, h, i, j]
      -- Combine.
      simpa [hform, mul_assoc] using (measurable_const.mul (mi.mul mj))
    · -- Otherwise constant 0.
      -- In this branch `hopfieldPotential ξ Δ` is the constant-0 function.
      have h0 : (hopfieldPotential (V := V) (m := m) ξ) Δ = (fun _ : V → Int => (0 : ℝ)) := by
        funext σ
        simp [hopfieldPotential, h]
      simpa [h0] using
        (measurable_const :
          Measurable[cylinderEvents (X := fun _ : V ↦ Int) (Δ : Set V)] (fun _ : V → Int => (0 : ℝ)))

/-- The Gibbs specification for the Hopfield model (Georgii API). -/
noncomputable def hopfieldSpecification
    (ξ : Patterns V m) (β : ℝ) (ν : Measure Int) [IsProbabilityMeasure ν]
    (hZ : ∀ (Λ : Finset V) (η : V → Int),
      Specification.premodifierZ ν
        (Potential.boltzmannWeight (Φ := hopfieldPotential (V := V) (m := m) ξ) β) Λ η ≠ ⊤) :
    Specification V Int :=
  Potential.gibbsSpecification (hopfieldPotential (V := V) (m := m) ξ) β ν hZ

end GibbsMeasure.Examples.Hopfield
