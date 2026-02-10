import GibbsMeasure.Potential
import GibbsMeasure.Specification
import GibbsMeasure.Prereqs.Filtration.Consistent
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
--import Riemann.PhysLean.SpinGlass.Kernel

open ENNReal MeasureTheory

namespace GibbsMeasure.Examples.SpinGlass

variable {V : Type*} [DecidableEq V] [Fintype V] -- Vertices/Spins

-- Ensure Int has a measurable space
instance : MeasurableSpace Int := ⊤


/-- The Sherrington-Kirkpatrick (or Edwards-Anderson) potential.
    Φ_{ij}(σ) = - J_{ij} * σ_i * σ_j.
    (Using -J for ferromagnetic convention, or just J). -/
noncomputable def skPotential (J : V → V → ℝ) : Potential V Int :=
  fun Δ σ ↦
    if h : ∃ i j, i ≠ j ∧ Δ = {i, j} then
      -- Use classical choice to extract witnesses from `∃` (cannot eliminate `Exists` into `ℝ` directly).
      let i : V := Classical.choose h;
      let hj : ∃ j : V, i ≠ j ∧ Δ = {i, j} := Classical.choose_spec h;
      let j : V := Classical.choose hj;
      - J i j * (σ i : ℝ) * (σ j : ℝ)
    else 0

instance (J : V → V → ℝ) : Potential.IsFinitary (skPotential J) where
  finite_support := by
    classical
    -- Since `V` is finite, the type `Finset V` is finite, hence any subset is finite.
    exact (Set.finite_univ.subset (by intro Δ hΔ; trivial))

instance (J : V → V → ℝ) : Potential.IsPotential (skPotential J) where
  measurable Δ := by
    classical
    -- With `MeasurableSpace Int := ⊤`, the induced measurable space on configurations is `⊤`,
    -- so every function is measurable.
    intro s hs
    -- `cylinderEvents` is a comap of a restriction map; comap of `⊤` is `⊤`, hence all sets are measurable.
    simp [cylinderEvents_eq_comap_restrict]

/-- The Gibbs specification for the SK model. -/
noncomputable def skSpecification (J : V → V → ℝ) (β : ℝ) (ν : Measure Int)
    [IsProbabilityMeasure ν]
    (hZ : ∀ (Λ : Finset V) (η : V → Int),
      Specification.premodifierZ ν (Potential.boltzmannWeight (Φ := skPotential J) β) Λ η ≠ ⊤) :
    Specification V Int :=
  Potential.gibbsSpecification (skPotential J) β ν hZ


end GibbsMeasure.Examples.SpinGlass
