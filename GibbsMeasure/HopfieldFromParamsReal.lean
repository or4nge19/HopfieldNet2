import GibbsMeasure.Potential
import NeuralNetwork.NeuralNetwork.Core

/-!
## Hopfield parameters → Georgii potential (real spins)

This is the “spin-type aligned” version of `GibbsMeasure.HopfieldFromParams`:
we build a Georgii potential on configurations `U → ℝ`, so it can be compared directly with
Hopfield energies computed from Hopfield states `s : (HopfieldNetwork ℝ U).State` (where `s.act : U → ℝ`).

We deliberately keep the definition **choice-free** on supports:
- singleton supports (`Δ.card = 1`) encode the external field / thresholds,
- pair supports (`Δ.card = 2`) encode the quadratic interaction term via a symmetric double sum over `Δ.attach`.

This file only provides the potential + finitary instance; measurability (`IsPotential`) is not needed
for the energy-equality bridge itself and can be added later when moving to infinite-volume theory.
-/

open scoped BigOperators

namespace GibbsMeasure.Examples.HopfieldFromParamsReal

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

/-- Extract the real threshold scalar `θ' (θ u)` from Hopfield parameters. -/
noncomputable def θu (p : Params (HopfieldNetwork ℝ U)) (u : U) : ℝ :=
  θ' (p.θ u)

/-- Georgii potential on real-spin configurations `U → ℝ`, induced by Hopfield parameters `(w, θ)`. -/
noncomputable def hopfieldPotentialFromParamsR (p : Params (HopfieldNetwork ℝ U)) :
    Potential U ℝ :=
  fun Δ η =>
    if Δ.card = 2 then
      (- (1 / 2 : ℝ)) *
        (Δ.attach.sum fun i =>
          (Δ.attach.sum fun j =>
            if j.1 ≠ i.1 then
              (p.w i.1 j.1) * (η i.1) * (η j.1)
            else 0))
    else if Δ.card = 1 then
      Δ.attach.sum fun i => (θu (U := U) p i.1) * (η i.1)
    else
      0

instance (p : Params (HopfieldNetwork ℝ U)) :
    Potential.IsFinitary (hopfieldPotentialFromParamsR (U := U) p) where
  finite_support := by
    classical
    -- Supports are only singletons or pairs, hence finite.
    let s1 : Finset (Finset U) := Finset.univ.image (fun i : U => ({i} : Finset U))
    let s2 : Finset (Finset U) :=
      Finset.univ.biUnion fun i : U =>
        (Finset.univ.erase i).image (fun j : U => ({i, j} : Finset U))
    let s : Finset (Finset U) := s1 ∪ s2
    apply Set.Finite.subset (s := (s : Set (Finset U)))
    · exact Finset.finite_toSet s
    · intro Δ hΔ
      -- If `Φ Δ ≠ 0`, then `Δ.card = 1` or `Δ.card = 2`.
      have hcard : Δ.card = 1 ∨ Δ.card = 2 := by
        by_contra hcard
        have hne1 : Δ.card ≠ 1 := by intro h1; exact hcard (Or.inl h1)
        have hne2 : Δ.card ≠ 2 := by intro h2; exact hcard (Or.inr h2)
        have hzero : hopfieldPotentialFromParamsR (U := U) p Δ = 0 := by
          funext η
          simp [hopfieldPotentialFromParamsR, hne2, hne1]
        exact hΔ hzero
      -- Now `Δ` is a singleton or a pair, hence belongs to `s`.
      cases hcard with
      | inl h1 =>
          rcases Finset.card_eq_one.1 h1 with ⟨i, rfl⟩
          have : ({i} : Finset U) ∈ s1 := by simp [s1]
          have : ({i} : Finset U) ∈ s := by simp [s, this]
          simpa using this
      | inr h2 =>
          rcases Finset.card_eq_two.1 h2 with ⟨i, j, hij, rfl⟩
          have : ({i, j} : Finset U) ∈ s2 := by
            have hj : j ∈ Finset.univ.erase i := by simp [Finset.mem_erase, hij.symm]
            have himg :
                ({i, j} : Finset U) ∈ (Finset.univ.erase i).image (fun k : U => ({i, k} : Finset U)) := by
              refine Finset.mem_image.2 ?_
              exact ⟨j, hj, rfl⟩
            refine Finset.mem_biUnion.2 ?_
            refine ⟨i, by simp, ?_⟩
            simpa [s2] using himg
          have : ({i, j} : Finset U) ∈ s := by simp [s, this]
          simpa using this

end GibbsMeasure.Examples.HopfieldFromParamsReal
