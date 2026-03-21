/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import HopfieldNet.ExactHopfield.Defs
import HopfieldNet.ExactHopfield.EnergyDescent
import HopfieldNet.CReals.CRealCCLOF

/-!
# Bridge: Exact Hopfield ↔ Classical Hopfield over ℝ

This file proves the **faithfulness theorem**: the `CReal`-valued Hopfield energy maps
exactly to the classical `ℝ`-valued Hopfield energy under the denotation ring
homomorphism `Computable.CReal.toRealRingHom`.

This is the key result that closes the "verification gap" between:
- **Proof world**: theorems about energy descent, convergence, etc., stated over `CReal`.
- **Execution world**: numeric evaluation via the fast dyadic backend.
- **Classical world**: the standard mathematical theory stated over `ℝ`.

The bridge says: anything proved about the `CReal` energy is automatically true of the
corresponding `ℝ` energy, and conversely, any `ℝ`-valued energy property transfers back.

## Main results

- `ExactHopfield.energy_toReal` : `φ (energy p s) = classicalEnergy (φ ∘ w) (toReal ∘ s)`.
- `ExactHopfield.localField_toReal` : `φ (localField p s i) = classicalLocalField …`.
- `ExactHopfield.energyDiff_toReal` : the energy difference is preserved.

where `φ = Computable.CReal.toRealRingHom`.
-/

namespace ExactHopfield

open Computable
open Finset BigOperators Matrix
open NeuralNetwork

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

noncomputable section

-- Match the numeral coercion used in `EnergyDescent.lean` to avoid the `2`-instance diamond.
local instance : NatCast R :=
  Computable.CReal.instField.toDivisionRing.toAddGroupWithOne.toNatCast

/-- Denotation ring hom `CReal →+* ℝ`. -/
noncomputable abbrev φ : R →+* ℝ :=
  Computable.CReal.toRealRingHom

/-- Classical threshold value at neuron `u`. -/
noncomputable abbrev classicalThreshold (p : SBParams (U := U)) (u : U) : ℝ :=
  φ (θ0 p u)

/-- Classical local field corresponding to `ExactHopfield.localField`. -/
noncomputable def classicalLocalField (p : SBParams (U := U)) (s : SBState (U := U)) (u : U) : ℝ :=
  ∑ v : U, if v ≠ u then φ (p.w u v) * φ (s.act v) else 0

/-- Classical margin `localField - θ`. -/
noncomputable def classicalMargin (p : SBParams (U := U)) (s : SBState (U := U)) (u : U) : ℝ :=
  classicalLocalField p s u - classicalThreshold p u

/--
Classical `ℝ`-valued energy corresponding to the exact `CReal` Hamiltonian.

We keep this definition *parameterized by the exact params/state*, mapping components through `φ`.
-/
noncomputable def classicalEnergy (p : SBParams (U := U)) (s : SBState (U := U)) : ℝ :=
  by
    classical
    -- Force the same `NatCast R` instance as used inside `HopfieldEnergy.hamiltonian`
    -- to avoid the `2`-diamond in `1/2`.
    letI : NatCast R :=
      Computable.CReal.instField.toDivisionRing.toAddGroupWithOne.toNatCast
    let wR : Matrix U U ℝ := fun i j => φ (p.w i j)
    let actR : U → ℝ := fun i => φ (s.act i)
    let θR : U → ℝ := fun i => φ ((p.θ i).get TwoState.fin0)
    let quad : ℝ := ∑ i : U, actR i * (wR.mulVec actR i)
    exact (- (φ (1 / 2 : R) * quad)) + ∑ i : U, θR i * actR i

theorem θ0_toReal (p : SBParams (U := U)) (u : U) :
    φ (θ0 p u) = classicalThreshold (U := U) p u := rfl

theorem localField_toReal (p : SBParams (U := U)) (s : SBState (U := U)) (u : U) :
    φ (localField p s u) = classicalLocalField (U := U) p s u := by
  classical
  unfold ExactHopfield.localField classicalLocalField NeuralNetwork.State.net NeuralNetwork.State.out
  simp [TwoState.SymmetricBinary]
  refine Finset.sum_congr rfl ?_
  intro x _
  by_cases hx : x = u
  · subst hx
    simp
  · simp [hx, map_mul]

theorem L_toReal (p : SBParams (U := U)) (s : SBState (U := U)) (u : U) :
    φ (L p s u) = classicalMargin (U := U) p s u := by
  unfold ExactHopfield.L classicalMargin classicalThreshold
  rw [map_sub, localField_toReal]

theorem energy_toReal (p : SBParams (U := U)) (s : SBState (U := U)) :
    φ (energy p s) = classicalEnergy (U := U) p s := by
  classical
  -- Unfold the `CReal` Hamiltonian and push `φ` through finite sums/products.
  -- We use `simp only` to avoid triggering `map_inv₀` side-goals (the coefficient `1/2` is left as `φ (1/2)`).
  simp only [ExactHopfield.energy, classicalEnergy, HopfieldEnergy.hamiltonian, φ,
    Matrix.mulVec, dotProduct, TwoState.fin0,
    map_sum, map_add, map_mul, map_neg, neg_mul]

theorem energyDiff_toReal (p : SBParams (U := U)) (s : SBState (U := U)) (u : U) :
    φ (energyDiff p s u) =
      classicalEnergy (U := U) p (updPos s u) - classicalEnergy (U := U) p (updNeg s u) := by
  rw [ExactHopfield.energyDiff, map_sub, energy_toReal, energy_toReal]

theorem energy_update_eq_toReal (p : SBParams (U := U)) (s : SBState (U := U)) (u : U) :
    classicalEnergy (U := U) p (updPos s u) - classicalEnergy (U := U) p (updNeg s u) =
      -(2 : ℝ) * classicalMargin (U := U) p s u := by
  calc
    classicalEnergy (U := U) p (updPos s u) - classicalEnergy (U := U) p (updNeg s u)
        = φ (energyDiff p s u) := by
            symm
            exact energyDiff_toReal (U := U) p s u
    _ = φ (-(2 : R) * L p s u) := by
          rw [energy_update_eq (U := U) p s u]
    _ = -(2 : ℝ) * φ (L p s u) := by
          rw [map_mul]
          calc
            φ (-(2 : R)) * φ (L p s u) = -(φ (2 : R)) * φ (L p s u) := by
              rw [map_neg]
            _ = -(2 : ℝ) * φ (L p s u) := by
              have h2 : φ (2 : R) = (2 : ℝ) := by
                simpa using (map_natCast (f := φ) 2)
              rw [h2]
    _ = -(2 : ℝ) * classicalMargin (U := U) p s u := by
          rw [L_toReal]

theorem energy_descent_toReal (p : SBParams (U := U)) (s : SBState (U := U)) (u : U) :
    classicalEnergy (U := U) p (detUpdate (U := U) p s u) ≤ classicalEnergy (U := U) p s := by
  calc
    classicalEnergy (U := U) p (detUpdate (U := U) p s u)
        = φ (energy p (detUpdate (U := U) p s u)) := by
            symm
            exact energy_toReal (U := U) p (detUpdate (U := U) p s u)
    _ ≤ φ (energy p s) := Computable.CReal.toReal_mono (energy_descent (U := U) p s u)
    _ = classicalEnergy (U := U) p s := energy_toReal (U := U) p s

end

end ExactHopfield
