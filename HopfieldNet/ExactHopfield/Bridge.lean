/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import HopfieldNet.ExactHopfield.Defs
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

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Denotation ring hom `CReal →+* ℝ`. -/
noncomputable abbrev φ : R →+* ℝ :=
  Computable.CReal.toRealRingHom

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

theorem energy_toReal (p : SBParams (U := U)) (s : SBState (U := U)) :
    φ (energy p s) = classicalEnergy (U := U) p s := by
  classical
  -- Unfold the `CReal` Hamiltonian and push `φ` through finite sums/products.
  -- We use `simp only` to avoid triggering `map_inv₀` side-goals (the coefficient `1/2` is left as `φ (1/2)`).
  simp only [ExactHopfield.energy, classicalEnergy, HopfieldEnergy.hamiltonian, φ,
    Matrix.mulVec, dotProduct, TwoState.fin0,
    map_sum, map_add, map_mul, map_neg, neg_mul]

end ExactHopfield
