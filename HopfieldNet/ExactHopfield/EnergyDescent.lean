/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import HopfieldNet.ExactHopfield.Defs
import HopfieldNet.CReals.CRealApart

/-!
# Energy Descent for Exact Hopfield Networks

This file proves the central theorem of discrete Hopfield network theory over
`Computable.CReal`: a single asynchronous neuron update that follows the sign of
the local field can only decrease the energy.

## Main results

- `ExactHopfield.energy_update_eq` : exact formula for the energy change after an update.
- `ExactHopfield.energyDiff_eq_energy_sub` : the energy difference formula is correct.
- `ExactHopfield.energy_descent` : the hero theorem — if the update follows the sign of the
  local field, the energy does not increase.

## Proof strategy

The energy difference when changing neuron `i` from value `old` to `new` is:
  `E(s') - E(s) = (old - new) · (localField_i(s) - θ_i)`.

When the update "follows the local field":
  - If `localField_i ≥ θ_i`, the new value is `up` (`+1`).
  - If `localField_i < θ_i`, the new value is `dn` (`-1`).

In either case, `(old - new)` and `(localField - θ)` have opposite signs (or one is zero),
so the product is `≤ 0`, i.e. the energy decreases or stays the same.

The proof proceeds purely algebraically: we expand the bilinear energy form, cancel all
terms where neuron `j ≠ i` is unchanged, and use `w_ii = 0` (zero diagonal) to eliminate
the self-interaction term. The case analysis on `old/new ∈ {+1, -1}` is then routine.

### Note on constructivity

The case analysis `localField ≥ θ ∨ localField < θ` is **not** constructively valid in
general for `CReal` (it requires the Limited Principle of Omniscience). We handle this by:

1. **Statement-level**: the theorem is universally quantified over *any* new spin value `v`
   and a *hypothesis* that the update is "correct" (i.e., sign-consistent with the local
   field). The hypothesis is expressed using the noncomputable `CReal` order from CCLOF.

2. **Execution-level**: in practice, the update decision is made by the fast backend's
   comparison procedure (which is total on concrete dyadic values), or by the semi-decision
   procedure `CReal.Pre.compareWitness`.

This separation of concerns — algebraic proof over the abstract type, computational
comparison at the concrete level — is the fundamental design pattern of this library.
-/

namespace ExactHopfield

open Computable
open NeuralNetwork HopfieldEnergy

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

noncomputable section

-- In this file we fix the `NatCast` instance on `R = CReal` to the one coming from the `Field` structure.
-- This avoids the `NatCast` instance diamond (notably around the numeral `2`) when rewriting with
-- `HopfieldEnergy.hamiltonian_flip_relation`.
local instance : NatCast R :=
  Computable.CReal.instField.toDivisionRing.toAddGroupWithOne.toNatCast

/-!
We avoid using `TwoState.zeroTempDet` directly in statements: it is written with a dependent `if`
and tends to make `simp` generate proof obligations. Instead, we use the simpler “threshold”
update as a plain `ite`.
-/
noncomputable def detUpdate (p : SBParams (U := U)) (s : SBState (U := U)) (u : U) : SBState (U := U) :=
  if θ0 p u ≤ localField p s u then updPos s u else updNeg s u

/-! ### Algebraic energy-gap lemmas (review-facing API) -/

lemma energy_updPos_sub_updNeg (p : SBParams (U := U)) (s : SBState (U := U)) (u : U) :
    energy p (updPos s u) - energy p (updNeg s u)
      = -(2 : R) * (State.net p s u - (p.θ u).get TwoState.fin0) := by
  classical
  dsimp [ExactHopfield.energy, ExactHopfield.updPos, ExactHopfield.updNeg]
  simpa using (HopfieldEnergy.hamiltonian_flip_relation (R := R) (U := U) p s u)

lemma margin_eq_zero_of_energy_updPos_eq_updNeg (p : SBParams (U := U)) (s : SBState (U := U)) (u : U)
    (heq : energy p (updPos s u) = energy p (updNeg s u)) :
    State.net p s u - (p.θ u).get TwoState.fin0 = 0 := by
  classical
  have hsub : energy p (updPos s u) - energy p (updNeg s u) = 0 := sub_eq_zero.mpr heq
  -- rewrite the energy gap using the flip relation
  have hgap :
      -(2 : R) * (State.net p s u - (p.θ u).get TwoState.fin0) = 0 := by
    simpa [energy_updPos_sub_updNeg (U := U) p s u] using hsub
  have h2 : (2 : R) ≠ 0 := by
    exact ne_of_gt (two_pos : (0 : R) < (2 : R))
  have h2' : (-(2 : R)) ≠ 0 := neg_ne_zero.mpr h2
  exact (mul_eq_zero.mp hgap).resolve_left h2'

lemma energy_updPos_le_updNeg_of_le (p : SBParams (U := U)) (s : SBState (U := U)) (u : U)
    (hθ : θ0 p u ≤ localField p s u) :
    energy p (updPos s u) ≤ energy p (updNeg s u) := by
  have hmargin : (0 : R) ≤ State.net p s u - (p.θ u).get TwoState.fin0 := by
    simpa [ExactHopfield.localField, ExactHopfield.θ0, sub_eq_add_neg] using sub_nonneg.mpr hθ
  have hdiff : energy p (updPos s u) - energy p (updNeg s u) ≤ 0 := by
    -- unfold to the concrete flip relation, then `nlinarith`
    dsimp [ExactHopfield.energy, ExactHopfield.updPos, ExactHopfield.updNeg]
    rw [HopfieldEnergy.hamiltonian_flip_relation (R := R) (U := U) p s u]
    -- rewrite away the coefficient `2` using `two_mul`
    -- `-(2:R) * m = -((2:R) * m) = -(m + m)`
    have hm : (0 : R) ≤ State.net p s u - (p.θ u).get TwoState.fin0 := hmargin
    -- goal: `-(2:R) * m ≤ 0`
    -- turn into `0 ≤ m + m`
    simpa [neg_mul, two_mul, neg_nonpos] using (add_nonneg hm hm)
  exact (sub_nonpos.mp hdiff)

lemma energy_updNeg_le_updPos_of_not_le (p : SBParams (U := U)) (s : SBState (U := U)) (u : U)
    (hθ : ¬ θ0 p u ≤ localField p s u) :
    energy p (updNeg s u) ≤ energy p (updPos s u) := by
  have hmargin : State.net p s u - (p.θ u).get TwoState.fin0 ≤ 0 := by
    have : localField p s u < θ0 p u := lt_of_not_ge hθ
    have : localField p s u - θ0 p u < 0 := sub_neg.mpr this
    simpa [ExactHopfield.localField, ExactHopfield.θ0] using (le_of_lt this)
  have hdiff : 0 ≤ energy p (updPos s u) - energy p (updNeg s u) := by
    dsimp [ExactHopfield.energy, ExactHopfield.updPos, ExactHopfield.updNeg]
    rw [HopfieldEnergy.hamiltonian_flip_relation (R := R) (U := U) p s u]
    have hm : State.net p s u - (p.θ u).get TwoState.fin0 ≤ 0 := hmargin
    -- goal: `0 ≤ -(2:R) * m`, i.e. `0 ≤ -(m+m)`; equivalently `m+m ≤ 0`
    have : State.net p s u - (p.θ u).get TwoState.fin0 +
          (State.net p s u - (p.θ u).get TwoState.fin0) ≤ 0 := add_nonpos hm hm
    simpa [neg_mul, two_mul, neg_nonneg] using this
  exact (sub_nonneg.mp hdiff)

lemma updPos_eq_self_of_act_eq_one (s : SBState (U := U)) (u : U) (hu : s.act u = (1 : R)) :
    updPos s u = s := by
  ext v
  by_cases hv : v = u
  · subst hv
    simp [ExactHopfield.updPos, TwoState.updPos, Function.update, hu, ExactHopfield.NN,
      TwoState.instTwoStateSymmetricBinary]
  · simp [ExactHopfield.updPos, TwoState.updPos, Function.update, hv]

lemma updNeg_eq_self_of_act_eq_neg_one (s : SBState (U := U)) (u : U) (hu : s.act u = (-1 : R)) :
    updNeg s u = s := by
  ext v
  by_cases hv : v = u
  · subst hv
    simp [ExactHopfield.updNeg, TwoState.updNeg, Function.update, hu, ExactHopfield.NN,
      TwoState.instTwoStateSymmetricBinary]
  · simp [ExactHopfield.updNeg, TwoState.updNeg, Function.update, hv]

theorem energy_descent_detUpdate (p : SBParams (U := U)) (s : SBState (U := U)) (u : U) :
    energy p (detUpdate (U := U) p s u) ≤ energy p s := by
  classical
  by_cases hθ : θ0 p u ≤ localField p s u
  · -- detUpdate = updPos
    have hdet : detUpdate (U := U) p s u = updPos s u := by simp [detUpdate, hθ]
    have hu : s.act u = (1 : R) ∨ s.act u = (-1 : R) := by simpa using (s.hp u)
    rcases hu with hu | hu
    · -- already `+1`: update does nothing
      have : updPos s u = s := updPos_eq_self_of_act_eq_one (U := U) s u hu
      simp [hdet, this]
    · -- currently `-1`: then `s = updNeg` and `E(updPos) ≤ E(updNeg) = E(s)`
      have hs : updNeg s u = s := updNeg_eq_self_of_act_eq_neg_one (U := U) s u hu
      have hle' : energy p (updPos s u) ≤ energy p (updNeg s u) :=
        energy_updPos_le_updNeg_of_le (U := U) p s u hθ
      simpa [hdet, hs] using hle'
  · -- detUpdate = updNeg
    have hdet : detUpdate (U := U) p s u = updNeg s u := by simp [detUpdate, hθ]
    have hu : s.act u = (1 : R) ∨ s.act u = (-1 : R) := by simpa using (s.hp u)
    rcases hu with hu | hu
    · -- currently `+1`: then `s = updPos` and `E(updNeg) ≤ E(updPos) = E(s)`
      have hs : updPos s u = s := updPos_eq_self_of_act_eq_one (U := U) s u hu
      have hle' : energy p (updNeg s u) ≤ energy p (updPos s u) :=
        energy_updNeg_le_updPos_of_not_le (U := U) p s u hθ
      simpa [hdet, hs] using hle'
    · -- already `-1`: update does nothing
      have : updNeg s u = s := updNeg_eq_self_of_act_eq_neg_one (U := U) s u hu
      simp [hdet, this]

theorem energy_strict_of_L_apart (p : SBParams (U := U)) (s : SBState (U := U)) (u : U)
    (hchange : detUpdate (U := U) p s u ≠ s)
    (hap : L p s u # 0) :
    energy p (detUpdate (U := U) p s u) < energy p s := by
  classical
  have hL0 : L p s u ≠ 0 := by
    intro h
    have hne := Computable.CReal.apart_toReal_ne (x := L p s u) (y := 0) hap
    exact hne (by simp [h])
  have hle : energy p (detUpdate (U := U) p s u) ≤ energy p s :=
    energy_descent_detUpdate (U := U) p s u
  refine lt_of_le_of_ne hle ?_
  intro heq
  by_cases hθ : θ0 p u ≤ localField p s u
  · -- detUpdate = updPos
    have hdet : detUpdate (U := U) p s u = updPos s u := by simp [detUpdate, hθ]
    have hu : s.act u = (1 : R) ∨ s.act u = (-1 : R) := by simpa using (s.hp u)
    rcases hu with hu | hu
    · -- update is a no-op; contradict `hchange`
      have : updPos s u = s := updPos_eq_self_of_act_eq_one (U := U) s u hu
      exact hchange (by simp [hdet, this])
    · -- real flip case: `updNeg = s`, and equality forces `L = 0`
      have hs : updNeg s u = s := updNeg_eq_self_of_act_eq_neg_one (U := U) s u hu
      have hEqPos : energy p (updPos s u) = energy p s := by simpa [hdet] using heq
      have hEqNeg : energy p (updNeg s u) = energy p s := by simp [hs]
      have hmargin0 :
          State.net p s u - (p.θ u).get TwoState.fin0 = 0 := by
        apply margin_eq_zero_of_energy_updPos_eq_updNeg (U := U) p s u
        exact by simp [hEqPos, hEqNeg]
      have : L p s u = 0 := by
        simpa [ExactHopfield.L, ExactHopfield.localField, ExactHopfield.θ0] using hmargin0
      exact hL0 this
  · -- detUpdate = updNeg
    have hdet : detUpdate (U := U) p s u = updNeg s u := by simp [detUpdate, hθ]
    have hu : s.act u = (1 : R) ∨ s.act u = (-1 : R) := by simpa using (s.hp u)
    rcases hu with hu | hu
    · -- real flip case: `updPos = s`, and equality forces `L = 0`
      have hs : updPos s u = s := updPos_eq_self_of_act_eq_one (U := U) s u hu
      have hEqNeg : energy p (updNeg s u) = energy p s := by simpa [hdet] using heq
      have hEqPos : energy p (updPos s u) = energy p s := by simp [hs]
      have hmargin0 :
          State.net p s u - (p.θ u).get TwoState.fin0 = 0 := by
        apply margin_eq_zero_of_energy_updPos_eq_updNeg (U := U) p s u
        exact by simp [hEqPos, hEqNeg]
      have : L p s u = 0 := by
        simpa [ExactHopfield.L, ExactHopfield.localField, ExactHopfield.θ0] using hmargin0
      exact hL0 this
    · -- update is a no-op; contradict `hchange`
      have : updNeg s u = s := updNeg_eq_self_of_act_eq_neg_one (U := U) s u hu
      exact hchange (by simp [hdet, this])

end

end ExactHopfield
