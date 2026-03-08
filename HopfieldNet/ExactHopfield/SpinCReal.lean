/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import HopfieldNet.CReals.CRealRealEquiv

/-!
# Spin States and their embedding into Computable Reals

This file defines a minimal `Spin` type (isomorphic to `{+1, -1}`) and its embedding into
`Computable.CReal`. The file is self-contained, avoiding dependencies on `SpinState.Basic`
(which has some pre-existing upstream issues).

The embedding `Spin.toCReal` is the first link in the chain connecting the Hopfield network
formalization to the exact-real computation stack.

## Main definitions

- `Spin`: the binary spin type (`up` = +1, `dn` = -1).
- `Spin.toCReal`: computable embedding into `CReal`.
- `Spin.toReal`: classical embedding into `ℝ`.

## Main results

- `Spin.toReal_toCReal`: `toRealRingHom (toCReal s) = toReal s`.
- `Spin.toCReal_sq`: `(toCReal s) ^ 2 = 1`.
-/

open Computable

/-- Binary spin: `up` represents +1, `dn` represents -1. -/
inductive Spin : Type
  | up : Spin
  | dn : Spin
  deriving DecidableEq, Inhabited

namespace Spin

instance : Fintype Spin where
  elems := {up, dn}
  complete := by intro x; cases x <;> simp

/-- Embed into `Computable.CReal`: `up ↦ 1`, `dn ↦ -1`. -/
def toCReal : Spin → CReal
  | up => 1
  | dn => -1

/-- Embed into `ℝ`: `up ↦ 1`, `dn ↦ -1`. -/
noncomputable def toReal : Spin → ℝ
  | up => 1
  | dn => -1

@[simp] theorem toCReal_up : toCReal up = (1 : CReal) := rfl
@[simp] theorem toCReal_dn : toCReal dn = (-1 : CReal) := rfl

@[simp] theorem toReal_up : toReal up = (1 : ℝ) := rfl
@[simp] theorem toReal_dn : toReal dn = (-1 : ℝ) := rfl

/-- `toCReal` is compatible with `toReal` via the denotation ring hom. -/
theorem toReal_toCReal (s : Spin) :
    CReal.toRealRingHom (toCReal s) = toReal s := by
  cases s <;> simp [toCReal, toReal, map_neg, map_one]

/-- `toCReal s` squares to `1`. -/
theorem toCReal_sq (s : Spin) : toCReal s ^ 2 = 1 := by
  cases s <;> simp [toCReal] <;> norm_num

/-- `toCReal s * toCReal s = 1`. -/
theorem toCReal_mul_self (s : Spin) : toCReal s * toCReal s = 1 := by
  cases s <;> simp [toCReal] <;> norm_num

/-- `toCReal` is injective. -/
theorem toCReal_injective : Function.Injective toCReal := by
  intro a b h
  cases a <;> cases b <;> simp_all [toCReal]
  · have : (1 : CReal) = -1 := h
    have h1 := congr_arg CReal.toRealRingHom this
    simp [map_neg, map_one] at h1; norm_num at h1
  · have : (-1 : CReal) = 1 := h
    have h1 := congr_arg CReal.toRealRingHom this
    simp [map_neg, map_one] at h1; norm_num at h1

/-- Each `toCReal s` is either `1` or `-1`. -/
theorem toCReal_one_or_neg_one (s : Spin) : toCReal s = 1 ∨ toCReal s = -1 := by
  cases s <;> simp [toCReal]

/-- Flip a spin. -/
def flip : Spin → Spin
  | up => dn
  | dn => up

@[simp] theorem flip_flip (s : Spin) : s.flip.flip = s := by cases s <;> rfl
@[simp] theorem flip_ne (s : Spin) : s.flip ≠ s := by cases s <;> simp [flip]

theorem toCReal_flip (s : Spin) : toCReal s.flip = -toCReal s := by
  cases s <;> simp [flip, toCReal]

/-- `toCReal s - toCReal s.flip` is either `2` or `-2`. -/
theorem toCReal_sub_flip (s : Spin) :
    toCReal s - toCReal s.flip = (1 + 1) * toCReal s := by
  cases s
  · show (1 : CReal) - (-1) = (1 + 1) * 1; ring
  · show (-1 : CReal) - 1 = (1 + 1) * (-1); ring

end Spin
