import Mathlib

set_option autoImplicit false

namespace Rebuild.Core

/-- A bare two-state local alphabet. -/
class TwoState (σ : Type*) where
  pos : σ
  neg : σ
  pos_ne_neg : pos ≠ neg

instance {σ : Type*} [TwoState σ] : Nonempty σ := ⟨TwoState.pos⟩

namespace TwoState

variable {σ : Type*} [TwoState σ]

@[simp]
theorem pos_ne_neg' : (TwoState.pos : σ) ≠ TwoState.neg :=
  TwoState.pos_ne_neg

@[simp]
theorem neg_ne_pos' : (TwoState.neg : σ) ≠ TwoState.pos :=
  Ne.symm TwoState.pos_ne_neg

end TwoState

/-- A numeric encoding of a two-state alphabet. -/
structure TwoStateEncoding (σ : Type*) [TwoState σ] where
  toReal : σ → ℝ
  strict_order : toReal TwoState.neg < toReal TwoState.pos

namespace TwoStateEncoding

variable {σ : Type*} [TwoState σ]

@[simp]
def scale (e : TwoStateEncoding σ) : ℝ :=
  e.toReal TwoState.pos - e.toReal TwoState.neg

lemma scale_pos (e : TwoStateEncoding σ) : 0 < e.scale := by
  dsimp [scale]
  linarith [e.strict_order]

end TwoStateEncoding

instance : TwoState Bool where
  pos := true
  neg := false
  pos_ne_neg := by decide

namespace TwoStateEncoding

/-- The signed-spin encoding `true ↦ 1`, `false ↦ -1`. -/
def boolSigned : TwoStateEncoding Bool where
  toReal b := if b then 1 else -1
  strict_order := by
    change (if false then (1 : ℝ) else -1) < if true then (1 : ℝ) else -1
    norm_num

/-- The zero-one encoding `true ↦ 1`, `false ↦ 0`. -/
def boolZeroOne : TwoStateEncoding Bool where
  toReal b := if b then 1 else 0
  strict_order := by
    change (if false then (1 : ℝ) else 0) < if true then (1 : ℝ) else 0
    norm_num

@[simp]
lemma boolSigned_true : boolSigned.toReal true = 1 := by simp [boolSigned]

@[simp]
lemma boolSigned_false : boolSigned.toReal false = -1 := by simp [boolSigned]

@[simp]
lemma boolZeroOne_true : boolZeroOne.toReal true = 1 := by simp [boolZeroOne]

@[simp]
lemma boolZeroOne_false : boolZeroOne.toReal false = 0 := by simp [boolZeroOne]

end TwoStateEncoding

end Rebuild.Core
