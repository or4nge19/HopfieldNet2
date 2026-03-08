import HopfieldNet.CReals.Mobius.Soundness

/-!
# Möbius ERA: oracle soundness

This file connects the integer-only corner oracle (`Tensor.oracle`) to real semantic bounds
on `Tensor.apply` over the square `[-1,1]×[-1,1]`.
-/

namespace Computable
namespace Mobius

open Tensor

namespace Tensor

lemma hasNoPole_cases (d1 d2 d3 d4 : ℤ) (h : Tensor.hasNoPole d1 d2 d3 d4 = true) :
    (d1 > 0 ∧ d2 > 0 ∧ d3 > 0 ∧ d4 > 0) ∨ (d1 < 0 ∧ d2 < 0 ∧ d3 < 0 ∧ d4 < 0) := by
  unfold Tensor.hasNoPole at h
  -- `hasNoPole` is a boolean disjunction of two decidable conjunctions.
  have : (d1 > 0 ∧ d2 > 0 ∧ d3 > 0 ∧ d4 > 0) ∨ (d1 < 0 ∧ d2 < 0 ∧ d3 < 0 ∧ d4 < 0) := by
    simpa [Bool.or_eq_true, decide_eq_true_eq] using h
  exact this

lemma inDigitNeg_sound_pos (n d : ℤ) (hd : 0 < d) (h : Tensor.inDigitNeg n d = true) :
    (n : ℝ) ≤ 0 ∧ (n : ℝ) + (d : ℝ) ≥ 0 := by
  unfold Tensor.inDigitNeg at h
  -- positive denominators => `s = 1`, so the check is `n ≤ 0 ∧ -d ≤ n`
  have h' : (n ≤ 0 ∧ -d ≤ n) := by
    simpa [hd, decide_eq_true_eq] using h
  constructor
  · exact_mod_cast h'.1
  · -- `-d ≤ n`  ↔  `0 ≤ n + d`
    have : 0 ≤ n + d := by linarith [h'.2]
    exact_mod_cast this

lemma inDigitNeg_sound_neg (n d : ℤ) (hd : d < 0) (h : Tensor.inDigitNeg n d = true) :
    (n : ℝ) ≥ 0 ∧ (n : ℝ) + (d : ℝ) ≤ 0 := by
  unfold Tensor.inDigitNeg at h
  have hd' : ¬ (0 < d) := by linarith
  -- negative denominators => `s = -1`, so the check is `-n ≤ 0 ∧ d ≤ -n`
  have h' : (-n ≤ 0 ∧ d ≤ -n) := by
    simpa [hd', decide_eq_true_eq] using h
  constructor
  · have : 0 ≤ n := by linarith [h'.1]
    exact_mod_cast this
  · have : n + d ≤ 0 := by linarith [h'.2]
    exact_mod_cast this

lemma inDigitPos_sound_pos (n d : ℤ) (hd : 0 < d) (h : Tensor.inDigitPos n d = true) :
    (n : ℝ) ≥ 0 ∧ (n : ℝ) - (d : ℝ) ≤ 0 := by
  unfold Tensor.inDigitPos at h
  have h' : (0 ≤ n ∧ n ≤ d) := by
    simpa [hd, decide_eq_true_eq] using h
  constructor
  · exact_mod_cast h'.1
  · have : n - d ≤ 0 := by linarith [h'.2]
    exact_mod_cast this

lemma inDigitPos_sound_neg (n d : ℤ) (hd : d < 0) (h : Tensor.inDigitPos n d = true) :
    (n : ℝ) ≤ 0 ∧ (n : ℝ) - (d : ℝ) ≥ 0 := by
  unfold Tensor.inDigitPos at h
  have hd' : ¬ (0 < d) := by linarith
  -- `s = -1`, so check is `0 ≤ -n ∧ -n ≤ -d` i.e. `n ≤ 0 ∧ d ≤ n`.
  have h' : (0 ≤ -n ∧ -n ≤ -d) := by
    simpa [hd', decide_eq_true_eq] using h
  constructor
  · have : n ≤ 0 := by linarith [h'.1]
    exact_mod_cast this
  · have : 0 ≤ n - d := by linarith [h'.2]
    exact_mod_cast this

-- A more direct version without the awkward previous line:
lemma inDigitZero_sound_pos' (n d : ℤ) (hd : 0 < d) (h : Tensor.inDigitZero n d = true) :
    (2 * (n : ℝ)) ≤ (d : ℝ) ∧ (-(d : ℝ)) ≤ (2 * (n : ℝ)) := by
  unfold Tensor.inDigitZero at h
  have h' : (2 * n ≤ d ∧ -d ≤ 2 * n) := by
    simpa [hd, decide_eq_true_eq, mul_assoc, mul_left_comm, mul_comm] using h
  constructor
  · exact_mod_cast h'.1
  · exact_mod_cast h'.2

lemma inDigitZero_sound_neg' (n d : ℤ) (hd : d < 0) (h : Tensor.inDigitZero n d = true) :
    (2 * (n : ℝ)) ≤ (-(d : ℝ)) ∧ (d : ℝ) ≤ (2 * (n : ℝ)) := by
  unfold Tensor.inDigitZero at h
  have hd' : ¬ (0 < d) := by linarith
  -- `s = -1`, so `num2 = -2n`, `abs_d = -d`.
  have h' : (-2 * n ≤ -d ∧ d ≤ -2 * n) := by
    simpa [hd', decide_eq_true_eq, mul_assoc, mul_left_comm, mul_comm, two_mul] using h
  constructor
  · -- `-2n ≤ -d` ↔ `2n ≥ d`; but with `d<0`, we want `2n ≤ -d` (same as `-2n ≥ d`) from the other conjunct
    have : 2 * n ≤ -d := by linarith [h'.2]
    exact_mod_cast this
  · have : d ≤ 2 * n := by linarith [h'.1]
    exact_mod_cast this

end Tensor

namespace Tensor

private lemma oracle_neg_data (T : Tensor) :
    Tensor.oracle T = Tensor.EmitDecision.neg →
      Tensor.hasNoPole (T.e + T.f + T.g + T.h) (-T.e + T.f - T.g + T.h)
        (-T.e - T.f + T.g + T.h) (T.e - T.f - T.g + T.h) = true
      ∧ (Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true)
      ∧ (Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true)
      ∧ (Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true)
      ∧ (Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true) := by
  intro h
  -- unfold the decision procedure and invert the nested `if`s
  dsimp [Tensor.oracle] at h
  -- expose the `cornerValues`-computed numerators/denominators
  -- (this keeps the statement readable while remaining definitional)
  change (
    if !Tensor.hasNoPole (T.e + T.f + T.g + T.h) (-T.e + T.f - T.g + T.h)
          (-T.e - T.f + T.g + T.h) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.absorb
    else if Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.neg
    else if Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.zero
    else if Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.pos
    else Tensor.EmitDecision.absorb
    ) = Tensor.EmitDecision.neg at h
  -- now invert by case analysis on the boolean tests
  cases hnp : Tensor.hasNoPole (T.e + T.f + T.g + T.h) (-T.e + T.f - T.g + T.h)
        (-T.e - T.f + T.g + T.h) (T.e - T.f - T.g + T.h) with
  | false =>
      -- then the outer `if` returns `absorb`
      have hz : EmitDecision.absorb = EmitDecision.neg := by
        simp [hnp] at h
      cases hz
  | true =>
      -- reduce to the `inDigitNeg` test
      set negTest :=
        Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
        Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
        Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h)
      cases hneg : negTest with
      | false =>
          -- falling through can never yield `neg`; split the remaining tests to contradiction
          set zeroTest :=
            Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h)
          set posTest :=
            Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h)
          cases hzero : zeroTest with
          | true =>
              have hz : EmitDecision.zero = EmitDecision.neg := by
                simp [hnp, negTest, hneg, zeroTest, hzero] at h
              cases hz
          | false =>
              cases hpos : posTest with
              | true =>
                  have hz : EmitDecision.pos = EmitDecision.neg := by
                    simp [hnp, negTest, hneg, zeroTest, hzero, posTest, hpos] at h
                  cases hz
              | false =>
                  have hz : EmitDecision.absorb = EmitDecision.neg := by
                    simp [hnp, negTest, hneg, zeroTest, hzero, posTest, hpos] at h
                  cases hz
      | true =>
          have hn0 :
              ((Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
                    Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
                  Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
                Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
            simpa [negTest, Bool.and_eq_true] using hneg
          rcases hn0 with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
          -- In this branch, the goal's first component is definitional `true = true`.
          exact ⟨rfl, h1, h2, h3, h4⟩

private lemma oracle_zero_data (T : Tensor) :
    Tensor.oracle T = Tensor.EmitDecision.zero →
      Tensor.hasNoPole (T.e + T.f + T.g + T.h) (-T.e + T.f - T.g + T.h)
        (-T.e - T.f + T.g + T.h) (T.e - T.f - T.g + T.h) = true
      ∧ (Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true)
      ∧ (Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true)
      ∧ (Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true)
      ∧ (Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true) := by
  intro h
  dsimp [Tensor.oracle] at h
  change (
    if !Tensor.hasNoPole (T.e + T.f + T.g + T.h) (-T.e + T.f - T.g + T.h)
          (-T.e - T.f + T.g + T.h) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.absorb
    else if Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.neg
    else if Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.zero
    else if Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.pos
    else Tensor.EmitDecision.absorb
    ) = Tensor.EmitDecision.zero at h
  cases hnp : Tensor.hasNoPole (T.e + T.f + T.g + T.h) (-T.e + T.f - T.g + T.h)
        (-T.e - T.f + T.g + T.h) (T.e - T.f - T.g + T.h) with
  | false =>
      have hz : EmitDecision.absorb = EmitDecision.zero := by simp [hnp] at h
      cases hz
  | true =>
      set negTest :=
        Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
        Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
        Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h)
      cases hneg : negTest with
      | true =>
          have hz : EmitDecision.neg = EmitDecision.zero := by
            simp [hnp, negTest, hneg] at h
          cases hz
      | false =>
          set zeroTest :=
            Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h)
          cases hzero : zeroTest with
          | false =>
              -- fall through: cannot be `zero`
              set posTest :=
                Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
                Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
                Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
                Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h)
              cases hpos : posTest with
              | true =>
                  have hz : EmitDecision.pos = EmitDecision.zero := by
                    simp [hnp, negTest, hneg, zeroTest, hzero, posTest, hpos] at h
                  cases hz
              | false =>
                  have hz : EmitDecision.absorb = EmitDecision.zero := by
                    simp [hnp, negTest, hneg, zeroTest, hzero, posTest, hpos] at h
                  cases hz
          | true =>
              have hz0 :
                  ((Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
                        Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
                      Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
                    Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
                simpa [zeroTest, Bool.and_eq_true] using hzero
              rcases hz0 with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
              exact ⟨rfl, h1, h2, h3, h4⟩

private lemma oracle_pos_data (T : Tensor) :
    Tensor.oracle T = Tensor.EmitDecision.pos →
      Tensor.hasNoPole (T.e + T.f + T.g + T.h) (-T.e + T.f - T.g + T.h)
        (-T.e - T.f + T.g + T.h) (T.e - T.f - T.g + T.h) = true
      ∧ (Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true)
      ∧ (Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true)
      ∧ (Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true)
      ∧ (Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true) := by
  intro h
  dsimp [Tensor.oracle] at h
  change (
    if !Tensor.hasNoPole (T.e + T.f + T.g + T.h) (-T.e + T.f - T.g + T.h)
          (-T.e - T.f + T.g + T.h) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.absorb
    else if Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.neg
    else if Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.zero
    else if Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) then Tensor.EmitDecision.pos
    else Tensor.EmitDecision.absorb
    ) = Tensor.EmitDecision.pos at h
  cases hnp : Tensor.hasNoPole (T.e + T.f + T.g + T.h) (-T.e + T.f - T.g + T.h)
        (-T.e - T.f + T.g + T.h) (T.e - T.f - T.g + T.h) with
  | false =>
      have : EmitDecision.absorb = EmitDecision.pos := by simp [hnp] at h
      cases this
  | true =>
      set negTest :=
        Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
        Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
        Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h)
      cases hneg : negTest with
      | true =>
          have : EmitDecision.neg = EmitDecision.pos := by simp [hnp, negTest, hneg] at h
          cases this
      | false =>
          set zeroTest :=
            Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
            Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
            Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
            Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h)
          cases hzero : zeroTest with
          | true =>
              have : EmitDecision.zero = EmitDecision.pos := by
                simp [hnp, negTest, hneg, zeroTest, hzero] at h
              cases this
          | false =>
              set posTest :=
                Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) &&
                Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) &&
                Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) &&
                Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h)
              cases hpos : posTest with
              | false =>
                  have : EmitDecision.absorb = EmitDecision.pos := by
                    simp [hnp, negTest, hneg, zeroTest, hzero, posTest, hpos] at h
                  cases this
              | true =>
                  have hp0 :
                      ((Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
                            Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
                          Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
                        Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
                    simpa [posTest, Bool.and_eq_true] using hpos
                  rcases hp0 with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
                  exact ⟨rfl, h1, h2, h3, h4⟩

theorem emitNeg_sound (T : Tensor) (x y : ℝ)
    (hx1 : -1 ≤ x) (hx2 : x ≤ 1) (hy1 : -1 ≤ y) (hy2 : y ≤ 1) :
    Tensor.oracle T = Tensor.EmitDecision.neg →
    -1 ≤ Tensor.apply T x y ∧ Tensor.apply T x y ≤ 0 := by
  intro h_oracle
  have hdata := oracle_neg_data (T := T) h_oracle
  have h_np_cases := Tensor.hasNoPole_cases _ _ _ _ hdata.1
  -- extract corner checks
  have hneg1 := hdata.2.1
  have hneg2 := hdata.2.2.1
  have hneg3 := hdata.2.2.2.1
  have hneg4 := hdata.2.2.2.2
  rcases h_np_cases with hd_pos | hd_neg
  · -- denominators positive everywhere
    have b1 := Tensor.inDigitNeg_sound_pos (n := T.a + T.b + T.c + T.d) (d := T.e + T.f + T.g + T.h)
      (by exact hd_pos.1) hneg1
    have b2 := Tensor.inDigitNeg_sound_pos (n := -T.a + T.b - T.c + T.d) (d := -T.e + T.f - T.g + T.h)
      (by exact hd_pos.2.1) hneg2
    have b3 := Tensor.inDigitNeg_sound_pos (n := -T.a - T.b + T.c + T.d) (d := -T.e - T.f + T.g + T.h)
      (by exact hd_pos.2.2.1) hneg3
    have b4 := Tensor.inDigitNeg_sound_pos (n := T.a - T.b - T.c + T.d) (d := T.e - T.f - T.g + T.h)
      (by exact hd_pos.2.2.2) hneg4
    have h_num_le_zero :
        (T.a:ℝ)*x*y + (T.b:ℝ)*x + (T.c:ℝ)*y + (T.d:ℝ) ≤ 0 := by
      apply bilinear_nonpos_of_corners (T.a:ℝ) (T.b:ℝ) (T.c:ℝ) (T.d:ℝ)
      ·
        have h := b1.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        have h := b2.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        have h := b3.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        have h := b4.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2
    have h_num_plus_den_ge_zero :
        ((T.a:ℝ)+(T.e:ℝ))*x*y + ((T.b:ℝ)+(T.f:ℝ))*x + ((T.c:ℝ)+(T.g:ℝ))*y + ((T.d:ℝ)+(T.h:ℝ)) ≥ 0 := by
      apply bilinear_nonneg_of_corners
      ·
        have h := b1.2
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        have h := b2.2
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        have h := b3.2
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        have h := b4.2
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2
    have h_den_pos :
        (T.e:ℝ)*x*y + (T.f:ℝ)*x + (T.g:ℝ)*y + (T.h:ℝ) > 0 := by
      apply bilinear_pos_of_corners
      ·
        have : (T.e + T.f + T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.1
        simpa [one_mul, mul_one, add_assoc, add_comm, add_left_comm] using this
      ·
        have : (-T.e + T.f - T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.2.1
        have hform :
            (↑T.e * (1:ℝ) * (-1) + ↑T.f * 1 + ↑T.g * (-1) + ↑T.h)
              = (-T.e + T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      ·
        have : (-T.e - T.f + T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.2.2.1
        have hform :
            (↑T.e * (-1:ℝ) * 1 + ↑T.f * (-1) + ↑T.g * 1 + ↑T.h)
              = (-T.e - T.f + T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      ·
        have : (T.e - T.f - T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.2.2.2
        have hform :
            (↑T.e * (-1:ℝ) * (-1) + ↑T.f * (-1) + ↑T.g * (-1) + ↑T.h)
              = (T.e - T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2
    unfold Tensor.apply
    constructor
    ·
      let N : ℝ := (↑T.a * x * y + ↑T.b * x + ↑T.c * y + ↑T.d)
      let D : ℝ := (↑T.e * x * y + ↑T.f * x + ↑T.g * y + ↑T.h)
      have hmul : (-1 : ℝ) * D ≤ N := by
        -- from `0 ≤ N + D` we get `-D ≤ N`
        dsimp [N, D]
        linarith [h_num_plus_den_ge_zero]
      have : (-1 : ℝ) ≤ N / D := (le_div_iff₀ h_den_pos).2 hmul
      simpa [N, D] using this
    ·
      let N : ℝ := (↑T.a * x * y + ↑T.b * x + ↑T.c * y + ↑T.d)
      let D : ℝ := (↑T.e * x * y + ↑T.f * x + ↑T.g * y + ↑T.h)
      have hmul : N ≤ (0 : ℝ) * D := by
        dsimp [N, D]
        simpa [zero_mul] using h_num_le_zero
      have : N / D ≤ (0 : ℝ) := (div_le_iff₀ h_den_pos).2 hmul
      simpa [N, D] using this
  · -- denominators negative everywhere
    have b1 := Tensor.inDigitNeg_sound_neg (n := T.a + T.b + T.c + T.d) (d := T.e + T.f + T.g + T.h)
      hd_neg.1 hneg1
    have b2 := Tensor.inDigitNeg_sound_neg (n := -T.a + T.b - T.c + T.d) (d := -T.e + T.f - T.g + T.h)
      hd_neg.2.1 hneg2
    have b3 := Tensor.inDigitNeg_sound_neg (n := -T.a - T.b + T.c + T.d) (d := -T.e - T.f + T.g + T.h)
      hd_neg.2.2.1 hneg3
    have b4 := Tensor.inDigitNeg_sound_neg (n := T.a - T.b - T.c + T.d) (d := T.e - T.f - T.g + T.h)
      hd_neg.2.2.2 hneg4
    have h_num_ge_zero :
        (T.a:ℝ)*x*y + (T.b:ℝ)*x + (T.c:ℝ)*y + (T.d:ℝ) ≥ 0 := by
      apply bilinear_nonneg_of_corners (T.a:ℝ) (T.b:ℝ) (T.c:ℝ) (T.d:ℝ)
      ·
        have h := b1.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        have h := b2.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        have h := b3.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        have h := b4.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2
    have h_num_plus_den_le_zero :
        ((T.a:ℝ)+(T.e:ℝ))*x*y + ((T.b:ℝ)+(T.f:ℝ))*x + ((T.c:ℝ)+(T.g:ℝ))*y + ((T.d:ℝ)+(T.h:ℝ)) ≤ 0 := by
      apply bilinear_nonpos_of_corners
      ·
        -- (1, 1)
        have h := b1.2
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        -- (1, -1)
        have h := b2.2
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        -- (-1, 1)
        have h := b3.2
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        -- (-1, -1)
        have h := b4.2
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2
    have h_den_neg :
        (T.e:ℝ)*x*y + (T.f:ℝ)*x + (T.g:ℝ)*y + (T.h:ℝ) < 0 := by
      apply bilinear_neg_of_corners
      ·
        have : (T.e + T.f + T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.1
        simpa [one_mul, mul_one, add_assoc, add_comm, add_left_comm] using this
      ·
        have : (-T.e + T.f - T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.2.1
        have hform :
            (↑T.e * (1:ℝ) * (-1) + ↑T.f * 1 + ↑T.g * (-1) + ↑T.h)
              = (-T.e + T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      ·
        have : (-T.e - T.f + T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.2.2.1
        have hform :
            (↑T.e * (-1:ℝ) * 1 + ↑T.f * (-1) + ↑T.g * 1 + ↑T.h)
              = (-T.e - T.f + T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      ·
        have : (T.e - T.f - T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.2.2.2
        have hform :
            (↑T.e * (-1:ℝ) * (-1) + ↑T.f * (-1) + ↑T.g * (-1) + ↑T.h)
              = (T.e - T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2
    unfold Tensor.apply
    constructor
    · -- `-1 ≤ N/D` with `D<0` ↔ `-1 * D ≥ N` ↔ `N + D ≤ 0`
      -- use the standard division lemma for negative denominators
      have hlin :
          (-1 : ℝ) * ((T.e:ℝ)*x*y + (T.f:ℝ)*x + (T.g:ℝ)*y + (T.h:ℝ))
            ≥ ((T.a:ℝ)*x*y + (T.b:ℝ)*x + (T.c:ℝ)*y + (T.d:ℝ)) := by
        -- `N + D ≤ 0` rearranges to `N ≤ -D = (-1)*D`
        linarith [h_num_plus_den_le_zero]
      -- `a ≤ b / c` with `c<0` is equivalent to `a*c ≥ b`
      have := (le_div_iff_of_neg h_den_neg).2 hlin
      simpa using this
    · -- `N/D ≤ 0` with `D<0` ↔ `0 * D ≥ N` ↔ `N ≥ 0`
      -- monotone sign reasoning: nonneg / neg is nonpos
      have hN : 0 ≤ (↑T.a * x * y + ↑T.b * x + ↑T.c * y + ↑T.d) := by linarith [h_num_ge_zero]
      have hD : (↑T.e * x * y + ↑T.f * x + ↑T.g * y + ↑T.h) ≤ 0 := le_of_lt h_den_neg
      exact div_nonpos_of_nonneg_of_nonpos hN hD

theorem emitZero_sound (T : Tensor) (x y : ℝ)
    (hx1 : -1 ≤ x) (hx2 : x ≤ 1) (hy1 : -1 ≤ y) (hy2 : y ≤ 1) :
    Tensor.oracle T = Tensor.EmitDecision.zero →
    (-1/2 : ℝ) ≤ Tensor.apply T x y ∧ Tensor.apply T x y ≤ (1/2 : ℝ) := by
  intro h_oracle
  have hdata := oracle_zero_data (T := T) h_oracle
  have h_np_cases := Tensor.hasNoPole_cases _ _ _ _ hdata.1
  have hz1 := hdata.2.1
  have hz2 := hdata.2.2.1
  have hz3 := hdata.2.2.2.1
  have hz4 := hdata.2.2.2.2
  rcases h_np_cases with hd_pos | hd_neg
  · -- denominators positive everywhere
    have b1 := Tensor.inDigitZero_sound_pos' (n := T.a + T.b + T.c + T.d) (d := T.e + T.f + T.g + T.h)
      (by exact hd_pos.1) hz1
    have b2 := Tensor.inDigitZero_sound_pos' (n := -T.a + T.b - T.c + T.d) (d := -T.e + T.f - T.g + T.h)
      (by exact hd_pos.2.1) hz2
    have b3 := Tensor.inDigitZero_sound_pos' (n := -T.a - T.b + T.c + T.d) (d := -T.e - T.f + T.g + T.h)
      (by exact hd_pos.2.2.1) hz3
    have b4 := Tensor.inDigitZero_sound_pos' (n := T.a - T.b - T.c + T.d) (d := T.e - T.f - T.g + T.h)
      (by exact hd_pos.2.2.2) hz4
    -- show `2N ≤ D` and `-D ≤ 2N` on the whole square
    have h_twoN_le_D :
        (2:ℝ) * ((↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d))
          ≤ (↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h) := by
      have hdiff :
          ((2:ℝ) * (↑T.a) - (↑T.e)) * x * y + ((2:ℝ) * (↑T.b) - (↑T.f)) * x
            + ((2:ℝ) * (↑T.c) - (↑T.g)) * y + ((2:ℝ) * (↑T.d) - (↑T.h)) ≤ 0 := by
        apply bilinear_nonpos_of_corners
        ·
          have h := b1.1
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b2.1
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b3.1
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b4.1
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        · exact hx1
        · exact hx2
        · exact hy1
        · exact hy2
      have hEq :
          ((2:ℝ) * (↑T.a) - (↑T.e)) * x * y + ((2:ℝ) * (↑T.b) - (↑T.f)) * x
              + ((2:ℝ) * (↑T.c) - (↑T.g)) * y + ((2:ℝ) * (↑T.d) - (↑T.h))
            =
          (2:ℝ) * ((↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d))
              - ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)) := by
        ring_nf
      have : (2:ℝ) * ((↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d))
              - ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)) ≤ 0 := by
        simpa [hEq] using hdiff
      linarith
    have h_negD_le_twoN :
        -((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h))
          ≤ (2:ℝ) * ((↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d)) := by
      have hdiff :
          ((2:ℝ) * (↑T.a) + (↑T.e)) * x * y + ((2:ℝ) * (↑T.b) + (↑T.f)) * x
            + ((2:ℝ) * (↑T.c) + (↑T.g)) * y + ((2:ℝ) * (↑T.d) + (↑T.h)) ≥ 0 := by
        apply bilinear_nonneg_of_corners
        ·
          have h := b1.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b2.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b3.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b4.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        · exact hx1
        · exact hx2
        · exact hy1
        · exact hy2
      have hEq :
          ((2:ℝ) * (↑T.a) + (↑T.e)) * x * y + ((2:ℝ) * (↑T.b) + (↑T.f)) * x
              + ((2:ℝ) * (↑T.c) + (↑T.g)) * y + ((2:ℝ) * (↑T.d) + (↑T.h))
            =
          (2:ℝ) * ((↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d))
              + ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)) := by
        ring_nf
      have : (2:ℝ) * ((↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d))
              + ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)) ≥ 0 := by
        simpa [hEq] using hdiff
      linarith
    have h_den_pos :
        (↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h) > 0 := by
      apply bilinear_pos_of_corners
      ·
        have : (T.e + T.f + T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.1
        simpa [one_mul, mul_one, add_assoc, add_comm, add_left_comm] using this
      ·
        have : (-T.e + T.f - T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.2.1
        have hform :
            (↑T.e * (1:ℝ) * (-1) + ↑T.f * 1 + ↑T.g * (-1) + ↑T.h)
              = (-T.e + T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      ·
        have : (-T.e - T.f + T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.2.2.1
        have hform :
            (↑T.e * (-1:ℝ) * 1 + ↑T.f * (-1) + ↑T.g * 1 + ↑T.h)
              = (-T.e - T.f + T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      ·
        have : (T.e - T.f - T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.2.2.2
        have hform :
            (↑T.e * (-1:ℝ) * (-1) + ↑T.f * (-1) + ↑T.g * (-1) + ↑T.h)
              = (T.e - T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2
    unfold Tensor.apply
    constructor
    · -- `-1/2 ≤ N/D` ↔ `(-1/2) * D ≤ N` ↔ `-D ≤ 2N`
      have hmul : (-1/2 : ℝ) * ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h))
          ≤ (↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d) := by
        have := h_negD_le_twoN
        linarith
      exact (le_div_iff₀ h_den_pos).2 hmul
    · -- `N/D ≤ 1/2` ↔ `N ≤ (1/2) * D` ↔ `2N ≤ D`
      have hmul : (↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d)
          ≤ (1/2 : ℝ) * ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)) := by
        have := h_twoN_le_D
        linarith
      exact (div_le_iff₀ h_den_pos).2 hmul
  · -- denominators negative everywhere
    have b1 := Tensor.inDigitZero_sound_neg' (n := T.a + T.b + T.c + T.d) (d := T.e + T.f + T.g + T.h)
      hd_neg.1 hz1
    have b2 := Tensor.inDigitZero_sound_neg' (n := -T.a + T.b - T.c + T.d) (d := -T.e + T.f - T.g + T.h)
      hd_neg.2.1 hz2
    have b3 := Tensor.inDigitZero_sound_neg' (n := -T.a - T.b + T.c + T.d) (d := -T.e - T.f + T.g + T.h)
      hd_neg.2.2.1 hz3
    have b4 := Tensor.inDigitZero_sound_neg' (n := T.a - T.b - T.c + T.d) (d := T.e - T.f - T.g + T.h)
      hd_neg.2.2.2 hz4
    have h_den_neg :
        (↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h) < 0 := by
      apply bilinear_neg_of_corners
      ·
        have : (T.e + T.f + T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.1
        simpa [one_mul, mul_one, add_assoc, add_comm, add_left_comm] using this
      ·
        have : (-T.e + T.f - T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.2.1
        have hform :
            (↑T.e * (1:ℝ) * (-1) + ↑T.f * 1 + ↑T.g * (-1) + ↑T.h)
              = (-T.e + T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      ·
        have : (-T.e - T.f + T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.2.2.1
        have hform :
            (↑T.e * (-1:ℝ) * 1 + ↑T.f * (-1) + ↑T.g * 1 + ↑T.h)
              = (-T.e - T.f + T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      ·
        have : (T.e - T.f - T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.2.2.2
        have hform :
            (↑T.e * (-1:ℝ) * (-1) + ↑T.f * (-1) + ↑T.g * (-1) + ↑T.h)
              = (T.e - T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2
    -- for `D<0`: `N/D ≤ 1/2` ↔ `N ≥ (1/2)*D` (i.e. `D - 2N ≤ 0`)
    have h_D_le_twoN :
        (↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)
          ≤ (2:ℝ) * ((↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d)) := by
      have hdiff :
          ((↑T.e) - (2:ℝ) * (↑T.a)) * x * y + ((↑T.f) - (2:ℝ) * (↑T.b)) * x
            + ((↑T.g) - (2:ℝ) * (↑T.c)) * y + ((↑T.h) - (2:ℝ) * (↑T.d)) ≤ 0 := by
        apply bilinear_nonpos_of_corners
        ·
          have h := b1.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b2.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b3.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b4.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        · exact hx1
        · exact hx2
        · exact hy1
        · exact hy2
      have hEq :
          ((↑T.e) - (2:ℝ) * (↑T.a)) * x * y + ((↑T.f) - (2:ℝ) * (↑T.b)) * x
              + ((↑T.g) - (2:ℝ) * (↑T.c)) * y + ((↑T.h) - (2:ℝ) * (↑T.d))
            =
          (↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)
              - (2:ℝ) * ((↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d)) := by
        ring_nf
      have : (↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)
            - (2:ℝ) * ((↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d)) ≤ 0 := by
        simpa [hEq] using hdiff
      linarith
    have h_twoN_le_negD :
        (2:ℝ) * ((↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d))
          ≤ -((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)) := by
      have hdiff :
          ((2:ℝ) * (↑T.a) + (↑T.e)) * x * y + ((2:ℝ) * (↑T.b) + (↑T.f)) * x
            + ((2:ℝ) * (↑T.c) + (↑T.g)) * y + ((2:ℝ) * (↑T.d) + (↑T.h)) ≤ 0 := by
        apply bilinear_nonpos_of_corners
        ·
          have h := b1.1
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b2.1
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b3.1
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b4.1
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        · exact hx1
        · exact hx2
        · exact hy1
        · exact hy2
      have hEq :
          ((2:ℝ) * (↑T.a) + (↑T.e)) * x * y + ((2:ℝ) * (↑T.b) + (↑T.f)) * x
              + ((2:ℝ) * (↑T.c) + (↑T.g)) * y + ((2:ℝ) * (↑T.d) + (↑T.h))
            =
          (2:ℝ) * ((↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d))
              + ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)) := by
        ring_nf
      have : (2:ℝ) * ((↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d))
              + ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)) ≤ 0 := by
        simpa [hEq] using hdiff
      linarith
    unfold Tensor.apply
    constructor
    · -- `-1/2 ≤ N/D` with `D<0` ↔ `(-1/2) * D ≥ N`
      have hmul :
          (-1/2 : ℝ) * ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h))
            ≥ (↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d) := by
        have := h_twoN_le_negD
        linarith
      exact (le_div_iff_of_neg h_den_neg).2 hmul
    · -- `N/D ≤ 1/2` with `D<0` ↔ `N ≥ (1/2) * D`
      have hmul :
          (↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d)
            ≥ (1/2 : ℝ) * ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)) := by
        have := h_D_le_twoN
        linarith
      exact (div_le_iff_of_neg h_den_neg).2 hmul

theorem emitPos_sound (T : Tensor) (x y : ℝ)
    (hx1 : -1 ≤ x) (hx2 : x ≤ 1) (hy1 : -1 ≤ y) (hy2 : y ≤ 1) :
    Tensor.oracle T = Tensor.EmitDecision.pos →
    0 ≤ Tensor.apply T x y ∧ Tensor.apply T x y ≤ 1 := by
  intro h_oracle
  have hdata := oracle_pos_data (T := T) h_oracle
  have h_np_cases := Tensor.hasNoPole_cases _ _ _ _ hdata.1
  have hp1 := hdata.2.1
  have hp2 := hdata.2.2.1
  have hp3 := hdata.2.2.2.1
  have hp4 := hdata.2.2.2.2
  rcases h_np_cases with hd_pos | hd_neg
  · -- denominators positive
    have b1 := Tensor.inDigitPos_sound_pos (n := T.a + T.b + T.c + T.d) (d := T.e + T.f + T.g + T.h)
      (by exact hd_pos.1) hp1
    have b2 := Tensor.inDigitPos_sound_pos (n := -T.a + T.b - T.c + T.d) (d := -T.e + T.f - T.g + T.h)
      (by exact hd_pos.2.1) hp2
    have b3 := Tensor.inDigitPos_sound_pos (n := -T.a - T.b + T.c + T.d) (d := -T.e - T.f + T.g + T.h)
      (by exact hd_pos.2.2.1) hp3
    have b4 := Tensor.inDigitPos_sound_pos (n := T.a - T.b - T.c + T.d) (d := T.e - T.f - T.g + T.h)
      (by exact hd_pos.2.2.2) hp4
    have h_num_nonneg :
        (↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d) ≥ 0 := by
      apply bilinear_nonneg_of_corners (↑T.a) (↑T.b) (↑T.c) (↑T.d)
      ·
        have h := b1.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        have h := b2.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        have h := b3.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        have h := b4.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2
    have h_num_le_den :
        (↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d)
          ≤ (↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h) := by
      -- N ≤ D is bilinear nonpos for (N - D)
      have hdiff :
          ((↑T.a) - (↑T.e)) * x * y + ((↑T.b) - (↑T.f)) * x + ((↑T.c) - (↑T.g)) * y + ((↑T.d) - (↑T.h)) ≤ 0 := by
        apply bilinear_nonpos_of_corners
        ·
          have h := b1.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b2.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b3.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b4.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        · exact hx1
        · exact hx2
        · exact hy1
        · exact hy2
      have hEq :
          ((↑T.a) - (↑T.e)) * x * y + ((↑T.b) - (↑T.f)) * x + ((↑T.c) - (↑T.g)) * y + ((↑T.d) - (↑T.h))
            =
          (↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d)
            - ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)) := by
        ring_nf
      have : (↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d)
            - ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)) ≤ 0 := by
        simpa [hEq] using hdiff
      linarith
    have h_den_pos :
        (↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h) > 0 := by
      apply bilinear_pos_of_corners
      ·
        have : (T.e + T.f + T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.1
        simpa [one_mul, mul_one, add_assoc, add_comm, add_left_comm] using this
      ·
        have : (-T.e + T.f - T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.2.1
        have hform :
            (↑T.e * (1:ℝ) * (-1) + ↑T.f * 1 + ↑T.g * (-1) + ↑T.h)
              = (-T.e + T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      ·
        have : (-T.e - T.f + T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.2.2.1
        have hform :
            (↑T.e * (-1:ℝ) * 1 + ↑T.f * (-1) + ↑T.g * 1 + ↑T.h)
              = (-T.e - T.f + T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      ·
        have : (T.e - T.f - T.g + T.h : ℝ) > 0 := by exact_mod_cast hd_pos.2.2.2
        have hform :
            (↑T.e * (-1:ℝ) * (-1) + ↑T.f * (-1) + ↑T.g * (-1) + ↑T.h)
              = (T.e - T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2
    unfold Tensor.apply
    constructor
    · exact div_nonneg h_num_nonneg.le (le_of_lt h_den_pos)
    · -- N/D ≤ 1 ↔ N ≤ 1*D
      have : (↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d)
          ≤ (1:ℝ) * ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)) := by
        simpa using h_num_le_den
      exact (div_le_iff₀ h_den_pos).2 this
  · -- denominators negative
    have b1 := Tensor.inDigitPos_sound_neg (n := T.a + T.b + T.c + T.d) (d := T.e + T.f + T.g + T.h)
      hd_neg.1 hp1
    have b2 := Tensor.inDigitPos_sound_neg (n := -T.a + T.b - T.c + T.d) (d := -T.e + T.f - T.g + T.h)
      hd_neg.2.1 hp2
    have b3 := Tensor.inDigitPos_sound_neg (n := -T.a - T.b + T.c + T.d) (d := -T.e - T.f + T.g + T.h)
      hd_neg.2.2.1 hp3
    have b4 := Tensor.inDigitPos_sound_neg (n := T.a - T.b - T.c + T.d) (d := T.e - T.f - T.g + T.h)
      hd_neg.2.2.2 hp4
    have h_den_neg :
        (↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h) < 0 := by
      apply bilinear_neg_of_corners
      ·
        have : (T.e + T.f + T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.1
        simpa [one_mul, mul_one, add_assoc, add_comm, add_left_comm] using this
      ·
        have : (-T.e + T.f - T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.2.1
        have hform :
            (↑T.e * (1:ℝ) * (-1) + ↑T.f * 1 + ↑T.g * (-1) + ↑T.h)
              = (-T.e + T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      ·
        have : (-T.e - T.f + T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.2.2.1
        have hform :
            (↑T.e * (-1:ℝ) * 1 + ↑T.f * (-1) + ↑T.g * 1 + ↑T.h)
              = (-T.e - T.f + T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      ·
        have : (T.e - T.f - T.g + T.h : ℝ) < 0 := by exact_mod_cast hd_neg.2.2.2
        have hform :
            (↑T.e * (-1:ℝ) * (-1) + ↑T.f * (-1) + ↑T.g * (-1) + ↑T.h)
              = (T.e - T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2
    have h_num_nonpos :
        (↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d) ≤ 0 := by
      apply bilinear_nonpos_of_corners (↑T.a) (↑T.b) (↑T.c) (↑T.d)
      ·
        have h := b1.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        have h := b2.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        have h := b3.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      ·
        have h := b4.1
        push_cast at h
        ring_nf at h
        ring_nf
        linarith [h]
      · exact hx1
      · exact hx2
      · exact hy1
      · exact hy2
    have h_den_le_num :
        (↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)
          ≤ (↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d) := by
      -- from `n - d ≥ 0` corners => `N - D ≥ 0` on square
      have hdiff :
          ((↑T.a) - (↑T.e)) * x * y + ((↑T.b) - (↑T.f)) * x + ((↑T.c) - (↑T.g)) * y + ((↑T.d) - (↑T.h)) ≥ 0 := by
        apply bilinear_nonneg_of_corners
        ·
          have h := b1.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b2.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b3.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        ·
          have h := b4.2
          push_cast at h
          ring_nf at h
          ring_nf
          linarith [h]
        · exact hx1
        · exact hx2
        · exact hy1
        · exact hy2
      -- rewrite `hdiff` into `0 ≤ N - D`
      have : (↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d)
            - ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)) ≥ 0 := by
        -- `hdiff` is exactly `N - D ≥ 0` after expanding products and collecting terms.
        have h' := hdiff
        have hEq :
            ((↑T.a) - (↑T.e)) * x * y + ((↑T.b) - (↑T.f)) * x + ((↑T.c) - (↑T.g)) * y + ((↑T.d) - (↑T.h))
              =
            (↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d)
              - ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)) := by
          ring_nf
        -- transport `≥ 0` across the equality
        simpa [hEq] using h'
      linarith
    unfold Tensor.apply
    constructor
    · -- 0 ≤ N/D with D<0 ↔ 0*D ≥ N ↔ N ≤ 0
      -- `N ≤ 0` and `D < 0` imply `0 ≤ N / D`.
      let N : ℝ := (↑T.a * x * y + ↑T.b * x + ↑T.c * y + ↑T.d)
      let D : ℝ := (↑T.e * x * y + ↑T.f * x + ↑T.g * y + ↑T.h)
      have hN' : 0 ≤ -N := by
        dsimp [N]
        linarith [h_num_nonpos]
      have hD' : 0 ≤ -D := by
        dsimp [D]
        linarith [le_of_lt h_den_neg]
      have : 0 ≤ (-N) / (-D) := div_nonneg hN' hD'
      simpa [div_eq_mul_inv] using this
    · -- N/D ≤ 1 with D<0 ↔ N ≥ 1*D
      have : (↑T.a) * x * y + (↑T.b) * x + (↑T.c) * y + (↑T.d)
            ≥ (1:ℝ) * ((↑T.e) * x * y + (↑T.f) * x + (↑T.g) * y + (↑T.h)) := by
        simpa using h_den_le_num
      exact (div_le_iff_of_neg h_den_neg).2 this

end Tensor

end Mobius
end Computable
