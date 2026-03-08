import HopfieldNet.CReals.SignedDigit.Operations
import Mathlib.Tactic

/-!
# Signed-digit shift / cons primitives

This file adds the standard corecursive primitive `cons` (prepend one digit to a stream),
and proves the key exact formula on partial sums:

`partialSum (cons d x) (n+1) = d/2 + (1/2) * partialSum x n`.

This is the main building block for corecursive arithmetic on streams.
-/

namespace Computable
namespace CReal
namespace SignedDigit

open scoped BigOperators

/-- Prepend a digit to a signed-digit stream. -/
def cons (d : Digit) (x : SDStream) : SDStream
  | 0     => d
  | n + 1 => x n

/-- Head digit of a signed-digit stream. -/
@[simp] def head (x : SDStream) : Digit := x 0

/-- Tail of a signed-digit stream (drop the head digit). -/
@[simp] def tail (x : SDStream) : SDStream := fun n => x (n + 1)

/-- Scaling by \(1/2\) at the stream level: `x ↦ 0 :: x`. -/
def scaleHalf (x : SDStream) : SDStream := cons Digit.zero x

@[simp] lemma cons_zero (d : Digit) (x : SDStream) : cons d x 0 = d := rfl
@[simp] lemma cons_succ (d : Digit) (x : SDStream) (n : ℕ) : cons d x (n + 1) = x n := rfl

@[simp] lemma coeff_cons_zero (d : Digit) (x : SDStream) :
    coeff (cons d x) 0 = d.toRat * (1/2 : ℚ) := by
  simp [coeff, cons]

@[simp] lemma coeff_cons_succ (d : Digit) (x : SDStream) (n : ℕ) :
    coeff (cons d x) (n + 1) = (1/2 : ℚ) * coeff x n := by
  simp [coeff, cons, pow_succ, mul_assoc, mul_comm]

lemma partialSum_succ (x : SDStream) (n : ℕ) :
    partialSum x (n + 1) = partialSum x n + coeff x (n + 1) := by
  simp [partialSum, Finset.range_add_one, Finset.sum_insert, add_assoc, add_left_comm, add_comm]

lemma partialSum_zero (x : SDStream) : partialSum x 0 = coeff x 0 := by
  simp [partialSum]

lemma partialSum_cons_succ (d : Digit) (x : SDStream) (n : ℕ) :
    partialSum (cons d x) (n + 1) = d.toRat * (1/2 : ℚ) + (1/2 : ℚ) * partialSum x n := by
  -- We prove this by induction on `n`, using the recursion lemma for `partialSum`.
  induction n with
  | zero =>
    -- `partialSum (cons d x) 1 = coeff 0 + coeff 1`
    -- and `coeff 1 = (1/2) * coeff x 0 = (1/2) * partialSum x 0`.
    calc
      partialSum (cons d x) 1
          = partialSum (cons d x) 0 + coeff (cons d x) 1 := by
              simpa using (partialSum_succ (x := cons d x) 0)
      _ = coeff (cons d x) 0 + coeff (cons d x) 1 := by
              simp [partialSum_zero]
      _ = d.toRat * (1/2 : ℚ) + (1/2 : ℚ) * coeff x 0 := by
              simp [coeff_cons_zero, coeff_cons_succ, add_comm]
      _ = d.toRat * (1/2 : ℚ) + (1/2 : ℚ) * partialSum x 0 := by
              simp [partialSum_zero]
  | succ n ih =>
    -- use recursion on both sides and the induction hypothesis
    have h1 :
        partialSum (cons d x) (n + 2) = partialSum (cons d x) (n + 1) + coeff (cons d x) (n + 2) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (partialSum_succ (x := cons d x) (n := n + 1))
    have h2 : partialSum x (n + 1) = partialSum x n + coeff x (n + 1) :=
      partialSum_succ (x := x) n
    -- substitute and finish by ring arithmetic in ℚ
    calc
      partialSum (cons d x) (n + 2)
          = partialSum (cons d x) (n + 1) + coeff (cons d x) (n + 2) := h1
      _ = (d.toRat * (1/2 : ℚ) + (1/2 : ℚ) * partialSum x n)
            + (1/2 : ℚ) * coeff x (n + 1) := by
            -- apply IH and simplify the last coefficient
            simp [ih, coeff_cons_succ]
      _ = d.toRat * (1/2 : ℚ) + (1/2 : ℚ) * (partialSum x n + coeff x (n + 1)) := by ring
      _ = d.toRat * (1/2 : ℚ) + (1/2 : ℚ) * partialSum x (n + 1) := by simp [h2]

lemma toPre_approx_cons_succ (d : Digit) (x : SDStream) (n : ℕ) :
    (toPre (cons d x)).approx (n + 1)
      = d.toRat * (1/2 : ℚ) + (1/2 : ℚ) * (toPre x).approx n := by
  -- unfold `toPre.approx` as `partialSum`
  simp [toPre, partialSum_cons_succ]

lemma toPre_approx_scaleHalf (x : SDStream) (n : ℕ) :
    (toPre (scaleHalf x)).approx (n + 1) = (1/2 : ℚ) * (toPre x).approx n := by
  simpa [scaleHalf] using (toPre_approx_cons_succ (d := Digit.zero) (x := x) (n := n))

end SignedDigit
end CReal
end Computable
