import HopfieldNet.CReals.SignedDigit.Shift

/-!
# Power-of-two scaling for signed-digit streams

Our base signed-digit stream `SDStream := ℕ → Digit` denotes a number in `[-1,1]` via

\[
x = \sum_{i=0}^{\infty} d_i 2^{-(i+1)}.
\]

To represent **unbounded** reals while keeping the stream corecursive, we add a *binary exponent*.

This file implements the simplest, fully constructive scaling operation: multiplying by a power of two.

Key idea:

If `aₙ` is a `CReal.Pre` approximation with error `≤ 2^{-(n+k)}`, then `2^k * a_{n+k}` has error
`≤ 2^k * 2^{-(n+k)} = 2^{-n}` and so is again a valid `CReal.Pre`.
-/

namespace Computable
namespace CReal
namespace SignedDigit

open scoped BigOperators

/-- Multiply a `CReal.Pre` by a power of two, preserving the fixed modulus by shifting the index. -/
def preScalePow2 (k : ℕ) (x : Computable.CReal.Pre) : Computable.CReal.Pre where
  approx := fun n => (2 : ℚ) ^ k * x.approx (n + k)
  is_regular := by
    intro n m hnm
    have hnm' : n + k ≤ m + k := Nat.add_le_add_right hnm k
    have hk0 : (0 : ℚ) ≤ (2 : ℚ) ^ k := by positivity
    -- start from regularity of `x` at shifted indices
    have hx := x.is_regular (n + k) (m + k) hnm'
    -- rewrite the LHS as `|(2^k) * (a - b)|`
    have hL :
        |(2 : ℚ) ^ k * x.approx (n + k) - (2 : ℚ) ^ k * x.approx (m + k)|
          = (2 : ℚ) ^ k * |x.approx (n + k) - x.approx (m + k)| := by
      calc
        |(2 : ℚ) ^ k * x.approx (n + k) - (2 : ℚ) ^ k * x.approx (m + k)|
            = |(2 : ℚ) ^ k * (x.approx (n + k) - x.approx (m + k))| := by ring_nf
        _ = |(2 : ℚ) ^ k| * |x.approx (n + k) - x.approx (m + k)| := by
              simp [abs_mul]
        _ = (2 : ℚ) ^ k * |x.approx (n + k) - x.approx (m + k)| := by
              simp [abs_of_nonneg hk0]
    -- simplify the RHS scalar factor
    have hR :
        (2 : ℚ) ^ k * ((1 : ℚ) / (2 ^ (n + k))) = (1 : ℚ) / (2 ^ n) := by
      have h2 : (2 : ℚ) ≠ 0 := by norm_num
      -- clear denominators
      -- (`ring_nf` is more robust than `ring` after `field_simp`)
      field_simp [pow_add, h2]
      ring_nf
    -- assemble via a `calc` chain (avoids simp-heuristics on inequalities)
    have hmul :
        (2 : ℚ) ^ k * |x.approx (n + k) - x.approx (m + k)|
          ≤ (2 : ℚ) ^ k * ((1 : ℚ) / (2 ^ (n + k))) :=
      mul_le_mul_of_nonneg_left hx hk0
    calc
      |(2 : ℚ) ^ k * x.approx (n + k) - (2 : ℚ) ^ k * x.approx (m + k)|
          = (2 : ℚ) ^ k * |x.approx (n + k) - x.approx (m + k)| := hL
      _ ≤ (2 : ℚ) ^ k * ((1 : ℚ) / (2 ^ (n + k))) := hmul
      _ = (1 : ℚ) / (2 ^ n) := hR

/-- Scale a signed-digit stream by `2^k`, viewed as a `CReal.Pre`. -/
def toPreScaled (k : ℕ) (x : SDStream) : Computable.CReal.Pre :=
  preScalePow2 k (toPre x)

/-- Scale a signed-digit stream by `2^k`, viewed as a quotient `CReal`. -/
def toCRealScaled (k : ℕ) (x : SDStream) : Computable.CReal :=
  ⟦toPreScaled k x⟧

end SignedDigit
end CReal
end Computable

