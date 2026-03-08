import HopfieldNet.CReals.CRealPre2
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Signed-digit corecursive reals (spec-level)

This module introduces a **signed-digit stream** representation as a *specification* layer,
meant to complement (not replace) `Computable.CReal.Pre` (regular Cauchy sequences).

We represent a real in \([-1,1]\) by an infinite stream of digits `{-1,0,+1}` interpreted as:

\[
x = \sum_{i=0}^\infty d_i \cdot 2^{-(i+1)}.
\]

The main result here is a fully constructive embedding:

- `Computable.CReal.SignedDigit.toPre` : `SDStream → CReal.Pre`

so we can always view a signed-digit stream as a `Computable.CReal` by quotienting.
-/

namespace Computable
namespace CReal
namespace SignedDigit

open scoped BigOperators

/-- A signed digit in `{-1,0,+1}`. -/
inductive Digit
  | neg
  | zero
  | pos
deriving DecidableEq, Repr

/-- Interpretation of a digit as a rational. -/
@[simp] def Digit.toRat : Digit → ℚ
  | .neg  => -1
  | .zero => 0
  | .pos  => 1

@[simp] lemma Digit.abs_toRat_le_one (d : Digit) : |d.toRat| ≤ (1 : ℚ) := by
  cases d <;> norm_num

/-- Corecursive signed-digit stream. -/
abbrev SDStream : Type := ℕ → Digit

/-- Coefficient at position `i`: `dᵢ * (1/2)^(i+1)`. -/
def coeff (x : SDStream) (i : ℕ) : ℚ :=
  (x i).toRat * (1/2 : ℚ) ^ (i + 1)

lemma abs_coeff_le (x : SDStream) (i : ℕ) : |coeff x i| ≤ (1/2 : ℚ) ^ (i + 1) := by
  have hdig : |(x i).toRat| ≤ (1 : ℚ) := Digit.abs_toRat_le_one (x i)
  have hpow : 0 ≤ (1/2 : ℚ) ^ (i + 1) := by positivity
  calc
    |coeff x i|
        = |(x i).toRat| * |(1/2 : ℚ) ^ (i + 1)| := by
            simp [coeff, abs_mul]
    _ = |(x i).toRat| * (1/2 : ℚ) ^ (i + 1) := by
            simp
    _ ≤ (1 : ℚ) * (1/2 : ℚ) ^ (i + 1) := by
            gcongr
    _ = (1/2 : ℚ) ^ (i + 1) := by simp

/-- Partial sum up to precision `n`: `∑_{i=0..n} dᵢ 2^{-(i+1)}`. -/
def partialSum (x : SDStream) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1), coeff x i

/--
Interpret a signed-digit stream as a `CReal.Pre` by taking partial sums.

Regularity proof: the difference of two partial sums is a tail sum over an `Ico`,
bounded by a geometric tail using `Mathlib.Algebra.Order.Field.GeomSum`.
-/
def toPre (x : SDStream) : Computable.CReal.Pre where
  approx := partialSum x
  is_regular := by
    intro n m hnm
    have hN : n + 1 ≤ m + 1 := Nat.succ_le_succ hnm
    -- rewrite the difference as an `Ico` tail sum
    have hsub :
        (∑ i ∈ Finset.range (m + 1), coeff x i) -
          (∑ i ∈ Finset.range (n + 1), coeff x i)
          =
        ∑ i ∈ Finset.Ico (n + 1) (m + 1), coeff x i := by
      simpa using (Finset.sum_Ico_eq_sub (f := fun i => coeff x i) hN).symm
    have habs :
        |(∑ i ∈ Finset.range (n + 1), coeff x i) -
            (∑ i ∈ Finset.range (m + 1), coeff x i)|
          =
        |∑ i ∈ Finset.Ico (n + 1) (m + 1), coeff x i| := by
      rw [abs_sub_comm]
      simp [hsub]
    -- bound by the sum of absolute values, then dominate by a geometric tail
    have hgeom :
        (∑ i ∈ Finset.Ico (n + 1) (m + 1), (1/2 : ℚ) ^ (i + 1))
          ≤ (1/2 : ℚ) ^ (n + 1) := by
      have hx0 : (0 : ℚ) ≤ (1/2 : ℚ) := by norm_num
      have hx1 : (1/2 : ℚ) < 1 := by norm_num
      -- geometric bound on `∑ (1/2)^i`, then multiply by `1/2` to get exponent `i+1`
      have hbase :
          (∑ i ∈ Finset.Ico (n + 1) (m + 1), (1/2 : ℚ) ^ i)
            ≤ (1/2 : ℚ) ^ (n + 1) / (1 - (1/2 : ℚ)) := by
        -- standard tail estimate
        simpa using
          (geom_sum_Ico_le_of_lt_one (K := ℚ) (m := n + 1) (n := m + 1) hx0 hx1)
      have hden : (1 - (1/2 : ℚ)) = (1/2 : ℚ) := by norm_num
      have hmul :
          (∑ i ∈ Finset.Ico (n + 1) (m + 1), (1/2 : ℚ) ^ (i + 1))
            =
          (1/2 : ℚ) * (∑ i ∈ Finset.Ico (n + 1) (m + 1), (1/2 : ℚ) ^ i) := by
        -- `(1/2)^(i+1) = (1/2) * (1/2)^i`
        simp [pow_succ, mul_comm, Finset.mul_sum]
      calc
        (∑ i ∈ Finset.Ico (n + 1) (m + 1), (1/2 : ℚ) ^ (i + 1))
            = (1/2 : ℚ) * (∑ i ∈ Finset.Ico (n + 1) (m + 1), (1/2 : ℚ) ^ i) := hmul
        _ ≤ (1/2 : ℚ) * ((1/2 : ℚ) ^ (n + 1) / (1 - (1/2 : ℚ))) := by
              gcongr
        _ = (1/2 : ℚ) ^ (n + 1) := by
              -- divide by `1-1/2 = 1/2` cancels the leading `1/2`
              have hden : (1 - (1/2 : ℚ)) = (1/2 : ℚ) := by norm_num
              have hhalf : (1/2 : ℚ) ≠ 0 := by norm_num
              rw [hden]
              field_simp [hhalf]
    have hgeom' : (1/2 : ℚ) ^ (n + 1) ≤ (1/2 : ℚ) ^ n := by
      -- powers are antitone for `0 ≤ x ≤ 1`
      have hx0 : (0 : ℚ) ≤ (1/2 : ℚ) := by norm_num
      have hx1 : (1/2 : ℚ) ≤ 1 := by norm_num
      exact pow_le_pow_of_le_one hx0 hx1 (Nat.le_succ n)
    calc
      |(∑ i ∈ Finset.range (n + 1), coeff x i) -
          (∑ i ∈ Finset.range (m + 1), coeff x i)|
          = |∑ i ∈ Finset.Ico (n + 1) (m + 1), coeff x i| := habs
      _ ≤ ∑ i ∈ Finset.Ico (n + 1) (m + 1), |coeff x i| := by
            simpa using
              (Finset.abs_sum_le_sum_abs (s := Finset.Ico (n + 1) (m + 1)) (f := fun i => coeff x i))
      _ ≤ ∑ i ∈ Finset.Ico (n + 1) (m + 1), (1/2 : ℚ) ^ (i + 1) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact abs_coeff_le x i
      _ ≤ (1/2 : ℚ) ^ (n + 1) := hgeom
      _ ≤ (1/2 : ℚ) ^ n := hgeom'
      _ = (1 : ℚ) / (2 ^ n) := by
            -- `(1/2)^n = 1/2^n`
            simp [div_eq_mul_inv]

/-- Signed-digit stream interpreted as a quotient `CReal`. -/
def toCReal (x : SDStream) : Computable.CReal :=
  ⟦toPre x⟧

end SignedDigit
end CReal
end Computable

