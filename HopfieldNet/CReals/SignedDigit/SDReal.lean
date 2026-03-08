import HopfieldNet.CReals.SignedDigit.Scaled

/-!
# Signed-digit reals with a binary exponent

`SDStream` alone denotes a real in `[-1,1]`. To represent larger magnitudes while keeping a
corecursive stream, we package a **binary exponent**:

`SDReal := (exp : ℤ) × (mant : SDStream)`

denoting \(2^{\mathrm{exp}} \cdot \text{mant}\).

This is a *representation* type: choosing an exponent for a given real is not computable in general,
but once provided, the denotation map is fully constructive.
-/

namespace Computable
namespace CReal
namespace SignedDigit

open scoped BigOperators

structure SDReal where
  exp : ℤ
  mant : SDStream

namespace SDReal

/-- Scale down by `2^k` (constructive, modulus-preserving via index shift). -/
def preScaleDownPow2 (k : ℕ) (x : Computable.CReal.Pre) : Computable.CReal.Pre where
  approx := fun n => ((1 : ℚ) / (2 ^ k)) * x.approx (n + k)
  is_regular := by
    intro n m hnm
    have hnm' : n + k ≤ m + k := Nat.add_le_add_right hnm k
    have hk0 : (0 : ℚ) ≤ (1 : ℚ) / (2 ^ k) := by positivity
    have hx := x.is_regular (n + k) (m + k) hnm'
    have hmul : ((1 : ℚ) / (2 ^ k)) * |x.approx (n + k) - x.approx (m + k)|
        ≤ ((1 : ℚ) / (2 ^ k)) * ((1 : ℚ) / (2 ^ (n + k))) :=
      mul_le_mul_of_nonneg_left hx hk0
    have hcoef :
        ((1 : ℚ) / (2 ^ k)) * ((1 : ℚ) / (2 ^ (n + k))) = (1 : ℚ) / (2 ^ (n + 2 * k)) := by
      have h2 : (2 : ℚ) ≠ 0 := by norm_num
      field_simp [pow_add, h2]
      ring_nf
    have hmono : (1 : ℚ) / (2 ^ (n + 2 * k)) ≤ (1 : ℚ) / (2 ^ n) := by
      have hnpos : (0 : ℚ) < (2 : ℚ) ^ n := by positivity
      have hpow : (2 : ℚ) ^ n ≤ (2 : ℚ) ^ (n + 2 * k) := by
        have hnonneg : (0 : ℚ) ≤ (2 : ℚ) ^ n := by positivity
        have h1 : (1 : ℚ) ≤ (2 : ℚ) ^ (2 * k) := by
          induction (2 * k) with
          | zero =>
            simp
          | succ t ih =>
            have h2 : (1 : ℚ) ≤ (2 : ℚ) := by norm_num
            have : (1 : ℚ) * 1 ≤ (2 : ℚ) ^ t * (2 : ℚ) :=
              mul_le_mul ih h2 (by positivity) (by positivity)
            simpa [pow_succ, mul_assoc] using this
        have : (2 : ℚ) ^ n ≤ (2 : ℚ) ^ n * (2 : ℚ) ^ (2 * k) :=
          le_mul_of_one_le_right hnonneg h1
        simpa [pow_add, add_assoc, add_left_comm, add_comm, mul_assoc] using this
      simpa [one_div] using (one_div_le_one_div_of_le hnpos hpow)
    have hL :
        |((1 : ℚ) / (2 ^ k)) * x.approx (n + k) - ((1 : ℚ) / (2 ^ k)) * x.approx (m + k)|
          = ((1 : ℚ) / (2 ^ k)) * |x.approx (n + k) - x.approx (m + k)| := by
      calc
        |((1 : ℚ) / (2 ^ k)) * x.approx (n + k) - ((1 : ℚ) / (2 ^ k)) * x.approx (m + k)|
            = |((1 : ℚ) / (2 ^ k)) * (x.approx (n + k) - x.approx (m + k))| := by ring_nf
        _ = |(1 : ℚ) / (2 ^ k)| * |x.approx (n + k) - x.approx (m + k)| := by
              simp [abs_mul]
        _ = ((1 : ℚ) / (2 ^ k)) * |x.approx (n + k) - x.approx (m + k)| := by
              simp
    calc
      |((1 : ℚ) / (2 ^ k)) * x.approx (n + k) - ((1 : ℚ) / (2 ^ k)) * x.approx (m + k)|
          = ((1 : ℚ) / (2 ^ k)) * |x.approx (n + k) - x.approx (m + k)| := hL
      _ ≤ ((1 : ℚ) / (2 ^ k)) * ((1 : ℚ) / (2 ^ (n + k))) := hmul
      _ = (1 : ℚ) / (2 ^ (n + 2 * k)) := hcoef
      _ ≤ (1 : ℚ) / (2 ^ n) := hmono

/-- Denotation of an `SDReal` as a `CReal.Pre`. -/
def toPre (x : SDReal) : Computable.CReal.Pre :=
  match x.exp with
  | .ofNat k    => preScalePow2 k (SignedDigit.toPre x.mant)
  | .negSucc k  => preScaleDownPow2 (k + 1) (SignedDigit.toPre x.mant)

/-- Denotation of an `SDReal` as a quotient `CReal`. -/
def toCReal (x : SDReal) : Computable.CReal :=
  ⟦toPre x⟧

/-! ### Basic operations -/

/-- Negation on `SDReal` (mantissa negation, exponent unchanged). -/
def neg (x : SDReal) : SDReal :=
  ⟨x.exp, SignedDigit.negStream x.mant⟩

/-- `toPre` commutes with `SDReal.neg` up to `CReal.Pre.Equiv`. -/
theorem toPre_neg_equiv (x : SDReal) :
    Computable.CReal.Pre.Equiv (toPre (neg x)) (Computable.CReal.Pre.neg (toPre x)) := by
  rcases x with ⟨e, m⟩
  cases e with
  | ofNat k =>
    intro n
    dsimp [neg, SDReal.toPre, preScalePow2, Computable.CReal.Pre.neg, Computable.CReal.Pre.Equiv]
    simp [SignedDigit.toPre_approx_negStream]
  | negSucc k =>
    intro n
    dsimp [neg, SDReal.toPre, SDReal.preScaleDownPow2, Computable.CReal.Pre.neg, Computable.CReal.Pre.Equiv]
    simp [SignedDigit.toPre_approx_negStream]

/-- `toPre` for a nonnegative exponent. -/
@[simp]
lemma toPre_ofNat (k : ℕ) (m : SDStream) :
  toPre ⟨Int.ofNat k, m⟩ = preScalePow2 k (SignedDigit.toPre m) := rfl

/-- `toPre` for a negative exponent. -/
@[simp]
lemma toPre_negSucc (k : ℕ) (m : SDStream) :
  toPre ⟨Int.negSucc k, m⟩ = preScaleDownPow2 (k + 1) (SignedDigit.toPre m) := rfl

/-!
### Representation equivalences

`(exp, mant)` and `(exp+1, scaleHalf mant)` denote the same real, since
`scaleHalf` divides the mantissa by 2.
-/

theorem toPre_shiftUp_scaleHalf_equiv_ofNat (k : ℕ) (m : SDStream) :
    Computable.CReal.Pre.Equiv
      (toPre ⟨Int.ofNat k, m⟩)
      (toPre ⟨Int.ofNat (k + 1), SignedDigit.scaleHalf m⟩) := by
  intro n
  rw [toPre_ofNat (k := k) (m := m)]
  rw [toPre_ofNat (k := k + 1) (m := SignedDigit.scaleHalf m)]
  dsimp [Computable.CReal.Pre.Equiv, preScalePow2]
  have hscale :
      (SignedDigit.toPre (SignedDigit.scaleHalf m)).approx (n + k + 2)
        = (1/2 : ℚ) * (SignedDigit.toPre m).approx (n + k + 1) := by
    simpa [SignedDigit.scaleHalf] using
      (SignedDigit.toPre_approx_scaleHalf (x := m) (n := n + k + 1))
  have hA :
      (2 : ℚ) ^ (k + 1) * (SignedDigit.toPre (SignedDigit.scaleHalf m)).approx (n + k + 2)
        = (2 : ℚ) ^ k * (SignedDigit.toPre m).approx (n + k + 1) := by
    simp [hscale, pow_succ, div_eq_mul_inv, mul_assoc, mul_comm]
    ring_nf
  have : |(2 : ℚ) ^ k * (SignedDigit.toPre m).approx (n + 1 + k) -
            (2 : ℚ) ^ (k + 1) * (SignedDigit.toPre (SignedDigit.scaleHalf m)).approx (n + 1 + (k + 1))|
          = 0 := by
    have hk : n + 1 + k = n + k + 1 := by omega
    have hk' : n + 1 + (k + 1) = n + k + 2 := by omega
    simp [hk, hk', hA]
  simp [this]

theorem toCReal_shiftUp_scaleHalf_ofNat (k : ℕ) (m : SDStream) :
    toCReal ⟨Int.ofNat k, m⟩ = toCReal ⟨Int.ofNat (k + 1), SignedDigit.scaleHalf m⟩ := by
  apply Quotient.sound
  exact toPre_shiftUp_scaleHalf_equiv_ofNat (k := k) (m := m)

end SDReal

end SignedDigit
end CReal
end Computable
