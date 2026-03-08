import HopfieldNet.CReals.SignedDigit.Basic

/-!
# Signed-digit operations (first corecursive layer)

This file adds basic operations on signed-digit streams and proves that the bridge
`SignedDigit.toPre` respects them (up to the `CReal.Pre` equivalence relation).

Currently implemented:

- corecursive negation on digits/streams
- proof that `toPre (neg x) ≈ (toPre x).neg`
-/

namespace Computable
namespace CReal
namespace SignedDigit

open scoped BigOperators

namespace Digit

/-- Negation of a signed digit. -/
@[simp]
def negate : Digit → Digit
  | .neg  => .pos
  | .zero => .zero
  | .pos  => .neg

@[simp]
lemma toRat_negate (d : Digit) : (Digit.toRat (negate d)) = - d.toRat := by
  cases d <;> rfl

end Digit

/-- Corecursive negation of a signed-digit stream. -/
def negStream (x : SDStream) : SDStream := fun n => Digit.negate (x n)

@[simp]
lemma coeff_negStream (x : SDStream) (i : ℕ) : coeff (negStream x) i = - coeff x i := by
  cases hx : x i <;>
    simp [coeff, negStream, Digit.negate, Digit.toRat, hx, neg_mul]

@[simp]
lemma partialSum_neg (x : SDStream) (n : ℕ) :
    partialSum (negStream x) n = - partialSum x n := by
  simp [partialSum, coeff_negStream, Finset.sum_neg_distrib]

@[simp]
lemma toPre_approx_negStream (x : SDStream) (n : ℕ) :
    (toPre (negStream x)).approx n = - (toPre x).approx n := by
  simp [SignedDigit.toPre, SignedDigit.partialSum]

theorem toPre_neg_equiv (x : SDStream) :
    Computable.CReal.Pre.Equiv (toPre (negStream x)) (Computable.CReal.Pre.neg (toPre x)) := by
  intro n
  dsimp [Computable.CReal.Pre.Equiv, toPre, Computable.CReal.Pre.neg]
  simp [partialSum_neg]

end SignedDigit
end CReal
end Computable
