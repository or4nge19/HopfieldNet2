
import HopfieldNet.CReals.CRealExpSmall

namespace Computable
namespace CReal

open scoped BigOperators

/-!
# Exponential (range-reduced skeleton)

This module currently defines the *range-reduced auxiliary* exponential `expAux`
parameterized by explicit range data, together with the basic congruence lemma
when the range selector agrees on the halving exponent `k`.

Constructive range reduction note:

- Turning `expSmall` (defined only for inputs in `[-1/2,1/2]`) into a total `exp` does **not**
  require branching on the sign of `x`. One can choose `k` using an *a priori magnitude bound*
  (e.g. from `cBound`) so that `|x| / 2^k ≤ 1/2`.
- This file does not yet implement such a chooser on the quotient `CReal`. Instead, we keep the
  design maximally explicit by requiring `ExpRangeData x` as an input: a `k` together with a
  bounded representative and a semantic link `small_spec : ⟦small.pre⟧ = x * 2^{-k}`.

The remaining well-definedness lemma across distinct `k` values (`chooser independence`)
requires the functional equation `exp(x) = (exp(x/2))^2` for the bounded exponential,
and is intentionally left to `CRealExpKIndep.lean`.
-/

/-- Range-reduction data for `exp`: a bounded representative of `x / 2^k`. -/
structure ExpRangeData (x : CReal) where
  k : ℕ
  small : ExpSmallInput
  /-- Semantic link: the bounded representative is `x / 2^k` (expressed via multiplication). -/
  -- `CReal` is only a ring at this stage (no `Inv CReal`), so take the inverse in `ℚ`
  -- and cast it into `CReal`.
  small_spec : (⟦small.pre⟧ : CReal) = x * (((((2 : ℚ) ^ k)⁻¹) : ℚ) : CReal)

/-- Range-reduced auxiliary exponential: `exp(x) = exp(x/2^k)^(2^k)`. -/
def expAux (x : CReal) (d : ExpRangeData x) [Pre.SmallExpModulus] : CReal :=
  (expSmall d.small) ^ (2 ^ d.k)

/--
If two range data packages agree on `k` and their bounded representatives agree,
then `expAux` agrees. This is the "same-`k`" half of chooser-independence.
-/
theorem expAux_congr_of_k_eq [Pre.SmallExpModulus]
    (x : CReal) (d₁ d₂ : ExpRangeData x) (hk : d₁.k = d₂.k)
    (hsmall : CReal.Pre.Equiv d₁.small.pre d₂.small.pre) :
    expAux x d₁ = expAux x d₂ := by
  simp [expAux, hk, expSmall_congr hsmall]

end CReal
end Computable
