import HopfieldNet.CReals.CRealCompare

namespace Computable
namespace CReal

namespace Pre

/-!
## Apartness on `CReal.Pre`

For computable (pre-)reals, the constructively meaningful replacement for “deciding equality”
is **apartness**: a positive piece of evidence that two reals are different.

In this development we take “apart” to mean: *there exists a strict separation certificate*
(`CompareCert`), i.e. we can exhibit an index where the rational approximants are separated by
more than the error margin.

This is:
- **sound**: `x # y` implies `Pre.toReal x ≠ Pre.toReal y`;
- **symmetric** and **irreflexive**;
- **complete as an existence statement**: if `Pre.toReal x < Pre.toReal y` then `x # y`
  (via `compareCert_nonempty_of_toReal_lt`).

Crucially, `#` is generally only **semi-decidable**: one can search for a certificate, but
failure to find one does not imply equality.
-/

/-- Apartness: existence of a strict comparison certificate. -/
def Apart (x y : CReal.Pre) : Prop := Nonempty (CompareCert x y)

infix:50 " # " => Apart

theorem apart_iff {x y : CReal.Pre} : x # y ↔ Nonempty (CompareCert x y) := Iff.rfl

/-! We will also use swapping of certificates when lifting to quotients. -/
def CompareCert.swap {x y : CReal.Pre} : CompareCert x y → CompareCert y x
  | .lt i h => .gt i h
  | .gt i h => .lt i h

theorem apart_symm {x y : CReal.Pre} : x # y → y # x
  | ⟨c⟩ => ⟨CompareCert.swap c⟩

theorem not_apart_self (x : CReal.Pre) : ¬ x # x := by
  intro hx
  rcases hx with ⟨c⟩
  have hlt_or : (Pre.toReal x < Pre.toReal x) ∨ (Pre.toReal x < Pre.toReal x) := by
    simpa using (toReal_lt_or_gt_of_cert (x := x) (y := x) c)
  exact lt_irrefl _ (hlt_or.elim id id)

theorem apart_toReal_ne {x y : CReal.Pre} (hxy : x # y) : Pre.toReal x ≠ Pre.toReal y := by
  rcases hxy with ⟨c⟩
  have hlt_or_gt := toReal_lt_or_gt_of_cert (x := x) (y := y) c
  exact (hlt_or_gt.elim (fun hlt => ne_of_lt hlt) (fun hgt => (ne_of_lt hgt).symm))

theorem apart_toReal_lt_or_gt {x y : CReal.Pre} (hxy : x # y) :
    (Pre.toReal x < Pre.toReal y) ∨ (Pre.toReal y < Pre.toReal x) := by
  rcases hxy with ⟨c⟩
  exact toReal_lt_or_gt_of_cert (x := x) (y := y) c

theorem apart_of_toReal_lt {x y : CReal.Pre} (hxy : Pre.toReal x < Pre.toReal y) : x # y :=
  compareCert_nonempty_of_toReal_lt (x := x) (y := y) hxy

theorem apart_of_toReal_gt {x y : CReal.Pre} (hxy : Pre.toReal y < Pre.toReal x) : x # y :=
by
  classical
  rcases compareCert_nonempty_of_toReal_lt (x := y) (y := x) hxy with ⟨c⟩
  exact ⟨CompareCert.swap c⟩

/-!
### Cotransitivity

Apartness should satisfy **cotransitivity**:

If `x # z`, then for any `y` we have `x # y ∨ y # z`.

This is the key “locatedness-style” property that makes apartness usable as a constructive
replacement for decidable inequality: it says that any third point must be apart from at least
one endpoint.
-/

theorem apart_cotrans {x y z : CReal.Pre} (hxz : x # z) : x # y ∨ y # z := by
  have hxz' := apart_toReal_lt_or_gt (x := x) (y := z) hxz
  cases hxz' with
  | inl hxz_lt =>
      -- `toReal x < toReal z`
      by_cases hxy : Pre.toReal x < Pre.toReal y
      · exact Or.inl (apart_of_toReal_lt (x := x) (y := y) hxy)
      · have hyx_le : Pre.toReal y ≤ Pre.toReal x := le_of_not_gt hxy
        have hyz_lt : Pre.toReal y < Pre.toReal z := lt_of_le_of_lt hyx_le hxz_lt
        exact Or.inr (apart_of_toReal_lt (x := y) (y := z) hyz_lt)
  | inr hzx_lt =>
      -- `toReal z < toReal x`
      by_cases hzy : Pre.toReal z < Pre.toReal y
      · -- then `y > z`, so `y # z`
        exact Or.inr (apart_of_toReal_gt (x := y) (y := z) hzy)
      · have hyz_le : Pre.toReal y ≤ Pre.toReal z := le_of_not_gt hzy
        have hyx_lt : Pre.toReal y < Pre.toReal x := lt_of_le_of_lt hyz_le hzx_lt
        exact Or.inl (apart_of_toReal_gt (x := x) (y := y) hyx_lt)

end Pre

/-!
## Apartness on the quotient `CReal`

To use apartness downstream, we also define it on the quotient `CReal`.

The key point is **well-definedness**: apartness is phrased via existence of a strict
separation certificate, which is invariant under `Pre.Equiv` because it is invariant under
equality of denotations in `ℝ` (proved in `CRealRealEquiv.lean`), and strict order on `ℝ`
is itself well-defined.
-/

namespace Pre

theorem apart_respects_equiv {x x' y y' : CReal.Pre}
    (hx : CReal.Pre.Equiv x x') (hy : CReal.Pre.Equiv y y') :
    (x # y) ↔ (x' # y') := by
  have imp :
      x # y → x' # y' := by
        intro hxy
        have hlt_or_gt : (Pre.toReal x < Pre.toReal y) ∨ (Pre.toReal y < Pre.toReal x) :=
          apart_toReal_lt_or_gt (x := x) (y := y) hxy
        have hxR : Pre.toReal x = Pre.toReal x' := Pre.toReal_congr (x := x) (y := x') hx
        have hyR : Pre.toReal y = Pre.toReal y' := Pre.toReal_congr (x := y) (y := y') hy
        cases hlt_or_gt with
        | inl hlt =>
            have : Pre.toReal x' < Pre.toReal y' := by simpa [hxR, hyR] using hlt
            exact apart_of_toReal_lt (x := x') (y := y') this
        | inr hgt =>
            have : Pre.toReal y' < Pre.toReal x' := by simpa [hxR, hyR] using hgt
            exact apart_of_toReal_gt (x := x') (y := y') this
  have imp' :
      x' # y' → x # y := by
        -- same argument with reversed equivalences
        have hx' : CReal.Pre.Equiv x' x := CReal.Pre.equiv_symm hx
        have hy' : CReal.Pre.Equiv y' y := CReal.Pre.equiv_symm hy
        intro hxy'
        -- reuse `imp` with swapped roles
        -- (this is not recursion: we apply the local lemma `imp`)
        have imp_rev :
            x' # y' → x # y := by
              -- copy of `imp` with `hx' hy'`
              intro hxy''
              have hlt_or_gt : (Pre.toReal x' < Pre.toReal y') ∨ (Pre.toReal y' < Pre.toReal x') :=
                apart_toReal_lt_or_gt (x := x') (y := y') hxy''
              have hxR : Pre.toReal x' = Pre.toReal x := Pre.toReal_congr (x := x') (y := x) hx'
              have hyR : Pre.toReal y' = Pre.toReal y := Pre.toReal_congr (x := y') (y := y) hy'
              cases hlt_or_gt with
              | inl hlt =>
                  have : Pre.toReal x < Pre.toReal y := by simpa [hxR, hyR] using hlt
                  exact apart_of_toReal_lt (x := x) (y := y) this
              | inr hgt =>
                  have : Pre.toReal y < Pre.toReal x := by simpa [hxR, hyR] using hgt
                  exact apart_of_toReal_gt (x := x) (y := y) this
        exact imp_rev hxy'
  exact ⟨imp, imp'⟩

end Pre

/-- Apartness on `CReal` induced from representatives (well-defined). -/
def Apart (x y : Computable.CReal) : Prop :=
  Quotient.liftOn₂ x y (fun a b : Computable.CReal.Pre => Pre.Apart a b)
    (by
      -- NOTE: `Quotient.liftOn₂` passes representatives as `(a,b)` and `(a',b')`.
      intro a b a' b' ha hb
      -- `Quotient.liftOn₂` needs proof of Prop-respectfulness.
      apply propext
      exact Pre.apart_respects_equiv (x := a) (x' := a') (y := b) (y' := b') ha hb)

infix:50 " # " => Apart

theorem apart_mk {x y : Computable.CReal.Pre} :
    ((⟦x⟧ : Computable.CReal) # (⟦y⟧ : Computable.CReal)) ↔ (x # y) :=
  Iff.rfl

theorem apart_symm {x y : Computable.CReal} : x # y → y # x := by
  refine Quotient.inductionOn₂ x y (fun a b hab => ?_)
  -- `hab : Pre.Apart a b`
  have : Pre.Apart b a := Pre.apart_symm (x := a) (y := b) hab
  simpa [Apart] using this

theorem not_apart_self (x : Computable.CReal) : ¬ x # x := by
  refine Quotient.inductionOn x ?_
  intro a
  simpa [Apart] using (Pre.not_apart_self a)

theorem apart_toReal_ne {x y : Computable.CReal} (hxy : x # y) :
    _root_.Computable.CReal.toReal x ≠ _root_.Computable.CReal.toReal y := by
  refine Quotient.inductionOn₂ x y (fun a b hab => ?_) hxy
  have hab' : a # b := hab
  have hne : Pre.toReal a ≠ Pre.toReal b := Pre.apart_toReal_ne (x := a) (y := b) hab'
  -- rewrite `toReal` of quotient by `toReal_mk`
  simpa using hne

theorem apart_cotrans {x y z : Computable.CReal} (hxz : x # z) : x # y ∨ y # z := by
  refine Quotient.inductionOn₃ x y z ?_ hxz
  intro a b c hac
  -- reduce to pre-level cotransitivity
  have := Pre.apart_cotrans (x := a) (y := b) (z := c) hac
  simpa [Apart] using this

/-!
## Apartness interaction with `toReal` and algebra

These lemmas turn apartness into a practical constructive inequality notion:

- it implies strict order in `ℝ` (one direction or the other),
- and it is stable under the ring operations (e.g. translation, negation).
-/

theorem apart_toReal_lt_or_gt {x y : Computable.CReal} (hxy : x # y) :
    (toReal x < toReal y) ∨ (toReal y < toReal x) := by
  refine Quotient.inductionOn₂ x y (fun a b hab => ?_) hxy
  -- `hab : Pre.Apart a b`, i.e. `a # b`
  have := Pre.apart_toReal_lt_or_gt (x := a) (y := b) hab
  simpa using this

theorem apart_of_toReal_lt {x y : Computable.CReal} (hxy : toReal x < toReal y) : x # y := by
  refine Quotient.inductionOn₂ x y (fun a b hab => ?_) hxy
  -- reduce to the pre-level statement and rewrap as quotient apartness
  have hab' : Pre.toReal a < Pre.toReal b := by simpa [toReal_mk] using hab
  -- `Pre.toReal a < Pre.toReal b` implies `a # b`
  exact Pre.apart_of_toReal_lt (x := a) (y := b) hab'

theorem apart_of_toReal_gt {x y : Computable.CReal} (hxy : toReal y < toReal x) : x # y :=
  apart_symm (x := y) (y := x) (apart_of_toReal_lt (x := y) (y := x) hxy)

theorem apart_add_right {x y z : Computable.CReal} (hxy : x # y) : (x + z) # (y + z) := by
  have h := apart_toReal_lt_or_gt (x := x) (y := y) hxy
  cases h with
  | inl hlt =>
      have : toReal (x + z) < toReal (y + z) := by
        -- add the same real to both sides and rewrite via `toReal_add`
        simpa [toReal_add] using (add_lt_add_right hlt (toReal z))
      exact apart_of_toReal_lt (x := x + z) (y := y + z) this
  | inr hgt =>
      have : toReal (y + z) < toReal (x + z) := by
        simpa [toReal_add] using (add_lt_add_right hgt (toReal z))
      exact apart_of_toReal_gt (x := x + z) (y := y + z) this

theorem apart_add_left {x y z : Computable.CReal} (hxy : x # y) : (z + x) # (z + y) := by
  -- commutativity reduces to `apart_add_right`
  simpa [add_comm, add_left_comm, add_assoc] using (apart_add_right (x := x) (y := y) (z := z) hxy)

theorem apart_neg {x y : Computable.CReal} (hxy : x # y) : (-x) # (-y) := by
  have h := apart_toReal_lt_or_gt (x := x) (y := y) hxy
  cases h with
  | inl hlt =>
      -- `x < y` implies `-y < -x`
      have : toReal (-y) < toReal (-x) := by
        simpa [toReal_neg] using (neg_lt_neg hlt)
      -- hence `-x # -y`
      exact apart_symm (x := -y) (y := -x) (apart_of_toReal_lt (x := -y) (y := -x) this)
  | inr hgt =>
      have : toReal (-x) < toReal (-y) := by
        simpa [toReal_neg] using (neg_lt_neg hgt)
      exact apart_of_toReal_lt (x := -x) (y := -y) this

theorem apart_sub_right {x y z : Computable.CReal} (hxy : x # y) : (x - z) # (y - z) := by
  -- `x - z = x + (-z)`
  simpa [sub_eq_add_neg] using (apart_add_right (x := x) (y := y) (z := -z) hxy)

/-!
### Multiplicative compatibility (with a sign hypothesis)

Multiplication preserves strict order in `ℝ` only under a sign hypothesis on the multiplier.
Accordingly, we provide the standard apartness compatibility lemmas assuming `toReal z > 0`
or `toReal z < 0`.

These are the lemmas you want for constructive algebraic reasoning:
they do **not** claim that multiplication by an arbitrary (possibly zero) real preserves apartness.
-/

theorem apart_mul_right_of_pos {x y z : Computable.CReal} (hz : 0 < toReal z) (hxy : x # y) :
    (x * z) # (y * z) := by
  have h := apart_toReal_lt_or_gt (x := x) (y := y) hxy
  cases h with
  | inl hlt =>
      have : toReal (x * z) < toReal (y * z) := by
        -- multiply the inequality by a positive real and rewrite via `toReal_mul`
        simpa [toReal_mul] using (mul_lt_mul_of_pos_right hlt hz)
      exact apart_of_toReal_lt (x := x * z) (y := y * z) this
  | inr hgt =>
      have : toReal (y * z) < toReal (x * z) := by
        simpa [toReal_mul] using (mul_lt_mul_of_pos_right hgt hz)
      exact apart_of_toReal_gt (x := x * z) (y := y * z) this

theorem apart_mul_right_of_neg {x y z : Computable.CReal} (hz : toReal z < 0) (hxy : x # y) :
    (x * z) # (y * z) := by
  have h := apart_toReal_lt_or_gt (x := x) (y := y) hxy
  cases h with
  | inl hlt =>
      -- `x < y` and `z < 0` implies `y*z < x*z`
      have : toReal (y * z) < toReal (x * z) := by
        simpa [toReal_mul] using (mul_lt_mul_of_neg_right hlt hz)
      exact apart_of_toReal_gt (x := x * z) (y := y * z) this
  | inr hgt =>
      have : toReal (x * z) < toReal (y * z) := by
        simpa [toReal_mul] using (mul_lt_mul_of_neg_right hgt hz)
      exact apart_of_toReal_lt (x := x * z) (y := y * z) this

theorem apart_mul_left_of_pos {x y z : Computable.CReal} (hz : 0 < toReal z) (hxy : x # y) :
    (z * x) # (z * y) := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using (apart_mul_right_of_pos (x := x) (y := y) (z := z) hz hxy)

theorem apart_mul_left_of_neg {x y z : Computable.CReal} (hz : toReal z < 0) (hxy : x # y) :
    (z * x) # (z * y) := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using (apart_mul_right_of_neg (x := x) (y := y) (z := z) hz hxy)

end CReal
end Computable

