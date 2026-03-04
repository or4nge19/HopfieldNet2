import HopfieldNet.CReals.CRealCCLOF
import HopfieldNet.CReals.CRealRep
import HopfieldNet.CReals.CRealRealEquiv

namespace Computable
namespace CReal

namespace Pre

/-- Separation certificate for strict comparison of two pre-reals. -/
inductive CompareCert (x y : CReal.Pre) : Type
  | lt (i : Nat) (h : x.approx (i + 1) + (1 : ℚ) / (2 ^ (i + 1)) <
      y.approx (i + 1) - (1 : ℚ) / (2 ^ (i + 1)))
  | gt (i : Nat) (h : y.approx (i + 1) + (1 : ℚ) / (2 ^ (i + 1)) <
      x.approx (i + 1) - (1 : ℚ) / (2 ^ (i + 1)))

/-!
## Semi-decision for strict order (and inequality)

The key point is that **total** decision procedures for real equality/order are not computable
in general. What we *can* do is give **sound partial procedures**:

- `compareWitness x y fuel : Option (CompareCert x y)` attempts to find a rational separation.
- If it returns `.lt …` or `.gt …`, we get a corresponding strict inequality in `ℝ`.
- If it returns `none`, we make **no claim** (this happens when `x` and `y` are equal, or are
  too close to separate within the given fuel, or when computation doesn’t reduce enough).

For “equality”, the meaningful computational notion is often **apartness** (`x ≠ y`), which is
also only semi-decidable: a separation witness implies `x ≠ y`, but failure to find a witness
does not imply equality.
-/

/-- Internal loop producing a `CompareCert` when interval separation succeeds. -/
private def compareLoop (x y : CReal.Pre) : Nat → Nat → Option (CompareCert x y)
  | _, 0 => none
  | i, fuel + 1 =>
      let δ : ℚ := (1 : ℚ) / (2 ^ (i + 1))
      if hlt : x.approx (i + 1) + δ < y.approx (i + 1) - δ then
        some (.lt i (by simpa [δ] using hlt))
      else if hgt : y.approx (i + 1) + δ < x.approx (i + 1) - δ then
        some (.gt i (by simpa [δ] using hgt))
      else
        compareLoop x y (i + 1) fuel

/--
Semi-decision procedure for strict comparison of pre-reals.

If it returns a certificate, the corresponding strict inequality holds on denotations in `ℝ`.
-/
def compareWitness (x y : CReal.Pre) (fuel : Nat := 100) : Option (CompareCert x y) :=
  compareLoop x y 0 (fuel + 1)

/-- A lightweight wrapper: return `.lt`/`.gt` as an `Ordering` when separable. -/
def compare? (x y : CReal.Pre) (fuel : Nat := 100) : Option Ordering :=
  match compareWitness x y fuel with
  | some (.lt _ _) => some Ordering.lt
  | some (.gt _ _) => some Ordering.gt
  | none => none

/-!
## Partial inversion: extracting an `InvWitness` from a separation certificate

Constructively, inversion is only defined when we have evidence that `x` is separated from `0`.
In this library that evidence is packaged as `CReal.Pre.InvWitness x` (see
`CRealPre2/InvTranscendental.lean`).

The strict-comparison certificate `CompareCert x 0` is strong enough to produce such a witness:
it exhibits an index at which the rational approximant is bounded away from `0` by a dyadic
margin. This gives a convenient, **sound, fuel-bounded** way to attempt to invert a pre-real.
-/

private lemma two_mul_inv_pow_succ (i : ℕ) :
    (2 : ℚ) * ((1 : ℚ) / (2 ^ (i + 1))) = (1 : ℚ) / (2 ^ i) := by
  -- `2^(i+1) = 2^i * 2`
  field_simp [pow_succ]
  ring

/-- Convert a strict separation certificate against `0` into an inverse witness. -/
def invWitness_of_compareCert_zero (x : CReal.Pre) :
    CompareCert x CReal.Pre.zero → CReal.Pre.InvWitness x
  | .lt i h =>
      -- `x.approx (i+1) + δ < -δ` ⇒ `x.approx (i+1) < -2δ` ⇒ `|x.approx (i+1)| > 2δ = 2^{-i}`
      let δ : ℚ := (1 : ℚ) / (2 ^ (i + 1))
      have h' : x.approx (i + 1) + δ < -δ := by
        simpa [CReal.Pre.zero, δ] using h
      have hlt : x.approx (i + 1) < -(2 : ℚ) * δ := by
        linarith
      have hδpos : 0 < δ := by
        -- `δ = 2^{-(i+1)} > 0`
        have : (0 : ℚ) < (2 : ℚ) ^ (i + 1) := pow_pos (by norm_num) _
        exact div_pos (by norm_num) this
      have h2δ : (2 : ℚ) * δ = (1 : ℚ) / (2 ^ i) := by
        simpa [δ] using two_mul_inv_pow_succ i
      have hle0 : x.approx (i + 1) ≤ 0 := by
        have : -(2 : ℚ) * δ < 0 := by nlinarith
        exact le_of_lt (lt_trans hlt this)
      have habs : |x.approx (i + 1)| = -(x.approx (i + 1)) := abs_of_nonpos hle0
      have hpos : (2 : ℚ) * δ < -(x.approx (i + 1)) := by
        nlinarith
      have hpow : (1 : ℚ) / (2 ^ i) < |x.approx (i + 1)| := by
        -- rewrite `2*δ` as `2^{-i}` and use `|a| = -a`
        have : (1 : ℚ) / (2 ^ i) < -(x.approx (i + 1)) := by
          simpa [h2δ] using hpos
        simpa [habs] using this
      ⟨i, by simpa using hpow⟩
  | .gt i h =>
      -- `δ < x.approx (i+1) - δ` ⇒ `2δ < x.approx (i+1)` ⇒ `|x.approx (i+1)| > 2δ = 2^{-i}`
      let δ : ℚ := (1 : ℚ) / (2 ^ (i + 1))
      have h' : δ < x.approx (i + 1) - δ := by
        simpa [CReal.Pre.zero, δ] using h
      have hgt : (2 : ℚ) * δ < x.approx (i + 1) := by
        linarith
      have h2δ : (2 : ℚ) * δ = (1 : ℚ) / (2 ^ i) := by
        simpa [δ] using two_mul_inv_pow_succ i
      have habs : |x.approx (i + 1)| = x.approx (i + 1) := by
        have hδpos : 0 < δ := by
          have : (0 : ℚ) < (2 : ℚ) ^ (i + 1) := pow_pos (by norm_num) _
          exact div_pos (by norm_num) this
        have h2δpos : (0 : ℚ) < (2 : ℚ) * δ := by nlinarith [hδpos]
        have hxpos : 0 < x.approx (i + 1) := lt_trans h2δpos hgt
        exact abs_of_pos hxpos
      have hpow : (1 : ℚ) / (2 ^ i) < |x.approx (i + 1)| := by
        -- rewrite `2*δ` as `2^{-i}` and use `|a| = a`
        have : (1 : ℚ) / (2 ^ i) < x.approx (i + 1) := by
          simpa [h2δ] using hgt
        simpa [habs] using this
      ⟨i, by simpa using hpow⟩

/--
Fuel-bounded attempt to construct an inverse witness.

If it returns `some W`, then `W` certifies that `x` is separated from `0`, hence one may form
`CReal.Pre.inv x W`. If it returns `none`, no conclusion is drawn.
-/
def invWitness? (x : CReal.Pre) (fuel : Nat := 100) : Option (CReal.Pre.InvWitness x) :=
  match compareWitness x CReal.Pre.zero fuel with
  | some c => some (invWitness_of_compareCert_zero x c)
  | none => none

theorem toReal_lt_of_sep {x y : CReal.Pre} (i : Nat)
    (h : x.approx (i + 1) + (1 : ℚ) / (2 ^ (i + 1)) <
      y.approx (i + 1) - (1 : ℚ) / (2 ^ (i + 1))) :
    Pre.toReal x < Pre.toReal y := by
      let δQ : ℚ := (1 : ℚ) / (2 ^ (i + 1))
      let δR : ℝ := (δQ : ℝ)
      have hx : |Pre.toReal x - (x.approx (i + 1) : ℝ)| ≤ δR := by
        simpa [δR, δQ] using (abs_toReal_sub_approx_le x i)
      have hy : |Pre.toReal y - (y.approx (i + 1) : ℝ)| ≤ δR := by
        simpa [δR, δQ] using (abs_toReal_sub_approx_le y i)
      have hx' := (abs_sub_le_iff).1 hx
      have hy' := (abs_sub_le_iff).1 hy
      have hx_up : Pre.toReal x ≤ (x.approx (i + 1) : ℝ) + δR := by
        linarith [hx'.2]
      have hy_low : (y.approx (i + 1) : ℝ) - δR ≤ Pre.toReal y := by
        linarith [hy'.1]
      have hsep : (x.approx (i + 1) : ℝ) + δR < (y.approx (i + 1) : ℝ) - δR := by
        have : ((x.approx (i + 1) : ℚ) + δQ) < ((y.approx (i + 1) : ℚ) - δQ) := by
          simpa [δQ] using h
        have : ((x.approx (i + 1) : ℚ) : ℝ) + (δQ : ℝ) < ((y.approx (i + 1) : ℚ) : ℝ) - (δQ : ℝ) := by
          exact_mod_cast this
        simpa [δR] using this
      exact lt_of_le_of_lt hx_up (lt_of_lt_of_le hsep hy_low)

theorem toReal_gt_of_sep {x y : CReal.Pre} (i : Nat)
    (h : y.approx (i + 1) + (1 : ℚ) / (2 ^ (i + 1)) <
      x.approx (i + 1) - (1 : ℚ) / (2 ^ (i + 1))) :
    Pre.toReal y < Pre.toReal x := by
      -- symmetric to the `.lt` case
      let δQ : ℚ := (1 : ℚ) / (2 ^ (i + 1))
      let δR : ℝ := (δQ : ℝ)
      have hy : |Pre.toReal y - (y.approx (i + 1) : ℝ)| ≤ δR := by
        simpa [δR, δQ] using (abs_toReal_sub_approx_le y i)
      have hx : |Pre.toReal x - (x.approx (i + 1) : ℝ)| ≤ δR := by
        simpa [δR, δQ] using (abs_toReal_sub_approx_le x i)
      have hy' := (abs_sub_le_iff).1 hy
      have hx' := (abs_sub_le_iff).1 hx
      have hy_up : Pre.toReal y ≤ (y.approx (i + 1) : ℝ) + δR := by
        linarith [hy'.2]
      have hx_low : (x.approx (i + 1) : ℝ) - δR ≤ Pre.toReal x := by
        linarith [hx'.1]
      have hsep : (y.approx (i + 1) : ℝ) + δR < (x.approx (i + 1) : ℝ) - δR := by
        have : ((y.approx (i + 1) : ℚ) + δQ) < ((x.approx (i + 1) : ℚ) - δQ) := by
          simpa [δQ] using h
        have : ((y.approx (i + 1) : ℚ) : ℝ) + (δQ : ℝ) < ((x.approx (i + 1) : ℚ) : ℝ) - (δQ : ℝ) := by
          exact_mod_cast this
        simpa [δR] using this
      exact lt_of_le_of_lt hy_up (lt_of_lt_of_le hsep hx_low)

/-- Semi-decision of inequality (apartness): returns `some` only when a strict separation is found. -/
def apart? (x y : CReal.Pre) (fuel : Nat := 100) : Option (PLift (Pre.toReal x ≠ Pre.toReal y)) :=
  match compareWitness x y fuel with
  | some (.lt i h) =>
      some ⟨by
        have hlt : Pre.toReal x < Pre.toReal y := toReal_lt_of_sep (x := x) (y := y) i h
        exact ne_of_lt hlt⟩
  | some (.gt i h) =>
      some ⟨by
        have hgt : Pre.toReal y < Pre.toReal x := toReal_gt_of_sep (x := x) (y := y) i h
        exact (ne_of_lt hgt).symm⟩
  | none => none

/-!
## Completeness (mathematical, not computable)

The procedures above are *sound*: if they return a certificate, the corresponding strict
inequality holds in `ℝ`. For “full rigour” it is also useful to know a **completeness** fact:

If `Pre.toReal x < Pre.toReal y`, then there exists some index `i` at which the rational
approximants are separated, hence `compareWitness` will succeed given enough fuel.

This is a classical existence statement (it uses that `ℚ` is dense in `ℝ` and that the
approximants converge).
-/

theorem exists_sep_of_toReal_lt {x y : CReal.Pre} (hxy : Pre.toReal x < Pre.toReal y) :
    ∃ i : Nat,
      x.approx (i + 1) + (1 : ℚ) / (2 ^ (i + 1)) <
        y.approx (i + 1) - (1 : ℚ) / (2 ^ (i + 1)) := by
  -- Let `gap = (toReal y - toReal x) / 4 > 0`, pick a rational `ε` with `0 < ε < gap`,
  -- then choose `i` so that `2^{-(i+1)} ≤ ε`, and use the approximation bounds.
  have hgap_pos : (0 : ℝ) < (Pre.toReal y - Pre.toReal x) / 4 := by
    have : (0 : ℝ) < Pre.toReal y - Pre.toReal x := sub_pos.mpr hxy
    nlinarith
  obtain ⟨εq, hεq0, hεq⟩ :
      ∃ εq : ℚ, (0 : ℝ) < (εq : ℝ) ∧ (εq : ℝ) < (Pre.toReal y - Pre.toReal x) / 4 := by
    -- density of ℚ in ℝ
    rcases exists_rat_btwn hgap_pos with ⟨εq, hεq⟩
    refine ⟨εq, ?_, ?_⟩
    · have : (0 : ℝ) < (εq : ℝ) := by linarith [hεq.1]
      simpa using this
    · exact hεq.2
  have hεq0' : (0 : ℚ) < εq := by
    -- `0 < (εq : ℝ)` implies `0 < εq`
    exact_mod_cast hεq0
  -- Choose `K` such that `(1/2) / 2^K = 1 / 2^(K+1) < εq`.
  obtain ⟨K, hK⟩ := find_index_for_bound (B := (1/2 : ℚ)) (ε := εq) (by norm_num) hεq0'
  let i : Nat := K
  refine ⟨i, ?_⟩
  -- set δ = 2^{-(i+1)}
  let δq : ℚ := (1 : ℚ) / (2 ^ (i + 1))
  let δr : ℝ := (δq : ℝ)
  have hδ_lt : δr < (Pre.toReal y - Pre.toReal x) / 4 := by
    have hδ_lt_ε : δr < (εq : ℝ) := by
      -- `hK : (1/2)/2^K < εq` (in ℚ), rewrite as `1/2^(K+1) < εq`.
      have hδq : δq < εq := by
        -- `(1/2)/2^K = 1/2^(K+1)`
        -- (keep the goal in `ℚ`, then cast)
        simpa [δq, i, div_eq_mul_inv, pow_succ, mul_assoc] using hK
      have : (δq : ℝ) < (εq : ℝ) := by exact_mod_cast hδq
      simpa [δr] using this
    exact lt_trans hδ_lt_ε hεq
  have hx : |Pre.toReal x - (x.approx (i + 1) : ℝ)| ≤ δr := by
    simpa [δq, δr] using (abs_toReal_sub_approx_le x i)
  have hy : |Pre.toReal y - (y.approx (i + 1) : ℝ)| ≤ δr := by
    simpa [δq, δr] using (abs_toReal_sub_approx_le y i)
  have hx' := (abs_sub_le_iff).1 hx
  have hy' := (abs_sub_le_iff).1 hy
  have hx_up : (x.approx (i + 1) : ℝ) ≤ Pre.toReal x + δr := by
    linarith [hx'.2]
  have hy_low : Pre.toReal y - δr ≤ (y.approx (i + 1) : ℝ) := by
    linarith [hy'.1]
  have hgap4 : Pre.toReal x + 4 * δr < Pre.toReal y := by
    -- from `δr < (toReal y - toReal x)/4`
    have : 4 * δr < Pre.toReal y - Pre.toReal x := by nlinarith [hδ_lt]
    linarith
  have hsepR : (x.approx (i + 1) : ℝ) + δr < (y.approx (i + 1) : ℝ) - δr := by
    -- bound LHS by `toReal x + 2δ`, RHS by `toReal y - 2δ`
    have hx2 : (x.approx (i + 1) : ℝ) + δr ≤ Pre.toReal x + 2 * δr := by
      linarith [hx_up]
    have hy2 : Pre.toReal y - 2 * δr ≤ (y.approx (i + 1) : ℝ) - δr := by
      linarith [hy_low]
    have hmid : Pre.toReal x + 2 * δr < Pre.toReal y - 2 * δr := by
      -- rearrange `toReal x + 4δ < toReal y`
      linarith [hgap4]
    exact lt_of_le_of_lt hx2 (lt_of_lt_of_le hmid hy2)
  -- Cast back to ℚ using the order embedding `ℚ ↪ ℝ`.
  have hsepR' :
      ((x.approx (i + 1) + δq : ℚ) : ℝ) < ((y.approx (i + 1) - δq : ℚ) : ℝ) := by
    -- `δr` is just the cast of `δq`.
    simpa [δr, δq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsepR
  have hsepQ : x.approx (i + 1) + δq < y.approx (i + 1) - δq := by
    exact_mod_cast hsepR'
  simpa [δq] using hsepQ

theorem compareCert_nonempty_of_toReal_lt {x y : CReal.Pre} (hxy : Pre.toReal x < Pre.toReal y) :
    Nonempty (CompareCert x y) := by
  rcases exists_sep_of_toReal_lt (x := x) (y := y) hxy with ⟨i, hi⟩
  exact ⟨CompareCert.lt i hi⟩

theorem toReal_lt_or_gt_of_cert {x y : CReal.Pre} :
    ∀ _ : CompareCert x y, (Pre.toReal x < Pre.toReal y) ∨ (Pre.toReal y < Pre.toReal x) := by
  intro c
  cases c with
  | lt i h => exact Or.inl (toReal_lt_of_sep (x := x) (y := y) i h)
  | gt i h => exact Or.inr (toReal_gt_of_sep (x := x) (y := y) i h)

theorem toReal_lt_or_gt_of_compareWitness_some {x y : CReal.Pre} {fuel : Nat}
    {c : CompareCert x y} (_ : compareWitness x y fuel = some c) :
    (Pre.toReal x < Pre.toReal y) ∨ (Pre.toReal y < Pre.toReal x) := by
  exact toReal_lt_or_gt_of_cert (x := x) (y := y) c

/-
Bridge lemma: separation at the pre-level implies strict inequality on the quotient `CReal`.
-/
theorem lt_mk_of_sep (x y : CReal.Pre) (i : Nat)
    (h : x.approx (i + 1) + (1 : ℚ) / (2 ^ (i + 1)) <
      y.approx (i + 1) - (1 : ℚ) / (2 ^ (i + 1))) :
    (⟦x⟧ : CReal) < (⟦y⟧ : CReal) := by
  apply (Computable.CReal.toReal_lt_iff (x := (⟦x⟧ : CReal)) (y := (⟦y⟧ : CReal))).1
  simpa using (toReal_lt_of_sep (x := x) (y := y) i h)

theorem gt_mk_of_sep (x y : CReal.Pre) (i : Nat)
    (h : y.approx (i + 1) + (1 : ℚ) / (2 ^ (i + 1)) <
      x.approx (i + 1) - (1 : ℚ) / (2 ^ (i + 1))) :
    (⟦x⟧ : CReal) > (⟦y⟧ : CReal) := by
  change (⟦y⟧ : CReal) < (⟦x⟧ : CReal)
  exact lt_mk_of_sep (x := y) (y := x) i h

end Pre

/-!
## Convenience lemmas on the quotient `CReal`

These let tactics and downstream automation prove inequalities about `CReal.toReal x`
by discharging a single rational separation goal about the chosen representatives
`Quotient.out x` and `Quotient.out y`.
-/

theorem toReal_eq_toReal_out (x : CReal) : toReal x = Pre.toReal (Quotient.out x) := by
  have h : toReal (Quotient.mk _ (Quotient.out x) : CReal) = toReal x :=
    congrArg toReal (Quotient.out_eq x)
  calc
    toReal x = toReal (Quotient.mk _ (Quotient.out x) : CReal) := by
      simp
    _ = Pre.toReal (Quotient.out x) := rfl

theorem toReal_lt_of_sep_out (x y : CReal) (i : Nat)
    (h : (Quotient.out x).approx (i + 1) + (1 : ℚ) / (2 ^ (i + 1)) <
      (Quotient.out y).approx (i + 1) - (1 : ℚ) / (2 ^ (i + 1))) :
    toReal x < toReal y := by
  have hx : toReal x = Pre.toReal (Quotient.out x) := toReal_eq_toReal_out (x := x)
  have hy : toReal y = Pre.toReal (Quotient.out y) := toReal_eq_toReal_out (x := y)
  have hpre : Pre.toReal (Quotient.out x) < Pre.toReal (Quotient.out y) :=
    Pre.toReal_lt_of_sep (x := Quotient.out x) (y := Quotient.out y) i h
  simpa [hx, hy] using hpre

theorem toReal_gt_of_sep_out (x y : CReal) (i : Nat)
    (h : (Quotient.out y).approx (i + 1) + (1 : ℚ) / (2 ^ (i + 1)) <
      (Quotient.out x).approx (i + 1) - (1 : ℚ) / (2 ^ (i + 1))) :
    toReal y < toReal x := by
  have hy : toReal y = Pre.toReal (Quotient.out y) := toReal_eq_toReal_out (x := y)
  have hx : toReal x = Pre.toReal (Quotient.out x) := toReal_eq_toReal_out (x := x)
  have hpre : Pre.toReal (Quotient.out y) < Pre.toReal (Quotient.out x) :=
    Pre.toReal_gt_of_sep (x := Quotient.out x) (y := Quotient.out y) i h
  simpa [hx, hy] using hpre

/-!
## Quotient induction helpers

These wrap `Quotient.inductionOn₂` in a way that is easy to use from metaprogrammed tactics.
-/

theorem lt_inductionOn₂ (x y : CReal)
    (h : ∀ a b : CReal.Pre, (⟦a⟧ : CReal) < (⟦b⟧ : CReal)) : x < y := by
  simpa using (Quotient.inductionOn₂ x y h)

theorem gt_inductionOn₂ (x y : CReal)
    (h : ∀ a b : CReal.Pre, (⟦a⟧ : CReal) > (⟦b⟧ : CReal)) : x > y := by
  simpa using (Quotient.inductionOn₂ x y h)

/-!
## Quotient-level (noncomputable) semi-decision wrappers

`CReal` is a quotient type, so extracting representatives uses `Quotient.out` and is therefore
`noncomputable`. Still, it is often useful to have **rigorous, proof-producing** wrappers that:

- attempt to find a rational separation certificate on the chosen representatives, and
- return a proof about the corresponding denotations in `ℝ` when successful.

These functions do **not** constitute total decision procedures for real order/equality; they
are sound *semi-deciders* (success implies truth; failure implies no information).
-/

namespace Pre

/-- Noncomputable lift of `compareWitness` to the quotient `CReal` via `Quotient.out`. -/
noncomputable def compareWitness_out (x y : CReal) (fuel : Nat := 100) :
    Option (CompareCert (Quotient.out x) (Quotient.out y)) :=
  compareWitness (Quotient.out x) (Quotient.out y) fuel

/-- Soundness: a successful `compareWitness_out` yields a strict inequality in `ℝ` (one direction). -/
theorem toReal_lt_or_gt_of_compareWitness_out_some {x y : CReal} {fuel : Nat}
    {c : CompareCert (Quotient.out x) (Quotient.out y)}
    (_ : compareWitness_out x y fuel = some c) :
    (_root_.Computable.CReal.toReal x < _root_.Computable.CReal.toReal y) ∨
      (_root_.Computable.CReal.toReal y < _root_.Computable.CReal.toReal x) := by
  have hx : _root_.Computable.CReal.toReal x = Pre.toReal (Quotient.out x) := by
    simpa using (toReal_eq_toReal_out (x := x))
  have hy : _root_.Computable.CReal.toReal y = Pre.toReal (Quotient.out y) := by
    simpa using (toReal_eq_toReal_out (x := y))
  have hpre :
      (Pre.toReal (Quotient.out x) < Pre.toReal (Quotient.out y)) ∨
        (Pre.toReal (Quotient.out y) < Pre.toReal (Quotient.out x)) :=
    toReal_lt_or_gt_of_cert (x := Quotient.out x) (y := Quotient.out y) c
  simpa [hx, hy] using hpre

/-- Semi-decision of inequality at the quotient level (in `ℝ`): success yields `toReal x ≠ toReal y`. -/
noncomputable def apart?_out (x y : CReal) (fuel : Nat := 100) :
    Option (PLift (_root_.Computable.CReal.toReal x ≠ _root_.Computable.CReal.toReal y)) :=
  match compareWitness_out x y fuel with
  | some (.lt i h) => some ⟨ne_of_lt (toReal_lt_of_sep_out (x := x) (y := y) i h)⟩
  | some (.gt i h) => some ⟨(ne_of_lt (toReal_gt_of_sep_out (x := x) (y := y) i h)).symm⟩
  | none => none

end Pre

namespace CRealRep

variable {AQ : Type} [ApproxRationals AQ]

/-- Lift the pre-real comparison semi-decision to computational representatives. -/
def compareWitness (x y : CRealRep AQ) (fuel : Nat := 100) :
    Option (CReal.Pre.CompareCert x.toPre y.toPre) :=
  CReal.Pre.compareWitness x.toPre y.toPre fuel

theorem toReal_lt_or_gt_of_compareWitness {x y : CRealRep AQ}
    (c : CReal.Pre.CompareCert x.toPre y.toPre) :
    (CReal.toReal (CRealRep.denote (AQ := AQ) x) < CReal.toReal (CRealRep.denote (AQ := AQ) y)) ∨
      (CReal.toReal (CRealRep.denote (AQ := AQ) y) < CReal.toReal (CRealRep.denote (AQ := AQ) x)) := by
  have hpre :
      (CReal.Pre.toReal x.toPre < CReal.Pre.toReal y.toPre) ∨
        (CReal.Pre.toReal y.toPre < CReal.Pre.toReal x.toPre) :=
    CReal.Pre.toReal_lt_or_gt_of_cert (x := x.toPre) (y := y.toPre) c
  simpa [CRealRep.denote, CReal.toReal_mk] using hpre

theorem toReal_lt_or_gt_of_compareWitness_some {x y : CRealRep AQ} {fuel : Nat}
    {c : CReal.Pre.CompareCert x.toPre y.toPre}
    (_ : compareWitness (AQ := AQ) x y fuel = some c) :
    (CReal.toReal (CRealRep.denote (AQ := AQ) x) < CReal.toReal (CRealRep.denote (AQ := AQ) y)) ∨
      (CReal.toReal (CRealRep.denote (AQ := AQ) y) < CReal.toReal (CRealRep.denote (AQ := AQ) x)) := by
  exact toReal_lt_or_gt_of_compareWitness (AQ := AQ) (x := x) (y := y) c

end CRealRep

end CReal
end Computable
