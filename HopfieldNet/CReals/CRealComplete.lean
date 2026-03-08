/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import HopfieldNet.CReals.CRealLim

/-!
# Native Constructive Completeness of CReal

This file proves that `CReal` (the quotient of regular Cauchy sequences with dyadic modulus)
is complete **constructively**: every regular Cauchy sequence of pre-reals has a computable
limit, and the convergence proof uses only the diagonal construction (`lim_pre`), rational
arithmetic and the regularity modulus of `CReal.Pre`, and the existing quotient order.

**No classical logic, axiom of choice, `noncomputable` definitions, or transport from
Mathlib's `ℝ`** are used in the core results.

## Main results

- `complete_eps`: ε-form convergence for `RCauSeq` (dyadic-modulus sequences).
- `lim_pre_well_defined`: the diagonal limit respects setoid equivalence.
- `GeneralCauSeq` + `toRCauSeq`: reparametrization from arbitrary moduli.
- `GeneralCauSeq.converges`: full convergence of the original sequence to the limit.
- `archimedean_constructive`: Archimedean property without classical axioms.
- `constructive_complete`: the headline completeness theorem, stated for `GeneralCauSeq`.

## Design notes

Constructive completeness operates at the **Pre-level** (setoid level): the diagonal
construction requires access to rational approximants of individual terms, which lives below
the quotient. This matches Bishop (1967), CoRN/O'Connor (2008), and Spitters.
-/

set_option maxHeartbeats 800000

namespace Computable.CReal.Completeness

open Computable.CReal.Pre (ofRat)

/-! ### Helpers -/

private lemma ratCast_le {a b : ℚ} (h : a ≤ b) :
    (a : Computable.CReal) ≤ (b : Computable.CReal) := by
  show Computable.CReal.Pre.le (ofRat a) (ofRat b)
  intro n
  simp only [ofRat]
  linarith [show (0 : ℚ) ≤ 1 / 2 ^ n from by positivity]

private lemma one_div_pow_le {n m : ℕ} (h : n ≤ m) :
    (1 : ℚ) / 2 ^ m ≤ (1 : ℚ) / 2 ^ n :=
  one_div_le_one_div_of_le (pow_pos (by norm_num) n)
    ((pow_le_pow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mpr h)

/-! ### 1. Epsilon-form convergence -/

/-- **Epsilon-form convergence** for the diagonal limit.

Given any rational `ε > 0`, we can explicitly compute an index `N` beyond which all terms
of the Cauchy sequence are within `ε` of the limit. -/
theorem complete_eps (s : RCauSeq) :
    ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      |s.seq n - lim s| ≤ (ε : Computable.CReal) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨k, hk⟩ := Computable.exists_pow_gt (one_div_pos.mpr hε2)
  have hk' : (1 : ℚ) / 2 ^ k < ε / 2 :=
    (one_div_lt (pow_pos (by norm_num) k) hε2).mpr hk
  refine ⟨k + 2, fun n hn => ?_⟩
  have hconv := converges_to_lim s k n hn
  have h_sum_le : (1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ (n + 1) ≤ ε := by
    have h1 : (1 : ℚ) / 2 ^ (n + 1) ≤ (1 : ℚ) / 2 ^ k := one_div_pow_le (by omega)
    linarith
  exact _root_.le_trans hconv (ratCast_le h_sum_le)

/-! ### 2. Well-definedness of `lim_pre` under representative change -/

/-- The diagonal limit respects setoid equivalence of representatives.

If two `RCauSeq`s have pointwise-equivalent pre-reals, their diagonal limits are equivalent
as pre-reals. This makes the limit map canonical on equivalence classes, without choice. -/
theorem lim_pre_well_defined (s₁ s₂ : RCauSeq)
    (h : ∀ n, Computable.CReal.Pre.Equiv (s₁.pre n) (s₂.pre n)) :
    Computable.CReal.Pre.Equiv (lim_pre s₁) (lim_pre s₂) := by
  intro n
  show |(lim_pre s₁).approx (n + 1) - (lim_pre s₂).approx (n + 1)| ≤ (1 : ℚ) / 2 ^ n
  have h1 : (lim_pre s₁).approx (n + 1) = (s₁.pre (n + 3)).approx (n + 3) := rfl
  have h2 : (lim_pre s₂).approx (n + 1) = (s₂.pre (n + 3)).approx (n + 3) := rfl
  rw [h1, h2]
  exact _root_.le_trans (h (n + 3) (n + 2)) (one_div_pow_le (by omega))

/-- Equivalent representatives produce equal quotient-level limits. -/
theorem lim_eq_of_equiv (s₁ s₂ : RCauSeq)
    (h : ∀ n, Computable.CReal.Pre.Equiv (s₁.pre n) (s₂.pre n)) :
    lim s₁ = lim s₂ :=
  Quotient.sound (lim_pre_well_defined s₁ s₂ h)

/-! ### 3. Generalized Cauchy sequences and reparametrization -/

/-- A Cauchy sequence of pre-reals with an **arbitrary modulus**.

Unlike `RCauSeq` (which uses a fixed dyadic diagonal condition), this structure accepts any
modulus function `μ : ℕ → ℕ` that tells us "at precision level `k`, terms beyond index `μ k`
are within `1/2^(k+1)` of each other" (measured at the `(k+2)`-th rational approximant).

This is the interface a user naturally has when proving that a custom construction yields
a convergent sequence of computable reals. -/
structure GeneralCauSeq where
  pre : ℕ → Computable.CReal.Pre
  μ : ℕ → ℕ
  μ_mono : Monotone μ
  is_cauchy : ∀ k n m, μ k ≤ n → μ k ≤ m →
    |(pre n).approx (k + 2) - (pre m).approx (k + 2)| ≤ (1 : ℚ) / 2 ^ (k + 1)

/-- Reparametrize a `GeneralCauSeq` into an `RCauSeq` by extracting a subsequence. -/
def GeneralCauSeq.toRCauSeq (g : GeneralCauSeq) : RCauSeq where
  seq := fun n => ⟦g.pre (g.μ (n + 2))⟧
  pre := fun n => g.pre (g.μ (n + 2))
  seq_spec := fun _ => rfl
  is_cauchy := by
    intro n m hnm
    exact g.is_cauchy n _ _ (g.μ_mono (by omega)) (g.μ_mono (by omega))

/-- The limit of a `GeneralCauSeq`, defined via reparametrization. -/
def GeneralCauSeq.limG (g : GeneralCauSeq) : Computable.CReal :=
  lim g.toRCauSeq

/-- The reparametrized subsequence converges to the limit in ε-form. -/
theorem GeneralCauSeq.subseq_converges (g : GeneralCauSeq) :
    ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      |⟦g.pre (g.μ (n + 2))⟧ - g.limG| ≤ (ε : Computable.CReal) :=
  complete_eps g.toRCauSeq

/-! ### Full convergence of the original sequence

This is the key result addressing a gap in the previous version: we show that the
**original** terms `⟦g.pre n⟧` (not just the reparametrized subsequence) converge to
`g.limG`. The proof works entirely at the Pre level using `abs_le_of_pre_abs_bound`,
avoiding the need for a CReal-level triangle inequality. -/

/-- Sync bound: at the diagonal index `k+1`, the Pre-level difference between `g.pre n`
and the limit is bounded by `1/2^k`, provided `n ≥ g.μ k`. -/
private lemma general_sync_bound (g : GeneralCauSeq) (k : ℕ) (n : ℕ) (hn : g.μ k ≤ n) :
    |(Computable.CReal.Pre.add (g.pre n)
        (Computable.CReal.Pre.neg (lim_pre g.toRCauSeq))).approx (k + 1)|
      ≤ (1 : ℚ) / 2 ^ k := by
  have hJ : (Computable.CReal.Pre.add (g.pre n)
      (Computable.CReal.Pre.neg (lim_pre g.toRCauSeq))).approx (k + 1)
    = (g.pre n).approx (k + 2) - (lim_pre g.toRCauSeq).approx (k + 2) := by
    dsimp [Computable.CReal.Pre.add, Computable.CReal.Pre.neg]; ring
  have hL : (lim_pre g.toRCauSeq).approx (k + 2) =
      (g.pre (g.μ (k + 6))).approx (k + 4) := by
    dsimp [lim_pre, GeneralCauSeq.toRCauSeq]
  rw [hJ, hL]
  have h_tri := abs_sub_le
    ((g.pre n).approx (k + 2))
    ((g.pre (g.μ (k + 6))).approx (k + 2))
    ((g.pre (g.μ (k + 6))).approx (k + 4))
  have h_cauchy : |(g.pre n).approx (k + 2) - (g.pre (g.μ (k + 6))).approx (k + 2)|
      ≤ (1 : ℚ) / 2 ^ (k + 1) :=
    g.is_cauchy k n (g.μ (k + 6)) hn (g.μ_mono (by omega))
  have h_reg : |(g.pre (g.μ (k + 6))).approx (k + 2) - (g.pre (g.μ (k + 6))).approx (k + 4)|
      ≤ (1 : ℚ) / 2 ^ (k + 2) :=
    (g.pre (g.μ (k + 6))).is_regular (k + 2) (k + 4) (by omega)
  have h_half : (1 : ℚ) / 2 ^ (k + 2) ≤ (1 : ℚ) / 2 ^ (k + 1) :=
    one_div_pow_le (by omega)
  have h_two : (1 : ℚ) / 2 ^ (k + 1) + (1 : ℚ) / 2 ^ (k + 1) = (1 : ℚ) / 2 ^ k :=
    Computable.CReal.two_halves_to_pred k
  linarith

/-- **Full convergence of a `GeneralCauSeq`**: every term of the original sequence
converges to the limit, not just the reparametrized subsequence.

The proof establishes a "sync bound" at a single Pre-level index using the Cauchy condition
and regularity, then propagates to all indices via `lift_sync_bound_with_uniform_tail`,
and finally lifts to CReal via `abs_le_of_pre_abs_bound`. -/
theorem GeneralCauSeq.converges (g : GeneralCauSeq) :
    ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      |⟦g.pre n⟧ - g.limG| ≤ (ε : Computable.CReal) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨k, hk⟩ := Computable.exists_pow_gt (one_div_pos.mpr hε2)
  have hk' : (1 : ℚ) / 2 ^ k < ε / 2 :=
    (one_div_lt (pow_pos (by norm_num) k) hε2).mpr hk
  refine ⟨g.μ k, fun n hn => ?_⟩
  let d : Computable.CReal.Pre :=
    Computable.CReal.Pre.add (g.pre n) (Computable.CReal.Pre.neg (lim_pre g.toRCauSeq))
  have hlim : lim g.toRCauSeq = ⟦lim_pre g.toRCauSeq⟧ := rfl
  have h_sync : |d.approx (k + 1)| ≤ (1 : ℚ) / 2 ^ k :=
    general_sync_bound g k n hn
  have h_all_raw :
      ∀ j, |d.approx (j + 1)| ≤ (1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (k + 1) :=
    lift_sync_bound_with_uniform_tail d k (by simpa using h_sync)
  have h_all :
      ∀ j, |d.approx (j + 1)| ≤ ((1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ (k + 1)) + (1 : ℚ) / 2 ^ j := by
    intro j; linarith [h_all_raw j]
  have h_abs := abs_le_of_pre_abs_bound d h_all
  have h_bound_le : (1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ (k + 1) ≤ ε := by
    have : (1 : ℚ) / 2 ^ (k + 1) ≤ (1 : ℚ) / 2 ^ k := one_div_pow_le (by omega)
    linarith
  have h_le_eps := _root_.le_trans h_abs (ratCast_le h_bound_le)
  simpa [hlim, d, Computable.CReal.Pre.add, Computable.CReal.Pre.neg, sub_eq_add_neg]
    using h_le_eps

/-! ### 4. Constructive Archimedean property -/

/-- CReal is Archimedean: for every `x : CReal`, there exists `n : ℕ` with `x ≤ n`.

This proof is fully constructive — it uses `Quotient.inductionOn` (which targets `Prop`)
and the computable `cBound` from `CReal.Pre`. -/
theorem archimedean_constructive (x : Computable.CReal) :
    ∃ n : ℕ, x ≤ (n : Computable.CReal) := by
  induction x using Quotient.inductionOn with
  | h x_pre =>
    refine ⟨x_pre.cBound, ?_⟩
    show Computable.CReal.Pre.le x_pre (ofRat (x_pre.cBound : ℚ))
    intro n
    simp only [ofRat]
    calc x_pre.approx (n + 1)
        ≤ |x_pre.approx (n + 1)| := le_abs_self _
      _ ≤ (x_pre.cBound : ℚ) := Computable.CReal.Pre.abs_approx_le_cBound x_pre (n + 1)
      _ ≤ (x_pre.cBound : ℚ) + 1 / 2 ^ n := le_add_of_nonneg_right (by positivity)

/-! ### 5. Headline constructive completeness theorem -/

/-- **Native constructive completeness of CReal.**

Every Cauchy sequence of pre-reals (with arbitrary modulus) has a computable limit in CReal,
and every term of the original sequence converges to that limit. The proof is fully
constructive:

- The limit is *explicitly computed* by the diagonal construction `lim_pre`.
- Convergence uses only rational arithmetic and the regularity modulus.
- **No classical logic, axiom of choice, or transport from `ℝ` is used.**

This is the standard completeness construction from Bishop's "Foundations of Constructive
Analysis" (1967), formalized and verified in Lean 4.

The user-facing interface takes a `GeneralCauSeq` (arbitrary monotone modulus), which is
the natural input format when proving convergence of custom constructions. -/
theorem constructive_complete (g : GeneralCauSeq) :
    ∃ L : Computable.CReal, ∀ ε : ℚ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, |⟦g.pre n⟧ - L| ≤ (ε : Computable.CReal) :=
  ⟨g.limG, g.converges⟩

/-- Variant of `constructive_complete` accepting the raw diagonal Cauchy condition directly,
without wrapping in a `GeneralCauSeq`. Useful when the modulus is the identity. -/
theorem constructive_complete_raw
    (pre : ℕ → Computable.CReal.Pre)
    (hcauchy : ∀ n m, n ≤ m →
      |(pre (n + 2)).approx (n + 2) - (pre (m + 2)).approx (n + 2)| ≤
        (1 : ℚ) / 2 ^ (n + 1)) :
    ∃ L : Computable.CReal, ∀ ε : ℚ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, |⟦pre n⟧ - L| ≤ (ε : Computable.CReal) := by
  let s : RCauSeq := RCauSeq.mk (fun n => ⟦pre n⟧) pre (fun _ => rfl) hcauchy
  exact ⟨lim s, complete_eps s⟩

end Computable.CReal.Completeness
