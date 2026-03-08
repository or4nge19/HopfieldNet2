import HopfieldNet.CReals.Mobius.Denotation
import HopfieldNet.CReals.Mobius.OracleSoundness
import HopfieldNet.CReals.SignedDigit.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace Computable
namespace Mobius

open scoped BigOperators

/-! ## Final boss: VM trace denotation -/

abbrev Digit := Computable.CReal.SignedDigit.Digit

def digit_to_LFT : Digit → LFT
  | .neg  => digitNeg
  | .zero => digitZero
  | .pos  => digitPos

abbrev DigitStream : Type := ℕ → Digit

def lftStreamOfDigits (out : DigitStream) : LFTStream :=
  fun n => digit_to_LFT (out n)

namespace DigitStream

@[simp] lemma digit_to_LFT_c (d : Digit) : (digit_to_LFT d).c = 0 := by
  cases d <;> rfl

@[simp] lemma digit_to_LFT_a (d : Digit) : (digit_to_LFT d).a = 1 := by
  cases d <;> rfl

@[simp] lemma digit_to_LFT_d (d : Digit) : (digit_to_LFT d).d = 2 := by
  cases d <;> rfl

@[simp] lemma digit_to_LFT_NoPoleOnBase (d : Digit) : (digit_to_LFT d).NoPoleOnBase := by
  -- `|0| < |2|`
  cases d <;> simp [LFT.NoPoleOnBase]

lemma digit_to_LFT_maps_baseI (d : Digit) :
    Set.MapsTo (fun x => LFT.apply (digit_to_LFT d) x) baseI baseI := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  cases d with
  | neg =>
      have hfx :
          LFT.apply (digit_to_LFT _root_.Computable.CReal.SignedDigit.Digit.neg) x = (x - 1) / 2 := by
        simp [digit_to_LFT, digitNeg, LFT.apply, sub_eq_add_neg, mul_comm]
      -- (x - 1)/2 ∈ [-1,0]
      have h1 : (-1 : ℝ) ≤ (x - 1) / 2 := by nlinarith
      have h2 : (x - 1) / 2 ≤ (1 : ℝ) := by nlinarith
      simpa [hfx] using And.intro h1 h2
  | zero =>
      have hfx :
          LFT.apply (digit_to_LFT _root_.Computable.CReal.SignedDigit.Digit.zero) x = x / 2 := by
        simp [digit_to_LFT, digitZero, LFT.apply, mul_comm]
      -- x/2 ∈ [-1/2, 1/2] ⊆ [-1,1]
      have h1 : (-1 : ℝ) ≤ x / 2 := by nlinarith
      have h2 : x / 2 ≤ (1 : ℝ) := by nlinarith
      simpa [hfx] using And.intro h1 h2
  | pos =>
      have hfx :
          LFT.apply (digit_to_LFT _root_.Computable.CReal.SignedDigit.Digit.pos) x = (x + 1) / 2 := by
        simp [digit_to_LFT, digitPos, LFT.apply, mul_comm]
      -- (x + 1)/2 ∈ [0,1]
      have h1 : (-1 : ℝ) ≤ (x + 1) / 2 := by nlinarith
      have h2 : (x + 1) / 2 ≤ (1 : ℝ) := by nlinarith
      simpa [hfx] using And.intro h1 h2

/-! ### Tail partial compositions for digit streams -/

lemma partialCompFrom_c_eq_zero (out : DigitStream) (k n : ℕ) :
    (partialCompFrom (lftStreamOfDigits out) k n).c = 0 := by
  induction n with
  | zero =>
      simp [partialCompFrom, lftStreamOfDigits]
  | succ n ih =>
      -- for `c=0` matrices, composition preserves `c=0`
      simp [partialCompFrom, LFT.comp, ih, lftStreamOfDigits]

lemma partialCompFrom_a_eq_one (out : DigitStream) (k n : ℕ) :
    (partialCompFrom (lftStreamOfDigits out) k n).a = 1 := by
  induction n with
  | zero =>
      simp [partialCompFrom, lftStreamOfDigits]
  | succ n ih =>
      -- for `c=0` matrices, `a` multiplies; digits have `a=1`
      simp [partialCompFrom, LFT.comp, ih, lftStreamOfDigits]

lemma partialCompFrom_d_eq_pow_two (out : DigitStream) (k n : ℕ) :
    (partialCompFrom (lftStreamOfDigits out) k n).d = (2 : ℤ) ^ (n + 1) := by
  induction n with
  | zero =>
      simp [partialCompFrom, lftStreamOfDigits]
  | succ n ih =>
      -- for `c=0` matrices, `d` multiplies
      have hc : (partialCompFrom (lftStreamOfDigits out) k n).c = 0 :=
        partialCompFrom_c_eq_zero (out := out) k n
      simp [partialCompFrom, LFT.comp, ih, hc, pow_succ, lftStreamOfDigits]

lemma partialCompFrom_NoPoleOnBase (out : DigitStream) (k n : ℕ) :
    (partialCompFrom (lftStreamOfDigits out) k n).NoPoleOnBase := by
  -- reduce to `|0| < |d|` with `d = 2^(n+1)`
  have hc : (partialCompFrom (lftStreamOfDigits out) k n).c = 0 :=
    partialCompFrom_c_eq_zero (out := out) k n
  have hd : (partialCompFrom (lftStreamOfDigits out) k n).d = (2 : ℤ) ^ (n + 1) :=
    partialCompFrom_d_eq_pow_two (out := out) k n
  have hpos : (0 : ℤ) < |(2 : ℤ) ^ (n + 1)| := by
    have hne : (2 : ℤ) ^ (n + 1) ≠ 0 := by
      exact pow_ne_zero _ (by decide : (2 : ℤ) ≠ 0)
    exact abs_pos.2 hne
  -- conclude `|0| < |d|`
  -- Goal is `|c| < |d|`; rewrite using `c=0` and `d=2^(n+1)` and use positivity of `|2^(n+1)|`.
  rw [LFT.NoPoleOnBase, hc, hd]
  simpa using hpos

lemma partialCompFrom_maps_baseI (out : DigitStream) (k n : ℕ) :
    Set.MapsTo (fun x => LFT.apply (partialCompFrom (lftStreamOfDigits out) k n) x) baseI baseI := by
  induction n generalizing k with
  | zero =>
      simpa [partialCompFrom, lftStreamOfDigits] using digit_to_LFT_maps_baseI (out k)
  | succ n ih =>
      -- use `partialCompFrom_succ_eq` to factor out the head digit
      intro x hx
      have hx' : LFT.apply (partialCompFrom (lftStreamOfDigits out) (k + 1) n) x ∈ baseI :=
        ih (k := k + 1) hx
      -- apply the head digit to stay in `baseI`
      have hhead : Set.MapsTo (fun z => LFT.apply ((lftStreamOfDigits out) k) z) baseI baseI := by
        simpa [lftStreamOfDigits] using digit_to_LFT_maps_baseI (out k)
      -- unfold `partialCompFrom_succ_eq` and rewrite via `LFT.apply_comp`
      have hpc :
          partialCompFrom (lftStreamOfDigits out) k (n + 1) =
            ((lftStreamOfDigits out) k).comp (partialCompFrom (lftStreamOfDigits out) (k + 1) n) := by
        simpa using (partialCompFrom_succ_eq (lftStreamOfDigits out) k n)
      -- denominators are never zero on `baseI` for digit partial compositions
      have hden_tail :
          (((partialCompFrom (lftStreamOfDigits out) (k + 1) n).c : ℝ) * x +
                ((partialCompFrom (lftStreamOfDigits out) (k + 1) n).d : ℝ)) ≠ 0 := by
        exact LFT.denom_ne_zero_of_NoPoleOnBase (partialCompFrom (lftStreamOfDigits out) (k + 1) n)
          (x := x) hx (partialCompFrom_NoPoleOnBase (out := out) (k := k + 1) n)
      have hden_head :
          (((((lftStreamOfDigits out) k).c : ℝ) *
              LFT.apply (partialCompFrom (lftStreamOfDigits out) (k + 1) n) x) +
            (((lftStreamOfDigits out) k).d : ℝ)) ≠ 0 := by
        exact LFT.denom_ne_zero_of_NoPoleOnBase ((lftStreamOfDigits out) k)
          (x := LFT.apply (partialCompFrom (lftStreamOfDigits out) (k + 1) n) x) hx'
          (digit_to_LFT_NoPoleOnBase (out k))
      have happ :
          LFT.apply (partialCompFrom (lftStreamOfDigits out) k (n + 1)) x =
            LFT.apply ((lftStreamOfDigits out) k)
              (LFT.apply (partialCompFrom (lftStreamOfDigits out) (k + 1) n) x) := by
        -- `apply_comp` gives `(M.comp N).apply = M.apply (N.apply _)`
        -- our `hpc` is `(head.comp tail)`.
        simpa [hpc] using
          (LFT.apply_comp ((lftStreamOfDigits out) k)
            (partialCompFrom (lftStreamOfDigits out) (k + 1) n) x hden_tail hden_head)
      -- finish using the head `MapsTo`
      simpa [happ] using hhead hx'

lemma partialCompFrom_apply_affine (out : DigitStream) (k n : ℕ) (x : ℝ) :
    LFT.apply (partialCompFrom (lftStreamOfDigits out) k n) x =
      (((partialCompFrom (lftStreamOfDigits out) k n).a : ℝ) * x +
          ((partialCompFrom (lftStreamOfDigits out) k n).b : ℝ)) /
        ((partialCompFrom (lftStreamOfDigits out) k n).d : ℝ) := by
  -- since `c = 0`, denominator is constant `(d : ℝ)`
  have hc : (partialCompFrom (lftStreamOfDigits out) k n).c = 0 :=
    partialCompFrom_c_eq_zero (out := out) k n
  simp [LFT.apply, hc, mul_comm]

lemma partialCompFrom_abs_sub_le (out : DigitStream) (k n : ℕ) {x y : ℝ}
    (hx : x ∈ baseI) (hy : y ∈ baseI) :
    |LFT.apply (partialCompFrom (lftStreamOfDigits out) k n) x -
        LFT.apply (partialCompFrom (lftStreamOfDigits out) k n) y|
      ≤ (2 : ℝ) / (2 : ℝ) ^ (n + 1) := by
  -- use the affine form `((x + b)/d)` with `a=1`, `c=0`, `d = 2^(n+1)`
  have ha : (partialCompFrom (lftStreamOfDigits out) k n).a = 1 :=
    partialCompFrom_a_eq_one (out := out) k n
  have hdZ : (partialCompFrom (lftStreamOfDigits out) k n).d = (2 : ℤ) ^ (n + 1) :=
    partialCompFrom_d_eq_pow_two (out := out) k n
  have hd : ((partialCompFrom (lftStreamOfDigits out) k n).d : ℝ) = (2 : ℝ) ^ (n + 1) := by
    exact_mod_cast hdZ
  have hdne : ((partialCompFrom (lftStreamOfDigits out) k n).d : ℝ) ≠ 0 := by
    simp [hd]
  have hformx := partialCompFrom_apply_affine (out := out) k n x
  have hformy := partialCompFrom_apply_affine (out := out) k n y

  have hxy : |x - y| ≤ (2 : ℝ) := by
    have h1 : x - y ≤ (2 : ℝ) := by nlinarith [hx.2, hy.1]
    have h2 : -(x - y) ≤ (2 : ℝ) := by nlinarith [hx.1, hy.2]
    exact abs_le.2 ⟨by simpa [sub_eq_add_neg] using h2, h1⟩

  have hdiff :
      |LFT.apply (partialCompFrom (lftStreamOfDigits out) k n) x -
          LFT.apply (partialCompFrom (lftStreamOfDigits out) k n) y|
        = |x - y| / ((partialCompFrom (lftStreamOfDigits out) k n).d : ℝ) := by
    -- both are `(x + b)/d`; subtraction cancels `b`
    -- do the algebra in the field (safe since `d ≠ 0`)
    have :
        LFT.apply (partialCompFrom (lftStreamOfDigits out) k n) x -
            LFT.apply (partialCompFrom (lftStreamOfDigits out) k n) y
          = (x - y) / ((partialCompFrom (lftStreamOfDigits out) k n).d : ℝ) := by
      simp [hformx, hformy, ha, sub_eq_add_neg, div_eq_mul_inv, add_mul]
      field_simp [hdne]
      ring_nf
    have hdpos : 0 < ((partialCompFrom (lftStreamOfDigits out) k n).d : ℝ) := by
      rw [hd]
      positivity
    have habs := congrArg (fun t : ℝ => |t|) this
    -- remove `|d|` using positivity
    simpa [abs_div, abs_of_pos hdpos] using habs

  rw [hdiff]
  have hdpos : 0 < ((partialCompFrom (lftStreamOfDigits out) k n).d : ℝ) := by
    rw [hd]
    positivity
  have : |x - y| / ((partialCompFrom (lftStreamOfDigits out) k n).d : ℝ) ≤
      (2 : ℝ) / ((partialCompFrom (lftStreamOfDigits out) k n).d : ℝ) := by
    -- rewrite division as multiplication by `inv`
    simpa [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_right hxy (le_of_lt (inv_pos.2 hdpos)))
  simpa [hd, div_eq_mul_inv] using this

end DigitStream

/-! ### A `MobiusReal` from a digit stream -/

noncomputable def MobiusReal.fromStream (out : DigitStream) : MobiusReal where
  stream := lftStreamOfDigits out
  contractive := by
    refine
      { no_poles_from := ?_
        maps_base_from := ?_
        shrinks_to_zero := ?_ }
    · intro k n
      exact DigitStream.partialCompFrom_NoPoleOnBase (out := out) k n
    · intro k n
      exact DigitStream.partialCompFrom_maps_baseI (out := out) k n
    · intro ε hε
      -- `f n = 2 / 2^(n+1)` tends to `0`, hence is eventually `< ε`.
      have ht : Filter.Tendsto (fun n : ℕ => (2 : ℝ) / (2 : ℝ) ^ (n + 1)) Filter.atTop (nhds (0 : ℝ)) := by
        -- rewrite as `(1/2)^n`
        have hrew :
            (fun n : ℕ => (2 : ℝ) / (2 : ℝ) ^ (n + 1)) = fun n : ℕ => (1 / 2 : ℝ) ^ n := by
          funext n
          simp [pow_succ, div_eq_mul_inv]
        -- `(1/2)^n → 0`
        have ht' :
            Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds (0 : ℝ)) := by
          -- `tendsto_pow_atTop_nhds_zero_of_lt_one`
          simpa [one_div] using
            (tendsto_pow_atTop_nhds_zero_of_lt_one (𝕜 := ℝ) (r := (1 / 2 : ℝ))
              (by positivity) (by norm_num))
        simpa [hrew] using ht'
      have hEv : ∀ᶠ n in Filter.atTop, (2 : ℝ) / (2 : ℝ) ^ (n + 1) < ε := by
        -- order-topology characterization of `Tendsto` on `ℝ`
        exact (tendsto_order.1 ht).2 ε hε
      rcases (Filter.eventually_atTop.1 hEv) with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro n hn k x hx y hy
      have hle :
          |LFT.apply (partialCompFrom (lftStreamOfDigits out) k n) x -
              LFT.apply (partialCompFrom (lftStreamOfDigits out) k n) y|
            ≤ (2 : ℝ) / (2 : ℝ) ^ (n + 1) :=
        DigitStream.partialCompFrom_abs_sub_le (out := out) k n hx hy
      exact lt_of_le_of_lt hle (hN n hn)

/-! ### N-step relation (simple) -/

inductive VMStep_n : ℕ → VMState → Option LFT → VMState → Prop
  | zero {s s' : VMState} {l : Option LFT} (h : VMStep s l s') :
      VMStep_n 0 s l s'
  | succ {n : ℕ} {s s1 s2 : VMState} {l1 l2 : Option LFT}
      (h1 : VMStep_n n s l1 s1) (h2 : VMStep s1 l2 s2) :
      VMStep_n (n + 1) s l2 s2

/-! ### VM soundness (emission-only trace form) -/

private lemma den_ne_zero_of_oracle_eq (T : Tensor) (x y : ℝ)
    (hx : x ∈ baseI) (hy : y ∈ baseI)
    {ed : Tensor.EmitDecision}
    (h : T.oracle = ed)
    (hed : ed = .neg ∨ ed = .zero ∨ ed = .pos) :
    ((T.e : ℝ) * x * y + (T.f : ℝ) * x + (T.g : ℝ) * y + (T.h : ℝ)) ≠ 0 := by
  -- Corner denominator values
  set d1 : ℤ := T.e + T.f + T.g + T.h with hd1
  set d2 : ℤ := -T.e + T.f - T.g + T.h with hd2
  set d3 : ℤ := -T.e - T.f + T.g + T.h with hd3
  set d4 : ℤ := T.e - T.f - T.g + T.h with hd4

  -- Emitting implies the initial `hasNoPole` check succeeded.
  have hnp : Tensor.hasNoPole d1 d2 d3 d4 = true := by
    by_cases hhp : Tensor.hasNoPole d1 d2 d3 d4 = true
    · exact hhp
    · have hhp' : Tensor.hasNoPole d1 d2 d3 d4 = false := by
        cases h' : Tensor.hasNoPole d1 d2 d3 d4 <;> simp_all
      -- if `hasNoPole` fails, `oracle` returns `absorb`
      have horb : T.oracle = Tensor.EmitDecision.absorb := by
        have hhp'' :
            Tensor.hasNoPole (T.e + T.f + T.g + T.h) (-T.e + T.f - T.g + T.h)
              (-T.e - T.f + T.g + T.h) (T.e - T.f - T.g + T.h) = false := by
          simpa [hd1, hd2, hd3, hd4] using hhp'
        unfold Tensor.oracle
        -- unfold `cornerValues` so the guard is `!hasNoPole ...`
        simp [Tensor.cornerValues, hhp'']
      -- contradiction with `ed ∈ {neg,zero,pos}`
      have : ed = Tensor.EmitDecision.absorb := by simpa [h] using horb
      have contra : False := by
        rcases hed with hneg | hrest
        · exact (by cases (this.symm.trans hneg))
        · rcases hrest with hzero | hpos
          · exact (by cases (this.symm.trans hzero))
          · exact (by cases (this.symm.trans hpos))
      exact False.elim contra

  have hcases := Tensor.hasNoPole_cases d1 d2 d3 d4 hnp
  rcases hcases with hd_pos | hd_neg
  · -- denominators positive everywhere on `baseI²`
    have hden_pos :
        (T.e : ℝ) * x * y + (T.f : ℝ) * x + (T.g : ℝ) * y + (T.h : ℝ) > 0 := by
      apply bilinear_pos_of_corners (T.e : ℝ) (T.f : ℝ) (T.g : ℝ) (T.h : ℝ)
      · have : (d1 : ℝ) > 0 := by exact_mod_cast hd_pos.1
        simpa [hd1, one_mul, mul_one, add_assoc, add_comm, add_left_comm] using this
      · have hd2pos : (0 : ℤ) < d2 := hd_pos.2.1
        have hd2pos' : (0 : ℤ) < (-T.e + T.f - T.g + T.h) := by simpa [hd2] using hd2pos
        have : (0 : ℝ) < (-T.e + T.f - T.g + T.h : ℝ) := by exact_mod_cast hd2pos'
        have hform :
            (↑T.e * (1 : ℝ) * (-1) + ↑T.f * 1 + ↑T.g * (-1) + ↑T.h) =
              (-T.e + T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      · have hd3pos : (0 : ℤ) < d3 := hd_pos.2.2.1
        have hd3pos' : (0 : ℤ) < (-T.e - T.f + T.g + T.h) := by simpa [hd3] using hd3pos
        have : (0 : ℝ) < (-T.e - T.f + T.g + T.h : ℝ) := by exact_mod_cast hd3pos'
        have hform :
            (↑T.e * (-1 : ℝ) * 1 + ↑T.f * (-1) + ↑T.g * 1 + ↑T.h) =
              (-T.e - T.f + T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      · have hd4pos : (0 : ℤ) < d4 := hd_pos.2.2.2
        have hd4pos' : (0 : ℤ) < (T.e - T.f - T.g + T.h) := by simpa [hd4] using hd4pos
        have : (0 : ℝ) < (T.e - T.f - T.g + T.h : ℝ) := by exact_mod_cast hd4pos'
        have hform :
            (↑T.e * (-1 : ℝ) * (-1) + ↑T.f * (-1) + ↑T.g * (-1) + ↑T.h) =
              (T.e - T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      · exact hx.1
      · exact hx.2
      · exact hy.1
      · exact hy.2
    exact ne_of_gt hden_pos
  · -- denominators negative everywhere
    have hden_neg :
        (T.e : ℝ) * x * y + (T.f : ℝ) * x + (T.g : ℝ) * y + (T.h : ℝ) < 0 := by
      apply bilinear_neg_of_corners (T.e : ℝ) (T.f : ℝ) (T.g : ℝ) (T.h : ℝ)
      · have : (d1 : ℝ) < 0 := by exact_mod_cast hd_neg.1
        simpa [hd1, one_mul, mul_one, add_assoc, add_comm, add_left_comm] using this
      · have hd2neg : d2 < 0 := hd_neg.2.1
        have hd2neg' : (-T.e + T.f - T.g + T.h) < 0 := by simpa [hd2] using hd2neg
        have : (-T.e + T.f - T.g + T.h : ℝ) < 0 := by exact_mod_cast hd2neg'
        have hform :
            (↑T.e * (1 : ℝ) * (-1) + ↑T.f * 1 + ↑T.g * (-1) + ↑T.h) =
              (-T.e + T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      · have hd3neg : d3 < 0 := hd_neg.2.2.1
        have hd3neg' : (-T.e - T.f + T.g + T.h) < 0 := by simpa [hd3] using hd3neg
        have : (-T.e - T.f + T.g + T.h : ℝ) < 0 := by exact_mod_cast hd3neg'
        have hform :
            (↑T.e * (-1 : ℝ) * 1 + ↑T.f * (-1) + ↑T.g * 1 + ↑T.h) =
              (-T.e - T.f + T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      · have hd4neg : d4 < 0 := hd_neg.2.2.2
        have hd4neg' : (T.e - T.f - T.g + T.h) < 0 := by simpa [hd4] using hd4neg
        have : (T.e - T.f - T.g + T.h : ℝ) < 0 := by exact_mod_cast hd4neg'
        have hform :
            (↑T.e * (-1 : ℝ) * (-1) + ↑T.f * (-1) + ↑T.g * (-1) + ↑T.h) =
              (T.e - T.f - T.g + T.h : ℝ) := by ring_nf
        simpa [hform] using this
      · exact hx.1
      · exact hx.2
      · exact hy.1
      · exact hy.2
    exact ne_of_lt hden_neg

theorem vm_soundness (s₀ : VMState) (X Y : MobiusReal) (out : DigitStream) :
    (∃ σ : ℕ → VMState,
        σ 0 = s₀ ∧
        ∀ n, ∃ s', VMStep (σ n) (some (digit_to_LFT (out n))) s' ∧ σ (n + 1) = s') →
    (MobiusReal.fromStream out).val =
      Tensor.valueAt s₀.T (MobiusReal.drop X s₀.idx_x).val (MobiusReal.drop Y s₀.idx_y).val := by
  let X0 : MobiusReal := MobiusReal.drop X s₀.idx_x
  let Y0 : MobiusReal := MobiusReal.drop Y s₀.idx_y
  rintro ⟨σ, hσ0, hσstep⟩
  have hx : X0.val ∈ baseI := MobiusReal.val_mem_baseI X0
  have hy : Y0.val ∈ baseI := MobiusReal.val_mem_baseI Y0
  -- shorthand for the “residual value” at step `n`
  let r : ℕ → ℝ := fun n => Tensor.valueAt (σ n).T X0.val Y0.val

  -- One-step semantic equation: `r n = D (r (n+1))`.
  have hrec : ∀ n, r n = LFT.apply (digit_to_LFT (out n)) (r (n + 1)) := by
    intro n
    rcases hσstep n with ⟨s', hstep, hσnext⟩
    -- rewrite `r (n+1)` using the chosen successor `s'`
    have hrnext : r (n + 1) = Tensor.valueAt s'.T X0.val Y0.val := by
      simp [r, hσnext]
    cases hout : out n with
    | neg =>
        have hstep' : VMStep (σ n) (some digitNeg) s' := by
          simpa [digit_to_LFT, hout] using hstep
        cases hstep' with
        | emitNeg hor =>
            have hden :
                ((σ n).T.e : ℝ) * X0.val * Y0.val + ((σ n).T.f : ℝ) * X0.val +
                    ((σ n).T.g : ℝ) * Y0.val + ((σ n).T.h : ℝ) ≠ 0 := by
              exact den_ne_zero_of_oracle_eq (T := (σ n).T) (x := X0.val) (y := Y0.val) hx hy (h := hor)
                (by exact Or.inl rfl)
            have hden' :
                (((((σ n).T.emit digitNeg).e : ℝ) * X0.val * Y0.val + (((σ n).T.emit digitNeg).f : ℝ) * X0.val +
                        (((σ n).T.emit digitNeg).g : ℝ) * Y0.val + (((σ n).T.emit digitNeg).h : ℝ))) ≠ 0 := by
              simpa [Tensor.emit, digitNeg] using hden
            have hlft :
                ((digitNeg.c : ℝ) * (Tensor.valueAt ((σ n).T.emit digitNeg) X0.val Y0.val) + (digitNeg.d : ℝ)) ≠ 0 := by
              simp [digitNeg]
            -- apply invariance and rewrite the RHS using `hrnext`
            simpa [r, digit_to_LFT, hout, hrnext] using
              (Tensor.emit_invariant (T := (σ n).T) (D := digitNeg) (x := X0.val) (y := Y0.val) hden' hden hlft)
    | zero =>
        have hstep' : VMStep (σ n) (some digitZero) s' := by
          simpa [digit_to_LFT, hout] using hstep
        cases hstep' with
        | emitZero hor =>
            have hden :
                ((σ n).T.e : ℝ) * X0.val * Y0.val + ((σ n).T.f : ℝ) * X0.val +
                    ((σ n).T.g : ℝ) * Y0.val + ((σ n).T.h : ℝ) ≠ 0 := by
              exact den_ne_zero_of_oracle_eq (T := (σ n).T) (x := X0.val) (y := Y0.val) hx hy (h := hor)
                (by exact Or.inr (Or.inl rfl))
            have hden' :
                (((((σ n).T.emit digitZero).e : ℝ) * X0.val * Y0.val + (((σ n).T.emit digitZero).f : ℝ) * X0.val +
                        (((σ n).T.emit digitZero).g : ℝ) * Y0.val + (((σ n).T.emit digitZero).h : ℝ))) ≠ 0 := by
              simpa [Tensor.emit, digitZero] using hden
            have hlft :
                ((digitZero.c : ℝ) * (Tensor.valueAt ((σ n).T.emit digitZero) X0.val Y0.val) + (digitZero.d : ℝ)) ≠ 0 := by
              simp [digitZero]
            simpa [r, digit_to_LFT, hout, hrnext] using
              (Tensor.emit_invariant (T := (σ n).T) (D := digitZero) (x := X0.val) (y := Y0.val) hden' hden hlft)
    | pos =>
        have hstep' : VMStep (σ n) (some digitPos) s' := by
          simpa [digit_to_LFT, hout] using hstep
        cases hstep' with
        | emitPos hor =>
            have hden :
                ((σ n).T.e : ℝ) * X0.val * Y0.val + ((σ n).T.f : ℝ) * X0.val +
                    ((σ n).T.g : ℝ) * Y0.val + ((σ n).T.h : ℝ) ≠ 0 := by
              exact den_ne_zero_of_oracle_eq (T := (σ n).T) (x := X0.val) (y := Y0.val) hx hy (h := hor)
                (by exact Or.inr (Or.inr rfl))
            have hden' :
                (((((σ n).T.emit digitPos).e : ℝ) * X0.val * Y0.val + (((σ n).T.emit digitPos).f : ℝ) * X0.val +
                        (((σ n).T.emit digitPos).g : ℝ) * Y0.val + (((σ n).T.emit digitPos).h : ℝ))) ≠ 0 := by
              simpa [Tensor.emit, digitPos] using hden
            have hlft :
                ((digitPos.c : ℝ) * (Tensor.valueAt ((σ n).T.emit digitPos) X0.val Y0.val) + (digitPos.d : ℝ)) ≠ 0 := by
              simp [digitPos]
            simpa [r, digit_to_LFT, hout, hrnext] using
              (Tensor.emit_invariant (T := (σ n).T) (D := digitPos) (x := X0.val) (y := Y0.val) hden' hden hlft)

  -- Residual values stay in `baseI`.
  have hr_baseI : ∀ n, r n ∈ baseI := by
    intro n
    rcases hσstep n with ⟨s', hstep, -⟩
    cases hout : out n with
    | neg =>
        have hstep' : VMStep (σ n) (some digitNeg) s' := by
          simpa [digit_to_LFT, hout] using hstep
        cases hstep' with
        | emitNeg hor =>
            have hrn := _root_.Computable.Mobius.Tensor.emitNeg_sound ((σ n).T) (x := X0.val) (y := Y0.val) hx.1 hx.2 hy.1 hy.2 hor
            have hrn' : (-1 : ℝ) ≤ r n ∧ r n ≤ 0 := by
              simpa [r, Tensor.valueAt] using hrn
            exact ⟨hrn'.1, by linarith [hrn'.2]⟩
    | zero =>
        have hstep' : VMStep (σ n) (some digitZero) s' := by
          simpa [digit_to_LFT, hout] using hstep
        cases hstep' with
        | emitZero hor =>
            have hrn := _root_.Computable.Mobius.Tensor.emitZero_sound ((σ n).T) (x := X0.val) (y := Y0.val) hx.1 hx.2 hy.1 hy.2 hor
            have hrn' : (-1 / 2 : ℝ) ≤ r n ∧ r n ≤ (1 / 2 : ℝ) := by
              simpa [r, Tensor.valueAt] using hrn
            exact ⟨by linarith [hrn'.1], by linarith [hrn'.2]⟩
    | pos =>
        have hstep' : VMStep (σ n) (some digitPos) s' := by
          simpa [digit_to_LFT, hout] using hstep
        cases hstep' with
        | emitPos hor =>
            have hrn := _root_.Computable.Mobius.Tensor.emitPos_sound ((σ n).T) (x := X0.val) (y := Y0.val) hx.1 hx.2 hy.1 hy.2 hor
            have hrn' : (0 : ℝ) ≤ r n ∧ r n ≤ 1 := by
              simpa [r, Tensor.valueAt] using hrn
            exact ⟨by linarith [hrn'.1], hrn'.2⟩

  -- Membership in all `imageSet`s: `r 0` is in every prefix image.
  have hr0_mem : r 0 ∈ ⋂ n, imageSet (MobiusReal.fromStream out) n := by
    let S : LFTStream := (MobiusReal.fromStream out).stream
    have happly : ∀ n, LFT.apply (partialComp S n) (r (n + 1)) = r 0 := by
      intro n
      induction n with
      | zero =>
          -- `partialComp S 0 = S 0`, and `hrec 0` is exactly the desired equation.
          simpa [S, MobiusReal.fromStream, lftStreamOfDigits, digit_to_LFT, partialComp, partialCompFrom, r] using (hrec 0).symm
      | succ n ih =>
          -- unfold `partialComp` one step and use `LFT.apply_comp`
          have hpc :
              partialComp S (n + 1) = (partialComp S n).comp (S (n + 1)) := by
            simp [partialComp, partialCompFrom]
          have hden_inner :
              (((S (n + 1)).c : ℝ) * r (n + 2) + ((S (n + 1)).d : ℝ)) ≠ 0 := by
            -- digits have `c = 0` and `d = 2`
            cases hout : out (n + 1) <;>
              simp [S, MobiusReal.fromStream, lftStreamOfDigits, digit_to_LFT, hout, digitNeg, digitZero, digitPos]
          have hmem : LFT.apply (S (n + 1)) (r (n + 2)) ∈ baseI := by
            -- by `hrec (n+1)`, this is `r (n+1)` and `hr_baseI` gives membership
            have : LFT.apply (S (n + 1)) (r (n + 2)) = r (n + 1) := by
              simpa [S, MobiusReal.fromStream, lftStreamOfDigits, digit_to_LFT, r] using (hrec (n + 1)).symm
            simpa [this] using hr_baseI (n + 1)
          have hden_outer :
              (((partialComp S n).c : ℝ) * (LFT.apply (S (n + 1)) (r (n + 2))) + ((partialComp S n).d : ℝ)) ≠ 0 := by
            exact LFT.denom_ne_zero_of_NoPoleOnBase (partialComp S n)
              (x := LFT.apply (S (n + 1)) (r (n + 2))) hmem
              (IsContractive.no_poles (MobiusReal.fromStream out).contractive n)
          have happ :
              LFT.apply (partialComp S (n + 1)) (r (n + 2)) =
                LFT.apply (partialComp S n) (LFT.apply (S (n + 1)) (r (n + 2))) := by
            simpa [hpc] using
              (LFT.apply_comp (partialComp S n) (S (n + 1)) (r (n + 2)) hden_inner hden_outer)
          -- replace the inner application by `r (n+1)` using `hrec (n+1)`, then apply IH
          have : LFT.apply (partialComp S n) (LFT.apply (S (n + 1)) (r (n + 2))) =
              LFT.apply (partialComp S n) (r (n + 1)) := by
            have : LFT.apply (S (n + 1)) (r (n + 2)) = r (n + 1) := by
              simpa [S, MobiusReal.fromStream, lftStreamOfDigits, digit_to_LFT, r] using (hrec (n + 1)).symm
            simp [this]
          -- finish
          simpa [happ] using (by simpa [this] using ih)

    refine Set.mem_iInter.2 (fun n => ?_)
    exact ⟨r (n + 1), hr_baseI (n + 1), happly n⟩

  -- conclude by uniqueness for the digit stream denotation
  have : r 0 = (MobiusReal.fromStream out).val :=
    (MobiusReal.val_eq_of_mem_iInter_imageSet (MobiusReal.fromStream out) hr0_mem)
  simpa [r, hσ0] using this.symm

/-! ## Prefix traces and the original `VMStep_n`-style statement -/

namespace Trace

/--
`VMStepsDigits out k n s t` means: starting in `s`, we make exactly `n` VM steps,
and the `i`-th step emits the digit `out (k+i)` (so all labels are `some _`).
-/
inductive VMStepsDigits (out : DigitStream) : (k : ℕ) → (n : ℕ) → VMState → VMState → Prop
  | refl (k) (s) : VMStepsDigits out k 0 s s
  | step {k n s s1 t}
      (h : VMStep s (some (digit_to_LFT (out k))) s1)
      (ht : VMStepsDigits out (k + 1) n s1 t) :
      VMStepsDigits out k (n + 1) s t

lemma emit_step_unique (s : VMState) (d : Digit) {s1 s2 : VMState}
    (h1 : VMStep s (some (digit_to_LFT d)) s1)
    (h2 : VMStep s (some (digit_to_LFT d)) s2) : s1 = s2 := by
  cases d <;> cases h1 <;> cases h2 <;> rfl

lemma steps_unique (out : DigitStream) (k n : ℕ) (s : VMState) {t1 t2 : VMState}
    (h1 : VMStepsDigits out k n s t1) (h2 : VMStepsDigits out k n s t2) : t1 = t2 := by
  induction n generalizing k s t1 t2 with
  | zero =>
      cases h1
      cases h2
      rfl
  | succ n ih =>
      cases h1 with
      | step h1a h1b =>
        cases h2 with
        | step h2a h2b =>
          have hs : _ := emit_step_unique (s := s) (d := out k) h1a h2a
          subst hs
          exact ih (k := k + 1) (s := _) h1b h2b

lemma snoc {out : DigitStream} {k n : ℕ} {s t : VMState} :
    VMStepsDigits out k (n + 1) s t →
      ∃ s', VMStepsDigits out k n s s' ∧ VMStep s' (some (digit_to_LFT (out (k + n)))) t := by
  intro h
  induction n generalizing k s t with
  | zero =>
      cases h with
      | step hstep hrefl =>
        cases hrefl
        -- n = 0, so `k+n = k`
        refine ⟨s, VMStepsDigits.refl (out := out) k s, ?_⟩
        simpa using hstep
  | succ n ih =>
      cases h with
      | step h0 ht =>
        rcases ih (k := k + 1) (s := _) (t := t) ht with ⟨s', hs', hlast⟩
        refine ⟨s', ?_, ?_⟩
        · exact VMStepsDigits.step (out := out) (k := k) (n := n) (s := s) (s1 := _) (t := s') h0 hs'
        · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlast

/-!
This is the rigorous version of your sketched `VMStep_n` premise: it says
“there is a run of length `n+1` that emits exactly the first `n+1` digits of `out`,
and `l` is the last label”.
-/
def VMStep_n (out : DigitStream) (n : ℕ) (s₀ : VMState) (l : Option LFT) (s' : VMState) : Prop :=
  VMStepsDigits out 0 (n + 1) s₀ s' ∧ l = some (digit_to_LFT (out n))

theorem vm_soundness_of_VMStep_n (s₀ : VMState) (X Y : MobiusReal) (out : DigitStream) :
    (∀ n, ∃ l s', VMStep_n out n s₀ l s' ∧ l = some (digit_to_LFT (out n))) →
    (MobiusReal.fromStream out).val =
      Tensor.valueAt s₀.T (MobiusReal.drop X s₀.idx_x).val (MobiusReal.drop Y s₀.idx_y).val := by
  intro hpref
  -- existence of a state after each nonempty prefix
  have hex : ∀ n, ∃ s', VMStepsDigits out 0 (n + 1) s₀ s' := by
    intro n
    rcases hpref n with ⟨l, s', ⟨hs, -⟩⟩
    rcases hs with ⟨hsteps, -⟩
    exact ⟨s', hsteps⟩

  -- define the canonical state after `n` digits
  let σ : ℕ → VMState
    | 0 => s₀
    | n + 1 => Classical.choose (hex n)
  have hσ0 : σ 0 = s₀ := rfl
  have hσpref : ∀ n, VMStepsDigits out 0 n s₀ (σ n) := by
    intro n
    cases n with
    | zero =>
        simpa [σ] using VMStepsDigits.refl (out := out) 0 s₀
    | succ n =>
        -- `σ (n+1)` was chosen from `hex n`
        simpa [σ] using (Classical.choose_spec (hex n))

  -- show `σ` is a coherent step-by-step trace
  have hσstep : ∀ n, ∃ s', VMStep (σ n) (some (digit_to_LFT (out n))) s' ∧ σ (n + 1) = s' := by
    intro n
    -- decompose the chosen prefix of length `n+1` into `n`-prefix + last step
    have hfull : VMStepsDigits out 0 (n + 1) s₀ (σ (n + 1)) := by
      simpa [σ] using (Classical.choose_spec (hex n))
    rcases snoc (k := 0) (n := n) (s := s₀) (t := σ (n + 1)) hfull with ⟨s', hs', hlast⟩
    -- identify `s'` with `σ n` by uniqueness of prefixes
    have : s' = σ n := steps_unique out 0 n s₀ hs' (hσpref n)
    subst this
    refine ⟨σ (n + 1), ?_, rfl⟩
    simpa using hlast

  -- now apply the proved `vm_soundness`
  exact vm_soundness (s₀ := s₀) (X := X) (Y := Y) (out := out) ⟨σ, hσ0, hσstep⟩

end Trace

/-! ## General traces with absorption (`none` labels) -/

namespace GeneralTrace

noncomputable def stateValue (X Y : MobiusReal) (s : VMState) : ℝ :=
  Tensor.valueAt s.T (MobiusReal.drop X s.idx_x).val (MobiusReal.drop Y s.idx_y).val

def SafeAt (X Y : MobiusReal) (s : VMState) : Prop :=
  Tensor.denAt s.T (MobiusReal.drop X s.idx_x).val (MobiusReal.drop Y s.idx_y).val ≠ 0

inductive VMStepXY (X Y : MobiusReal) : VMState → Option LFT → VMState → Prop
  | emitNeg {s : VMState} (h : s.T.oracle = Tensor.EmitDecision.neg) :
      VMStepXY X Y s (some digitNeg) { s with T := s.T.emit digitNeg }
  | emitZero {s : VMState} (h : s.T.oracle = Tensor.EmitDecision.zero) :
      VMStepXY X Y s (some digitZero) { s with T := s.T.emit digitZero }
  | emitPos {s : VMState} (h : s.T.oracle = Tensor.EmitDecision.pos) :
      VMStepXY X Y s (some digitPos) { s with T := s.T.emit digitPos }
  | absorbX {s : VMState}
      (h1 : s.T.oracle = Tensor.EmitDecision.absorb)
      (h2 : s.absorb_x_next = true) :
      VMStepXY X Y s none { s with
        T := s.T.absorbX (X.stream s.idx_x)
        idx_x := s.idx_x + 1
        absorb_x_next := false }
  | absorbY {s : VMState}
      (h1 : s.T.oracle = Tensor.EmitDecision.absorb)
      (h2 : s.absorb_x_next = false) :
      VMStepXY X Y s none { s with
        T := s.T.absorbY (Y.stream s.idx_y)
        idx_y := s.idx_y + 1
        absorb_x_next := true }

lemma drop_val_mem_baseI (X : MobiusReal) (k : ℕ) : (MobiusReal.drop X k).val ∈ baseI :=
  MobiusReal.val_mem_baseI (MobiusReal.drop X k)

lemma oracle_eq_of_step_neg
    (X Y : MobiusReal) {s s' : VMState}
    (h : VMStepXY X Y s (some digitNeg) s') :
    s.T.oracle = Tensor.EmitDecision.neg := by
  cases h with
  | emitNeg hor => simpa using hor

lemma oracle_eq_of_step_zero
    (X Y : MobiusReal) {s s' : VMState}
    (h : VMStepXY X Y s (some digitZero) s') :
    s.T.oracle = Tensor.EmitDecision.zero := by
  cases h with
  | emitZero hor => simpa using hor

lemma oracle_eq_of_step_pos
    (X Y : MobiusReal) {s s' : VMState}
    (h : VMStepXY X Y s (some digitPos) s') :
    s.T.oracle = Tensor.EmitDecision.pos := by
  cases h with
  | emitPos hor => simpa using hor

lemma safe_den_old_new_of_absorbX (X Y : MobiusReal) (s : VMState) :
    SafeAt X Y s →
    SafeAt X Y { s with
      T := s.T.absorbX (X.stream s.idx_x)
      idx_x := s.idx_x + 1
      absorb_x_next := false } →
    (Tensor.denAt s.T ((X.stream s.idx_x).apply (MobiusReal.drop X (s.idx_x + 1)).val)
        (MobiusReal.drop Y s.idx_y).val ≠ 0) ∧
      (Tensor.denAt (s.T.absorbX (X.stream s.idx_x)) (MobiusReal.drop X (s.idx_x + 1)).val
        (MobiusReal.drop Y s.idx_y).val ≠ 0) := by
  intro hs hs'
  -- rewrite the old `x`-value using `val_drop_succ`
  have hx : (MobiusReal.drop X s.idx_x).val =
      LFT.apply (X.stream s.idx_x) (MobiusReal.drop X (s.idx_x + 1)).val := by
    simpa [MobiusReal.drop, Nat.add_assoc] using (MobiusReal.val_drop_succ X s.idx_x)
  constructor
  · -- old denominator at `(apply M xTail, y)` is nonzero
    simpa [SafeAt, Tensor.denAt, hx] using hs
  · -- new denominator is exactly `SafeAt` of the next state
    simpa [SafeAt, Tensor.denAt] using hs'

lemma stateValue_step_none
    (X Y : MobiusReal) {s s' : VMState}
    (h : VMStepXY X Y s none s') (hs : SafeAt X Y s) (hs' : SafeAt X Y s') :
    stateValue X Y s = stateValue X Y s' := by
  cases h with
  | absorbX h1 h2 =>
      -- abbreviate the absorbed LFT and the tail value
      set M : LFT := X.stream s.idx_x
      set xTail : ℝ := (MobiusReal.drop X (s.idx_x + 1)).val
      set yVal : ℝ := (MobiusReal.drop Y s.idx_y).val
      have hxTail_mem : xTail ∈ baseI := by simpa [xTail] using drop_val_mem_baseI X (s.idx_x + 1)
      have hMden : ((M.c : ℝ) * xTail + (M.d : ℝ)) ≠ 0 := by
        exact LFT.denom_ne_zero_of_NoPoleOnBase M (x := xTail) hxTail_mem
          (IsContractive.no_poles_step X.contractive s.idx_x)
      have hsden :
          Tensor.denAt s.T (LFT.apply M xTail) yVal ≠ 0 ∧ Tensor.denAt (s.T.absorbX M) xTail yVal ≠ 0 := by
        -- feed safety into both denominators
        have hs'': SafeAt X Y { s with
          T := s.T.absorbX (X.stream s.idx_x)
          idx_x := s.idx_x + 1
          absorb_x_next := false } := by
            simpa using hs'
        simpa [M, xTail, yVal] using (safe_den_old_new_of_absorbX X Y s hs hs'')
      have habs :=
        Tensor.absorbX_invariant (T := s.T) (M := M) (x := xTail) (y := yVal)
          hMden hsden.1 hsden.2
      -- turn it into a statement about `stateValue`
      -- left side uses `X.drop idx_x` which is `M.apply xTail`
      have hx :
          (MobiusReal.drop X s.idx_x).val = LFT.apply M xTail := by
        simpa [M, xTail, MobiusReal.drop, Nat.add_assoc] using (MobiusReal.val_drop_succ X s.idx_x)
      simpa [stateValue, Tensor.valueAt, xTail, yVal, M, hx] using habs
  | absorbY h1 h2 =>
      -- symmetric argument via `absorbY_invariant`
      set M : LFT := Y.stream s.idx_y
      set yTail : ℝ := (MobiusReal.drop Y (s.idx_y + 1)).val
      set xVal : ℝ := (MobiusReal.drop X s.idx_x).val
      have hyTail_mem : yTail ∈ baseI := by simpa [yTail] using drop_val_mem_baseI Y (s.idx_y + 1)
      have hMden : ((M.c : ℝ) * yTail + (M.d : ℝ)) ≠ 0 := by
        exact LFT.denom_ne_zero_of_NoPoleOnBase M (x := yTail) hyTail_mem
          (IsContractive.no_poles_step Y.contractive s.idx_y)
      have hy :
          (MobiusReal.drop Y s.idx_y).val = LFT.apply M yTail := by
        simpa [M, yTail, MobiusReal.drop, Nat.add_assoc] using (MobiusReal.val_drop_succ Y s.idx_y)
      have hsden_old : Tensor.denAt s.T xVal (LFT.apply M yTail) ≠ 0 := by
        simpa [SafeAt, Tensor.denAt, hy, xVal] using hs
      have hsden_new : Tensor.denAt (s.T.absorbY M) xVal yTail ≠ 0 := by
        -- safety at `s'`
        simpa [SafeAt, Tensor.denAt, xVal, yTail] using hs'
      have habs :=
        Tensor.absorbY_invariant (T := s.T) (M := M) (x := xVal) (y := yTail)
          hMden hsden_old hsden_new
      -- rewrite `stateValue` and finish
      simpa [stateValue, Tensor.valueAt, xVal, yTail, hy, M] using habs

lemma stateValue_step_some
    (X Y : MobiusReal) {s s' : VMState} {D : LFT}
    (h : VMStepXY X Y s (some D) s') (hs : SafeAt X Y s) (hs' : SafeAt X Y s') :
    stateValue X Y s = LFT.apply D (stateValue X Y s') := by
  cases h with
  | emitNeg hor =>
      -- use `emit_invariant` plus safety (old/new denominators) and digit denominator
      have hx : (MobiusReal.drop X s.idx_x).val ∈ baseI := drop_val_mem_baseI X s.idx_x
      have hy : (MobiusReal.drop Y s.idx_y).val ∈ baseI := drop_val_mem_baseI Y s.idx_y
      have hden_old : Tensor.denAt s.T (MobiusReal.drop X s.idx_x).val (MobiusReal.drop Y s.idx_y).val ≠ 0 := by
        simpa [SafeAt] using hs
      have hden_new : Tensor.denAt (s.T.emit digitNeg) (MobiusReal.drop X s.idx_x).val (MobiusReal.drop Y s.idx_y).val ≠ 0 := by
        simpa [SafeAt] using hs'
      have hlft : ((digitNeg.c : ℝ) * Tensor.valueAt (s.T.emit digitNeg)
            (MobiusReal.drop X s.idx_x).val (MobiusReal.drop Y s.idx_y).val + (digitNeg.d : ℝ)) ≠ 0 := by
        simp [digitNeg]
      -- apply `emit_invariant` and simplify
      simpa [stateValue, SafeAt] using
        (Tensor.emit_invariant (T := s.T) (D := digitNeg)
          (x := (MobiusReal.drop X s.idx_x).val) (y := (MobiusReal.drop Y s.idx_y).val)
          (by simpa [Tensor.denAt] using hden_new) (by simpa [Tensor.denAt] using hden_old) hlft)
  | emitZero hor =>
      have hden_old : Tensor.denAt s.T (MobiusReal.drop X s.idx_x).val (MobiusReal.drop Y s.idx_y).val ≠ 0 := by
        simpa [SafeAt] using hs
      have hden_new : Tensor.denAt (s.T.emit digitZero) (MobiusReal.drop X s.idx_x).val (MobiusReal.drop Y s.idx_y).val ≠ 0 := by
        simpa [SafeAt] using hs'
      have hlft : ((digitZero.c : ℝ) * Tensor.valueAt (s.T.emit digitZero)
            (MobiusReal.drop X s.idx_x).val (MobiusReal.drop Y s.idx_y).val + (digitZero.d : ℝ)) ≠ 0 := by
        simp [digitZero]
      simpa [stateValue, SafeAt] using
        (Tensor.emit_invariant (T := s.T) (D := digitZero)
          (x := (MobiusReal.drop X s.idx_x).val) (y := (MobiusReal.drop Y s.idx_y).val)
          (by simpa [Tensor.denAt] using hden_new) (by simpa [Tensor.denAt] using hden_old) hlft)
  | emitPos hor =>
      have hden_old : Tensor.denAt s.T (MobiusReal.drop X s.idx_x).val (MobiusReal.drop Y s.idx_y).val ≠ 0 := by
        simpa [SafeAt] using hs
      have hden_new : Tensor.denAt (s.T.emit digitPos) (MobiusReal.drop X s.idx_x).val (MobiusReal.drop Y s.idx_y).val ≠ 0 := by
        simpa [SafeAt] using hs'
      have hlft : ((digitPos.c : ℝ) * Tensor.valueAt (s.T.emit digitPos)
            (MobiusReal.drop X s.idx_x).val (MobiusReal.drop Y s.idx_y).val + (digitPos.d : ℝ)) ≠ 0 := by
        simp [digitPos]
      simpa [stateValue, SafeAt] using
        (Tensor.emit_invariant (T := s.T) (D := digitPos)
          (x := (MobiusReal.drop X s.idx_x).val) (y := (MobiusReal.drop Y s.idx_y).val)
          (by simpa [Tensor.denAt] using hden_new) (by simpa [Tensor.denAt] using hden_old) hlft)

structure EmitSchedule (ℓ : ℕ → Option LFT) (out : DigitStream) where
  f : ℕ → ℕ
  strictMono : StrictMono f
  emits : ∀ n, ℓ (f n) = some (digit_to_LFT (out n))
  prefixNone : ∀ i, i < f 0 → ℓ i = none
  noneBetween : ∀ n i, f n < i → i < f (n + 1) → ℓ i = none

theorem vm_soundness_with_absorb
    (X Y : MobiusReal) (s₀ : VMState) (out : DigitStream)
    (σ : ℕ → VMState) (ℓ : ℕ → Option LFT)
    (hσ0 : σ 0 = s₀)
    (hstep : ∀ i, VMStepXY X Y (σ i) (ℓ i) (σ (i + 1)))
    (hsafe : ∀ i, SafeAt X Y (σ i))
    (sched : EmitSchedule ℓ out) :
    (MobiusReal.fromStream out).val = stateValue X Y s₀ := by
  classical
  -- Abbreviate the semantic value along the whole trace.
  let R : ℕ → ℝ := fun i => stateValue X Y (σ i)

  have R_none : ∀ i, ℓ i = none → R i = R (i + 1) := by
    intro i hi
    have h := hstep i
    rw [hi] at h
    simpa [R] using
      stateValue_step_none (X := X) (Y := Y) (s := σ i) (s' := σ (i + 1))
        (h := h) (hs := hsafe i) (hs' := hsafe (i + 1))

  have R_emit : ∀ i D, ℓ i = some D → R i = LFT.apply D (R (i + 1)) := by
    intro i D hi
    have h := hstep i
    rw [hi] at h
    simpa [R] using
      stateValue_step_some (X := X) (Y := Y) (s := σ i) (s' := σ (i + 1))
        (D := D) (h := h) (hs := hsafe i) (hs' := hsafe (i + 1))

  -- Collapse `R` across a `none`-only interval.
  have R_eq_of_none_between :
      ∀ {a b}, a ≤ b → (∀ i, a ≤ i → i < b → ℓ i = none) → R a = R b := by
    intro a b hab hnone
    have haux : ∀ a k, (∀ i, a ≤ i → i < a + k → ℓ i = none) → R a = R (a + k) := by
      intro a k
      induction k generalizing a with
      | zero =>
          intro hnone'
          simp
      | succ k ih =>
          intro hnone'
          have hlt : a < a + (k + 1) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              Nat.lt_succ_of_le (Nat.le_add_right a k)
          have h0 : ℓ a = none := hnone' a le_rfl hlt
          have hstep' : R a = R (a + 1) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using R_none a h0
          have hrest : R (a + 1) = R ((a + 1) + k) := by
            apply ih
            intro i hi1 hi2
            exact hnone' i (Nat.le_trans (Nat.le_succ a) hi1)
              (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi2)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep'.trans hrest
    have : R a = R (a + (b - a)) := by
      apply haux
      intro i hi1 hi2
      exact hnone i hi1 (by simpa [Nat.add_sub_of_le hab] using hi2)
    simpa [Nat.add_sub_of_le hab] using this

  -- Define the subsequence at emission indices.
  let f := sched.f
  let A : ℕ → ℝ := fun n => R (f n)

  have A_rec : ∀ n, A n = LFT.apply (digit_to_LFT (out n)) (A (n + 1)) := by
    intro n
    have hem := sched.emits n
    have hR : R (f n) = LFT.apply (digit_to_LFT (out n)) (R (f n + 1)) :=
      R_emit (i := f n) (D := digit_to_LFT (out n)) hem
    -- between `(f n)+1` and `f(n+1)` all labels are `none`
    have hcollapse : R (f n + 1) = R (f (n + 1)) := by
      apply (R_eq_of_none_between (a := f n + 1) (b := f (n + 1))
        (by exact Nat.succ_le_of_lt (sched.strictMono (Nat.lt_succ_self n))))
      intro i hi1 hi2
      -- show `f n < i < f(n+1)`
      have hlt1 : f n < i := lt_of_lt_of_le (Nat.lt_succ_self _) hi1
      exact sched.noneBetween n i hlt1 hi2
    have : LFT.apply (digit_to_LFT (out n)) (R (f n + 1)) =
        LFT.apply (digit_to_LFT (out n)) (A (n + 1)) := by
      -- collapse and rewrite `A (n+1) = R (f (n+1))`
      simpa [A] using congrArg (fun t => LFT.apply (digit_to_LFT (out n)) t) hcollapse
    simpa [A] using hR.trans this

  -- `A 0` equals the initial state value (prefix is `none`).
  have A0_eq : A 0 = stateValue X Y s₀ := by
    have hpref : R 0 = R (f 0) :=
      R_eq_of_none_between (a := 0) (b := f 0) (Nat.zero_le _) (by
        intro i hi1 hi2
        exact sched.prefixNone i hi2)
    calc
      A 0 = R (f 0) := by simp [A]
      _ = R 0 := hpref.symm
      _ = stateValue X Y s₀ := by simp [R, hσ0]

  -- Now reuse the emission-only argument from `vm_soundness` specialized to the recursion `A_rec`.
  -- We show `A 0` lies in the intersection of digit-stream image sets, hence equals the denotation.
  have hmem : A 0 ∈ ⋂ n, imageSet (MobiusReal.fromStream out) n := by
    -- First, show all `A n` stay in `baseI` using oracle soundness at the scheduled emission points.
    have A_mem_baseI : ∀ n, A n ∈ baseI := by
      intro n
      set i : ℕ := f n
      set s : VMState := σ i
      have hxmem : (MobiusReal.drop X s.idx_x).val ∈ baseI := drop_val_mem_baseI X s.idx_x
      have hymem : (MobiusReal.drop Y s.idx_y).val ∈ baseI := drop_val_mem_baseI Y s.idx_y
      have hx1 : (-1 : ℝ) ≤ (MobiusReal.drop X s.idx_x).val := hxmem.1
      have hx2 : (MobiusReal.drop X s.idx_x).val ≤ (1 : ℝ) := hxmem.2
      have hy1 : (-1 : ℝ) ≤ (MobiusReal.drop Y s.idx_y).val := hymem.1
      have hy2 : (MobiusReal.drop Y s.idx_y).val ≤ (1 : ℝ) := hymem.2
      have hlab : ℓ i = some (digit_to_LFT (out n)) := by simpa [i] using sched.emits n
      have hstep_i : VMStepXY X Y (σ i) (ℓ i) (σ (i + 1)) := hstep i
      cases hout : out n with
      | neg =>
          have hlab' : ℓ i = some digitNeg := by simp [hlab, digit_to_LFT, hout]
          have hstep_neg : VMStepXY X Y (σ i) (some digitNeg) (σ (i + 1)) := by
            simpa [hlab'] using hstep_i
          have hor := oracle_eq_of_step_neg X Y hstep_neg
          have hbounds :=
            (_root_.Computable.Mobius.Tensor.emitNeg_sound (T := (σ i).T)
              (x := (MobiusReal.drop X (σ i).idx_x).val) (y := (MobiusReal.drop Y (σ i).idx_y).val)
              hx1 hx2 hy1 hy2) hor
          have hle1 : Tensor.apply (σ i).T (MobiusReal.drop X (σ i).idx_x).val
              (MobiusReal.drop Y (σ i).idx_y).val ≤ (1 : ℝ) := by linarith [hbounds.2]
          simpa [A, R, i, s, stateValue, Tensor.valueAt, baseI] using And.intro hbounds.1 hle1
      | zero =>
          have hlab' : ℓ i = some digitZero := by simp [hlab, digit_to_LFT, hout]
          have hstep_zero : VMStepXY X Y (σ i) (some digitZero) (σ (i + 1)) := by
            simpa [hlab'] using hstep_i
          have hor := oracle_eq_of_step_zero X Y hstep_zero
          have hbounds :=
            (_root_.Computable.Mobius.Tensor.emitZero_sound (T := (σ i).T)
              (x := (MobiusReal.drop X (σ i).idx_x).val) (y := (MobiusReal.drop Y (σ i).idx_y).val)
              hx1 hx2 hy1 hy2) hor
          -- `emitZero_sound` returns `-1/2 ≤ ... ≤ 1/2`; this implies membership in `[-1,1]`.
          have hlow : (-1 : ℝ) ≤ Tensor.apply (σ i).T (MobiusReal.drop X (σ i).idx_x).val
              (MobiusReal.drop Y (σ i).idx_y).val := by linarith [hbounds.1]
          have hhigh : Tensor.apply (σ i).T (MobiusReal.drop X (σ i).idx_x).val
              (MobiusReal.drop Y (σ i).idx_y).val ≤ (1 : ℝ) := by linarith [hbounds.2]
          simpa [A, R, i, s, stateValue, Tensor.valueAt, baseI] using And.intro hlow hhigh
      | pos =>
          have hlab' : ℓ i = some digitPos := by simp [hlab, digit_to_LFT, hout]
          have hstep_pos : VMStepXY X Y (σ i) (some digitPos) (σ (i + 1)) := by
            simpa [hlab'] using hstep_i
          have hor := oracle_eq_of_step_pos X Y hstep_pos
          have hbounds :=
            (_root_.Computable.Mobius.Tensor.emitPos_sound (T := (σ i).T)
              (x := (MobiusReal.drop X (σ i).idx_x).val) (y := (MobiusReal.drop Y (σ i).idx_y).val)
              hx1 hx2 hy1 hy2) hor
          have hge1 : (-1 : ℝ) ≤ Tensor.apply (σ i).T (MobiusReal.drop X (σ i).idx_x).val
              (MobiusReal.drop Y (σ i).idx_y).val := by linarith [hbounds.1]
          simpa [A, R, i, s, stateValue, Tensor.valueAt, baseI] using And.intro hge1 hbounds.2

    let S : LFTStream := (MobiusReal.fromStream out).stream
    have happly : ∀ n, LFT.apply (partialComp S n) (A (n + 1)) = A 0 := by
      intro n
      induction n with
      | zero =>
          -- `partialComp S 0 = S 0`
          simpa [S, MobiusReal.fromStream, lftStreamOfDigits, partialComp, partialCompFrom, A] using (A_rec 0).symm
      | succ n ih =>
          have hpc : partialComp S (n + 1) = (partialComp S n).comp (S (n + 1)) := by
            simp [partialComp, partialCompFrom]
          have hden_inner :
              (((S (n + 1)).c : ℝ) * A (n + 2) + ((S (n + 1)).d : ℝ)) ≠ 0 := by
            cases hout : out (n + 1) <;>
              simp [S, MobiusReal.fromStream, lftStreamOfDigits, digit_to_LFT, hout, digitNeg, digitZero, digitPos]
          have hmemBase : LFT.apply (S (n + 1)) (A (n + 2)) ∈ baseI := by
            -- digit LFTs map `baseI` into `baseI`
            have hmaps := DigitStream.digit_to_LFT_maps_baseI (out (n + 1))
            have hA : A (n + 2) ∈ baseI := A_mem_baseI (n + 2)
            simpa [S, MobiusReal.fromStream, lftStreamOfDigits] using hmaps hA
          have hden_outer :
              (((partialComp S n).c : ℝ) * LFT.apply (S (n + 1)) (A (n + 2)) + ((partialComp S n).d : ℝ)) ≠ 0 := by
            exact LFT.denom_ne_zero_of_NoPoleOnBase (partialComp S n)
              (x := LFT.apply (S (n + 1)) (A (n + 2))) hmemBase
              (IsContractive.no_poles (MobiusReal.fromStream out).contractive n)
          have happ :
              LFT.apply (partialComp S (n + 1)) (A (n + 2)) =
                LFT.apply (partialComp S n) (LFT.apply (S (n + 1)) (A (n + 2))) := by
            simpa [hpc] using
              (LFT.apply_comp (partialComp S n) (S (n + 1)) (A (n + 2)) hden_inner hden_outer)
          -- replace inner by `A(n+1)` via recursion
          have : LFT.apply (S (n + 1)) (A (n + 2)) = A (n + 1) := by
            simpa [S, MobiusReal.fromStream, lftStreamOfDigits, digit_to_LFT, A] using (A_rec (n + 1)).symm
          simpa [happ, this] using ih

    refine Set.mem_iInter.2 (fun n => ?_)
    refine ⟨A (n + 1), A_mem_baseI (n + 1), ?_⟩
    exact happly n

  have : A 0 = (MobiusReal.fromStream out).val :=
    MobiusReal.val_eq_of_mem_iInter_imageSet (MobiusReal.fromStream out) hmem
  -- conclude, rewriting `A 0`
  simpa [A0_eq] using this.symm

end GeneralTrace

end Mobius
end Computable

