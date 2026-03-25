import HopfieldNet.CReals.Mobius.Eval
import HopfieldNet.CReals.CRealCCLOF
import HopfieldNet.CReals.SignedDigit.Operations
import HopfieldNet.CReals.SignedDigit.SDReal

namespace Computable
namespace Mobius

open scoped BigOperators

abbrev SDStream := Computable.CReal.SignedDigit.SDStream
abbrev SDReal := Computable.CReal.SignedDigit.SDReal

def toSDStream (out : DigitStream) : SDStream := out

def toCReal (out : DigitStream) : Computable.CReal :=
  Computable.CReal.SignedDigit.toCReal (toSDStream out)

/-- Reinterpret a Möbius digit stream as a signed-digit real with a fixed binary exponent. -/
def toSDReal (exp : ℤ) (out : DigitStream) : SDReal :=
  ⟨exp, toSDStream out⟩

/-- Interpret a Möbius digit stream as a `CReal` after scaling by `2^k`. -/
def toCRealScaled (k : ℕ) (out : DigitStream) : Computable.CReal :=
  Computable.CReal.SignedDigit.SDReal.toCReal (toSDReal (Int.ofNat k) out)

namespace DigitStream

/-- Constant zero digit stream. -/
def zeroDigits : DigitStream := fun _ => .zero

/-- Constant `+1` digit stream. -/
def oneDigits : DigitStream := fun _ => .pos

/-- Constant `-1` digit stream. -/
def minusOneDigits : DigitStream := fun _ => .neg

/-- Pointwise digit negation, reusing the signed-digit stream negation. -/
def negStream (out : DigitStream) : DigitStream :=
  Computable.CReal.SignedDigit.negStream out

@[simp] theorem partialSum_zeroDigits (n : ℕ) :
    Computable.CReal.SignedDigit.partialSum zeroDigits n = 0 := by
  simp [zeroDigits, Computable.CReal.SignedDigit.partialSum, Computable.CReal.SignedDigit.coeff]

theorem partialSum_oneDigits (n : ℕ) :
    Computable.CReal.SignedDigit.partialSum oneDigits n = 1 - (1 / 2 : ℚ) ^ (n + 1) := by
  induction n with
  | zero =>
      norm_num [oneDigits, Computable.CReal.SignedDigit.partialSum, Computable.CReal.SignedDigit.coeff]
  | succ n ih =>
      calc
        Computable.CReal.SignedDigit.partialSum oneDigits (n + 1)
            = ∑ x ∈ Finset.range (n + 1), Computable.CReal.SignedDigit.coeff oneDigits x +
                Computable.CReal.SignedDigit.coeff oneDigits (n + 1) := by
                  rw [Computable.CReal.SignedDigit.partialSum, Finset.sum_range_succ]
        _ = Computable.CReal.SignedDigit.partialSum oneDigits n +
              Computable.CReal.SignedDigit.coeff oneDigits (n + 1) := by
              rfl
        _ = (1 - (1 / 2 : ℚ) ^ (n + 1)) + (1 / 2 : ℚ) ^ (n + 2) := by
              rw [ih]
              simp [Computable.CReal.SignedDigit.coeff, oneDigits, pow_succ]
        _ = 1 - (1 / 2 : ℚ) ^ (n + 2) := by ring

theorem partialSum_minusOneDigits (n : ℕ) :
    Computable.CReal.SignedDigit.partialSum minusOneDigits n = -1 + (1 / 2 : ℚ) ^ (n + 1) := by
  induction n with
  | zero =>
      norm_num [minusOneDigits, Computable.CReal.SignedDigit.partialSum, Computable.CReal.SignedDigit.coeff]
  | succ n ih =>
      calc
        Computable.CReal.SignedDigit.partialSum minusOneDigits (n + 1)
            = ∑ x ∈ Finset.range (n + 1), Computable.CReal.SignedDigit.coeff minusOneDigits x +
                Computable.CReal.SignedDigit.coeff minusOneDigits (n + 1) := by
                  rw [Computable.CReal.SignedDigit.partialSum, Finset.sum_range_succ]
        _ = Computable.CReal.SignedDigit.partialSum minusOneDigits n +
              Computable.CReal.SignedDigit.coeff minusOneDigits (n + 1) := by
              rfl
        _ = (-1 + (1 / 2 : ℚ) ^ (n + 1)) + (-(1 / 2 : ℚ) ^ (n + 2)) := by
              rw [ih]
              simp [Computable.CReal.SignedDigit.coeff, minusOneDigits, pow_succ]
        _ = -1 + (1 / 2 : ℚ) ^ (n + 2) := by ring

theorem partialSum_oneDigits_real (n : ℕ) :
    (Computable.CReal.SignedDigit.partialSum oneDigits n : ℝ) = 1 - (1 / (2 : ℝ) ^ (n + 1)) := by
  rw [partialSum_oneDigits]
  push_cast
  have hpow : (1 / 2 : ℝ) ^ (n + 1) = 1 / (2 : ℝ) ^ (n + 1) := by
    rw [one_div]
    simpa using (inv_pow (2 : ℝ) (n + 1)).symm
  rw [hpow]

theorem partialSum_minusOneDigits_real (n : ℕ) :
    (Computable.CReal.SignedDigit.partialSum minusOneDigits n : ℝ) = -1 + (1 / (2 : ℝ) ^ (n + 1)) := by
  rw [partialSum_minusOneDigits]
  push_cast
  have hpow : (1 / 2 : ℝ) ^ (n + 1) = 1 / (2 : ℝ) ^ (n + 1) := by
    rw [one_div]
    simpa using (inv_pow (2 : ℝ) (n + 1)).symm
  rw [hpow]

@[simp] lemma digit_to_LFT_apply (d : Digit) (x : ℝ) :
    LFT.apply (digit_to_LFT d) x = (x + d.toRat) / 2 := by
  cases d <;> simp [digit_to_LFT, digitNeg, digitZero, digitPos, LFT.apply, mul_comm]

lemma partialCompFrom_apply_prefix (out : DigitStream) :
    ∀ k n x, x ∈ baseI →
      LFT.apply (partialCompFrom (lftStreamOfDigits out) k n) x =
        x / (2 : ℝ) ^ (n + 1) +
          (Computable.CReal.SignedDigit.partialSum (fun i => out (k + i)) n : ℝ)
  | k, 0, x, hx => by
      simp [partialCompFrom, lftStreamOfDigits, Computable.CReal.SignedDigit.partialSum,
        Computable.CReal.SignedDigit.coeff, div_eq_mul_inv]
      ring
  | k, n + 1, x, hx => by
      have hx' :
          LFT.apply (partialCompFrom (lftStreamOfDigits out) (k + 1) n) x ∈ baseI := by
        exact DigitStream.partialCompFrom_maps_baseI (out := out) (k := k + 1) (n := n) hx
      have htailDen :
          (((partialCompFrom (lftStreamOfDigits out) (k + 1) n).c : ℝ) * x +
                ((partialCompFrom (lftStreamOfDigits out) (k + 1) n).d : ℝ)) ≠ 0 := by
        exact LFT.denom_ne_zero_of_NoPoleOnBase
          (partialCompFrom (lftStreamOfDigits out) (k + 1) n)
          (x := x) hx
          (DigitStream.partialCompFrom_NoPoleOnBase (out := out) (k := k + 1) n)
      have hheadDen :
          ((((lftStreamOfDigits out) k).c : ℝ) *
                LFT.apply (partialCompFrom (lftStreamOfDigits out) (k + 1) n) x +
              (((lftStreamOfDigits out) k).d : ℝ)) ≠ 0 := by
        exact LFT.denom_ne_zero_of_NoPoleOnBase ((lftStreamOfDigits out) k)
          (x := LFT.apply (partialCompFrom (lftStreamOfDigits out) (k + 1) n) x) hx'
          (DigitStream.digit_to_LFT_NoPoleOnBase (out k))
      have happ :
          LFT.apply (partialCompFrom (lftStreamOfDigits out) k (n + 1)) x =
            LFT.apply ((lftStreamOfDigits out) k)
              (LFT.apply (partialCompFrom (lftStreamOfDigits out) (k + 1) n) x) := by
        have hpc :
            partialCompFrom (lftStreamOfDigits out) k (n + 1) =
              ((lftStreamOfDigits out) k).comp (partialCompFrom (lftStreamOfDigits out) (k + 1) n) := by
          simpa using partialCompFrom_succ_eq (lftStreamOfDigits out) k n
        simpa [hpc] using
          (LFT.apply_comp ((lftStreamOfDigits out) k)
            (partialCompFrom (lftStreamOfDigits out) (k + 1) n) x htailDen hheadDen)
      have ih :=
        partialCompFrom_apply_prefix out (k + 1) n x hx
      have hpartial :
          (Computable.CReal.SignedDigit.partialSum (fun i => out (k + i)) (n + 1) : ℝ) =
            ((out k).toRat : ℝ) * (1 / 2 : ℝ) +
              (1 / 2 : ℝ) *
                (Computable.CReal.SignedDigit.partialSum (fun i => out (k + 1 + i)) n : ℝ) := by
        have hq :=
          Computable.CReal.SignedDigit.partialSum_cons_succ
            (d := out k) (x := fun i => out (k + 1 + i)) n
        have hcons :
            (fun i => out (k + i)) =
              Computable.CReal.SignedDigit.cons (out k) (fun i => out (k + 1 + i)) := by
          funext i
          cases i with
          | zero =>
              simp [Computable.CReal.SignedDigit.cons]
          | succ i =>
              simp [Computable.CReal.SignedDigit.cons, Nat.add_left_comm, Nat.add_comm]
        have hqR := congrArg (fun q : ℚ => (q : ℝ)) hq
        simpa [hcons] using hqR
      calc
        LFT.apply (partialCompFrom (lftStreamOfDigits out) k (n + 1)) x
            = LFT.apply ((lftStreamOfDigits out) k)
                (LFT.apply (partialCompFrom (lftStreamOfDigits out) (k + 1) n) x) := happ
        _ = (LFT.apply (partialCompFrom (lftStreamOfDigits out) (k + 1) n) x + (out k).toRat) / 2 := by
              simp [lftStreamOfDigits]
        _ = (x / (2 : ℝ) ^ (n + 1) +
                (Computable.CReal.SignedDigit.partialSum (fun i => out (k + 1 + i)) n : ℝ) +
                (out k).toRat) / 2 := by
              rw [ih]
        _ = x / (2 : ℝ) ^ (n + 2) +
              (((out k).toRat : ℝ) * (1 / 2 : ℝ) +
                (1 / 2 : ℝ) *
                  (Computable.CReal.SignedDigit.partialSum (fun i => out (k + 1 + i)) n : ℝ)) := by
              field_simp
              ring
        _ = x / (2 : ℝ) ^ (n + 2) +
              (Computable.CReal.SignedDigit.partialSum (fun i => out (k + i)) (n + 1) : ℝ) := by
              rw [hpartial]

lemma partialComp_apply_prefix (out : DigitStream) :
    ∀ n x, x ∈ baseI →
      LFT.apply (partialComp (lftStreamOfDigits out) n) x =
        x / (2 : ℝ) ^ (n + 1) + (Computable.CReal.SignedDigit.partialSum out n : ℝ)
  | n, x, hx => by
      simpa [partialComp] using partialCompFrom_apply_prefix out 0 n x hx

theorem partialComp_apply_zero_eq_partialSum (out : DigitStream) (n : ℕ) :
    LFT.apply (partialComp (lftStreamOfDigits out) n) 0 =
      (Computable.CReal.SignedDigit.partialSum out n : ℝ) := by
  have h0 : (0 : ℝ) ∈ baseI := by constructor <;> norm_num
  simpa using partialComp_apply_prefix out n 0 h0

theorem fromStream_val_sub_partialSum_le (out : DigitStream) (n : ℕ) :
    |(MobiusReal.fromStream out).val -
        (Computable.CReal.SignedDigit.partialSum out n : ℝ)| ≤
      (1 : ℝ) / (2 ^ (n + 1)) := by
  let S : MobiusReal := MobiusReal.fromStream out
  have hmem : S.val ∈ imageSet S n :=
    (Set.mem_iInter.1 (MobiusReal.val_mem_iInter_imageSet S)) n
  rcases hmem with ⟨t, ht, htEq⟩
  have hrepr :
      S.val =
        t / (2 : ℝ) ^ (n + 1) +
          (Computable.CReal.SignedDigit.partialSum out n : ℝ) := by
    calc
      S.val = LFT.apply (partialComp S.stream n) t := by simpa [S] using htEq.symm
      _ = t / (2 : ℝ) ^ (n + 1) +
            (Computable.CReal.SignedDigit.partialSum out n : ℝ) := by
          simpa [S, MobiusReal.fromStream] using partialComp_apply_prefix out n t ht
  have htabs : |t| ≤ (1 : ℝ) := by
    exact abs_le.mpr ⟨ht.1, ht.2⟩
  calc
    |S.val - (Computable.CReal.SignedDigit.partialSum out n : ℝ)|
        = |t / (2 : ℝ) ^ (n + 1)| := by
            rw [hrepr]
            ring_nf
    _ = |t| * ((1 : ℝ) / (2 ^ (n + 1))) := by
          simp [div_eq_mul_inv, abs_mul]
    _ ≤ 1 * ((1 : ℝ) / (2 ^ (n + 1))) := by
          gcongr
    _ = (1 : ℝ) / (2 ^ (n + 1)) := by ring

theorem fromStream_val_zeroDigits :
    (MobiusReal.fromStream zeroDigits).val = 0 := by
  have h0 : (0 : ℝ) ∈ baseI := by
    constructor <;> norm_num
  have hmem : (0 : ℝ) ∈ ⋂ n, imageSet (MobiusReal.fromStream zeroDigits) n := by
    refine Set.mem_iInter.2 ?_
    intro n
    refine ⟨0, h0, ?_⟩
    simpa [partialSum_zeroDigits] using partialComp_apply_zero_eq_partialSum zeroDigits n
  symm
  exact MobiusReal.val_eq_of_mem_iInter_imageSet (MobiusReal.fromStream zeroDigits) hmem

theorem fromStream_val_oneDigits :
    (MobiusReal.fromStream oneDigits).val = 1 := by
  have h1 : (1 : ℝ) ∈ baseI := by
    constructor <;> norm_num
  have hmem : (1 : ℝ) ∈ ⋂ n, imageSet (MobiusReal.fromStream oneDigits) n := by
    refine Set.mem_iInter.2 ?_
    intro n
    refine ⟨1, h1, ?_⟩
    have happ := partialComp_apply_prefix oneDigits n 1 h1
    calc
      LFT.apply (partialComp (lftStreamOfDigits oneDigits) n) 1
          = 1 / (2 : ℝ) ^ (n + 1) +
              (Computable.CReal.SignedDigit.partialSum oneDigits n : ℝ) := happ
      _ = 1 / (2 : ℝ) ^ (n + 1) + (1 - (1 / (2 : ℝ) ^ (n + 1))) := by
            rw [partialSum_oneDigits_real]
      _ = 1 := by ring
  symm
  exact MobiusReal.val_eq_of_mem_iInter_imageSet (MobiusReal.fromStream oneDigits) hmem

theorem fromStream_val_minusOneDigits :
    (MobiusReal.fromStream minusOneDigits).val = -1 := by
  have hm1 : ((-1 : ℝ)) ∈ baseI := by
    constructor <;> norm_num
  have hmem : (-1 : ℝ) ∈ ⋂ n, imageSet (MobiusReal.fromStream minusOneDigits) n := by
    refine Set.mem_iInter.2 ?_
    intro n
    refine ⟨-1, hm1, ?_⟩
    have happ := partialComp_apply_prefix minusOneDigits n (-1) hm1
    calc
      LFT.apply (partialComp (lftStreamOfDigits minusOneDigits) n) (-1)
          = (-1 : ℝ) / (2 : ℝ) ^ (n + 1) +
              (Computable.CReal.SignedDigit.partialSum minusOneDigits n : ℝ) := happ
      _ = -(1 / (2 : ℝ) ^ (n + 1)) + (-1 + (1 / (2 : ℝ) ^ (n + 1))) := by
            rw [partialSum_minusOneDigits_real]
            ring_nf
      _ = -1 := by ring
  symm
  exact MobiusReal.val_eq_of_mem_iInter_imageSet (MobiusReal.fromStream minusOneDigits) hmem

private theorem exists_pow_inv_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, (1 : ℝ) / (2 ^ N) < ε := by
  obtain ⟨δq, hδq0, hδqε⟩ : ∃ δq : ℚ, (0 : ℝ) < (δq : ℝ) ∧ (δq : ℝ) < ε := by
    rcases exists_rat_btwn hε with ⟨δq, hδq⟩
    exact ⟨δq, hδq.1, hδq.2⟩
  have hδq0' : (0 : ℚ) < δq := by exact_mod_cast hδq0
  have hposQ : 0 < (1 : ℚ) / δq := one_div_pos.mpr hδq0'
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 : ℚ) / δq < (2 : ℚ) ^ N :=
    exists_pow_gt (x := (1 : ℚ) / δq) hposQ
  have hpowposQ : 0 < (2 : ℚ) ^ N := by positivity
  have hsmallQ : (1 : ℚ) / (2 ^ N) < δq := (one_div_lt hpowposQ hδq0').mpr hN
  have hsmallR' : ((((1 : ℚ) / (2 ^ N) : ℚ) : ℝ) < (δq : ℝ)) := by
    exact_mod_cast hsmallQ
  have hsmallR : (1 : ℝ) / (2 ^ N) < (δq : ℝ) := by
    simpa using hsmallR'
  exact ⟨N, lt_trans hsmallR hδqε⟩

private theorem pow_error_sum_le (N : ℕ) :
    (1 : ℝ) / (2 ^ (N + 1)) + (1 : ℝ) / (2 ^ (N + 2)) ≤ (1 : ℝ) / (2 ^ N) := by
  have hnonneg : 0 ≤ (1 : ℝ) / (2 ^ N) := by positivity
  calc
    (1 : ℝ) / (2 ^ (N + 1)) + (1 : ℝ) / (2 ^ (N + 2))
        = ((1 / 2 : ℝ) + (1 / 4 : ℝ)) * ((1 : ℝ) / (2 ^ N)) := by
            have htwo : (2 : ℝ) ≠ 0 := by norm_num
            field_simp [pow_succ, htwo]
            ring
    _ ≤ (1 : ℝ) * ((1 : ℝ) / (2 ^ N)) := by
          nlinarith
    _ = (1 : ℝ) / (2 ^ N) := by ring

theorem toReal_toCReal (out : DigitStream) :
    Computable.CReal.toReal (toCReal out) = (MobiusReal.fromStream out).val := by
  let A : ℝ := Computable.CReal.toReal (toCReal out)
  let B : ℝ := (MobiusReal.fromStream out).val
  apply le_antisymm
  · refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨N, hsmall⟩ := exists_pow_inv_lt hε
    let p : ℝ := (Computable.CReal.SignedDigit.partialSum out (N + 1) : ℝ)
    have hAnear : |A - p| ≤ (1 : ℝ) / (2 ^ (N + 1)) := by
      dsimp [A, p, toCReal, toSDStream]
      simpa [Computable.CReal.toReal_mk, Computable.CReal.SignedDigit.toPre] using
        (Computable.CReal.Pre.abs_toReal_sub_approx_le
          (x := Computable.CReal.SignedDigit.toPre out) (n := N))
    have hBnear : |B - p| ≤ (1 : ℝ) / (2 ^ (N + 2)) := by
      dsimp [B, p]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (fromStream_val_sub_partialSum_le out (N + 1))
    have hdist : |A - B| ≤ (1 : ℝ) / (2 ^ N) := by
      calc
        |A - B| = |(A - p) - (B - p)| := by
                    dsimp [p]
                    ring_nf
        _ ≤ |A - p| + |B - p| := by
              simpa [abs_sub_comm] using (abs_sub_le (A - p) 0 (B - p))
        _ ≤ (1 : ℝ) / (2 ^ (N + 1)) + (1 : ℝ) / (2 ^ (N + 2)) := by
              gcongr
        _ ≤ (1 : ℝ) / (2 ^ N) := pow_error_sum_le N
    have habs : |A - B| < ε := lt_of_le_of_lt hdist hsmall
    have hAB : A - B < ε := (abs_lt.mp habs).2
    linarith
  · refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨N, hsmall⟩ := exists_pow_inv_lt hε
    let p : ℝ := (Computable.CReal.SignedDigit.partialSum out (N + 1) : ℝ)
    have hAnear : |A - p| ≤ (1 : ℝ) / (2 ^ (N + 1)) := by
      dsimp [A, p, toCReal, toSDStream]
      simpa [Computable.CReal.toReal_mk, Computable.CReal.SignedDigit.toPre] using
        (Computable.CReal.Pre.abs_toReal_sub_approx_le
          (x := Computable.CReal.SignedDigit.toPre out) (n := N))
    have hBnear : |B - p| ≤ (1 : ℝ) / (2 ^ (N + 2)) := by
      dsimp [B, p]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (fromStream_val_sub_partialSum_le out (N + 1))
    have hdist : |A - B| ≤ (1 : ℝ) / (2 ^ N) := by
      calc
        |A - B| = |(A - p) - (B - p)| := by
                    dsimp [p]
                    ring_nf
        _ ≤ |A - p| + |B - p| := by
              simpa [abs_sub_comm] using (abs_sub_le (A - p) 0 (B - p))
        _ ≤ (1 : ℝ) / (2 ^ (N + 1)) + (1 : ℝ) / (2 ^ (N + 2)) := by
              gcongr
        _ ≤ (1 : ℝ) / (2 ^ N) := pow_error_sum_le N
    have habs : |A - B| < ε := lt_of_le_of_lt hdist hsmall
    have hBA : -ε < A - B := (abs_lt.mp habs).1
    linarith

@[simp] theorem toReal_toCReal_zeroDigits :
    Computable.CReal.toReal (toCReal zeroDigits) = 0 := by
  simpa [fromStream_val_zeroDigits] using toReal_toCReal zeroDigits

@[simp] theorem toReal_toCReal_oneDigits :
    Computable.CReal.toReal (toCReal oneDigits) = 1 := by
  simpa [fromStream_val_oneDigits] using toReal_toCReal oneDigits

@[simp] theorem toReal_toCReal_minusOneDigits :
    Computable.CReal.toReal (toCReal minusOneDigits) = -1 := by
  simpa [fromStream_val_minusOneDigits] using toReal_toCReal minusOneDigits

@[simp] theorem toCReal_zeroDigits_eq_zero :
    toCReal zeroDigits = 0 := by
  apply Computable.CReal.toReal_injective
  simpa using toReal_toCReal_zeroDigits

@[simp] theorem toCReal_oneDigits_eq_one :
    toCReal oneDigits = 1 := by
  apply Computable.CReal.toReal_injective
  simpa using toReal_toCReal_oneDigits

@[simp] theorem toCReal_minusOneDigits_eq_neg_one :
    toCReal minusOneDigits = (-1 : Computable.CReal) := by
  apply Computable.CReal.toReal_injective
  rw [toReal_toCReal_minusOneDigits]
  rw [Computable.CReal.toReal_neg]
  norm_num

@[simp] theorem toCReal_negStream (out : DigitStream) :
    toCReal (negStream out) = - toCReal out := by
  change (⟦Computable.CReal.SignedDigit.toPre (Computable.CReal.SignedDigit.negStream out)⟧ : Computable.CReal) =
    (⟦Computable.CReal.Pre.neg (Computable.CReal.SignedDigit.toPre out)⟧ : Computable.CReal)
  exact Quotient.sound (Computable.CReal.SignedDigit.toPre_neg_equiv out)

@[simp] theorem toReal_toCReal_negStream (out : DigitStream) :
    Computable.CReal.toReal (toCReal (negStream out)) = - (MobiusReal.fromStream out).val := by
  calc
    Computable.CReal.toReal (toCReal (negStream out))
        = Computable.CReal.toReal (- toCReal out) := by rw [toCReal_negStream]
    _ = - Computable.CReal.toReal (toCReal out) := by simp [Computable.CReal.toReal_neg]
    _ = - (MobiusReal.fromStream out).val := by rw [toReal_toCReal]

@[simp] theorem fromStream_val_negStream (out : DigitStream) :
    (MobiusReal.fromStream (negStream out)).val = - (MobiusReal.fromStream out).val := by
  rw [← toReal_toCReal (negStream out)]
  exact toReal_toCReal_negStream out

theorem toReal_toCRealScaled_one (out : DigitStream) :
    Computable.CReal.toReal (toCRealScaled 1 out) = 2 * (MobiusReal.fromStream out).val := by
  let A : ℝ := Computable.CReal.toReal (toCRealScaled 1 out)
  let B : ℝ := 2 * (MobiusReal.fromStream out).val
  apply le_antisymm
  · refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨N, hsmall⟩ := exists_pow_inv_lt hε
    let p : ℝ := (2 : ℝ) * (Computable.CReal.SignedDigit.partialSum out (N + 2) : ℝ)
    have hAnear : |A - p| ≤ (1 : ℝ) / (2 ^ (N + 1)) := by
      dsimp [A, p, toCRealScaled, toSDReal, toSDStream]
      simpa [Computable.CReal.toReal_mk, Computable.CReal.SignedDigit.SDReal.toCReal,
        Computable.CReal.SignedDigit.SDReal.toPre, Computable.CReal.SignedDigit.preScalePow2,
        Computable.CReal.SignedDigit.toPre, pow_one] using
        (Computable.CReal.Pre.abs_toReal_sub_approx_le
          (x := Computable.CReal.SignedDigit.preScalePow2 1
            (Computable.CReal.SignedDigit.toPre out)) (n := N))
    have hBnear0 :
        |(MobiusReal.fromStream out).val -
            (Computable.CReal.SignedDigit.partialSum out (N + 2) : ℝ)| ≤
          (1 : ℝ) / (2 ^ (N + 3)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (fromStream_val_sub_partialSum_le out (N + 2))
    have hBnear : |B - p| ≤ (1 : ℝ) / (2 ^ (N + 2)) := by
      dsimp [B, p]
      calc
        |2 * (MobiusReal.fromStream out).val -
            2 * (Computable.CReal.SignedDigit.partialSum out (N + 2) : ℝ)|
            = 2 * |(MobiusReal.fromStream out).val -
                (Computable.CReal.SignedDigit.partialSum out (N + 2) : ℝ)| := by
                  rw [show 2 * (MobiusReal.fromStream out).val -
                      2 * (Computable.CReal.SignedDigit.partialSum out (N + 2) : ℝ) =
                        2 * ((MobiusReal.fromStream out).val -
                          (Computable.CReal.SignedDigit.partialSum out (N + 2) : ℝ)) by ring]
                  simp [abs_mul]
        _ ≤ 2 * ((1 : ℝ) / (2 ^ (N + 3))) := by
              gcongr
        _ = (1 : ℝ) / (2 ^ (N + 2)) := by
              have htwo : (2 : ℝ) ≠ 0 := by norm_num
              field_simp [pow_succ, htwo]
              ring
    have hdist : |A - B| ≤ (1 : ℝ) / (2 ^ N) := by
      calc
        |A - B| = |(A - p) - (B - p)| := by
                    dsimp [p]
                    ring_nf
        _ ≤ |A - p| + |B - p| := by
              simpa [abs_sub_comm] using (abs_sub_le (A - p) 0 (B - p))
        _ ≤ (1 : ℝ) / (2 ^ (N + 1)) + (1 : ℝ) / (2 ^ (N + 2)) := by
              gcongr
        _ ≤ (1 : ℝ) / (2 ^ N) := pow_error_sum_le N
    have habs : |A - B| < ε := lt_of_le_of_lt hdist hsmall
    have hAB : A - B < ε := (abs_lt.mp habs).2
    linarith
  · refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨N, hsmall⟩ := exists_pow_inv_lt hε
    let p : ℝ := (2 : ℝ) * (Computable.CReal.SignedDigit.partialSum out (N + 2) : ℝ)
    have hAnear : |A - p| ≤ (1 : ℝ) / (2 ^ (N + 1)) := by
      dsimp [A, p, toCRealScaled, toSDReal, toSDStream]
      simpa [Computable.CReal.toReal_mk, Computable.CReal.SignedDigit.SDReal.toCReal,
        Computable.CReal.SignedDigit.SDReal.toPre, Computable.CReal.SignedDigit.preScalePow2,
        Computable.CReal.SignedDigit.toPre, pow_one] using
        (Computable.CReal.Pre.abs_toReal_sub_approx_le
          (x := Computable.CReal.SignedDigit.preScalePow2 1
            (Computable.CReal.SignedDigit.toPre out)) (n := N))
    have hBnear0 :
        |(MobiusReal.fromStream out).val -
            (Computable.CReal.SignedDigit.partialSum out (N + 2) : ℝ)| ≤
          (1 : ℝ) / (2 ^ (N + 3)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (fromStream_val_sub_partialSum_le out (N + 2))
    have hBnear : |B - p| ≤ (1 : ℝ) / (2 ^ (N + 2)) := by
      dsimp [B, p]
      calc
        |2 * (MobiusReal.fromStream out).val -
            2 * (Computable.CReal.SignedDigit.partialSum out (N + 2) : ℝ)|
            = 2 * |(MobiusReal.fromStream out).val -
                (Computable.CReal.SignedDigit.partialSum out (N + 2) : ℝ)| := by
                  rw [show 2 * (MobiusReal.fromStream out).val -
                      2 * (Computable.CReal.SignedDigit.partialSum out (N + 2) : ℝ) =
                        2 * ((MobiusReal.fromStream out).val -
                          (Computable.CReal.SignedDigit.partialSum out (N + 2) : ℝ)) by ring]
                  simp [abs_mul]
        _ ≤ 2 * ((1 : ℝ) / (2 ^ (N + 3))) := by
              gcongr
        _ = (1 : ℝ) / (2 ^ (N + 2)) := by
              have htwo : (2 : ℝ) ≠ 0 := by norm_num
              field_simp [pow_succ, htwo]
              ring
    have hdist : |A - B| ≤ (1 : ℝ) / (2 ^ N) := by
      calc
        |A - B| = |(A - p) - (B - p)| := by
                    dsimp [p]
                    ring_nf
        _ ≤ |A - p| + |B - p| := by
              simpa [abs_sub_comm] using (abs_sub_le (A - p) 0 (B - p))
        _ ≤ (1 : ℝ) / (2 ^ (N + 1)) + (1 : ℝ) / (2 ^ (N + 2)) := by
              gcongr
        _ ≤ (1 : ℝ) / (2 ^ N) := pow_error_sum_le N
    have habs : |A - B| < ε := lt_of_le_of_lt hdist hsmall
    have hBA : -ε < A - B := (abs_lt.mp habs).1
    linarith

theorem toCRealScaled_one_eq_two_mul (out : DigitStream) :
    toCRealScaled 1 out = Computable.CReal.two * toCReal out := by
  apply Computable.CReal.toReal_injective
  rw [Computable.CReal.toReal_mul, DigitStream.toReal_toCReal, Computable.CReal.toReal_two]
  exact toReal_toCRealScaled_one out

theorem toCRealScaled_one_eq_add_self (out : DigitStream) :
    toCRealScaled 1 out = toCReal out + toCReal out := by
  rw [toCRealScaled_one_eq_two_mul, Computable.CReal.two_mul]

end DigitStream

end Mobius
end Computable
