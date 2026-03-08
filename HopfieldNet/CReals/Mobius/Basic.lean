import Mathlib

/-!
# Möbius Streams / LFTs for Exact Real Arithmetic (experimental)

This is an **alternative** exact-real arithmetic architecture, based on Möbius (linear fractional)
transformations and the tensor-product machine.

This folder currently provides:

- the algebraic specification layer (`LFT`, `LFTStream`, contractiveness predicate)
- the integer-only execution core (`Tensor`, `oracle`)
- a small-step *relational* operational semantics (`VMStep`)

The long-horizon productivity story is kept at the specification layer. The trusted surface now
tracks pole-freeness explicitly so width estimates cannot silently become vacuous on tensors with
interior poles.
-/

namespace Computable
namespace Mobius

/-! =========================================================================
  PART 1: ALGEBRAIC SPECIFICATION
  ========================================================================== -/

@[ext]
structure LFT where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  det_neq_zero : a * d - b * c ≠ 0

namespace LFT

def id : LFT where
  a := 1
  b := 0
  c := 0
  d := 1
  det_neq_zero := by decide

def comp (M N : LFT) : LFT where
  a := M.a * N.a + M.b * N.c
  b := M.a * N.b + M.b * N.d
  c := M.c * N.a + M.d * N.c
  d := M.c * N.b + M.d * N.d
  det_neq_zero := by
    -- `det (M ∘ N) = det M * det N`
    have h :
        (M.a * N.a + M.b * N.c) * (M.c * N.b + M.d * N.d)
          - (M.a * N.b + M.b * N.d) * (M.c * N.a + M.d * N.c)
        = (M.a * M.d - M.b * M.c) * (N.a * N.d - N.b * N.c) := by
      ring
    intro h0
    have : (M.a * M.d - M.b * M.c) * (N.a * N.d - N.b * N.c) = 0 := by simpa [h] using h0
    rcases mul_eq_zero.mp this with hM | hN
    · exact M.det_neq_zero hM
    · exact N.det_neq_zero hN

theorem comp_assoc (A B C : LFT) : (A.comp B).comp C = A.comp (B.comp C) := by
  ext <;> simp [LFT.comp] <;> ring

noncomputable def apply (M : LFT) (x : ℝ) : ℝ :=
  ((M.a : ℝ) * x + (M.b : ℝ)) / ((M.c : ℝ) * x + (M.d : ℝ))

theorem apply_comp (M N : LFT) (x : ℝ)
    (hN : ((N.c : ℝ) * x + (N.d : ℝ)) ≠ 0)
    (hM : ((M.c : ℝ) * (LFT.apply N x) + (M.d : ℝ)) ≠ 0) :
    LFT.apply (M.comp N) x = LFT.apply M (LFT.apply N x) := by
  -- Write `N.apply x` as a single fraction `numN / denN`.
  set numN : ℝ := (N.a : ℝ) * x + (N.b : ℝ)
  set denN : ℝ := (N.c : ℝ) * x + (N.d : ℝ)
  have hdenN : denN ≠ 0 := by simp [denN] at hN; simpa using hN
  have hM' : (M.c : ℝ) * (numN / denN) + (M.d : ℝ) ≠ 0 := by
    simpa [LFT.apply, numN, denN] using hM

  -- Common numerator/denominator after clearing the inner division by `denN`.
  let numC : ℝ := (M.a : ℝ) * numN + (M.b : ℝ) * denN
  -- Use the syntactic form that appears naturally after `field_simp`.
  let denC : ℝ := (M.c : ℝ) * numN + denN * (M.d : ℝ)

  have hdenC : denC ≠ 0 := by
    intro h0
    apply hM'
    have : denC / denN = 0 := by simp [h0]
    -- rewrite `denC/denN` into the outer denominator expression
    have hEq : denC / denN = (M.c : ℝ) * (numN / denN) + (M.d : ℝ) := by
      -- unfold `denC` so `field_simp` sees the right shape
      simp [denC]
      field_simp [hdenN]
      try ring_nf
    simpa [hEq] using this

  have rhs :
      LFT.apply M (LFT.apply N x) = numC / denC := by
    -- Expand and clear the inner division by `denN`.
    unfold LFT.apply
    -- both `N.apply x` occurrences become `numN / denN`
    simp [numN, denN, numC, denC]
    -- clear denominators using `denN ≠ 0` and the outer denominator hypothesis
    have hdenN1 : (N.c : ℝ) * x + (N.d : ℝ) ≠ 0 := by
      simpa [denN] using hdenN
    have hdenN2 : x * (N.c : ℝ) + (N.d : ℝ) ≠ 0 := by
      simpa [denN, mul_comm] using hdenN
    field_simp [hdenN1, hdenN2, hM', hdenC]
    try ring_nf

  have lhs :
      LFT.apply (M.comp N) x = numC / denC := by
    unfold LFT.apply LFT.comp
    simp [numN, denN, numC, denC]
    ring_nf

  simp [lhs, rhs]

def NoPoleOnBase (M : LFT) : Prop :=
  |M.c| < |M.d|

theorem denom_ne_zero_of_NoPoleOnBase (M : LFT) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (h : M.NoPoleOnBase) :
    ((M.c : ℝ) * x + (M.d : ℝ)) ≠ 0 := by
  have hxabs : |x| ≤ (1 : ℝ) := by
    -- `abs_le` : |x| ≤ 1 ↔ -1 ≤ x ∧ x ≤ 1
    exact (abs_le.2 ⟨by simpa using hx.1, by simpa using hx.2⟩)
  have hR : |(M.c : ℝ)| < |(M.d : ℝ)| := by
    -- transport the integer inequality to reals
    exact_mod_cast h
  intro h0
  have hd : (M.d : ℝ) = -((M.c : ℝ) * x) := by
    linarith
  have habs_le : |(M.d : ℝ)| ≤ |(M.c : ℝ)| := by
    calc
      |(M.d : ℝ)| = |(M.c : ℝ) * x| := by simp [hd, abs_mul, abs_neg, mul_comm]
      _ = |(M.c : ℝ)| * |x| := by simp [abs_mul]
      _ ≤ |(M.c : ℝ)| * (1 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hxabs (abs_nonneg (M.c : ℝ))
      _ = |(M.c : ℝ)| := by ring
  exact (not_lt_of_ge habs_le) hR

end LFT

def digitNeg : LFT where
  a := 1
  b := -1
  c := 0
  d := 2
  det_neq_zero := by decide

def digitZero : LFT where
  a := 1
  b := 0
  c := 0
  d := 2
  det_neq_zero := by decide

def digitPos : LFT where
  a := 1
  b := 1
  c := 0
  d := 2
  det_neq_zero := by decide

abbrev LFTStream : Type := ℕ → LFT

def partialCompFrom (s : LFTStream) (k : ℕ) : ℕ → LFT
  | 0     => s k
  | n + 1 => (partialCompFrom s k n).comp (s (k + (n + 1)))

def partialComp (s : LFTStream) : ℕ → LFT :=
  partialCompFrom s 0

lemma partialCompFrom_zero (s : LFTStream) :
    partialCompFrom s 0 = partialComp s := by
  rfl

lemma partialCompFrom_succ_eq (s : LFTStream) (k n : ℕ) :
    partialCompFrom s k (n + 1) = (s k).comp (partialCompFrom s (k + 1) n) := by
  induction n with
  | zero =>
      simp [partialCompFrom]
  | succ n ih =>
      -- One-step unfold + associativity.
      -- The only nontrivial part is aligning the index arithmetic.
      calc
        partialCompFrom s k (n + 2)
            = (partialCompFrom s k (n + 1)).comp (s (k + (n + 2))) := by
                simp [partialCompFrom, Nat.add_assoc]
        _ = ((s k).comp (partialCompFrom s (k + 1) n)).comp (s (k + (n + 2))) := by
              simpa [Nat.add_assoc] using congrArg (fun M => M.comp (s (k + (n + 2)))) ih
        _ = (s k).comp ((partialCompFrom s (k + 1) n).comp (s (k + (n + 2)))) := by
              simp [LFT.comp_assoc]
        _ = (s k).comp (partialCompFrom s (k + 1) (n + 1)) := by
              -- unfold `partialCompFrom` at tail index `k+1`
              simp [partialCompFrom, Nat.add_left_comm, Nat.add_comm]

lemma partialCompFrom_shift (s : LFTStream) (k j n : ℕ) :
    partialCompFrom (fun m => s (m + k)) j n = partialCompFrom s (j + k) n := by
  induction n with
  | zero =>
      simp [partialCompFrom]
  | succ n ih =>
      simp [partialCompFrom, ih]
      congr 1
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma partialComp_drop (s : LFTStream) (k n : ℕ) :
    partialComp (fun m => s (m + k)) n = partialCompFrom s k n := by
  -- unfold `partialComp = partialCompFrom _ 0`, then apply the shift lemma at `j = 0`.
  simpa [partialComp] using (partialCompFrom_shift s k 0 n)

class IsContractive (s : LFTStream) : Prop where
  /-- No poles for any tail partial composition. -/
  no_poles_from : ∀ k n, (partialCompFrom s k n).NoPoleOnBase
  /-- Any tail partial composition maps the base interval into itself. -/
  maps_base_from : ∀ k n,
    Set.MapsTo (fun x => LFT.apply (partialCompFrom s k n) x) (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1)
  /-- The image diameter of `[-1,1]` under tail partial compositions tends to `0` (uniformly in the tail index). -/
  shrinks_to_zero :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k, ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |LFT.apply (partialCompFrom s k n) x - LFT.apply (partialCompFrom s k n) y| < ε

namespace IsContractive

lemma no_poles_step {s : LFTStream} (h : IsContractive s) (n : ℕ) : (s n).NoPoleOnBase := by
  simpa [partialCompFrom] using h.no_poles_from n 0

lemma no_poles {s : LFTStream} (h : IsContractive s) (n : ℕ) : (partialComp s n).NoPoleOnBase := by
  simpa [partialComp] using h.no_poles_from 0 n

lemma maps_base_step {s : LFTStream} (h : IsContractive s) (n : ℕ) :
    Set.MapsTo (fun x => LFT.apply (s n) x) (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) := by
  simpa [partialCompFrom] using h.maps_base_from n 0

lemma maps_base {s : LFTStream} (h : IsContractive s) (n : ℕ) :
    Set.MapsTo (fun x => LFT.apply (partialComp s n) x) (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) := by
  simpa [partialComp] using h.maps_base_from 0 n

end IsContractive

structure MobiusReal where
  stream : LFTStream
  contractive : IsContractive stream

namespace MobiusReal

private lemma partialCompFrom_drop (s : LFTStream) (k j n : ℕ) :
    partialCompFrom (fun m => s (m + k)) j n = partialCompFrom s (j + k) n := by
  induction n with
  | zero =>
      simp [partialCompFrom]
  | succ n ih =>
      simp [partialCompFrom, ih]
      congr 1
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

def drop (X : MobiusReal) (k : ℕ) : MobiusReal where
  stream := fun n => X.stream (n + k)
  contractive := by
    classical
    refine
      { no_poles_from := ?_
        maps_base_from := ?_
        shrinks_to_zero := ?_ }
    · intro j n
      simpa [partialCompFrom_drop] using X.contractive.no_poles_from (j + k) n
    · intro j n
      simpa [partialCompFrom_drop] using X.contractive.maps_base_from (j + k) n
    · intro ε hε
      rcases X.contractive.shrinks_to_zero ε hε with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro n hn j x hx y hy
      simpa [partialCompFrom_drop, Nat.add_assoc] using hN n hn (j + k) x hx y hy

end MobiusReal

/-! =========================================================================
  PART 2: INTEGER-ONLY EXECUTION CORE
  ========================================================================== -/

structure Tensor where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
  g : ℤ
  h : ℤ

namespace Tensor

def absorbX (T : Tensor) (M : LFT) : Tensor where
  a := T.a * M.a + T.c * M.c
  b := T.b * M.a + T.d * M.c
  c := T.a * M.b + T.c * M.d
  d := T.b * M.b + T.d * M.d
  e := T.e * M.a + T.g * M.c
  f := T.f * M.a + T.h * M.c
  g := T.e * M.b + T.g * M.d
  h := T.f * M.b + T.h * M.d

def absorbY (T : Tensor) (M : LFT) : Tensor where
  a := T.a * M.a + T.b * M.c
  b := T.a * M.b + T.b * M.d
  c := T.c * M.a + T.d * M.c
  d := T.c * M.b + T.d * M.d
  e := T.e * M.a + T.f * M.c
  f := T.e * M.b + T.f * M.d
  g := T.g * M.a + T.h * M.c
  h := T.g * M.b + T.h * M.d

def emit (T : Tensor) (D : LFT) : Tensor where
  a := D.d * T.a - D.b * T.e
  b := D.d * T.b - D.b * T.f
  c := D.d * T.c - D.b * T.g
  d := D.d * T.d - D.b * T.h
  e := -D.c * T.a + D.a * T.e
  f := -D.c * T.b + D.a * T.f
  g := -D.c * T.c + D.a * T.g
  h := -D.c * T.d + D.a * T.h

/-- Matrix normalization by dividing out a common gcd (projective scaling). -/
def normalizeFactor (T : Tensor) : ℕ :=
  let g1 := (T.a.natAbs.gcd T.b.natAbs).gcd (T.c.natAbs.gcd T.d.natAbs)
  let g2 := (T.e.natAbs.gcd T.f.natAbs).gcd (T.g.natAbs.gcd T.h.natAbs)
  let g := g1.gcd g2
  g

def divideBy (T : Tensor) (gZ : ℤ) : Tensor :=
  { a := T.a / gZ, b := T.b / gZ, c := T.c / gZ, d := T.d / gZ
    e := T.e / gZ, f := T.f / gZ, g := T.g / gZ, h := T.h / gZ }

/-- Matrix normalization by dividing out a common gcd (projective scaling). -/
def normalize (T : Tensor) : Tensor :=
  let g := T.normalizeFactor
  if g ≤ 1 then T else
    let gZ : ℤ := (g : ℤ)
    T.divideBy gZ

def cornerValues (T : Tensor) : (ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ) :=
  let n1 :=  T.a + T.b + T.c + T.d
  let d1 :=  T.e + T.f + T.g + T.h
  let n2 := -T.a + T.b - T.c + T.d
  let d2 := -T.e + T.f - T.g + T.h
  let n3 := -T.a - T.b + T.c + T.d
  let d3 := -T.e - T.f + T.g + T.h
  let n4 :=  T.a - T.b - T.c + T.d
  let d4 :=  T.e - T.f - T.g + T.h
  ((n1, d1), (n2, d2), (n3, d3), (n4, d4))

/-- Pole-freeness check on the square via corner denominators (Boolean oracle). -/
def hasNoPole (d1 d2 d3 d4 : ℤ) : Bool :=
  decide (d1 > 0 ∧ d2 > 0 ∧ d3 > 0 ∧ d4 > 0)
    || decide (d1 < 0 ∧ d2 < 0 ∧ d3 < 0 ∧ d4 < 0)

/-- Check \(n/d ∈ [-1,0]\) using only integers. -/
def inDigitNeg (n d : ℤ) : Bool :=
  let s : ℤ := if 0 < d then 1 else -1
  let abs_d := d * s
  let num := n * s
  decide (num ≤ 0 ∧ -abs_d ≤ num)

/-- Check \(n/d ∈ [-1/2,1/2]\) using only integers. -/
def inDigitZero (n d : ℤ) : Bool :=
  let s : ℤ := if 0 < d then 1 else -1
  let abs_d := d * s
  let num2 := 2 * n * s
  decide (num2 ≤ abs_d ∧ -abs_d ≤ num2)

/-- Check \(n/d ∈ [0,1]\) using only integers. -/
def inDigitPos (n d : ℤ) : Bool :=
  let s : ℤ := if 0 < d then 1 else -1
  let abs_d := d * s
  let num := n * s
  decide (0 ≤ num ∧ num ≤ abs_d)

inductive EmitDecision
  | neg | zero | pos | absorb
  deriving DecidableEq, Repr

/-- The core computable oracle: emit a digit if the whole image lies in the digit interval. -/
def oracle (T : Tensor) : EmitDecision :=
  let ((n1,d1), (n2,d2), (n3,d3), (n4,d4)) := T.cornerValues
  if !hasNoPole d1 d2 d3 d4 then EmitDecision.absorb else
  if inDigitNeg n1 d1 && inDigitNeg n2 d2 && inDigitNeg n3 d3 && inDigitNeg n4 d4 then
    EmitDecision.neg
  else if inDigitZero n1 d1 && inDigitZero n2 d2 && inDigitZero n3 d3 && inDigitZero n4 d4 then
    EmitDecision.zero
  else if inDigitPos n1 d1 && inDigitPos n2 d2 && inDigitPos n3 d3 && inDigitPos n4 d4 then
    EmitDecision.pos
  else EmitDecision.absorb

end Tensor

/-! =========================================================================
  PART 3: STRUCTURAL OPERATIONAL SEMANTICS (RELATIONAL VM)
  ========================================================================== -/

structure VMState where
  T : Tensor
  idx_x : ℕ
  idx_y : ℕ
  absorb_x_next : Bool

inductive VMStep : VMState → Option LFT → VMState → Prop
  | emitNeg {s : VMState} (h : s.T.oracle = Tensor.EmitDecision.neg) :
      VMStep s (some digitNeg) { s with T := s.T.emit digitNeg }
  | emitZero {s : VMState} (h : s.T.oracle = Tensor.EmitDecision.zero) :
      VMStep s (some digitZero) { s with T := s.T.emit digitZero }
  | emitPos {s : VMState} (h : s.T.oracle = Tensor.EmitDecision.pos) :
      VMStep s (some digitPos) { s with T := s.T.emit digitPos }
  | absorbX {s : VMState} (sx : LFTStream)
      (h1 : s.T.oracle = Tensor.EmitDecision.absorb)
      (h2 : s.absorb_x_next = true) :
      VMStep s none { s with
        T := s.T.absorbX (sx s.idx_x)
        idx_x := s.idx_x + 1
        absorb_x_next := false }
  | absorbY {s : VMState} (sy : LFTStream)
      (h1 : s.T.oracle = Tensor.EmitDecision.absorb)
      (h2 : s.absorb_x_next = false) :
      VMStep s none { s with
        T := s.T.absorbY (sy s.idx_y)
        idx_y := s.idx_y + 1
        absorb_x_next := true }

/-! =========================================================================
  PART 4/5 (placeholders): semantics/width/productivity specs
  ========================================================================== -/

namespace Tensor

noncomputable def apply (T : Tensor) (x y : ℝ) : ℝ :=
  ((T.a : ℝ) * x * y + (T.b : ℝ) * x + (T.c : ℝ) * y + (T.d : ℝ)) /
    ((T.e : ℝ) * x * y + (T.f : ℝ) * x + (T.g : ℝ) * y + (T.h : ℝ))

noncomputable def numAt (T : Tensor) (x y : ℝ) : ℝ :=
  ((T.a : ℝ) * x * y + (T.b : ℝ) * x + (T.c : ℝ) * y + (T.d : ℝ))

noncomputable def denAt (T : Tensor) (x y : ℝ) : ℝ :=
  ((T.e : ℝ) * x * y + (T.f : ℝ) * x + (T.g : ℝ) * y + (T.h : ℝ))

lemma apply_eq (T : Tensor) (x y : ℝ) : Tensor.apply T x y = numAt T x y / denAt T x y := by
  rfl

end Tensor

def Tensor.HasNoPoleOnBase (T : Tensor) : Prop :=
  ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1, Tensor.denAt T x y ≠ 0

def Tensor.widthSet (T : Tensor) : Set ℝ :=
  { d | ∃ x y w z,
    x ∈ Set.Icc (-1 : ℝ) 1 ∧ y ∈ Set.Icc (-1 : ℝ) 1 ∧
    w ∈ Set.Icc (-1 : ℝ) 1 ∧ z ∈ Set.Icc (-1 : ℝ) 1 ∧
    d = |Tensor.apply T x y - Tensor.apply T w z| }

noncomputable def tensorWidth (T : Tensor) : ℝ :=
  sSup (Tensor.widthSet T)

def Tensor.EmitsDigit (T : Tensor) : Prop :=
  T.oracle = Tensor.EmitDecision.neg ∨
    T.oracle = Tensor.EmitDecision.zero ∨
    T.oracle = Tensor.EmitDecision.pos

def Tensor.ProductiveOnBase (T : Tensor) : Prop :=
  T.HasNoPoleOnBase ∧ tensorWidth T < (1 / 2 : ℝ) ∧ T.EmitsDigit

lemma Tensor.ProductiveOnBase.hasNoPoleOnBase {T : Tensor} (h : T.ProductiveOnBase) :
    T.HasNoPoleOnBase :=
  h.1

lemma Tensor.ProductiveOnBase.width_lt_half {T : Tensor} (h : T.ProductiveOnBase) :
    tensorWidth T < (1 / 2 : ℝ) :=
  h.2.1

lemma Tensor.ProductiveOnBase.emitsDigit {T : Tensor} (h : T.ProductiveOnBase) :
    T.EmitsDigit :=
  h.2.2

def Tensor.absorbBoth_n (T : Tensor) (sx sy : LFTStream) : ℕ → Tensor
  | 0     => T
  | n + 1 => ((Tensor.absorbBoth_n T sx sy n).absorbX (sx n)).absorbY (sy n)

end Mobius
end Computable

