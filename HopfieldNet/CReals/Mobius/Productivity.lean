import HopfieldNet.CReals.Mobius.TraceSoundness
import HopfieldNet.CReals.Mobius.Eval
import HopfieldNet.CReals.Mobius.CRealBridge

namespace Computable
namespace Mobius

/--
The streamable addition machine is the averaged tensor `(x + y) / 2`.
The unscaled sum is then recovered by reinterpreting the output with exponent `1`.
-/
def addOutput (out : DigitStream) :=
  Computable.Mobius.toSDReal 1 out

def halfAddInitState : VMState where
  T := halfAddTensor
  idx_x := 0
  idx_y := 0
  absorb_x_next := true

def halfAddTensorStateAfter (X Y : MobiusReal) (N : ℕ) : VMState where
  T := Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N
  idx_x := N
  idx_y := N
  absorb_x_next := true

def halfAddTensorXStateAfter (X Y : MobiusReal) (N : ℕ) : VMState where
  T := (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).absorbX (X.stream N)
  idx_x := N + 1
  idx_y := N
  absorb_x_next := false

/--
Residual output transform after emitting one signed digit.

If `digit_to_LFT d` realizes the emitted step, then `residualDigitLFT d`
is the affine map sending the old value to the post-emission residual.
-/
private def residualDigitLFT : Digit → LFT
  | .neg =>
      { a := 2, b := 1, c := 0, d := 1, det_neq_zero := by decide }
  | .zero =>
      { a := 2, b := 0, c := 0, d := 1, det_neq_zero := by decide }
  | .pos =>
      { a := 2, b := -1, c := 0, d := 1, det_neq_zero := by decide }

@[simp] theorem residualDigitLFT_comp_c (d : Digit) (M : LFT) :
    ((residualDigitLFT d).comp M).c = M.c := by
  cases d <;> simp [residualDigitLFT, LFT.comp]

@[simp] theorem residualDigitLFT_comp_d (d : Digit) (M : LFT) :
    ((residualDigitLFT d).comp M).d = M.d := by
  cases d <;> simp [residualDigitLFT, LFT.comp]

private theorem Tensor.ext
    {T S : Tensor}
    (ha : T.a = S.a) (hb : T.b = S.b) (hc : T.c = S.c) (hd : T.d = S.d)
    (he : T.e = S.e) (hf : T.f = S.f) (hg : T.g = S.g) (hh : T.h = S.h) :
    T = S := by
  cases T
  cases S
  simp_all

/-- Prefix composition with `0` absorbed digits uses the identity LFT. -/
def pairedPrefix (s : LFTStream) : ℕ → LFT
  | 0 => LFT.id
  | n + 1 => (pairedPrefix s n).comp (s n)

/-- Tensor representing the arithmetic mean `(M x + N y)/2`. -/
def avgTensor (M N : LFT) : Tensor where
  a := M.a * N.c + M.c * N.a
  b := M.a * N.d + M.c * N.b
  c := M.b * N.c + M.d * N.a
  d := M.b * N.d + M.d * N.b
  e := 2 * M.c * N.c
  f := 2 * M.c * N.d
  g := 2 * M.d * N.c
  h := 2 * M.d * N.d

@[simp]
theorem pairedPrefix_zero (s : LFTStream) :
    pairedPrefix s 0 = LFT.id := rfl

@[simp]
theorem pairedPrefix_succ (s : LFTStream) (n : ℕ) :
    pairedPrefix s (n + 1) = (pairedPrefix s n).comp (s n) := rfl

theorem pairedPrefix_eq_partialComp (s : LFTStream) :
    ∀ n, pairedPrefix s (n + 1) = partialComp s n
  | 0 => by
      ext <;> simp [pairedPrefix, partialComp, partialCompFrom, LFT.comp, LFT.id]
  | n + 1 => by
      calc
        pairedPrefix s (n + 2)
            = (pairedPrefix s (n + 1)).comp (s (n + 1)) := by simp [pairedPrefix]
        _ = (partialComp s n).comp (s (n + 1)) := by rw [pairedPrefix_eq_partialComp s n]
        _ = partialComp s (n + 1) := by simp [partialComp, partialCompFrom]

theorem pairedPrefix_append_shift (s : LFTStream) (N K : ℕ) :
    (pairedPrefix s N).comp (pairedPrefix (fun m => s (m + N)) K) = pairedPrefix s (N + K) := by
  induction K with
  | zero =>
      ext <;> simp [pairedPrefix, LFT.comp, LFT.id]
  | succ K ih =>
      calc
        (pairedPrefix s N).comp (pairedPrefix (fun m => s (m + N)) (K + 1))
            = ((pairedPrefix s N).comp (pairedPrefix (fun m => s (m + N)) K)).comp (s (K + N)) := by
                simp [pairedPrefix, LFT.comp_assoc, Nat.add_comm]
        _ = (pairedPrefix s (N + K)).comp (s (N + K)) := by
              rw [ih]
              simp [Nat.add_comm]
        _ = pairedPrefix s (N + (K + 1)) := by
              simp [pairedPrefix]

@[simp]
theorem avgTensor_id_id :
    avgTensor LFT.id LFT.id = halfAddTensor := by
  apply Tensor.ext <;> simp [avgTensor, halfAddTensor, LFT.id]

theorem avgTensor_absorbX_absorbY (M N Px Py : LFT) :
    ((avgTensor M N).absorbX Px).absorbY Py = avgTensor (M.comp Px) (N.comp Py) := by
  apply Tensor.ext <;> simp [avgTensor, Tensor.absorbX, Tensor.absorbY, LFT.comp] <;> ring

theorem avgTensor_absorbX (M N Px : LFT) :
    (avgTensor M N).absorbX Px = avgTensor (M.comp Px) N := by
  apply Tensor.ext <;> simp [avgTensor, Tensor.absorbX, LFT.comp] <;> ring

theorem avgTensor_absorbY (M N Py : LFT) :
    (avgTensor M N).absorbY Py = avgTensor M (N.comp Py) := by
  apply Tensor.ext <;> simp [avgTensor, Tensor.absorbY, LFT.comp] <;> ring

def Tensor.MapsBaseI (T : Tensor) : Prop :=
  ∀ x ∈ baseI, ∀ y ∈ baseI, Tensor.apply T x y ∈ baseI

theorem avgTensor_emit_digit (M N : LFT) (d : Digit) :
    (avgTensor M N).emit (digit_to_LFT d) =
      avgTensor ((residualDigitLFT d).comp M) ((residualDigitLFT d).comp N) := by
  cases d <;> apply Tensor.ext <;>
    simp [avgTensor, residualDigitLFT, digit_to_LFT, digitNeg, digitZero, digitPos,
      Tensor.emit, LFT.comp] <;> ring_nf

theorem absorbBoth_n_avgTensor_eq (M N : LFT) (sx sy : LFTStream) :
    ∀ K, Tensor.absorbBoth_n (avgTensor M N) sx sy K =
      avgTensor (M.comp (pairedPrefix sx K)) (N.comp (pairedPrefix sy K))
  | 0 => by
      apply Tensor.ext <;> simp [Tensor.absorbBoth_n, pairedPrefix, avgTensor, LFT.comp, LFT.id]
  | K + 1 => by
      calc
        Tensor.absorbBoth_n (avgTensor M N) sx sy (K + 1)
            = ((Tensor.absorbBoth_n (avgTensor M N) sx sy K).absorbX (sx K)).absorbY (sy K) := by
                simp [Tensor.absorbBoth_n]
        _ = ((avgTensor (M.comp (pairedPrefix sx K)) (N.comp (pairedPrefix sy K))).absorbX (sx K)).absorbY (sy K) := by
              rw [absorbBoth_n_avgTensor_eq (M := M) (N := N) (sx := sx) (sy := sy) K]
        _ = avgTensor ((M.comp (pairedPrefix sx K)).comp (sx K))
              ((N.comp (pairedPrefix sy K)).comp (sy K)) := by
                simpa using avgTensor_absorbX_absorbY
                  (M.comp (pairedPrefix sx K)) (N.comp (pairedPrefix sy K)) (sx K) (sy K)
        _ = avgTensor (M.comp (pairedPrefix sx (K + 1))) (N.comp (pairedPrefix sy (K + 1))) := by
              simp [pairedPrefix, LFT.comp_assoc]

@[simp] theorem avgTensor_eq_absorbed (M N : LFT) :
    avgTensor M N = (halfAddTensor.absorbX M).absorbY N := by
  apply Tensor.ext <;> simp [avgTensor, halfAddTensor, Tensor.absorbX, Tensor.absorbY] <;> ring

theorem absorbBoth_n_halfAdd_eq_avgTensor (sx sy : LFTStream) :
    ∀ N, Tensor.absorbBoth_n halfAddTensor sx sy N = avgTensor (pairedPrefix sx N) (pairedPrefix sy N)
  | 0 => by
      simpa [pairedPrefix, Tensor.absorbBoth_n] using avgTensor_id_id.symm
  | N + 1 => by
      calc
        Tensor.absorbBoth_n halfAddTensor sx sy (N + 1)
            = ((Tensor.absorbBoth_n halfAddTensor sx sy N).absorbX (sx N)).absorbY (sy N) := by
                simp [Tensor.absorbBoth_n]
        _ = ((avgTensor (pairedPrefix sx N) (pairedPrefix sy N)).absorbX (sx N)).absorbY (sy N) := by
              rw [absorbBoth_n_halfAdd_eq_avgTensor sx sy N]
        _ = avgTensor ((pairedPrefix sx N).comp (sx N)) ((pairedPrefix sy N).comp (sy N)) := by
              simpa using avgTensor_absorbX_absorbY (pairedPrefix sx N) (pairedPrefix sy N) (sx N) (sy N)
        _ = avgTensor (pairedPrefix sx (N + 1)) (pairedPrefix sy (N + 1)) := by
              simp [pairedPrefix]

theorem pairedPrefix_noPoleOnBase (X : MobiusReal) :
    ∀ N, (pairedPrefix X.stream N).NoPoleOnBase
  | 0 => by
      simp [pairedPrefix, LFT.id, LFT.NoPoleOnBase]
  | N + 1 => by
      rw [pairedPrefix_eq_partialComp]
      exact IsContractive.no_poles X.contractive N

theorem pairedPrefix_maps_base (X : MobiusReal) :
    ∀ N, Set.MapsTo (fun x => LFT.apply (pairedPrefix X.stream N) x) baseI baseI
  | 0 => by
      intro x hx
      simpa [pairedPrefix, baseI, LFT.id, LFT.apply]
  | N + 1 => by
      rw [pairedPrefix_eq_partialComp]
      exact IsContractive.maps_base X.contractive N

theorem pairedPrefix_denom_ne_zero (X : MobiusReal) (N : ℕ) {x : ℝ}
    (hx : x ∈ baseI) :
    (((pairedPrefix X.stream N).c : ℝ) * x + ((pairedPrefix X.stream N).d : ℝ)) ≠ 0 := by
  exact LFT.denom_ne_zero_of_NoPoleOnBase (pairedPrefix X.stream N) hx
    (pairedPrefix_noPoleOnBase X N)

theorem avgTensor_apply (M N : LFT) (x y : ℝ)
    (hx : ((M.c : ℝ) * x + (M.d : ℝ)) ≠ 0)
    (hy : ((N.c : ℝ) * y + (N.d : ℝ)) ≠ 0) :
    Tensor.apply (avgTensor M N) x y = (LFT.apply M x + LFT.apply N y) / 2 := by
  rw [avgTensor_eq_absorbed]
  have hdenHalf :
      Tensor.denAt halfAddTensor (LFT.apply M x) (LFT.apply N y) ≠ 0 := by
    simp [Tensor.denAt, halfAddTensor]
  have hdenAbsorbX :
      Tensor.denAt (halfAddTensor.absorbX M) x (LFT.apply N y) ≠ 0 := by
    intro h0
    have : ((M.c : ℝ) * x + (M.d : ℝ)) = 0 := by
      simp [Tensor.denAt, Tensor.absorbX, halfAddTensor] at h0
      linarith
    exact hx this
  have hdenFinal :
      Tensor.denAt ((halfAddTensor.absorbX M).absorbY N) x y ≠ 0 := by
    intro h0
    have hmul : (((M.c : ℝ) * x + (M.d : ℝ)) * (((N.c : ℝ) * y + (N.d : ℝ)))) = 0 := by
      simp [Tensor.denAt, Tensor.absorbY, Tensor.absorbX, halfAddTensor] at h0
      nlinarith
    rcases mul_eq_zero.mp hmul with hMx | hNy
    · exact hx hMx
    · exact hy hNy
  have hX :
      Tensor.valueAt halfAddTensor (LFT.apply M x) (LFT.apply N y) =
        Tensor.valueAt (halfAddTensor.absorbX M) x (LFT.apply N y) :=
    Tensor.absorbX_invariant (T := halfAddTensor) (M := M) (x := x) (y := LFT.apply N y)
      hx hdenHalf hdenAbsorbX
  have hY :
      Tensor.valueAt (halfAddTensor.absorbX M) x (LFT.apply N y) =
        Tensor.valueAt ((halfAddTensor.absorbX M).absorbY N) x y :=
    Tensor.absorbY_invariant (T := halfAddTensor.absorbX M) (M := N) (x := x) (y := y)
      hy hdenAbsorbX hdenFinal
  calc
    Tensor.apply ((halfAddTensor.absorbX M).absorbY N) x y
        = Tensor.valueAt (halfAddTensor.absorbX M) x (LFT.apply N y) := by
            simpa [Tensor.valueAt] using hY.symm
    _ = Tensor.valueAt halfAddTensor (LFT.apply M x) (LFT.apply N y) := by
          simpa [Tensor.valueAt] using hX.symm
    _ = (LFT.apply M x + LFT.apply N y) / 2 := by
          simpa [Tensor.valueAt] using halfAddTensor_valueAt (LFT.apply M x) (LFT.apply N y)

theorem halfAddTensorStateAfter_apply (X Y : MobiusReal) (N : ℕ) {x y : ℝ}
    (hx : x ∈ baseI) (hy : y ∈ baseI) :
    Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) x y =
      (LFT.apply (pairedPrefix X.stream N) x + LFT.apply (pairedPrefix Y.stream N) y) / 2 := by
  rw [absorbBoth_n_halfAdd_eq_avgTensor]
  exact avgTensor_apply (pairedPrefix X.stream N) (pairedPrefix Y.stream N) x y
    (pairedPrefix_denom_ne_zero X N hx) (pairedPrefix_denom_ne_zero Y N hy)

theorem halfAddTensorStateAfter_emit_eq_avgTensor
    (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    (halfAddTensorStateAfter X Y N).T.emit (digit_to_LFT d) =
      avgTensor
        ((residualDigitLFT d).comp (pairedPrefix X.stream N))
        ((residualDigitLFT d).comp (pairedPrefix Y.stream N)) := by
  rw [halfAddTensorStateAfter, absorbBoth_n_halfAdd_eq_avgTensor]
  exact avgTensor_emit_digit (pairedPrefix X.stream N) (pairedPrefix Y.stream N) d

theorem halfAddTensorXStateAfter_eq_avgTensor
    (X Y : MobiusReal) (N : ℕ) :
    (halfAddTensorXStateAfter X Y N).T =
      avgTensor ((pairedPrefix X.stream N).comp (X.stream N)) (pairedPrefix Y.stream N) := by
  rw [halfAddTensorXStateAfter, absorbBoth_n_halfAdd_eq_avgTensor]
  apply Tensor.ext <;> simp [avgTensor, Tensor.absorbX, LFT.comp] <;> ring

theorem halfAddTensorXStateAfter_emit_eq_avgTensor
    (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) =
      avgTensor
        ((residualDigitLFT d).comp ((pairedPrefix X.stream N).comp (X.stream N)))
        ((residualDigitLFT d).comp (pairedPrefix Y.stream N)) := by
  have habsorbX :
      (halfAddTensorXStateAfter X Y N).T =
        avgTensor ((pairedPrefix X.stream N).comp (X.stream N)) (pairedPrefix Y.stream N) := by
    exact halfAddTensorXStateAfter_eq_avgTensor X Y N
  rw [habsorbX]
  exact avgTensor_emit_digit ((pairedPrefix X.stream N).comp (X.stream N))
    (pairedPrefix Y.stream N) d

def halfAddResidualStateAfter (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) : VMState where
  T := Tensor.absorbBoth_n
    ((halfAddTensorStateAfter X Y N).T.emit (digit_to_LFT d))
    (MobiusReal.drop X N).stream (MobiusReal.drop Y N).stream K
  idx_x := N + K
  idx_y := N + K
  absorb_x_next := true

def halfAddResidualXStateAfter (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) : VMState where
  T := (halfAddResidualStateAfter X Y N d K).T.absorbX ((MobiusReal.drop X N).stream K)
  idx_x := N + K + 1
  idx_y := N + K
  absorb_x_next := false

@[simp] theorem halfAddResidualStateAfter_zero (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    halfAddResidualStateAfter X Y N d 0 =
      { halfAddTensorStateAfter X Y N with
          T := (halfAddTensorStateAfter X Y N).T.emit (digit_to_LFT d) } := by
  simp [halfAddResidualStateAfter, halfAddTensorStateAfter, Tensor.absorbBoth_n]

theorem halfAddResidualStateAfter_eq_avgTensor
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    (halfAddResidualStateAfter X Y N d K).T =
      avgTensor
        (((residualDigitLFT d).comp (pairedPrefix X.stream N)).comp
          (pairedPrefix (MobiusReal.drop X N).stream K))
        (((residualDigitLFT d).comp (pairedPrefix Y.stream N)).comp
          (pairedPrefix (MobiusReal.drop Y N).stream K)) := by
  unfold halfAddResidualStateAfter
  rw [halfAddTensorStateAfter_emit_eq_avgTensor]
  simpa [LFT.comp_assoc] using
    absorbBoth_n_avgTensor_eq
      ((residualDigitLFT d).comp (pairedPrefix X.stream N))
      ((residualDigitLFT d).comp (pairedPrefix Y.stream N))
      (MobiusReal.drop X N).stream (MobiusReal.drop Y N).stream K

theorem halfAddResidualStateAfter_eq_avgTensor'
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    (halfAddResidualStateAfter X Y N d K).T =
      avgTensor
        ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K)))
        ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) := by
  rw [halfAddResidualStateAfter_eq_avgTensor]
  simp [MobiusReal.drop, pairedPrefix_append_shift, LFT.comp_assoc]

theorem halfAddResidualXStateAfter_eq_avgTensor
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    (halfAddResidualXStateAfter X Y N d K).T =
      avgTensor
        ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K + 1)))
        ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) := by
  rw [halfAddResidualXStateAfter, halfAddResidualStateAfter_eq_avgTensor']
  have hdrop : (MobiusReal.drop X N).stream K = X.stream (N + K) := by
    simp [MobiusReal.drop, Nat.add_comm]
  rw [hdrop, avgTensor_absorbX]
  simp [pairedPrefix, LFT.comp_assoc]

theorem halfAddResidualStateAfter_apply
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) {x y : ℝ}
    (hx : x ∈ baseI) (hy : y ∈ baseI) :
    Tensor.apply (halfAddResidualStateAfter X Y N d K).T x y =
      (LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) x +
        LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) y) / 2 := by
  let MX := (residualDigitLFT d).comp (pairedPrefix X.stream (N + K))
  let MY := (residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))
  rw [halfAddResidualStateAfter_eq_avgTensor']
  exact avgTensor_apply
    MX MY x y
    (by
      cases d <;>
        simpa [MX, residualDigitLFT, LFT.comp] using pairedPrefix_denom_ne_zero X (N + K) hx)
    (by
      cases d <;>
        simpa [MY, residualDigitLFT, LFT.comp] using pairedPrefix_denom_ne_zero Y (N + K) hy)

theorem residualDigitLFT_apply_diff (d : Digit) (u v : ℝ) :
    |LFT.apply (residualDigitLFT d) u - LFT.apply (residualDigitLFT d) v| = 2 * |u - v| := by
  cases d
  · have hlin : 2 * u - 2 * v = 2 * (u - v) := by ring
    simp [residualDigitLFT, LFT.apply, hlin, abs_mul]
  · have hlin : 2 * u - 2 * v = 2 * (u - v) := by ring
    simp [residualDigitLFT, LFT.apply, hlin, abs_mul]
  · have hlin : 2 * u - 2 * v = 2 * (u - v) := by ring
    simp [residualDigitLFT, LFT.apply, hlin, abs_mul]

theorem residualDigitLFT_outer_denom_ne_zero (d : Digit) (r : ℝ) :
    (((residualDigitLFT d).c : ℝ) * r + ((residualDigitLFT d).d : ℝ)) ≠ 0 := by
  cases d <;> simp [residualDigitLFT]

theorem halfAddResidualStateAfter_diff_lt
    (X Y : MobiusReal) (N : ℕ) (d : Digit) {ε : ℝ} (hε : 0 < ε) :
    ∃ K0 : ℕ, ∀ K ≥ K0, ∀ x ∈ baseI, ∀ w ∈ baseI, ∀ y ∈ baseI, ∀ z ∈ baseI,
      |Tensor.apply (halfAddResidualStateAfter X Y N d K).T x y -
        Tensor.apply (halfAddResidualStateAfter X Y N d K).T w z| < ε := by
  have hε2 : 0 < ε / 2 := by linarith
  rcases X.contractive.shrinks_to_zero (ε / 2) hε2 with ⟨NX, hNX⟩
  rcases Y.contractive.shrinks_to_zero (ε / 2) hε2 with ⟨NY, hNY⟩
  refine ⟨max NX NY + 1, ?_⟩
  intro K hK x hx w hw y hy z hz
  have hKN : K ≤ N + K := by
    omega
  have hNk : max NX NY + 1 ≤ N + K := le_trans hK hKN
  cases hsum : N + K with
  | zero =>
      exfalso
      simp [hsum] at hNk
  | succ n =>
      have hn : max NX NY ≤ n := Nat.le_of_succ_le_succ (by simpa [hsum] using hNk)
      have hnX : n ≥ NX := le_trans (Nat.le_max_left _ _) hn
      have hnY : n ≥ NY := le_trans (Nat.le_max_right _ _) hn
      have hdx0 :
          |LFT.apply (partialComp X.stream n) x - LFT.apply (partialComp X.stream n) w| < ε / 2 := by
        simpa [partialComp] using hNX n hnX 0 x hx w hw
      have hdy0 :
          |LFT.apply (partialComp Y.stream n) y - LFT.apply (partialComp Y.stream n) z| < ε / 2 := by
        simpa [partialComp] using hNY n hnY 0 y hy z hz
      have hdx :
          |LFT.apply (pairedPrefix X.stream (N + K)) x - LFT.apply (pairedPrefix X.stream (N + K)) w| < ε / 2 := by
        rw [hsum, pairedPrefix_eq_partialComp]
        exact hdx0
      have hdy :
          |LFT.apply (pairedPrefix Y.stream (N + K)) y - LFT.apply (pairedPrefix Y.stream (N + K)) z| < ε / 2 := by
        rw [hsum, pairedPrefix_eq_partialComp]
        exact hdy0
      rw [halfAddResidualStateAfter_apply X Y N d K hx hy,
        halfAddResidualStateAfter_apply X Y N d K hw hz]
      have hsplit :
          |((LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) x +
                LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) y) / 2) -
            ((LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) w +
                LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) z) / 2)|
              ≤ (|LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) x -
                    LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) w| +
                  |LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) y -
                    LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) z|) / 2 := by
        calc
          |((LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) x +
                LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) y) / 2) -
              ((LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) w +
                LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) z) / 2)|
              = |((LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) x -
                    LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) w) +
                  (LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) y -
                    LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) z)) / 2| := by
                  ring_nf
          _ = |(LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) x -
                LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) w) +
              (LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) y -
                LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) z)| / 2 := by
                simp [abs_div]
          _ ≤ (|LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) x -
                  LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) w| +
                |LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) y -
                  LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) z|) / 2 := by
                gcongr
                exact abs_add_le _ _
      have hdenx1 : (((pairedPrefix X.stream (N + K)).c : ℝ) * x + ((pairedPrefix X.stream (N + K)).d : ℝ)) ≠ 0 :=
        pairedPrefix_denom_ne_zero X (N + K) hx
      have hdenx2 : (((pairedPrefix X.stream (N + K)).c : ℝ) * w + ((pairedPrefix X.stream (N + K)).d : ℝ)) ≠ 0 :=
        pairedPrefix_denom_ne_zero X (N + K) hw
      have hdx' :
          |LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) x -
            LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) w| < ε := by
        have hcomp1 :
            LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) x =
              LFT.apply (residualDigitLFT d) (LFT.apply (pairedPrefix X.stream (N + K)) x) := by
          simpa using
            LFT.apply_comp (residualDigitLFT d) (pairedPrefix X.stream (N + K)) x
              hdenx1 (residualDigitLFT_outer_denom_ne_zero d _)
        have hcomp2 :
            LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) w =
              LFT.apply (residualDigitLFT d) (LFT.apply (pairedPrefix X.stream (N + K)) w) := by
          simpa using
            LFT.apply_comp (residualDigitLFT d) (pairedPrefix X.stream (N + K)) w
              hdenx2 (residualDigitLFT_outer_denom_ne_zero d _)
        rw [hcomp1, hcomp2, residualDigitLFT_apply_diff]
        nlinarith
      have hdeny1 : (((pairedPrefix Y.stream (N + K)).c : ℝ) * y + ((pairedPrefix Y.stream (N + K)).d : ℝ)) ≠ 0 :=
        pairedPrefix_denom_ne_zero Y (N + K) hy
      have hdeny2 : (((pairedPrefix Y.stream (N + K)).c : ℝ) * z + ((pairedPrefix Y.stream (N + K)).d : ℝ)) ≠ 0 :=
        pairedPrefix_denom_ne_zero Y (N + K) hz
      have hdy' :
          |LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) y -
            LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) z| < ε := by
        have hcomp1 :
            LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) y =
              LFT.apply (residualDigitLFT d) (LFT.apply (pairedPrefix Y.stream (N + K)) y) := by
          simpa using
            LFT.apply_comp (residualDigitLFT d) (pairedPrefix Y.stream (N + K)) y
              hdeny1 (residualDigitLFT_outer_denom_ne_zero d _)
        have hcomp2 :
            LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) z =
              LFT.apply (residualDigitLFT d) (LFT.apply (pairedPrefix Y.stream (N + K)) z) := by
          simpa using
            LFT.apply_comp (residualDigitLFT d) (pairedPrefix Y.stream (N + K)) z
              hdeny2 (residualDigitLFT_outer_denom_ne_zero d _)
        rw [hcomp1, hcomp2, residualDigitLFT_apply_diff]
        nlinarith
      have hsum' :
          (|LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) x -
              LFT.apply ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))) w| +
            |LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) y -
              LFT.apply ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))) z|) / 2 < ε := by
        nlinarith
      exact lt_of_le_of_lt hsplit hsum'

theorem halfAddResidualStateAfter_hasNoPoleOnBase
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    (halfAddResidualStateAfter X Y N d K).T.HasNoPoleOnBase := by
  intro x hx y hy
  rw [halfAddResidualStateAfter_eq_avgTensor']
  have hMx : (((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))).c : ℝ) * x +
      (((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))).d : ℝ) ≠ 0 := by
    simpa using pairedPrefix_denom_ne_zero X (N + K) hx
  have hMy : (((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))).c : ℝ) * y +
      (((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))).d : ℝ) ≠ 0 := by
    simpa using pairedPrefix_denom_ne_zero Y (N + K) hy
  intro h0
  have hmul :
      ((((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))).c : ℝ) * x +
        (((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))).d : ℝ)) *
      ((((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))).c : ℝ) * y +
        (((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))).d : ℝ)) = 0 := by
    set AX : ℝ :=
      (((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))).c : ℝ) * x +
        (((residualDigitLFT d).comp (pairedPrefix X.stream (N + K))).d : ℝ)
    set AY : ℝ :=
      (((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))).c : ℝ) * y +
        (((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))).d : ℝ)
    have h0' : (2 : ℝ) * AX * AY = 0 := by
      subst AX AY
      convert h0 using 1
      simp [Tensor.denAt, avgTensor, residualDigitLFT, LFT.comp]
      ring_nf
    nlinarith
  rcases mul_eq_zero.mp hmul with hX | hY
  · exact hMx hX
  · exact hMy hY

theorem halfAddResidualXStateAfter_hasNoPoleOnBase
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    (halfAddResidualXStateAfter X Y N d K).T.HasNoPoleOnBase := by
  intro x hx y hy
  rw [halfAddResidualXStateAfter_eq_avgTensor]
  have hMx : (((residualDigitLFT d).comp (pairedPrefix X.stream (N + K + 1))).c : ℝ) * x +
      (((residualDigitLFT d).comp (pairedPrefix X.stream (N + K + 1))).d : ℝ) ≠ 0 := by
    simpa using pairedPrefix_denom_ne_zero X (N + K + 1) hx
  have hMy : (((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))).c : ℝ) * y +
      (((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))).d : ℝ) ≠ 0 := by
    simpa using pairedPrefix_denom_ne_zero Y (N + K) hy
  intro h0
  have hmul :
      ((((residualDigitLFT d).comp (pairedPrefix X.stream (N + K + 1))).c : ℝ) * x +
        (((residualDigitLFT d).comp (pairedPrefix X.stream (N + K + 1))).d : ℝ)) *
      ((((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))).c : ℝ) * y +
        (((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))).d : ℝ)) = 0 := by
    set AX : ℝ :=
      (((residualDigitLFT d).comp (pairedPrefix X.stream (N + K + 1))).c : ℝ) * x +
        (((residualDigitLFT d).comp (pairedPrefix X.stream (N + K + 1))).d : ℝ)
    set AY : ℝ :=
      (((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))).c : ℝ) * y +
        (((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K))).d : ℝ)
    have h0' : (2 : ℝ) * AX * AY = 0 := by
      subst AX AY
      convert h0 using 1
      simp [Tensor.denAt, avgTensor, residualDigitLFT, LFT.comp]
      ring_nf
    nlinarith
  rcases mul_eq_zero.mp hmul with hX | hY
  · exact hMx hX
  · exact hMy hY

theorem halfAddTensorXStateAfter_hasNoPoleOnBase
    (X Y : MobiusReal) (N : ℕ) :
    (halfAddTensorXStateAfter X Y N).T.HasNoPoleOnBase := by
  intro x hx y hy
  rw [halfAddTensorXStateAfter_eq_avgTensor]
  have hMx : ((((pairedPrefix X.stream N).comp (X.stream N)).c : ℝ) * x +
      (((pairedPrefix X.stream N).comp (X.stream N)).d : ℝ)) ≠ 0 := by
    simpa [pairedPrefix] using pairedPrefix_denom_ne_zero X (N + 1) hx
  have hMy : (((pairedPrefix Y.stream N).c : ℝ) * y + ((pairedPrefix Y.stream N).d : ℝ)) ≠ 0 := by
    simpa using pairedPrefix_denom_ne_zero Y N hy
  intro h0
  have hmul :
      ((((pairedPrefix X.stream N).comp (X.stream N)).c : ℝ) * x +
        (((pairedPrefix X.stream N).comp (X.stream N)).d : ℝ)) *
      ((((pairedPrefix Y.stream N).c : ℝ) * y + ((pairedPrefix Y.stream N).d : ℝ))) = 0 := by
    set AX : ℝ :=
      (((pairedPrefix X.stream N).comp (X.stream N)).c : ℝ) * x +
        (((pairedPrefix X.stream N).comp (X.stream N)).d : ℝ)
    set AY : ℝ :=
      (((pairedPrefix Y.stream N).c : ℝ) * y + ((pairedPrefix Y.stream N).d : ℝ))
    have h0' : (2 : ℝ) * AX * AY = 0 := by
      subst AX AY
      convert h0 using 1
      simp [Tensor.denAt, avgTensor, LFT.comp]
      ring_nf
    nlinarith
  rcases mul_eq_zero.mp hmul with hX | hY
  · exact hMx hX
  · exact hMy hY

theorem halfAddTensorXStateAfter_emit_hasNoPoleOnBase
    (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    ({ halfAddTensorXStateAfter X Y N with
        T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }).T.HasNoPoleOnBase := by
  intro x hx y hy
  rw [halfAddTensorXStateAfter_emit_eq_avgTensor]
  have hMx : (((residualDigitLFT d).comp (pairedPrefix X.stream (N + 1))).c : ℝ) * x +
      (((residualDigitLFT d).comp (pairedPrefix X.stream (N + 1))).d : ℝ) ≠ 0 := by
    simpa using pairedPrefix_denom_ne_zero X (N + 1) hx
  have hMy : (((residualDigitLFT d).comp (pairedPrefix Y.stream N)).c : ℝ) * y +
      (((residualDigitLFT d).comp (pairedPrefix Y.stream N)).d : ℝ) ≠ 0 := by
    simpa using pairedPrefix_denom_ne_zero Y N hy
  intro h0
  have hmul :
      ((((residualDigitLFT d).comp (pairedPrefix X.stream (N + 1))).c : ℝ) * x +
        (((residualDigitLFT d).comp (pairedPrefix X.stream (N + 1))).d : ℝ)) *
      ((((residualDigitLFT d).comp (pairedPrefix Y.stream N)).c : ℝ) * y +
        (((residualDigitLFT d).comp (pairedPrefix Y.stream N)).d : ℝ)) = 0 := by
    set AX : ℝ :=
      (((residualDigitLFT d).comp (pairedPrefix X.stream (N + 1))).c : ℝ) * x +
        (((residualDigitLFT d).comp (pairedPrefix X.stream (N + 1))).d : ℝ)
    set AY : ℝ :=
      (((residualDigitLFT d).comp (pairedPrefix Y.stream N)).c : ℝ) * y +
        (((residualDigitLFT d).comp (pairedPrefix Y.stream N)).d : ℝ)
    have h0' : (2 : ℝ) * AX * AY = 0 := by
      subst AX AY
      convert h0 using 1
      simp [Tensor.denAt, avgTensor, residualDigitLFT, LFT.comp]
      ring_nf
    nlinarith
  rcases mul_eq_zero.mp hmul with hX | hY
  · exact hMx hX
  · exact hMy hY

theorem halfAddTensorXStateAfter_emit_mapsBaseI_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorXStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorXStateAfter X Y N with
          T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ({ halfAddTensorXStateAfter X Y N with
        T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }).T.MapsBaseI := by
  intro x hx y hy
  let s' : VMState := { halfAddTensorXStateAfter X Y N with
    T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }
  have hdenOld : Tensor.denAt (halfAddTensorXStateAfter X Y N).T x y ≠ 0 := by
    exact halfAddTensorXStateAfter_hasNoPoleOnBase X Y N x hx y hy
  have hdenNew : Tensor.denAt s'.T x y ≠ 0 := by
    simpa [s'] using halfAddTensorXStateAfter_emit_hasNoPoleOnBase X Y N d x hx y hy
  cases d with
  | neg =>
      have horacle :
          (halfAddTensorXStateAfter X Y N).T.oracle = Tensor.EmitDecision.neg := by
        exact GeneralTrace.oracle_eq_of_step_neg X Y (by simpa [digit_to_LFT] using hstep)
      have hold :
          -1 ≤ Tensor.apply (halfAddTensorXStateAfter X Y N).T x y ∧
            Tensor.apply (halfAddTensorXStateAfter X Y N).T x y ≤ 0 := by
        simpa using Tensor.emitNeg_sound (T := (halfAddTensorXStateAfter X Y N).T)
          (x := x) (y := y) hx.1 hx.2 hy.1 hy.2 horacle
      have hlft :
          ((digitNeg.c : ℝ) * Tensor.valueAt s'.T x y + (digitNeg.d : ℝ)) ≠ 0 := by
        simp [digitNeg]
      have hEq :
          Tensor.apply (halfAddTensorXStateAfter X Y N).T x y =
            LFT.apply digitNeg (Tensor.apply s'.T x y) := by
        simpa [Tensor.valueAt, s'] using
          (Tensor.emit_invariant (T := (halfAddTensorXStateAfter X Y N).T) (D := digitNeg)
            (x := x) (y := y) hdenNew hdenOld hlft)
      constructor
      · have heq :
            Tensor.apply (halfAddTensorXStateAfter X Y N).T x y =
              ((Tensor.apply s'.T x y) - 1) / 2 := by
            simpa [digitNeg, LFT.apply] using hEq
        nlinarith [hold.1, heq]
      · have heq :
            Tensor.apply (halfAddTensorXStateAfter X Y N).T x y =
              ((Tensor.apply s'.T x y) - 1) / 2 := by
            simpa [digitNeg, LFT.apply] using hEq
        nlinarith [hold.2, heq]
  | zero =>
      have horacle :
          (halfAddTensorXStateAfter X Y N).T.oracle = Tensor.EmitDecision.zero := by
        exact GeneralTrace.oracle_eq_of_step_zero X Y (by simpa [digit_to_LFT] using hstep)
      have hold :
          (-1 / 2 : ℝ) ≤ Tensor.apply (halfAddTensorXStateAfter X Y N).T x y ∧
            Tensor.apply (halfAddTensorXStateAfter X Y N).T x y ≤ (1 / 2 : ℝ) := by
        simpa using Tensor.emitZero_sound (T := (halfAddTensorXStateAfter X Y N).T)
          (x := x) (y := y) hx.1 hx.2 hy.1 hy.2 horacle
      have hlft :
          ((digitZero.c : ℝ) * Tensor.valueAt s'.T x y + (digitZero.d : ℝ)) ≠ 0 := by
        simp [digitZero]
      have hEq :
          Tensor.apply (halfAddTensorXStateAfter X Y N).T x y =
            LFT.apply digitZero (Tensor.apply s'.T x y) := by
        simpa [Tensor.valueAt, s'] using
          (Tensor.emit_invariant (T := (halfAddTensorXStateAfter X Y N).T) (D := digitZero)
            (x := x) (y := y) hdenNew hdenOld hlft)
      constructor
      · have heq :
            Tensor.apply (halfAddTensorXStateAfter X Y N).T x y =
              (Tensor.apply s'.T x y) / 2 := by
            simpa [digitZero, LFT.apply] using hEq
        nlinarith [hold.1, heq]
      · have heq :
            Tensor.apply (halfAddTensorXStateAfter X Y N).T x y =
              (Tensor.apply s'.T x y) / 2 := by
            simpa [digitZero, LFT.apply] using hEq
        nlinarith [hold.2, heq]
  | pos =>
      have horacle :
          (halfAddTensorXStateAfter X Y N).T.oracle = Tensor.EmitDecision.pos := by
        exact GeneralTrace.oracle_eq_of_step_pos X Y (by simpa [digit_to_LFT] using hstep)
      have hold :
          0 ≤ Tensor.apply (halfAddTensorXStateAfter X Y N).T x y ∧
            Tensor.apply (halfAddTensorXStateAfter X Y N).T x y ≤ 1 := by
        simpa using Tensor.emitPos_sound (T := (halfAddTensorXStateAfter X Y N).T)
          (x := x) (y := y) hx.1 hx.2 hy.1 hy.2 horacle
      have hlft :
          ((digitPos.c : ℝ) * Tensor.valueAt s'.T x y + (digitPos.d : ℝ)) ≠ 0 := by
        simp [digitPos]
      have hEq :
          Tensor.apply (halfAddTensorXStateAfter X Y N).T x y =
            LFT.apply digitPos (Tensor.apply s'.T x y) := by
        simpa [Tensor.valueAt, s'] using
          (Tensor.emit_invariant (T := (halfAddTensorXStateAfter X Y N).T) (D := digitPos)
            (x := x) (y := y) hdenNew hdenOld hlft)
      constructor
      · have heq :
            Tensor.apply (halfAddTensorXStateAfter X Y N).T x y =
              ((Tensor.apply s'.T x y) + 1) / 2 := by
            simpa [digitPos, LFT.apply] using hEq
        nlinarith [hold.1, heq]
      · have heq :
            Tensor.apply (halfAddTensorXStateAfter X Y N).T x y =
              ((Tensor.apply s'.T x y) + 1) / 2 := by
            simpa [digitPos, LFT.apply] using hEq
        nlinarith [hold.2, heq]

theorem halfAddResidualStateAfter_one_eq_from_Xstep
    (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    (halfAddResidualStateAfter X Y N d 1).T =
      ({ halfAddTensorXStateAfter X Y N with
          T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }).T.absorbY (Y.stream N) := by
  rw [halfAddResidualStateAfter_eq_avgTensor']
  rw [halfAddTensorXStateAfter_emit_eq_avgTensor]
  rw [avgTensor_absorbY]
  simp [pairedPrefix, LFT.comp_assoc]


theorem Tensor.mapsBaseI_absorbX (T : Tensor) (M : LFT)
    (hT : T.MapsBaseI)
    (hTNoPole : T.HasNoPoleOnBase)
    (hNewNoPole : (T.absorbX M).HasNoPoleOnBase)
    (hMMaps : Set.MapsTo (fun x => LFT.apply M x) baseI baseI)
    (hMNoPole : M.NoPoleOnBase) :
    (T.absorbX M).MapsBaseI := by
  intro x hx y hy
  let x' := LFT.apply M x
  have hx' : x' ∈ baseI := by
    exact hMMaps hx
  have hdenM : ((M.c : ℝ) * x + (M.d : ℝ)) ≠ 0 := by
    exact LFT.denom_ne_zero_of_NoPoleOnBase M hx hMNoPole
  have hdenOld : Tensor.denAt T x' y ≠ 0 := by
    exact hTNoPole x' hx' y hy
  have hdenNew : Tensor.denAt (T.absorbX M) x y ≠ 0 := by
    exact hNewNoPole x hx y hy
  have hEq :
      Tensor.apply (T.absorbX M) x y = Tensor.apply T x' y := by
    simpa [Tensor.valueAt, x'] using
      (Tensor.absorbX_invariant (T := T) (M := M) (x := x) (y := y) hdenM hdenOld hdenNew).symm
  rw [hEq]
  exact hT x' hx' y hy

theorem Tensor.mapsBaseI_absorbY (T : Tensor) (M : LFT)
    (hT : T.MapsBaseI)
    (hTNoPole : T.HasNoPoleOnBase)
    (hNewNoPole : (T.absorbY M).HasNoPoleOnBase)
    (hMMaps : Set.MapsTo (fun y => LFT.apply M y) baseI baseI)
    (hMNoPole : M.NoPoleOnBase) :
    (T.absorbY M).MapsBaseI := by
  intro x hx y hy
  let y' := LFT.apply M y
  have hy' : y' ∈ baseI := by
    exact hMMaps hy
  have hdenM : ((M.c : ℝ) * y + (M.d : ℝ)) ≠ 0 := by
    exact LFT.denom_ne_zero_of_NoPoleOnBase M hy hMNoPole
  have hdenOld : Tensor.denAt T x y' ≠ 0 := by
    exact hTNoPole x hx y' hy'
  have hdenNew : Tensor.denAt (T.absorbY M) x y ≠ 0 := by
    exact hNewNoPole x hx y hy
  have hEq :
      Tensor.apply (T.absorbY M) x y = Tensor.apply T x y' := by
    simpa [Tensor.valueAt, y'] using
      (Tensor.absorbY_invariant (T := T) (M := M) (x := x) (y := y) hdenM hdenOld hdenNew).symm
  rw [hEq]
  exact hT x hx y' hy'

theorem halfAddResidualStateAfter_mapsBaseI_pair_of_Xstep
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorXStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorXStateAfter X Y N with
          T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∀ K,
      (halfAddResidualStateAfter X Y N d (K + 1)).T.MapsBaseI ∧
      (halfAddResidualXStateAfter X Y N d (K + 1)).T.MapsBaseI
  | 0 => by
      let s' : VMState := { halfAddTensorXStateAfter X Y N with
        T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }
      have hState1 :
          (halfAddResidualStateAfter X Y N d 1).T.MapsBaseI := by
        have hNoPole1 : (s'.T.absorbY (Y.stream N)).HasNoPoleOnBase := by
          rw [← halfAddResidualStateAfter_one_eq_from_Xstep X Y N d]
          exact halfAddResidualStateAfter_hasNoPoleOnBase X Y N d 1
        rw [halfAddResidualStateAfter_one_eq_from_Xstep]
        exact Tensor.mapsBaseI_absorbY s'.T (Y.stream N)
          (halfAddTensorXStateAfter_emit_mapsBaseI_of_step X Y N d hstep)
          (by simpa [s'] using halfAddTensorXStateAfter_emit_hasNoPoleOnBase X Y N d)
          hNoPole1
          (IsContractive.maps_base_step Y.contractive N)
          (IsContractive.no_poles_step Y.contractive N)
      refine ⟨hState1, ?_⟩
      exact Tensor.mapsBaseI_absorbX
        ((halfAddResidualStateAfter X Y N d 1).T)
        ((MobiusReal.drop X N).stream 1)
        hState1
        (halfAddResidualStateAfter_hasNoPoleOnBase X Y N d 1)
        (halfAddResidualXStateAfter_hasNoPoleOnBase X Y N d 1)
        (IsContractive.maps_base_step (MobiusReal.drop X N).contractive 1)
        (IsContractive.no_poles_step (MobiusReal.drop X N).contractive 1)
  | K + 1 => by
      rcases halfAddResidualStateAfter_mapsBaseI_pair_of_Xstep X Y N d hstep K with
        ⟨hStateK, hXK⟩
      have hStateSucc :
          (halfAddResidualStateAfter X Y N d (K + 2)).T.MapsBaseI := by
        have hEq :
            (halfAddResidualStateAfter X Y N d (K + 2)).T =
              (halfAddResidualXStateAfter X Y N d (K + 1)).T.absorbY
                ((MobiusReal.drop Y N).stream (K + 1)) := by
          simp [halfAddResidualStateAfter, halfAddResidualXStateAfter, Tensor.absorbBoth_n]
        rw [hEq]
        exact Tensor.mapsBaseI_absorbY
          ((halfAddResidualXStateAfter X Y N d (K + 1)).T)
          ((MobiusReal.drop Y N).stream (K + 1))
          hXK
          (halfAddResidualXStateAfter_hasNoPoleOnBase X Y N d (K + 1))
          (halfAddResidualStateAfter_hasNoPoleOnBase X Y N d (K + 2))
          (IsContractive.maps_base_step (MobiusReal.drop Y N).contractive (K + 1))
          (IsContractive.no_poles_step (MobiusReal.drop Y N).contractive (K + 1))
      have hXSucc :
          (halfAddResidualXStateAfter X Y N d (K + 2)).T.MapsBaseI := by
        exact Tensor.mapsBaseI_absorbX
          ((halfAddResidualStateAfter X Y N d (K + 2)).T)
          ((MobiusReal.drop X N).stream (K + 2))
          hStateSucc
          (halfAddResidualStateAfter_hasNoPoleOnBase X Y N d (K + 2))
          (halfAddResidualXStateAfter_hasNoPoleOnBase X Y N d (K + 2))
          (IsContractive.maps_base_step (MobiusReal.drop X N).contractive (K + 2))
          (IsContractive.no_poles_step (MobiusReal.drop X N).contractive (K + 2))
      exact ⟨hStateSucc, hXSucc⟩

theorem halfAddResidualStateAfter_corner_mem_baseI_of_Xstep
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorXStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorXStateAfter X Y N with
          T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∀ K,
      Tensor.apply (halfAddResidualStateAfter X Y N d (K + 1)).T 1 1 ∈ baseI ∧
        Tensor.apply (halfAddResidualStateAfter X Y N d (K + 1)).T 1 (-1) ∈ baseI ∧
        Tensor.apply (halfAddResidualStateAfter X Y N d (K + 1)).T (-1) 1 ∈ baseI ∧
        Tensor.apply (halfAddResidualStateAfter X Y N d (K + 1)).T (-1) (-1) ∈ baseI := by
  intro K
  have hMaps := (halfAddResidualStateAfter_mapsBaseI_pair_of_Xstep X Y N d hstep K).1
  have h1 : (1 : ℝ) ∈ baseI := by constructor <;> norm_num
  have hm1 : (-1 : ℝ) ∈ baseI := by constructor <;> norm_num
  constructor
  · exact hMaps 1 h1 1 h1
  constructor
  · exact hMaps 1 h1 (-1) hm1
  constructor
  · exact hMaps (-1) hm1 1 h1
  · exact hMaps (-1) hm1 (-1) hm1

theorem halfAddResidualStateAfter_zero_mapsBaseI_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorStateAfter X Y N with
          T := (halfAddTensorStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    (halfAddResidualStateAfter X Y N d 0).T.MapsBaseI := by
  intro x hx y hy
  have hdenOld :
      Tensor.denAt (halfAddTensorStateAfter X Y N).T x y ≠ 0 := by
    rw [halfAddTensorStateAfter, absorbBoth_n_halfAdd_eq_avgTensor]
    let AX : ℝ :=
      (((pairedPrefix X.stream N).c : ℝ) * x + ((pairedPrefix X.stream N).d : ℝ))
    let AY : ℝ :=
      (((pairedPrefix Y.stream N).c : ℝ) * y + ((pairedPrefix Y.stream N).d : ℝ))
    have hMx : AX ≠ 0 := by
      simpa [AX] using pairedPrefix_denom_ne_zero X N hx
    have hMy : AY ≠ 0 := by
      simpa [AY] using pairedPrefix_denom_ne_zero Y N hy
    intro h0
    have h0' : (2 : ℝ) * AX * AY = 0 := by
      subst AX AY
      convert h0 using 1
      simp [Tensor.denAt, avgTensor]
      ring_nf
    have hmul : AX * AY = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hmul with hX | hY
    · exact hMx hX
    · exact hMy hY
  have hdenNew :
      Tensor.denAt (halfAddResidualStateAfter X Y N d 0).T x y ≠ 0 := by
    simpa using halfAddResidualStateAfter_hasNoPoleOnBase X Y N d 0 x hx y hy
  cases d with
  | neg =>
      have horacle :
          (halfAddTensorStateAfter X Y N).T.oracle = Tensor.EmitDecision.neg := by
        exact GeneralTrace.oracle_eq_of_step_neg X Y (by simpa [digit_to_LFT] using hstep)
      have hold :
          -1 ≤ Tensor.apply (halfAddTensorStateAfter X Y N).T x y ∧
            Tensor.apply (halfAddTensorStateAfter X Y N).T x y ≤ 0 := by
        simpa using Tensor.emitNeg_sound (T := (halfAddTensorStateAfter X Y N).T)
          (x := x) (y := y) hx.1 hx.2 hy.1 hy.2 horacle
      have hlft :
          ((digitNeg.c : ℝ) * Tensor.valueAt (halfAddResidualStateAfter X Y N .neg 0).T x y +
            (digitNeg.d : ℝ)) ≠ 0 := by
        simp [digitNeg]
      have hEq :
          Tensor.apply (halfAddTensorStateAfter X Y N).T x y =
            LFT.apply digitNeg (Tensor.apply (halfAddResidualStateAfter X Y N .neg 0).T x y) := by
        simpa [halfAddResidualStateAfter_zero, Tensor.valueAt] using
          (Tensor.emit_invariant
            (T := (halfAddTensorStateAfter X Y N).T) (D := digitNeg)
            (x := x) (y := y) hdenNew hdenOld hlft)
      constructor
      · have heq :
            Tensor.apply (halfAddTensorStateAfter X Y N).T x y =
              ((Tensor.apply (halfAddResidualStateAfter X Y N .neg 0).T x y) - 1) / 2 := by
            simpa [digitNeg, LFT.apply] using hEq
        nlinarith [hold.1, heq]
      · have heq :
            Tensor.apply (halfAddTensorStateAfter X Y N).T x y =
              ((Tensor.apply (halfAddResidualStateAfter X Y N .neg 0).T x y) - 1) / 2 := by
            simpa [digitNeg, LFT.apply] using hEq
        nlinarith [hold.2, heq]
  | zero =>
      have horacle :
          (halfAddTensorStateAfter X Y N).T.oracle = Tensor.EmitDecision.zero := by
        exact GeneralTrace.oracle_eq_of_step_zero X Y (by simpa [digit_to_LFT] using hstep)
      have hold :
          (-1 / 2 : ℝ) ≤ Tensor.apply (halfAddTensorStateAfter X Y N).T x y ∧
            Tensor.apply (halfAddTensorStateAfter X Y N).T x y ≤ (1 / 2 : ℝ) := by
        simpa using Tensor.emitZero_sound (T := (halfAddTensorStateAfter X Y N).T)
          (x := x) (y := y) hx.1 hx.2 hy.1 hy.2 horacle
      have hlft :
          ((digitZero.c : ℝ) * Tensor.valueAt (halfAddResidualStateAfter X Y N .zero 0).T x y +
            (digitZero.d : ℝ)) ≠ 0 := by
        simp [digitZero]
      have hEq :
          Tensor.apply (halfAddTensorStateAfter X Y N).T x y =
            LFT.apply digitZero (Tensor.apply (halfAddResidualStateAfter X Y N .zero 0).T x y) := by
        simpa [halfAddResidualStateAfter_zero, Tensor.valueAt] using
          (Tensor.emit_invariant
            (T := (halfAddTensorStateAfter X Y N).T) (D := digitZero)
            (x := x) (y := y) hdenNew hdenOld hlft)
      constructor
      · have heq :
            Tensor.apply (halfAddTensorStateAfter X Y N).T x y =
              (Tensor.apply (halfAddResidualStateAfter X Y N .zero 0).T x y) / 2 := by
            simpa [digitZero, LFT.apply] using hEq
        nlinarith [hold.1, hold.2, heq]
      · have heq :
            Tensor.apply (halfAddTensorStateAfter X Y N).T x y =
              (Tensor.apply (halfAddResidualStateAfter X Y N .zero 0).T x y) / 2 := by
            simpa [digitZero, LFT.apply] using hEq
        nlinarith [hold.1, hold.2, heq]
  | pos =>
      have horacle :
          (halfAddTensorStateAfter X Y N).T.oracle = Tensor.EmitDecision.pos := by
        exact GeneralTrace.oracle_eq_of_step_pos X Y (by simpa [digit_to_LFT] using hstep)
      have hold :
          0 ≤ Tensor.apply (halfAddTensorStateAfter X Y N).T x y ∧
            Tensor.apply (halfAddTensorStateAfter X Y N).T x y ≤ 1 := by
        simpa using Tensor.emitPos_sound (T := (halfAddTensorStateAfter X Y N).T)
          (x := x) (y := y) hx.1 hx.2 hy.1 hy.2 horacle
      have hlft :
          ((digitPos.c : ℝ) * Tensor.valueAt (halfAddResidualStateAfter X Y N .pos 0).T x y +
            (digitPos.d : ℝ)) ≠ 0 := by
        simp [digitPos]
      have hEq :
          Tensor.apply (halfAddTensorStateAfter X Y N).T x y =
            LFT.apply digitPos (Tensor.apply (halfAddResidualStateAfter X Y N .pos 0).T x y) := by
        simpa [halfAddResidualStateAfter_zero, Tensor.valueAt] using
          (Tensor.emit_invariant
            (T := (halfAddTensorStateAfter X Y N).T) (D := digitPos)
            (x := x) (y := y) hdenNew hdenOld hlft)
      constructor
      · have heq :
            Tensor.apply (halfAddTensorStateAfter X Y N).T x y =
              ((Tensor.apply (halfAddResidualStateAfter X Y N .pos 0).T x y) + 1) / 2 := by
            simpa [digitPos, LFT.apply] using hEq
        nlinarith [hold.1, hold.2, heq]
      · have heq :
            Tensor.apply (halfAddTensorStateAfter X Y N).T x y =
              ((Tensor.apply (halfAddResidualStateAfter X Y N .pos 0).T x y) + 1) / 2 := by
            simpa [digitPos, LFT.apply] using hEq
        nlinarith [hold.1, hold.2, heq]

theorem halfAddResidualStateAfter_mapsBaseI_pair_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorStateAfter X Y N with
          T := (halfAddTensorStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∀ K,
      (halfAddResidualStateAfter X Y N d K).T.MapsBaseI ∧
      (halfAddResidualXStateAfter X Y N d K).T.MapsBaseI
  | 0 => by
      refine ⟨halfAddResidualStateAfter_zero_mapsBaseI_of_step X Y N d hstep, ?_⟩
      exact Tensor.mapsBaseI_absorbX
        ((halfAddResidualStateAfter X Y N d 0).T)
        ((MobiusReal.drop X N).stream 0)
        (halfAddResidualStateAfter_zero_mapsBaseI_of_step X Y N d hstep)
        (halfAddResidualStateAfter_hasNoPoleOnBase X Y N d 0)
        (halfAddResidualXStateAfter_hasNoPoleOnBase X Y N d 0)
        (IsContractive.maps_base_step (MobiusReal.drop X N).contractive 0)
        (IsContractive.no_poles_step (MobiusReal.drop X N).contractive 0)
  | K + 1 => by
      rcases halfAddResidualStateAfter_mapsBaseI_pair_of_step X Y N d hstep K with
        ⟨hStateK, hXK⟩
      have hStateSucc :
          (halfAddResidualStateAfter X Y N d (K + 1)).T.MapsBaseI := by
        have hEq :
            (halfAddResidualStateAfter X Y N d (K + 1)).T =
              (halfAddResidualXStateAfter X Y N d K).T.absorbY ((MobiusReal.drop Y N).stream K) := by
          simp [halfAddResidualStateAfter, halfAddResidualXStateAfter, Tensor.absorbBoth_n]
        rw [hEq]
        exact Tensor.mapsBaseI_absorbY
          ((halfAddResidualXStateAfter X Y N d K).T)
          ((MobiusReal.drop Y N).stream K)
          hXK
          (halfAddResidualXStateAfter_hasNoPoleOnBase X Y N d K)
          (halfAddResidualStateAfter_hasNoPoleOnBase X Y N d (K + 1))
          (IsContractive.maps_base_step (MobiusReal.drop Y N).contractive K)
          (IsContractive.no_poles_step (MobiusReal.drop Y N).contractive K)
      have hXSucc :
          (halfAddResidualXStateAfter X Y N d (K + 1)).T.MapsBaseI := by
        exact Tensor.mapsBaseI_absorbX
          ((halfAddResidualStateAfter X Y N d (K + 1)).T)
          ((MobiusReal.drop X N).stream (K + 1))
          hStateSucc
          (halfAddResidualStateAfter_hasNoPoleOnBase X Y N d (K + 1))
          (halfAddResidualXStateAfter_hasNoPoleOnBase X Y N d (K + 1))
          (IsContractive.maps_base_step (MobiusReal.drop X N).contractive (K + 1))
          (IsContractive.no_poles_step (MobiusReal.drop X N).contractive (K + 1))
      exact ⟨hStateSucc, hXSucc⟩

theorem halfAddResidualStateAfter_mapsBaseI_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorStateAfter X Y N with
          T := (halfAddTensorStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∀ K, (halfAddResidualStateAfter X Y N d K).T.MapsBaseI :=
  fun K => (halfAddResidualStateAfter_mapsBaseI_pair_of_step X Y N d hstep K).1

theorem halfAddResidualStateAfter_corner_mem_baseI_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorStateAfter X Y N with
          T := (halfAddTensorStateAfter X Y N).T.emit (digit_to_LFT d) }) (K : ℕ) :
    Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 1 ∈ baseI ∧
      Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 (-1) ∈ baseI ∧
      Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) 1 ∈ baseI ∧
      Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) (-1) ∈ baseI := by
  have hMaps := halfAddResidualStateAfter_mapsBaseI_of_step X Y N d hstep K
  have h1 : (1 : ℝ) ∈ baseI := by constructor <;> norm_num
  have hm1 : (-1 : ℝ) ∈ baseI := by constructor <;> norm_num
  constructor
  · exact hMaps 1 h1 1 h1
  constructor
  · exact hMaps 1 h1 (-1) hm1
  constructor
  · exact hMaps (-1) hm1 1 h1
  · exact hMaps (-1) hm1 (-1) hm1

theorem halfAddResidualStateAfter_width_le_eventually
    (X Y : MobiusReal) (N : ℕ) (d : Digit) {ε : ℝ} (hε : 0 < ε) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      tensorWidth (halfAddResidualStateAfter X Y N d K).T ≤ ε := by
  rcases halfAddResidualStateAfter_diff_lt X Y N d hε with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  unfold tensorWidth
  exact csSup_le
    (by
      refine ⟨0, ?_⟩
      refine ⟨0, 0, 0, 0, ?_, ?_, ?_, ?_, ?_⟩
      · constructor <;> norm_num
      · constructor <;> norm_num
      · constructor <;> norm_num
      · constructor <;> norm_num
      · simp)
    (by
      intro r hr
      rcases hr with ⟨x, y, w, z, hx, hy, hw, hz, rfl⟩
      exact le_of_lt (hK0 K hK x hx w hw y hy z hz))

theorem halfAddResidualStateAfter_width_lt_half_eventually
    (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      tensorWidth (halfAddResidualStateAfter X Y N d K).T < (1 / 2 : ℝ) := by
  rcases halfAddResidualStateAfter_width_le_eventually X Y N d
    (ε := (1 / 4 : ℝ)) (by norm_num) with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  have hwidth : tensorWidth (halfAddResidualStateAfter X Y N d K).T ≤ (1 / 4 : ℝ) :=
    hK0 K hK
  linarith

theorem halfAddResidualStateAfter_safeEventually
    (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (halfAddResidualStateAfter X Y N d K).T.HasNoPoleOnBase ∧
        tensorWidth (halfAddResidualStateAfter X Y N d K).T < (1 / 2 : ℝ) := by
  rcases halfAddResidualStateAfter_width_lt_half_eventually X Y N d with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  exact ⟨halfAddResidualStateAfter_hasNoPoleOnBase X Y N d K, hK0 K hK⟩


theorem halfAddTensorStateAfter_diff_lt
    (X Y : MobiusReal) {ε : ℝ} (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ x ∈ baseI, ∀ w ∈ baseI, ∀ y ∈ baseI, ∀ z ∈ baseI,
      |Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) x y -
        Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) w z| < ε := by
  have hε2 : 0 < ε / 2 := by linarith
  rcases X.contractive.shrinks_to_zero (ε / 2) hε2 with ⟨NX, hNX⟩
  rcases Y.contractive.shrinks_to_zero (ε / 2) hε2 with ⟨NY, hNY⟩
  refine ⟨max NX NY + 1, ?_⟩
  intro N hN x hx w hw y hy z hz
  cases N with
  | zero =>
      exfalso
      exact Nat.not_succ_le_zero (max NX NY) hN
  | succ n =>
      have hn : max NX NY ≤ n := Nat.le_of_succ_le_succ hN
      have hnX : n ≥ NX := le_trans (Nat.le_max_left _ _) hn
      have hnY : n ≥ NY := le_trans (Nat.le_max_right _ _) hn
      have hdx0 :
          |LFT.apply (partialComp X.stream n) x - LFT.apply (partialComp X.stream n) w| < ε / 2 := by
        simpa [partialComp] using hNX n hnX 0 x hx w hw
      have hdy0 :
          |LFT.apply (partialComp Y.stream n) y - LFT.apply (partialComp Y.stream n) z| < ε / 2 := by
        simpa [partialComp] using hNY n hnY 0 y hy z hz
      have hdx :
          |LFT.apply (pairedPrefix X.stream (n + 1)) x - LFT.apply (pairedPrefix X.stream (n + 1)) w| < ε / 2 := by
        rw [pairedPrefix_eq_partialComp]
        exact hdx0
      have hdy :
          |LFT.apply (pairedPrefix Y.stream (n + 1)) y - LFT.apply (pairedPrefix Y.stream (n + 1)) z| < ε / 2 := by
        rw [pairedPrefix_eq_partialComp]
        exact hdy0
      rw [halfAddTensorStateAfter_apply X Y (n + 1) hx hy, halfAddTensorStateAfter_apply X Y (n + 1) hw hz]
      have hsplit :
          |((LFT.apply (pairedPrefix X.stream (n + 1)) x + LFT.apply (pairedPrefix Y.stream (n + 1)) y) / 2) -
            ((LFT.apply (pairedPrefix X.stream (n + 1)) w + LFT.apply (pairedPrefix Y.stream (n + 1)) z) / 2)|
            ≤ (|LFT.apply (pairedPrefix X.stream (n + 1)) x - LFT.apply (pairedPrefix X.stream (n + 1)) w| +
                |LFT.apply (pairedPrefix Y.stream (n + 1)) y - LFT.apply (pairedPrefix Y.stream (n + 1)) z|) / 2 := by
        calc
          |((LFT.apply (pairedPrefix X.stream (n + 1)) x + LFT.apply (pairedPrefix Y.stream (n + 1)) y) / 2) -
              ((LFT.apply (pairedPrefix X.stream (n + 1)) w + LFT.apply (pairedPrefix Y.stream (n + 1)) z) / 2)|
              = |((LFT.apply (pairedPrefix X.stream (n + 1)) x - LFT.apply (pairedPrefix X.stream (n + 1)) w) +
                    (LFT.apply (pairedPrefix Y.stream (n + 1)) y - LFT.apply (pairedPrefix Y.stream (n + 1)) z)) / 2| := by
                    ring_nf
          _ = |(LFT.apply (pairedPrefix X.stream (n + 1)) x - LFT.apply (pairedPrefix X.stream (n + 1)) w) +
                (LFT.apply (pairedPrefix Y.stream (n + 1)) y - LFT.apply (pairedPrefix Y.stream (n + 1)) z)| / 2 := by
                simp [abs_div]
          _ ≤ (|LFT.apply (pairedPrefix X.stream (n + 1)) x - LFT.apply (pairedPrefix X.stream (n + 1)) w| +
                |LFT.apply (pairedPrefix Y.stream (n + 1)) y - LFT.apply (pairedPrefix Y.stream (n + 1)) z|) / 2 := by
                gcongr
                exact abs_add_le _ _
      have hsum : (|LFT.apply (pairedPrefix X.stream (n + 1)) x - LFT.apply (pairedPrefix X.stream (n + 1)) w| +
          |LFT.apply (pairedPrefix Y.stream (n + 1)) y - LFT.apply (pairedPrefix Y.stream (n + 1)) z|) / 2 < ε := by
        nlinarith
      exact lt_of_le_of_lt hsplit hsum

theorem halfAddTensorStateAfter_hasNoPoleOnBase (X Y : MobiusReal) (N : ℕ) :
    (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).HasNoPoleOnBase := by
  intro x hx y hy
  rw [absorbBoth_n_halfAdd_eq_avgTensor]
  have hMx := pairedPrefix_denom_ne_zero X N hx
  have hMy := pairedPrefix_denom_ne_zero Y N hy
  intro h0
  have hmul :
      ((((pairedPrefix X.stream N).c : ℝ) * x + ((pairedPrefix X.stream N).d : ℝ)) *
        ((((pairedPrefix Y.stream N).c : ℝ) * y + ((pairedPrefix Y.stream N).d : ℝ)))) = 0 := by
    simp [Tensor.denAt, avgTensor] at h0
    nlinarith
  rcases mul_eq_zero.mp hmul with hX | hY
  · exact hMx hX
  · exact hMy hY

theorem Tensor.widthSet_nonempty (T : Tensor) : (Tensor.widthSet T).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨0, 0, 0, 0, ?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> norm_num
  · constructor <;> norm_num
  · constructor <;> norm_num
  · constructor <;> norm_num
  · simp

theorem halfAddTensorStateAfter_width_le_eventually
    (X Y : MobiusReal) {ε : ℝ} (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      tensorWidth (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) ≤ ε := by
  rcases halfAddTensorStateAfter_diff_lt X Y hε with ⟨N0, hN0⟩
  refine ⟨N0, ?_⟩
  intro N hN
  unfold tensorWidth
  exact csSup_le
    (Tensor.widthSet_nonempty (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N))
    (by
      intro d hd
      rcases hd with ⟨x, y, w, z, hx, hy, hw, hz, rfl⟩
      exact le_of_lt (hN0 N hN x hx w hw y hy z hz))

theorem halfAddTensorStateAfter_width_lt_half_eventually (X Y : MobiusReal) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      tensorWidth (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) < (1 / 2 : ℝ) := by
  rcases halfAddTensorStateAfter_width_le_eventually X Y (show (0 : ℝ) < 1 / 4 by norm_num) with
    ⟨N0, hN0⟩
  refine ⟨N0, ?_⟩
  intro N hN
  have hwidth : tensorWidth (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) ≤ (1 / 4 : ℝ) :=
    hN0 N hN
  linarith

theorem halfAddTensorStateAfter_safeEventually (X Y : MobiusReal) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).HasNoPoleOnBase ∧
        tensorWidth (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) < (1 / 2 : ℝ) := by
  rcases halfAddTensorStateAfter_width_lt_half_eventually X Y with ⟨N0, hN0⟩
  refine ⟨N0, ?_⟩
  intro N hN
  exact ⟨halfAddTensorStateAfter_hasNoPoleOnBase X Y N, hN0 N hN⟩

theorem LFT.endpoint_sign_cases (M : LFT) (h : M.NoPoleOnBase) :
    (M.c + M.d > 0 ∧ -M.c + M.d > 0) ∨
      (M.c + M.d < 0 ∧ -M.c + M.d < 0) := by
  have hR : |(M.c : ℝ)| < |(M.d : ℝ)| := by
    exact_mod_cast h
  have hdne : M.d ≠ 0 := by
    intro hd0
    have : |(M.c : ℝ)| < 0 := by simpa [hd0] using hR
    linarith [abs_nonneg (M.c : ℝ)]
  rcases lt_or_gt_of_ne hdne with hdneg | hdpos
  · right
    have hdR : (M.d : ℝ) < 0 := by exact_mod_cast hdneg
    have hcd : |(M.c : ℝ)| < -((M.d : ℝ)) := by
      simpa [abs_of_neg hdR] using hR
    have hcBounds : (M.d : ℝ) < (M.c : ℝ) ∧ (M.c : ℝ) < -((M.d : ℝ)) := by
      simpa using (abs_lt.mp hcd)
    constructor
    · have : (M.c : ℝ) + (M.d : ℝ) < 0 := by linarith
      exact_mod_cast this
    · have : -((M.c : ℝ)) + (M.d : ℝ) < 0 := by linarith
      exact_mod_cast this
  · left
    have hdR : (0 : ℝ) < (M.d : ℝ) := by exact_mod_cast hdpos
    have hcd : |(M.c : ℝ)| < (M.d : ℝ) := by
      simpa [abs_of_pos hdR] using hR
    have hcBounds : -((M.d : ℝ)) < (M.c : ℝ) ∧ (M.c : ℝ) < (M.d : ℝ) := abs_lt.mp hcd
    constructor
    · have : (0 : ℝ) < (M.c : ℝ) + (M.d : ℝ) := by linarith
      exact_mod_cast this
    · have : (0 : ℝ) < -(M.c : ℝ) + (M.d : ℝ) := by linarith
      exact_mod_cast this

theorem Tensor.inDigitNeg_complete_pos (n d : ℤ) (hd : 0 < d)
    (hlow : (-(d : ℝ)) ≤ (n : ℝ)) (hhigh : (n : ℝ) ≤ 0) :
    Tensor.inDigitNeg n d = true := by
  unfold Tensor.inDigitNeg
  have hlow' : -d ≤ n := by exact_mod_cast hlow
  have hhigh' : n ≤ 0 := by exact_mod_cast hhigh
  simpa [hd, decide_eq_true_eq] using And.intro hhigh' hlow'

theorem Tensor.inDigitNeg_complete_neg (n d : ℤ) (hd : d < 0)
    (hlow : (0 : ℝ) ≤ (n : ℝ)) (hhigh : (n : ℝ) + (d : ℝ) ≤ 0) :
    Tensor.inDigitNeg n d = true := by
  unfold Tensor.inDigitNeg
  have hd' : ¬ (0 < d) := by linarith
  have hlow' : -n ≤ 0 := by
    have : (0 : ℤ) ≤ n := by exact_mod_cast hlow
    linarith
  have hhigh' : d ≤ -n := by
    have : (n : ℤ) + d ≤ 0 := by exact_mod_cast hhigh
    linarith
  simpa [hd', decide_eq_true_eq] using And.intro hlow' hhigh'

theorem Tensor.inDigitZero_complete_pos (n d : ℤ) (hd : 0 < d)
    (hlow : (-(d : ℝ)) ≤ 2 * (n : ℝ)) (hhigh : 2 * (n : ℝ) ≤ (d : ℝ)) :
    Tensor.inDigitZero n d = true := by
  unfold Tensor.inDigitZero
  have hlow' : -d ≤ 2 * n := by exact_mod_cast hlow
  have hhigh' : 2 * n ≤ d := by exact_mod_cast hhigh
  simpa [hd, decide_eq_true_eq, mul_assoc, mul_left_comm, mul_comm] using And.intro hhigh' hlow'

theorem Tensor.inDigitZero_complete_neg (n d : ℤ) (hd : d < 0)
    (hlow : (d : ℝ) ≤ 2 * (n : ℝ)) (hhigh : 2 * (n : ℝ) ≤ (-(d : ℝ))) :
    Tensor.inDigitZero n d = true := by
  unfold Tensor.inDigitZero
  have hd' : ¬ (0 < d) := by linarith
  have hhigh' : d ≤ -2 * n := by
    have : 2 * n ≤ -d := by exact_mod_cast hhigh
    linarith
  have hlow' : -2 * n ≤ -d := by
    have : d ≤ 2 * n := by exact_mod_cast hlow
    linarith
  simpa [hd', decide_eq_true_eq, mul_assoc, mul_left_comm, mul_comm, two_mul] using
    And.intro hlow' hhigh'

theorem Tensor.inDigitPos_complete_pos (n d : ℤ) (hd : 0 < d)
    (hlow : (0 : ℝ) ≤ (n : ℝ)) (hhigh : (n : ℝ) ≤ (d : ℝ)) :
    Tensor.inDigitPos n d = true := by
  unfold Tensor.inDigitPos
  have hlow' : 0 ≤ n := by exact_mod_cast hlow
  have hhigh' : n ≤ d := by exact_mod_cast hhigh
  simpa [hd, decide_eq_true_eq] using And.intro hlow' hhigh'

theorem Tensor.inDigitPos_complete_neg (n d : ℤ) (hd : d < 0)
    (hlow : (n : ℝ) ≤ 0) (hhigh : (d : ℝ) ≤ (n : ℝ)) :
    Tensor.inDigitPos n d = true := by
  unfold Tensor.inDigitPos
  have hd' : ¬ (0 < d) := by linarith
  have hlow' : 0 ≤ -n := by
    have : (n : ℤ) ≤ 0 := by exact_mod_cast hlow
    linarith
  have hhigh' : -n ≤ -d := by
    have : d ≤ n := by exact_mod_cast hhigh
    linarith
  simpa [hd', decide_eq_true_eq] using And.intro hlow' hhigh'

theorem Tensor.inDigitNeg_of_ratio_pos (n d : ℤ) (hd : 0 < d)
    (hlo : (-(1 : ℝ)) ≤ (n : ℝ) / d) (hhi : (n : ℝ) / d ≤ 0) :
    Tensor.inDigitNeg n d = true := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlow : (-(d : ℝ)) ≤ (n : ℝ) := by
    have := (le_div_iff₀  hdR).mp hlo
    simpa using this
  have hhigh : (n : ℝ) ≤ 0 := by
    have := (div_le_iff₀ hdR).mp hhi
    simpa using this
  exact Tensor.inDigitNeg_complete_pos n d hd hlow hhigh

theorem Tensor.inDigitNeg_of_ratio_neg (n d : ℤ) (hd : d < 0)
    (hlo : (-(1 : ℝ)) ≤ (n : ℝ) / d) (hhi : (n : ℝ) / d ≤ 0) :
    Tensor.inDigitNeg n d = true := by
  have hdR : (d : ℝ) < 0 := by exact_mod_cast hd
  have hlow : (0 : ℝ) ≤ (n : ℝ) := by
    have := (div_le_iff_of_neg hdR).mp hhi
    simpa using this
  have hhigh : (n : ℝ) + d ≤ 0 := by
    have : (n : ℝ) ≤ -(d : ℝ) := by
      have h := (le_div_iff_of_neg hdR).mp hlo
      simpa using h
    linarith
  exact Tensor.inDigitNeg_complete_neg n d hd hlow hhigh

theorem Tensor.inDigitZero_of_ratio_pos (n d : ℤ) (hd : 0 < d)
    (hlo : (-(1 / 2 : ℝ)) ≤ (n : ℝ) / d) (hhi : (n : ℝ) / d ≤ (1 / 2 : ℝ)) :
    Tensor.inDigitZero n d = true := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlow : (-(d : ℝ)) ≤ 2 * (n : ℝ) := by
    have h := (le_div_iff₀ hdR).mp hlo
    nlinarith
  have hhigh : 2 * (n : ℝ) ≤ (d : ℝ) := by
    have h := (div_le_iff₀ hdR).mp hhi
    nlinarith
  exact Tensor.inDigitZero_complete_pos n d hd hlow hhigh

theorem Tensor.inDigitZero_of_ratio_neg (n d : ℤ) (hd : d < 0)
    (hlo : (-(1 / 2 : ℝ)) ≤ (n : ℝ) / d) (hhi : (n : ℝ) / d ≤ (1 / 2 : ℝ)) :
    Tensor.inDigitZero n d = true := by
  have hdR : (d : ℝ) < 0 := by exact_mod_cast hd
  have hlow : (d : ℝ) ≤ 2 * (n : ℝ) := by
    have h := (div_le_iff_of_neg hdR).mp hhi
    nlinarith
  have hhigh : 2 * (n : ℝ) ≤ (-(d : ℝ)) := by
    have h := (le_div_iff_of_neg hdR).mp hlo
    nlinarith
  exact Tensor.inDigitZero_complete_neg n d hd hlow hhigh

theorem Tensor.inDigitPos_of_ratio_pos (n d : ℤ) (hd : 0 < d)
    (hlo : (0 : ℝ) ≤ (n : ℝ) / d) (hhi : (n : ℝ) / d ≤ 1) :
    Tensor.inDigitPos n d = true := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlow : (0 : ℝ) ≤ (n : ℝ) := by
    have := (le_div_iff₀ hdR).mp hlo
    simpa using this
  have hhigh : (n : ℝ) ≤ (d : ℝ) := by
    have := (div_le_iff₀ hdR).mp hhi
    simpa using this
  exact Tensor.inDigitPos_complete_pos n d hd hlow hhigh

theorem Tensor.inDigitPos_of_ratio_neg (n d : ℤ) (hd : d < 0)
    (hlo : (0 : ℝ) ≤ (n : ℝ) / d) (hhi : (n : ℝ) / d ≤ 1) :
    Tensor.inDigitPos n d = true := by
  have hdR : (d : ℝ) < 0 := by exact_mod_cast hd
  have hlow : (n : ℝ) ≤ 0 := by
    have := (le_div_iff_of_neg hdR).mp hlo
    simpa using this
  have hhigh : (d : ℝ) ≤ (n : ℝ) := by
    have := (div_le_iff_of_neg hdR).mp hhi
    simpa using this
  exact Tensor.inDigitPos_complete_neg n d hd hlow hhigh

theorem four_values_digit_trichotomy
    (r₁ r₂ r₃ r₄ : ℝ)
    (_h₁ : r₁ ∈ baseI) (_h₂ : r₂ ∈ baseI) (_h₃ : r₃ ∈ baseI) (_h₄ : r₄ ∈ baseI)
    (h12 : |r₁ - r₂| < (1 / 2 : ℝ))
    (h13 : |r₁ - r₃| < (1 / 2 : ℝ))
    (h14 : |r₁ - r₄| < (1 / 2 : ℝ))
    (h23 : |r₂ - r₃| < (1 / 2 : ℝ))
    (h24 : |r₂ - r₄| < (1 / 2 : ℝ))
    (h34 : |r₃ - r₄| < (1 / 2 : ℝ)) :
    (0 ≤ r₁ ∧ 0 ≤ r₂ ∧ 0 ≤ r₃ ∧ 0 ≤ r₄) ∨
      (r₁ ≤ 0 ∧ r₂ ≤ 0 ∧ r₃ ≤ 0 ∧ r₄ ≤ 0) ∨
      ((-1 / 2 : ℝ) ≤ r₁ ∧ r₁ ≤ (1 / 2 : ℝ) ∧
        (-1 / 2 : ℝ) ≤ r₂ ∧ r₂ ≤ (1 / 2 : ℝ) ∧
        (-1 / 2 : ℝ) ≤ r₃ ∧ r₃ ≤ (1 / 2 : ℝ) ∧
        (-1 / 2 : ℝ) ≤ r₄ ∧ r₄ ≤ (1 / 2 : ℝ)) := by
  by_cases hpos :
      r₁ > (1 / 2 : ℝ) ∨ r₂ > (1 / 2 : ℝ) ∨ r₃ > (1 / 2 : ℝ) ∨ r₄ > (1 / 2 : ℝ)
  · left
    rcases hpos with hp1 | hp2 | hp3 | hp4
    · have hr2 : 0 ≤ r₂ := by
        have : r₁ - r₂ < (1 / 2 : ℝ) := (abs_lt.mp h12).2
        linarith
      have hr3 : 0 ≤ r₃ := by
        have : r₁ - r₃ < (1 / 2 : ℝ) := (abs_lt.mp h13).2
        linarith
      have hr4 : 0 ≤ r₄ := by
        have : r₁ - r₄ < (1 / 2 : ℝ) := (abs_lt.mp h14).2
        linarith
      have hr1 : 0 ≤ r₁ := by linarith
      exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
    · have hr1 : 0 ≤ r₁ := by
        have : -(1 / 2 : ℝ) < r₁ - r₂ := (abs_lt.mp h12).1
        linarith
      have hr3 : 0 ≤ r₃ := by
        have : r₂ - r₃ < (1 / 2 : ℝ) := (abs_lt.mp h23).2
        linarith
      have hr4 : 0 ≤ r₄ := by
        have : r₂ - r₄ < (1 / 2 : ℝ) := (abs_lt.mp h24).2
        linarith
      have hr2 : 0 ≤ r₂ := by linarith
      exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
    · have hr1 : 0 ≤ r₁ := by
        have : -(1 / 2 : ℝ) < r₁ - r₃ := (abs_lt.mp h13).1
        linarith
      have hr2 : 0 ≤ r₂ := by
        have : -(1 / 2 : ℝ) < r₂ - r₃ := by simpa [abs_sub_comm] using (abs_lt.mp h23).1
        linarith
      have hr4 : 0 ≤ r₄ := by
        have : r₃ - r₄ < (1 / 2 : ℝ) := (abs_lt.mp h34).2
        linarith
      have hr3 : 0 ≤ r₃ := by linarith
      exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
    · have hr1 : 0 ≤ r₁ := by
        have : -(1 / 2 : ℝ) < r₁ - r₄ := (abs_lt.mp h14).1
        linarith
      have hr2 : 0 ≤ r₂ := by
        have : -(1 / 2 : ℝ) < r₂ - r₄ := by simpa [abs_sub_comm] using (abs_lt.mp h24).1
        linarith
      have hr3 : 0 ≤ r₃ := by
        have : -(1 / 2 : ℝ) < r₃ - r₄ := by simpa [abs_sub_comm] using (abs_lt.mp h34).1
        linarith
      have hr4 : 0 ≤ r₄ := by linarith
      exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
  · by_cases hneg :
        r₁ < (-1 / 2 : ℝ) ∨ r₂ < (-1 / 2 : ℝ) ∨ r₃ < (-1 / 2 : ℝ) ∨ r₄ < (-1 / 2 : ℝ)
    · right
      left
      rcases hneg with hn1 | hn2 | hn3 | hn4
      · have hr2 : r₂ ≤ 0 := by
          have : -(1 / 2 : ℝ) < r₁ - r₂ := (abs_lt.mp h12).1
          linarith
        have hr3 : r₃ ≤ 0 := by
          have : -(1 / 2 : ℝ) < r₁ - r₃ := (abs_lt.mp h13).1
          linarith
        have hr4 : r₄ ≤ 0 := by
          have : -(1 / 2 : ℝ) < r₁ - r₄ := (abs_lt.mp h14).1
          linarith
        have hr1 : r₁ ≤ 0 := by linarith
        exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
      · have hr1 : r₁ ≤ 0 := by
          have : r₁ - r₂ < (1 / 2 : ℝ) := (abs_lt.mp h12).2
          linarith
        have hr3 : r₃ ≤ 0 := by
          have : -(1 / 2 : ℝ) < r₂ - r₃ := (abs_lt.mp h23).1
          linarith
        have hr4 : r₄ ≤ 0 := by
          have : -(1 / 2 : ℝ) < r₂ - r₄ := (abs_lt.mp h24).1
          linarith
        have hr2 : r₂ ≤ 0 := by linarith
        exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
      · have hr1 : r₁ ≤ 0 := by
          have : r₁ - r₃ < (1 / 2 : ℝ) := (abs_lt.mp h13).2
          linarith
        have hr2 : r₂ ≤ 0 := by
          have : r₂ - r₃ < (1 / 2 : ℝ) := (abs_lt.mp h23).2
          linarith
        have hr4 : r₄ ≤ 0 := by
          have : -(1 / 2 : ℝ) < r₃ - r₄ := (abs_lt.mp h34).1
          linarith
        have hr3 : r₃ ≤ 0 := by linarith
        exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
      · have hr1 : r₁ ≤ 0 := by
          have : r₁ - r₄ < (1 / 2 : ℝ) := (abs_lt.mp h14).2
          linarith
        have hr2 : r₂ ≤ 0 := by
          have : r₂ - r₄ < (1 / 2 : ℝ) := (abs_lt.mp h24).2
          linarith
        have hr3 : r₃ ≤ 0 := by
          have : r₃ - r₄ < (1 / 2 : ℝ) := (abs_lt.mp h34).2
          linarith
        have hr4 : r₄ ≤ 0 := by linarith
        exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
    · right
      right
      have hr1lo : (-1 / 2 : ℝ) ≤ r₁ := by
        by_contra hlt
        have hlt' : r₁ < (-1 / 2 : ℝ) := by linarith
        exact hneg (Or.inl hlt')
      have hr2lo : (-1 / 2 : ℝ) ≤ r₂ := by
        by_contra hlt
        have hlt' : r₂ < (-1 / 2 : ℝ) := by linarith
        exact hneg (Or.inr (Or.inl hlt'))
      have hr3lo : (-1 / 2 : ℝ) ≤ r₃ := by
        by_contra hlt
        have hlt' : r₃ < (-1 / 2 : ℝ) := by linarith
        exact hneg (Or.inr (Or.inr (Or.inl hlt')))
      have hr4lo : (-1 / 2 : ℝ) ≤ r₄ := by
        by_contra hlt
        have hlt' : r₄ < (-1 / 2 : ℝ) := by linarith
        exact hneg (Or.inr (Or.inr (Or.inr hlt')))
      have hr1hi : r₁ ≤ (1 / 2 : ℝ) := by
        by_contra hgt
        have hgt' : r₁ > (1 / 2 : ℝ) := by linarith
        exact hpos (Or.inl hgt')
      have hr2hi : r₂ ≤ (1 / 2 : ℝ) := by
        by_contra hgt
        have hgt' : r₂ > (1 / 2 : ℝ) := by linarith
        exact hpos (Or.inr (Or.inl hgt'))
      have hr3hi : r₃ ≤ (1 / 2 : ℝ) := by
        by_contra hgt
        have hgt' : r₃ > (1 / 2 : ℝ) := by linarith
        exact hpos (Or.inr (Or.inr (Or.inl hgt')))
      have hr4hi : r₄ ≤ (1 / 2 : ℝ) := by
        by_contra hgt
        have hgt' : r₄ > (1 / 2 : ℝ) := by linarith
        exact hpos (Or.inr (Or.inr (Or.inr hgt')))
      exact ⟨hr1lo, hr1hi, hr2lo, hr2hi, hr3lo, hr3hi, hr4lo, hr4hi⟩

theorem four_values_digit_trichotomy_of_close
    (r₁ r₂ r₃ r₄ : ℝ)
    (h12 : |r₁ - r₂| < (1 / 2 : ℝ))
    (h13 : |r₁ - r₃| < (1 / 2 : ℝ))
    (h14 : |r₁ - r₄| < (1 / 2 : ℝ))
    (h23 : |r₂ - r₃| < (1 / 2 : ℝ))
    (h24 : |r₂ - r₄| < (1 / 2 : ℝ))
    (h34 : |r₃ - r₄| < (1 / 2 : ℝ)) :
    (0 ≤ r₁ ∧ 0 ≤ r₂ ∧ 0 ≤ r₃ ∧ 0 ≤ r₄) ∨
      (r₁ ≤ 0 ∧ r₂ ≤ 0 ∧ r₃ ≤ 0 ∧ r₄ ≤ 0) ∨
      ((-1 / 2 : ℝ) ≤ r₁ ∧ r₁ ≤ (1 / 2 : ℝ) ∧
        (-1 / 2 : ℝ) ≤ r₂ ∧ r₂ ≤ (1 / 2 : ℝ) ∧
        (-1 / 2 : ℝ) ≤ r₃ ∧ r₃ ≤ (1 / 2 : ℝ) ∧
        (-1 / 2 : ℝ) ≤ r₄ ∧ r₄ ≤ (1 / 2 : ℝ)) := by
  by_cases hpos :
      r₁ > (1 / 2 : ℝ) ∨ r₂ > (1 / 2 : ℝ) ∨ r₃ > (1 / 2 : ℝ) ∨ r₄ > (1 / 2 : ℝ)
  · left
    rcases hpos with hp1 | hp2 | hp3 | hp4
    · have hr2 : 0 ≤ r₂ := by
        have : r₁ - r₂ < (1 / 2 : ℝ) := (abs_lt.mp h12).2
        linarith
      have hr3 : 0 ≤ r₃ := by
        have : r₁ - r₃ < (1 / 2 : ℝ) := (abs_lt.mp h13).2
        linarith
      have hr4 : 0 ≤ r₄ := by
        have : r₁ - r₄ < (1 / 2 : ℝ) := (abs_lt.mp h14).2
        linarith
      have hr1 : 0 ≤ r₁ := by linarith
      exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
    · have hr1 : 0 ≤ r₁ := by
        have : -(1 / 2 : ℝ) < r₁ - r₂ := (abs_lt.mp h12).1
        linarith
      have hr3 : 0 ≤ r₃ := by
        have : r₂ - r₃ < (1 / 2 : ℝ) := (abs_lt.mp h23).2
        linarith
      have hr4 : 0 ≤ r₄ := by
        have : r₂ - r₄ < (1 / 2 : ℝ) := (abs_lt.mp h24).2
        linarith
      have hr2 : 0 ≤ r₂ := by linarith
      exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
    · have hr1 : 0 ≤ r₁ := by
        have : -(1 / 2 : ℝ) < r₁ - r₃ := (abs_lt.mp h13).1
        linarith
      have hr2 : 0 ≤ r₂ := by
        have : -(1 / 2 : ℝ) < r₂ - r₃ := by simpa [abs_sub_comm] using (abs_lt.mp h23).1
        linarith
      have hr4 : 0 ≤ r₄ := by
        have : r₃ - r₄ < (1 / 2 : ℝ) := (abs_lt.mp h34).2
        linarith
      have hr3 : 0 ≤ r₃ := by linarith
      exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
    · have hr1 : 0 ≤ r₁ := by
        have : -(1 / 2 : ℝ) < r₁ - r₄ := (abs_lt.mp h14).1
        linarith
      have hr2 : 0 ≤ r₂ := by
        have : -(1 / 2 : ℝ) < r₂ - r₄ := by simpa [abs_sub_comm] using (abs_lt.mp h24).1
        linarith
      have hr3 : 0 ≤ r₃ := by
        have : -(1 / 2 : ℝ) < r₃ - r₄ := by simpa [abs_sub_comm] using (abs_lt.mp h34).1
        linarith
      have hr4 : 0 ≤ r₄ := by linarith
      exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
  · by_cases hneg :
        r₁ < (-1 / 2 : ℝ) ∨ r₂ < (-1 / 2 : ℝ) ∨ r₃ < (-1 / 2 : ℝ) ∨ r₄ < (-1 / 2 : ℝ)
    · right
      left
      rcases hneg with hn1 | hn2 | hn3 | hn4
      · have hr2 : r₂ ≤ 0 := by
          have : -(1 / 2 : ℝ) < r₁ - r₂ := (abs_lt.mp h12).1
          linarith
        have hr3 : r₃ ≤ 0 := by
          have : -(1 / 2 : ℝ) < r₁ - r₃ := (abs_lt.mp h13).1
          linarith
        have hr4 : r₄ ≤ 0 := by
          have : -(1 / 2 : ℝ) < r₁ - r₄ := (abs_lt.mp h14).1
          linarith
        have hr1 : r₁ ≤ 0 := by linarith
        exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
      · have hr1 : r₁ ≤ 0 := by
          have : r₁ - r₂ < (1 / 2 : ℝ) := (abs_lt.mp h12).2
          linarith
        have hr3 : r₃ ≤ 0 := by
          have : -(1 / 2 : ℝ) < r₂ - r₃ := (abs_lt.mp h23).1
          linarith
        have hr4 : r₄ ≤ 0 := by
          have : -(1 / 2 : ℝ) < r₂ - r₄ := (abs_lt.mp h24).1
          linarith
        have hr2 : r₂ ≤ 0 := by linarith
        exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
      · have hr1 : r₁ ≤ 0 := by
          have : r₁ - r₃ < (1 / 2 : ℝ) := (abs_lt.mp h13).2
          linarith
        have hr2 : r₂ ≤ 0 := by
          have : r₂ - r₃ < (1 / 2 : ℝ) := (abs_lt.mp h23).2
          linarith
        have hr4 : r₄ ≤ 0 := by
          have : -(1 / 2 : ℝ) < r₃ - r₄ := (abs_lt.mp h34).1
          linarith
        have hr3 : r₃ ≤ 0 := by linarith
        exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
      · have hr1 : r₁ ≤ 0 := by
          have : r₁ - r₄ < (1 / 2 : ℝ) := (abs_lt.mp h14).2
          linarith
        have hr2 : r₂ ≤ 0 := by
          have : r₂ - r₄ < (1 / 2 : ℝ) := (abs_lt.mp h24).2
          linarith
        have hr3 : r₃ ≤ 0 := by
          have : r₃ - r₄ < (1 / 2 : ℝ) := (abs_lt.mp h34).2
          linarith
        have hr4 : r₄ ≤ 0 := by linarith
        exact ⟨hr1, ⟨hr2, ⟨hr3, hr4⟩⟩⟩
    · right
      right
      have hr1lo : (-1 / 2 : ℝ) ≤ r₁ := by
        by_contra hlt
        have hlt' : r₁ < (-1 / 2 : ℝ) := by linarith
        exact hneg (Or.inl hlt')
      have hr2lo : (-1 / 2 : ℝ) ≤ r₂ := by
        by_contra hlt
        have hlt' : r₂ < (-1 / 2 : ℝ) := by linarith
        exact hneg (Or.inr (Or.inl hlt'))
      have hr3lo : (-1 / 2 : ℝ) ≤ r₃ := by
        by_contra hlt
        have hlt' : r₃ < (-1 / 2 : ℝ) := by linarith
        exact hneg (Or.inr (Or.inr (Or.inl hlt')))
      have hr4lo : (-1 / 2 : ℝ) ≤ r₄ := by
        by_contra hlt
        have hlt' : r₄ < (-1 / 2 : ℝ) := by linarith
        exact hneg (Or.inr (Or.inr (Or.inr hlt')))
      have hr1hi : r₁ ≤ (1 / 2 : ℝ) := by
        by_contra hgt
        have hgt' : r₁ > (1 / 2 : ℝ) := by linarith
        exact hpos (Or.inl hgt')
      have hr2hi : r₂ ≤ (1 / 2 : ℝ) := by
        by_contra hgt
        have hgt' : r₂ > (1 / 2 : ℝ) := by linarith
        exact hpos (Or.inr (Or.inl hgt'))
      have hr3hi : r₃ ≤ (1 / 2 : ℝ) := by
        by_contra hgt
        have hgt' : r₃ > (1 / 2 : ℝ) := by linarith
        exact hpos (Or.inr (Or.inr (Or.inl hgt')))
      have hr4hi : r₄ ≤ (1 / 2 : ℝ) := by
        by_contra hgt
        have hgt' : r₄ > (1 / 2 : ℝ) := by linarith
        exact hpos (Or.inr (Or.inr (Or.inr hgt')))
      exact ⟨hr1lo, hr1hi, hr2lo, hr2hi, hr3lo, hr3hi, hr4lo, hr4hi⟩

theorem avg_mem_baseI {a b : ℝ} (ha : a ∈ baseI) (hb : b ∈ baseI) :
    (a + b) / 2 ∈ baseI := by
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

theorem halfAddTensorStateAfter_corner_mem_baseI
    (X Y : MobiusReal) (N : ℕ) :
    Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 1 ∈ baseI ∧
      Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 (-1) ∈ baseI ∧
      Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) 1 ∈ baseI ∧
      Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) (-1) ∈ baseI := by
  have h1 : (1 : ℝ) ∈ baseI := by constructor <;> norm_num
  have hm1 : (-1 : ℝ) ∈ baseI := by constructor <;> norm_num
  have hX1 := pairedPrefix_maps_base X N h1
  have hXm1 := pairedPrefix_maps_base X N hm1
  have hY1 := pairedPrefix_maps_base Y N h1
  have hYm1 := pairedPrefix_maps_base Y N hm1
  constructor
  · simpa [halfAddTensorStateAfter_apply X Y N h1 h1] using avg_mem_baseI hX1 hY1
  constructor
  · simpa [halfAddTensorStateAfter_apply X Y N h1 hm1] using avg_mem_baseI hX1 hYm1
  constructor
  · simpa [halfAddTensorStateAfter_apply X Y N hm1 h1] using avg_mem_baseI hXm1 hY1
  · simpa [halfAddTensorStateAfter_apply X Y N hm1 hm1] using avg_mem_baseI hXm1 hYm1

theorem avgTensor_hasNoPole_bool (M N : LFT)
    (hM : M.NoPoleOnBase) (hN : N.NoPoleOnBase) :
    Tensor.hasNoPole
      (2 * (M.c + M.d) * (N.c + N.d))
      (2 * (M.c + M.d) * (-N.c + N.d))
      (2 * (-M.c + M.d) * (N.c + N.d))
      (2 * (-M.c + M.d) * (-N.c + N.d)) = true := by
  rcases LFT.endpoint_sign_cases M hM with hMp | hMn
  · rcases LFT.endpoint_sign_cases N hN with hNp | hNn
    · have hd1 : 0 < 2 * (M.c + M.d) * (N.c + N.d) := by nlinarith [hMp.1, hNp.1]
      have hd2 : 0 < 2 * (M.c + M.d) * (-N.c + N.d) := by nlinarith [hMp.1, hNp.2]
      have hd3 : 0 < 2 * (-M.c + M.d) * (N.c + N.d) := by nlinarith [hMp.2, hNp.1]
      have hd4 : 0 < 2 * (-M.c + M.d) * (-N.c + N.d) := by nlinarith [hMp.2, hNp.2]
      unfold Tensor.hasNoPole
      simp [hd1, hd2, hd3, hd4]
    · have hd1 : 2 * (M.c + M.d) * (N.c + N.d) < 0 := by nlinarith [hMp.1, hNn.1]
      have hd2 : 2 * (M.c + M.d) * (-N.c + N.d) < 0 := by nlinarith [hMp.1, hNn.2]
      have hd3 : 2 * (-M.c + M.d) * (N.c + N.d) < 0 := by nlinarith [hMp.2, hNn.1]
      have hd4 : 2 * (-M.c + M.d) * (-N.c + N.d) < 0 := by nlinarith [hMp.2, hNn.2]
      unfold Tensor.hasNoPole
      simp [hd1, hd2, hd3, hd4]
  · rcases LFT.endpoint_sign_cases N hN with hNp | hNn
    · have hd1 : 2 * (M.c + M.d) * (N.c + N.d) < 0 := by nlinarith [hMn.1, hNp.1]
      have hd2 : 2 * (M.c + M.d) * (-N.c + N.d) < 0 := by nlinarith [hMn.1, hNp.2]
      have hd3 : 2 * (-M.c + M.d) * (N.c + N.d) < 0 := by nlinarith [hMn.2, hNp.1]
      have hd4 : 2 * (-M.c + M.d) * (-N.c + N.d) < 0 := by nlinarith [hMn.2, hNp.2]
      unfold Tensor.hasNoPole
      simp [hd1, hd2, hd3, hd4]
    · have hd1 : 0 < 2 * (M.c + M.d) * (N.c + N.d) := by nlinarith [hMn.1, hNn.1]
      have hd2 : 0 < 2 * (M.c + M.d) * (-N.c + N.d) := by nlinarith [hMn.1, hNn.2]
      have hd3 : 0 < 2 * (-M.c + M.d) * (N.c + N.d) := by nlinarith [hMn.2, hNn.1]
      have hd4 : 0 < 2 * (-M.c + M.d) * (-N.c + N.d) := by nlinarith [hMn.2, hNn.2]
      unfold Tensor.hasNoPole
      simp [hd1, hd2, hd3, hd4]

theorem avgTensor_corner_denom_sign_cases (M N : LFT)
    (hM : M.NoPoleOnBase) (hN : N.NoPoleOnBase) :
    let T := avgTensor M N
    let d1 : ℤ := T.e + T.f + T.g + T.h
    let d2 : ℤ := -T.e + T.f - T.g + T.h
    let d3 : ℤ := -T.e - T.f + T.g + T.h
    let d4 : ℤ := T.e - T.f - T.g + T.h
    (0 < d1 ∧ 0 < d2 ∧ 0 < d3 ∧ 0 < d4) ∨
      (d1 < 0 ∧ d2 < 0 ∧ d3 < 0 ∧ d4 < 0) := by
  dsimp [avgTensor]
  rcases LFT.endpoint_sign_cases M hM with hMp | hMn
  · rcases LFT.endpoint_sign_cases N hN with hNp | hNn
    · left
      constructor
      · have : 0 < 2 * (M.c + M.d) * (N.c + N.d) := by nlinarith [hMp.1, hNp.1]
        convert this using 1
        ring_nf
      constructor
      · have : 0 < 2 * (M.c + M.d) * (-N.c + N.d) := by nlinarith [hMp.1, hNp.2]
        convert this using 1
        ring_nf
      constructor
      · have : 0 < 2 * (-M.c + M.d) * (N.c + N.d) := by nlinarith [hMp.2, hNp.1]
        convert this using 1
        ring_nf
      · have : 0 < 2 * (-M.c + M.d) * (-N.c + N.d) := by nlinarith [hMp.2, hNp.2]
        convert this using 1
        ring_nf
    · right
      constructor
      · have : 2 * (M.c + M.d) * (N.c + N.d) < 0 := by nlinarith [hMp.1, hNn.1]
        convert this using 1
        ring_nf
      constructor
      · have : 2 * (M.c + M.d) * (-N.c + N.d) < 0 := by nlinarith [hMp.1, hNn.2]
        convert this using 1
        ring_nf
      constructor
      · have : 2 * (-M.c + M.d) * (N.c + N.d) < 0 := by nlinarith [hMp.2, hNn.1]
        convert this using 1
        ring_nf
      · have : 2 * (-M.c + M.d) * (-N.c + N.d) < 0 := by nlinarith [hMp.2, hNn.2]
        convert this using 1
        ring_nf
  · rcases LFT.endpoint_sign_cases N hN with hNp | hNn
    · right
      constructor
      · have : 2 * (M.c + M.d) * (N.c + N.d) < 0 := by nlinarith [hMn.1, hNp.1]
        convert this using 1
        ring_nf
      constructor
      · have : 2 * (M.c + M.d) * (-N.c + N.d) < 0 := by nlinarith [hMn.1, hNp.2]
        convert this using 1
        ring_nf
      constructor
      · have : 2 * (-M.c + M.d) * (N.c + N.d) < 0 := by nlinarith [hMn.2, hNp.1]
        convert this using 1
        ring_nf
      · have : 2 * (-M.c + M.d) * (-N.c + N.d) < 0 := by nlinarith [hMn.2, hNp.2]
        convert this using 1
        ring_nf
    · left
      constructor
      · have : 0 < 2 * (M.c + M.d) * (N.c + N.d) := by nlinarith [hMn.1, hNn.1]
        convert this using 1
        ring_nf
      constructor
      · have : 0 < 2 * (M.c + M.d) * (-N.c + N.d) := by nlinarith [hMn.1, hNn.2]
        convert this using 1
        ring_nf
      constructor
      · have : 0 < 2 * (-M.c + M.d) * (N.c + N.d) := by nlinarith [hMn.2, hNn.1]
        convert this using 1
        ring_nf
      · have : 0 < 2 * (-M.c + M.d) * (-N.c + N.d) := by nlinarith [hMn.2, hNn.2]
        convert this using 1
        ring_nf

theorem avgTensor_corner_ratio_11 (M N : LFT) :
    let T := avgTensor M N
    let n1 : ℤ := T.a + T.b + T.c + T.d
    let d1 : ℤ := T.e + T.f + T.g + T.h
    Tensor.apply T 1 1 = (n1 : ℝ) / d1 := by
  simp [Tensor.apply]

theorem avgTensor_corner_ratio_1m (M N : LFT) :
    let T := avgTensor M N
    let n2 : ℤ := -T.a + T.b - T.c + T.d
    let d2 : ℤ := -T.e + T.f - T.g + T.h
    Tensor.apply T 1 (-1) = (n2 : ℝ) / d2 := by
  simp [Tensor.apply]
  ring_nf

theorem avgTensor_corner_ratio_m1 (M N : LFT) :
    let T := avgTensor M N
    let n3 : ℤ := -T.a - T.b + T.c + T.d
    let d3 : ℤ := -T.e - T.f + T.g + T.h
    Tensor.apply T (-1) 1 = (n3 : ℝ) / d3 := by
  simp [Tensor.apply]
  ring_nf

theorem avgTensor_corner_ratio_mm (M N : LFT) :
    let T := avgTensor M N
    let n4 : ℤ := T.a - T.b - T.c + T.d
    let d4 : ℤ := T.e - T.f - T.g + T.h
    Tensor.apply T (-1) (-1) = (n4 : ℝ) / d4 := by
  simp [Tensor.apply]
  ring_nf

theorem residualPairedPrefix_noPoleOnBase
    (X : MobiusReal) (n : ℕ) (d : Digit) :
    ((residualDigitLFT d).comp (pairedPrefix X.stream n)).NoPoleOnBase := by
  rw [LFT.NoPoleOnBase]
  cases d <;> simpa [residualDigitLFT, LFT.comp] using pairedPrefix_noPoleOnBase X n

theorem halfAddResidualStateAfter_corner_digit_trichotomy_eventually
    (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      let T := (halfAddResidualStateAfter X Y N d K).T
      let r₁ := Tensor.apply T 1 1
      let r₂ := Tensor.apply T 1 (-1)
      let r₃ := Tensor.apply T (-1) 1
      let r₄ := Tensor.apply T (-1) (-1)
      (0 ≤ r₁ ∧ 0 ≤ r₂ ∧ 0 ≤ r₃ ∧ 0 ≤ r₄) ∨
        (r₁ ≤ 0 ∧ r₂ ≤ 0 ∧ r₃ ≤ 0 ∧ r₄ ≤ 0) ∨
        ((-1 / 2 : ℝ) ≤ r₁ ∧ r₁ ≤ (1 / 2 : ℝ) ∧
          (-1 / 2 : ℝ) ≤ r₂ ∧ r₂ ≤ (1 / 2 : ℝ) ∧
          (-1 / 2 : ℝ) ≤ r₃ ∧ r₃ ≤ (1 / 2 : ℝ) ∧
          (-1 / 2 : ℝ) ≤ r₄ ∧ r₄ ≤ (1 / 2 : ℝ)) := by
  rcases halfAddResidualStateAfter_diff_lt X Y N d (ε := (1 / 2 : ℝ)) (by norm_num) with
    ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  dsimp
  have h1 : (1 : ℝ) ∈ baseI := by constructor <;> norm_num
  have hm1 : (-1 : ℝ) ∈ baseI := by constructor <;> norm_num
  have h12 :
      |Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 1 -
        Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 (-1)| < (1 / 2 : ℝ) :=
    hK0 K hK 1 h1 1 h1 1 h1 (-1) hm1
  have h13 :
      |Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 1 -
        Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) 1| < (1 / 2 : ℝ) :=
    hK0 K hK 1 h1 (-1) hm1 1 h1 1 h1
  have h14 :
      |Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 1 -
        Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) (-1)| < (1 / 2 : ℝ) :=
    hK0 K hK 1 h1 (-1) hm1 1 h1 (-1) hm1
  have h23 :
      |Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 (-1) -
        Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) 1| < (1 / 2 : ℝ) :=
    hK0 K hK 1 h1 (-1) hm1 (-1) hm1 1 h1
  have h24 :
      |Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 (-1) -
        Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) (-1)| < (1 / 2 : ℝ) :=
    hK0 K hK 1 h1 (-1) hm1 (-1) hm1 (-1) hm1
  have h34 :
      |Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) 1 -
        Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) (-1)| < (1 / 2 : ℝ) :=
    hK0 K hK (-1) hm1 (-1) hm1 1 h1 (-1) hm1
  simpa using
    four_values_digit_trichotomy_of_close
      (Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 1)
      (Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 (-1))
      (Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) 1)
      (Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) (-1))
      h12 h13 h14 h23 h24 h34

theorem halfAddResidualStateAfter_hasNoPole_bool
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    let T := (halfAddResidualStateAfter X Y N d K).T
    Tensor.hasNoPole
      (T.e + T.f + T.g + T.h)
      (-T.e + T.f - T.g + T.h)
      (-T.e - T.f + T.g + T.h)
      (T.e - T.f - T.g + T.h) = true := by
  rw [halfAddResidualStateAfter_eq_avgTensor']
  dsimp [avgTensor]
  convert
    avgTensor_hasNoPole_bool
      ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K)))
      ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K)))
      (residualPairedPrefix_noPoleOnBase X (N + K) d)
      (residualPairedPrefix_noPoleOnBase Y (N + K) d) using 1
  ring_nf

theorem halfAddResidualStateAfter_corner_denom_sign_cases
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    let T := (halfAddResidualStateAfter X Y N d K).T
    let d1 : ℤ := T.e + T.f + T.g + T.h
    let d2 : ℤ := -T.e + T.f - T.g + T.h
    let d3 : ℤ := -T.e - T.f + T.g + T.h
    let d4 : ℤ := T.e - T.f - T.g + T.h
    (0 < d1 ∧ 0 < d2 ∧ 0 < d3 ∧ 0 < d4) ∨
      (d1 < 0 ∧ d2 < 0 ∧ d3 < 0 ∧ d4 < 0) := by
  rw [halfAddResidualStateAfter_eq_avgTensor']
  exact avgTensor_corner_denom_sign_cases
    ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K)))
    ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K)))
    (residualPairedPrefix_noPoleOnBase X (N + K) d)
    (residualPairedPrefix_noPoleOnBase Y (N + K) d)

theorem halfAddResidualStateAfter_corner_ratio_11
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    let T := (halfAddResidualStateAfter X Y N d K).T
    let n1 : ℤ := T.a + T.b + T.c + T.d
    let d1 : ℤ := T.e + T.f + T.g + T.h
    Tensor.apply T 1 1 = (n1 : ℝ) / d1 := by
  rw [halfAddResidualStateAfter_eq_avgTensor']
  exact avgTensor_corner_ratio_11
    ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K)))
    ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K)))

theorem halfAddResidualStateAfter_corner_ratio_1m
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    let T := (halfAddResidualStateAfter X Y N d K).T
    let n2 : ℤ := -T.a + T.b - T.c + T.d
    let d2 : ℤ := -T.e + T.f - T.g + T.h
    Tensor.apply T 1 (-1) = (n2 : ℝ) / d2 := by
  rw [halfAddResidualStateAfter_eq_avgTensor']
  exact avgTensor_corner_ratio_1m
    ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K)))
    ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K)))

theorem halfAddResidualStateAfter_corner_ratio_m1
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    let T := (halfAddResidualStateAfter X Y N d K).T
    let n3 : ℤ := -T.a - T.b + T.c + T.d
    let d3 : ℤ := -T.e - T.f + T.g + T.h
    Tensor.apply T (-1) 1 = (n3 : ℝ) / d3 := by
  rw [halfAddResidualStateAfter_eq_avgTensor']
  exact avgTensor_corner_ratio_m1
    ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K)))
    ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K)))

theorem halfAddResidualStateAfter_corner_ratio_mm
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    let T := (halfAddResidualStateAfter X Y N d K).T
    let n4 : ℤ := T.a - T.b - T.c + T.d
    let d4 : ℤ := T.e - T.f - T.g + T.h
    Tensor.apply T (-1) (-1) = (n4 : ℝ) / d4 := by
  rw [halfAddResidualStateAfter_eq_avgTensor']
  exact avgTensor_corner_ratio_mm
    ((residualDigitLFT d).comp (pairedPrefix X.stream (N + K)))
    ((residualDigitLFT d).comp (pairedPrefix Y.stream (N + K)))

theorem halfAddResidualStateAfter_emitsDigit_of_nonneg
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorStateAfter X Y N with
          T := (halfAddTensorStateAfter X Y N).T.emit (digit_to_LFT d) })
    (hnonneg :
      0 ≤ Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 1 ∧
      0 ≤ Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 (-1) ∧
      0 ≤ Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) 1 ∧
      0 ≤ Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) (-1)) :
    (halfAddResidualStateAfter X Y N d K).T.EmitsDigit := by
  let T := (halfAddResidualStateAfter X Y N d K).T
  let n1 : ℤ := T.a + T.b + T.c + T.d
  let d1 : ℤ := T.e + T.f + T.g + T.h
  let n2 : ℤ := -T.a + T.b - T.c + T.d
  let d2 : ℤ := -T.e + T.f - T.g + T.h
  let n3 : ℤ := -T.a - T.b + T.c + T.d
  let d3 : ℤ := -T.e - T.f + T.g + T.h
  let n4 : ℤ := T.a - T.b - T.c + T.d
  let d4 : ℤ := T.e - T.f - T.g + T.h
  have hnp : Tensor.hasNoPole d1 d2 d3 d4 = true := by
    simpa [T, d1, d2, d3, d4] using halfAddResidualStateAfter_hasNoPole_bool X Y N d K
  have hnp' :
      Tensor.hasNoPole
        (T.e + T.f + T.g + T.h)
        (-T.e + T.f - T.g + T.h)
        (-T.e - T.f + T.g + T.h)
        (T.e - T.f - T.g + T.h) = true := by
    simpa [d1, d2, d3, d4] using hnp
  rcases halfAddResidualStateAfter_corner_mem_baseI_of_step X Y N d hstep K with
    ⟨hr1, hr2, hr3, hr4⟩
  rcases hnonneg with ⟨hr1lo, hr2lo, hr3lo, hr4lo⟩
  have hratio1 : Tensor.apply T 1 1 = (n1 : ℝ) / d1 := by
    simpa [T, n1, d1] using halfAddResidualStateAfter_corner_ratio_11 X Y N d K
  have hratio2 : Tensor.apply T 1 (-1) = (n2 : ℝ) / d2 := by
    simpa [T, n2, d2] using halfAddResidualStateAfter_corner_ratio_1m X Y N d K
  have hratio3 : Tensor.apply T (-1) 1 = (n3 : ℝ) / d3 := by
    simpa [T, n3, d3] using halfAddResidualStateAfter_corner_ratio_m1 X Y N d K
  have hratio4 : Tensor.apply T (-1) (-1) = (n4 : ℝ) / d4 := by
    simpa [T, n4, d4] using halfAddResidualStateAfter_corner_ratio_mm X Y N d K
  rcases halfAddResidualStateAfter_corner_denom_sign_cases X Y N d K with hden | hden
  · have h1 : Tensor.inDigitPos n1 d1 = true := by
      apply Tensor.inDigitPos_of_ratio_pos n1 d1 hden.1
      · simpa [T, hratio1] using hr1lo
      · simpa [T, hratio1] using hr1.2
    have h2 : Tensor.inDigitPos n2 d2 = true := by
      apply Tensor.inDigitPos_of_ratio_pos n2 d2 hden.2.1
      · simpa [T, hratio2] using hr2lo
      · simpa [T, hratio2] using hr2.2
    have h3 : Tensor.inDigitPos n3 d3 = true := by
      apply Tensor.inDigitPos_of_ratio_pos n3 d3 hden.2.2.1
      · simpa [T, hratio3] using hr3lo
      · simpa [T, hratio3] using hr3.2
    have h4 : Tensor.inDigitPos n4 d4 = true := by
      apply Tensor.inDigitPos_of_ratio_pos n4 d4 hden.2.2.2
      · simpa [T, hratio4] using hr4lo
      · simpa [T, hratio4] using hr4.2
    have h1' : Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    have hposAll :
        ((Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      exact ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    by_cases hnegAll :
        ((Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
    · left
      simp [Tensor.cornerValues, hnp', hnegAll]
    · by_cases hzeroAll :
          ((Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
              Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
            Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
          Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
      · right
        left
        simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll]
      · right
        right
        simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll, hposAll]
  · have h1 : Tensor.inDigitPos n1 d1 = true := by
      apply Tensor.inDigitPos_of_ratio_neg n1 d1 hden.1
      · simpa [T, hratio1] using hr1lo
      · simpa [T, hratio1] using hr1.2
    have h2 : Tensor.inDigitPos n2 d2 = true := by
      apply Tensor.inDigitPos_of_ratio_neg n2 d2 hden.2.1
      · simpa [T, hratio2] using hr2lo
      · simpa [T, hratio2] using hr2.2
    have h3 : Tensor.inDigitPos n3 d3 = true := by
      apply Tensor.inDigitPos_of_ratio_neg n3 d3 hden.2.2.1
      · simpa [T, hratio3] using hr3lo
      · simpa [T, hratio3] using hr3.2
    have h4 : Tensor.inDigitPos n4 d4 = true := by
      apply Tensor.inDigitPos_of_ratio_neg n4 d4 hden.2.2.2
      · simpa [T, hratio4] using hr4lo
      · simpa [T, hratio4] using hr4.2
    have h1' : Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    have hposAll :
        ((Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      exact ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    by_cases hnegAll :
        ((Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
    · left
      simp [Tensor.cornerValues, hnp', hnegAll]
    · by_cases hzeroAll :
          ((Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
              Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
            Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
          Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
      · right
        left
        simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll]
      · right
        right
        simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll, hposAll]

theorem halfAddResidualStateAfter_emitsDigit_of_nonpos
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorStateAfter X Y N with
          T := (halfAddTensorStateAfter X Y N).T.emit (digit_to_LFT d) })
    (hnonpos :
      Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 1 ≤ 0 ∧
      Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 (-1) ≤ 0 ∧
      Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) 1 ≤ 0 ∧
      Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) (-1) ≤ 0) :
    (halfAddResidualStateAfter X Y N d K).T.EmitsDigit := by
  let T := (halfAddResidualStateAfter X Y N d K).T
  let n1 : ℤ := T.a + T.b + T.c + T.d
  let d1 : ℤ := T.e + T.f + T.g + T.h
  let n2 : ℤ := -T.a + T.b - T.c + T.d
  let d2 : ℤ := -T.e + T.f - T.g + T.h
  let n3 : ℤ := -T.a - T.b + T.c + T.d
  let d3 : ℤ := -T.e - T.f + T.g + T.h
  let n4 : ℤ := T.a - T.b - T.c + T.d
  let d4 : ℤ := T.e - T.f - T.g + T.h
  have hnp : Tensor.hasNoPole d1 d2 d3 d4 = true := by
    simpa [T, d1, d2, d3, d4] using halfAddResidualStateAfter_hasNoPole_bool X Y N d K
  have hnp' :
      Tensor.hasNoPole
        (T.e + T.f + T.g + T.h)
        (-T.e + T.f - T.g + T.h)
        (-T.e - T.f + T.g + T.h)
        (T.e - T.f - T.g + T.h) = true := by
    simpa [d1, d2, d3, d4] using hnp
  rcases halfAddResidualStateAfter_corner_mem_baseI_of_step X Y N d hstep K with
    ⟨hr1, hr2, hr3, hr4⟩
  rcases hnonpos with ⟨hr1hi, hr2hi, hr3hi, hr4hi⟩
  have hratio1 : Tensor.apply T 1 1 = (n1 : ℝ) / d1 := by
    simpa [T, n1, d1] using halfAddResidualStateAfter_corner_ratio_11 X Y N d K
  have hratio2 : Tensor.apply T 1 (-1) = (n2 : ℝ) / d2 := by
    simpa [T, n2, d2] using halfAddResidualStateAfter_corner_ratio_1m X Y N d K
  have hratio3 : Tensor.apply T (-1) 1 = (n3 : ℝ) / d3 := by
    simpa [T, n3, d3] using halfAddResidualStateAfter_corner_ratio_m1 X Y N d K
  have hratio4 : Tensor.apply T (-1) (-1) = (n4 : ℝ) / d4 := by
    simpa [T, n4, d4] using halfAddResidualStateAfter_corner_ratio_mm X Y N d K
  rcases halfAddResidualStateAfter_corner_denom_sign_cases X Y N d K with hden | hden
  · have h1 : Tensor.inDigitNeg n1 d1 = true := by
      apply Tensor.inDigitNeg_of_ratio_pos n1 d1 hden.1
      · simpa [T, hratio1] using hr1.1
      · simpa [T, hratio1] using hr1hi
    have h2 : Tensor.inDigitNeg n2 d2 = true := by
      apply Tensor.inDigitNeg_of_ratio_pos n2 d2 hden.2.1
      · simpa [T, hratio2] using hr2.1
      · simpa [T, hratio2] using hr2hi
    have h3 : Tensor.inDigitNeg n3 d3 = true := by
      apply Tensor.inDigitNeg_of_ratio_pos n3 d3 hden.2.2.1
      · simpa [T, hratio3] using hr3.1
      · simpa [T, hratio3] using hr3hi
    have h4 : Tensor.inDigitNeg n4 d4 = true := by
      apply Tensor.inDigitNeg_of_ratio_pos n4 d4 hden.2.2.2
      · simpa [T, hratio4] using hr4.1
      · simpa [T, hratio4] using hr4hi
    have h1' : Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    have hnegAll :
        ((Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      exact ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    simp [Tensor.cornerValues, hnp', hnegAll]
  · have h1 : Tensor.inDigitNeg n1 d1 = true := by
      apply Tensor.inDigitNeg_of_ratio_neg n1 d1 hden.1
      · simpa [T, hratio1] using hr1.1
      · simpa [T, hratio1] using hr1hi
    have h2 : Tensor.inDigitNeg n2 d2 = true := by
      apply Tensor.inDigitNeg_of_ratio_neg n2 d2 hden.2.1
      · simpa [T, hratio2] using hr2.1
      · simpa [T, hratio2] using hr2hi
    have h3 : Tensor.inDigitNeg n3 d3 = true := by
      apply Tensor.inDigitNeg_of_ratio_neg n3 d3 hden.2.2.1
      · simpa [T, hratio3] using hr3.1
      · simpa [T, hratio3] using hr3hi
    have h4 : Tensor.inDigitNeg n4 d4 = true := by
      apply Tensor.inDigitNeg_of_ratio_neg n4 d4 hden.2.2.2
      · simpa [T, hratio4] using hr4.1
      · simpa [T, hratio4] using hr4hi
    have h1' : Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    have hnegAll :
        ((Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      exact ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    simp [Tensor.cornerValues, hnp', hnegAll]

theorem halfAddResidualStateAfter_emitsDigit_of_mid
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (hmid :
      (-1 / 2 : ℝ) ≤ Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 1 ∧
      Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 1 ≤ (1 / 2 : ℝ) ∧
      (-1 / 2 : ℝ) ≤ Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 (-1) ∧
      Tensor.apply (halfAddResidualStateAfter X Y N d K).T 1 (-1) ≤ (1 / 2 : ℝ) ∧
      (-1 / 2 : ℝ) ≤ Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) 1 ∧
      Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) 1 ≤ (1 / 2 : ℝ) ∧
      (-1 / 2 : ℝ) ≤ Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) (-1) ∧
      Tensor.apply (halfAddResidualStateAfter X Y N d K).T (-1) (-1) ≤ (1 / 2 : ℝ)) :
    (halfAddResidualStateAfter X Y N d K).T.EmitsDigit := by
  let T := (halfAddResidualStateAfter X Y N d K).T
  let n1 : ℤ := T.a + T.b + T.c + T.d
  let d1 : ℤ := T.e + T.f + T.g + T.h
  let n2 : ℤ := -T.a + T.b - T.c + T.d
  let d2 : ℤ := -T.e + T.f - T.g + T.h
  let n3 : ℤ := -T.a - T.b + T.c + T.d
  let d3 : ℤ := -T.e - T.f + T.g + T.h
  let n4 : ℤ := T.a - T.b - T.c + T.d
  let d4 : ℤ := T.e - T.f - T.g + T.h
  have hnp : Tensor.hasNoPole d1 d2 d3 d4 = true := by
    simpa [T, d1, d2, d3, d4] using halfAddResidualStateAfter_hasNoPole_bool X Y N d K
  have hnp' :
      Tensor.hasNoPole
        (T.e + T.f + T.g + T.h)
        (-T.e + T.f - T.g + T.h)
        (-T.e - T.f + T.g + T.h)
        (T.e - T.f - T.g + T.h) = true := by
    simpa [d1, d2, d3, d4] using hnp
  rcases hmid with ⟨hr1lo, hr1hi, hr2lo, hr2hi, hr3lo, hr3hi, hr4lo, hr4hi⟩
  have hratio1 : Tensor.apply T 1 1 = (n1 : ℝ) / d1 := by
    simpa [T, n1, d1] using halfAddResidualStateAfter_corner_ratio_11 X Y N d K
  have hratio2 : Tensor.apply T 1 (-1) = (n2 : ℝ) / d2 := by
    simpa [T, n2, d2] using halfAddResidualStateAfter_corner_ratio_1m X Y N d K
  have hratio3 : Tensor.apply T (-1) 1 = (n3 : ℝ) / d3 := by
    simpa [T, n3, d3] using halfAddResidualStateAfter_corner_ratio_m1 X Y N d K
  have hratio4 : Tensor.apply T (-1) (-1) = (n4 : ℝ) / d4 := by
    simpa [T, n4, d4] using halfAddResidualStateAfter_corner_ratio_mm X Y N d K
  have hr1lo' : (-(1 / 2 : ℝ)) ≤ (n1 : ℝ) / d1 := by
    have hsrc : (-((2 : ℝ)⁻¹)) ≤ Tensor.apply T 1 1 := by
      have htmp : (-(1 / 2 : ℝ)) ≤ Tensor.apply T 1 1 := by
        convert hr1lo using 1
        ring_nf
      nlinarith
    have htmp : (-((2 : ℝ)⁻¹)) ≤ (n1 : ℝ) / d1 := by
      rw [← hratio1]
      exact hsrc
    nlinarith
  have hr1hi' : (n1 : ℝ) / d1 ≤ (1 / 2 : ℝ) := by
    rw [← hratio1]
    exact hr1hi
  have hr2lo' : (-(1 / 2 : ℝ)) ≤ (n2 : ℝ) / d2 := by
    have hsrc : (-((2 : ℝ)⁻¹)) ≤ Tensor.apply T 1 (-1) := by
      have htmp : (-(1 / 2 : ℝ)) ≤ Tensor.apply T 1 (-1) := by
        convert hr2lo using 1
        ring_nf
      nlinarith
    have htmp : (-((2 : ℝ)⁻¹)) ≤ (n2 : ℝ) / d2 := by
      rw [← hratio2]
      exact hsrc
    nlinarith
  have hr2hi' : (n2 : ℝ) / d2 ≤ (1 / 2 : ℝ) := by
    rw [← hratio2]
    exact hr2hi
  have hr3lo' : (-(1 / 2 : ℝ)) ≤ (n3 : ℝ) / d3 := by
    have hsrc : (-((2 : ℝ)⁻¹)) ≤ Tensor.apply T (-1) 1 := by
      have htmp : (-(1 / 2 : ℝ)) ≤ Tensor.apply T (-1) 1 := by
        convert hr3lo using 1
        ring_nf
      nlinarith
    have htmp : (-((2 : ℝ)⁻¹)) ≤ (n3 : ℝ) / d3 := by
      rw [← hratio3]
      exact hsrc
    nlinarith
  have hr3hi' : (n3 : ℝ) / d3 ≤ (1 / 2 : ℝ) := by
    rw [← hratio3]
    exact hr3hi
  have hr4lo' : (-(1 / 2 : ℝ)) ≤ (n4 : ℝ) / d4 := by
    have hsrc : (-((2 : ℝ)⁻¹)) ≤ Tensor.apply T (-1) (-1) := by
      have htmp : (-(1 / 2 : ℝ)) ≤ Tensor.apply T (-1) (-1) := by
        convert hr4lo using 1
        ring_nf
      nlinarith
    have htmp : (-((2 : ℝ)⁻¹)) ≤ (n4 : ℝ) / d4 := by
      rw [← hratio4]
      exact hsrc
    nlinarith
  have hr4hi' : (n4 : ℝ) / d4 ≤ (1 / 2 : ℝ) := by
    rw [← hratio4]
    exact hr4hi
  rcases halfAddResidualStateAfter_corner_denom_sign_cases X Y N d K with hden | hden
  · have h1 : Tensor.inDigitZero n1 d1 = true := by
      apply Tensor.inDigitZero_of_ratio_pos n1 d1 hden.1 <;> assumption
    have h2 : Tensor.inDigitZero n2 d2 = true := by
      apply Tensor.inDigitZero_of_ratio_pos n2 d2 hden.2.1 <;> assumption
    have h3 : Tensor.inDigitZero n3 d3 = true := by
      apply Tensor.inDigitZero_of_ratio_pos n3 d3 hden.2.2.1 <;> assumption
    have h4 : Tensor.inDigitZero n4 d4 = true := by
      apply Tensor.inDigitZero_of_ratio_pos n4 d4 hden.2.2.2 <;> assumption
    have h1' : Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    have hzeroAll :
        ((Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      exact ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    by_cases hnegAll :
        ((Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
    · left
      simp [Tensor.cornerValues, hnp', hnegAll]
    · right
      left
      simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll]
  · have h1 : Tensor.inDigitZero n1 d1 = true := by
      apply Tensor.inDigitZero_of_ratio_neg n1 d1 hden.1
      · exact hr1lo'
      · exact hr1hi'
    have h2 : Tensor.inDigitZero n2 d2 = true := by
      apply Tensor.inDigitZero_of_ratio_neg n2 d2 hden.2.1
      · exact hr2lo'
      · exact hr2hi'
    have h3 : Tensor.inDigitZero n3 d3 = true := by
      apply Tensor.inDigitZero_of_ratio_neg n3 d3 hden.2.2.1
      · exact hr3lo'
      · exact hr3hi'
    have h4 : Tensor.inDigitZero n4 d4 = true := by
      apply Tensor.inDigitZero_of_ratio_neg n4 d4 hden.2.2.2
      · exact hr4lo'
      · exact hr4hi'
    have h1' : Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    have hzeroAll :
        ((Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      exact ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    by_cases hnegAll :
        ((Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
    · left
      simp [Tensor.cornerValues, hnp', hnegAll]
    · right
      left
      simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll]

theorem halfAddResidualStateAfter_emitsDigit_of_nonneg_Xstep
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorXStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorXStateAfter X Y N with
          T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) })
    (hnonneg :
      0 ≤ Tensor.apply (halfAddResidualStateAfter X Y N d (K + 1)).T 1 1 ∧
      0 ≤ Tensor.apply (halfAddResidualStateAfter X Y N d (K + 1)).T 1 (-1) ∧
      0 ≤ Tensor.apply (halfAddResidualStateAfter X Y N d (K + 1)).T (-1) 1 ∧
      0 ≤ Tensor.apply (halfAddResidualStateAfter X Y N d (K + 1)).T (-1) (-1)) :
    (halfAddResidualStateAfter X Y N d (K + 1)).T.EmitsDigit := by
  let T := (halfAddResidualStateAfter X Y N d (K + 1)).T
  let n1 : ℤ := T.a + T.b + T.c + T.d
  let d1 : ℤ := T.e + T.f + T.g + T.h
  let n2 : ℤ := -T.a + T.b - T.c + T.d
  let d2 : ℤ := -T.e + T.f - T.g + T.h
  let n3 : ℤ := -T.a - T.b + T.c + T.d
  let d3 : ℤ := -T.e - T.f + T.g + T.h
  let n4 : ℤ := T.a - T.b - T.c + T.d
  let d4 : ℤ := T.e - T.f - T.g + T.h
  have hnp : Tensor.hasNoPole d1 d2 d3 d4 = true := by
    simpa [T, d1, d2, d3, d4] using halfAddResidualStateAfter_hasNoPole_bool X Y N d (K + 1)
  have hnp' :
      Tensor.hasNoPole
        (T.e + T.f + T.g + T.h)
        (-T.e + T.f - T.g + T.h)
        (-T.e - T.f + T.g + T.h)
        (T.e - T.f - T.g + T.h) = true := by
    simpa [d1, d2, d3, d4] using hnp
  rcases halfAddResidualStateAfter_corner_mem_baseI_of_Xstep X Y N d hstep K with
    ⟨hr1, hr2, hr3, hr4⟩
  rcases hnonneg with ⟨hr1lo, hr2lo, hr3lo, hr4lo⟩
  have hratio1 : Tensor.apply T 1 1 = (n1 : ℝ) / d1 := by
    simpa [T, n1, d1] using halfAddResidualStateAfter_corner_ratio_11 X Y N d (K + 1)
  have hratio2 : Tensor.apply T 1 (-1) = (n2 : ℝ) / d2 := by
    simpa [T, n2, d2] using halfAddResidualStateAfter_corner_ratio_1m X Y N d (K + 1)
  have hratio3 : Tensor.apply T (-1) 1 = (n3 : ℝ) / d3 := by
    simpa [T, n3, d3] using halfAddResidualStateAfter_corner_ratio_m1 X Y N d (K + 1)
  have hratio4 : Tensor.apply T (-1) (-1) = (n4 : ℝ) / d4 := by
    simpa [T, n4, d4] using halfAddResidualStateAfter_corner_ratio_mm X Y N d (K + 1)
  rcases halfAddResidualStateAfter_corner_denom_sign_cases X Y N d (K + 1) with hden | hden
  · have h1 : Tensor.inDigitPos n1 d1 = true := by
      apply Tensor.inDigitPos_of_ratio_pos n1 d1 hden.1
      · simpa [T, hratio1] using hr1lo
      · simpa [T, hratio1] using hr1.2
    have h2 : Tensor.inDigitPos n2 d2 = true := by
      apply Tensor.inDigitPos_of_ratio_pos n2 d2 hden.2.1
      · simpa [T, hratio2] using hr2lo
      · simpa [T, hratio2] using hr2.2
    have h3 : Tensor.inDigitPos n3 d3 = true := by
      apply Tensor.inDigitPos_of_ratio_pos n3 d3 hden.2.2.1
      · simpa [T, hratio3] using hr3lo
      · simpa [T, hratio3] using hr3.2
    have h4 : Tensor.inDigitPos n4 d4 = true := by
      apply Tensor.inDigitPos_of_ratio_pos n4 d4 hden.2.2.2
      · simpa [T, hratio4] using hr4lo
      · simpa [T, hratio4] using hr4.2
    have h1' : Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    have hposAll :
        ((Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      exact ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    by_cases hnegAll :
        ((Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
    · left
      simp [Tensor.cornerValues, hnp', hnegAll]
    · by_cases hzeroAll :
          ((Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
              Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
            Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
          Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
      · right
        left
        simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll]
      · right
        right
        simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll, hposAll]
  · have h1 : Tensor.inDigitPos n1 d1 = true := by
      apply Tensor.inDigitPos_of_ratio_neg n1 d1 hden.1
      · simpa [T, hratio1] using hr1lo
      · simpa [T, hratio1] using hr1.2
    have h2 : Tensor.inDigitPos n2 d2 = true := by
      apply Tensor.inDigitPos_of_ratio_neg n2 d2 hden.2.1
      · simpa [T, hratio2] using hr2lo
      · simpa [T, hratio2] using hr2.2
    have h3 : Tensor.inDigitPos n3 d3 = true := by
      apply Tensor.inDigitPos_of_ratio_neg n3 d3 hden.2.2.1
      · simpa [T, hratio3] using hr3lo
      · simpa [T, hratio3] using hr3.2
    have h4 : Tensor.inDigitPos n4 d4 = true := by
      apply Tensor.inDigitPos_of_ratio_neg n4 d4 hden.2.2.2
      · simpa [T, hratio4] using hr4lo
      · simpa [T, hratio4] using hr4.2
    have h1' : Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    have hposAll :
        ((Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      exact ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    by_cases hnegAll :
        ((Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
    · left
      simp [Tensor.cornerValues, hnp', hnegAll]
    · by_cases hzeroAll :
          ((Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
              Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
            Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
          Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
      · right
        left
        simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll]
      · right
        right
        simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll, hposAll]

theorem halfAddResidualStateAfter_emitsDigit_of_nonpos_Xstep
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorXStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorXStateAfter X Y N with
          T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) })
    (hnonpos :
      Tensor.apply (halfAddResidualStateAfter X Y N d (K + 1)).T 1 1 ≤ 0 ∧
      Tensor.apply (halfAddResidualStateAfter X Y N d (K + 1)).T 1 (-1) ≤ 0 ∧
      Tensor.apply (halfAddResidualStateAfter X Y N d (K + 1)).T (-1) 1 ≤ 0 ∧
      Tensor.apply (halfAddResidualStateAfter X Y N d (K + 1)).T (-1) (-1) ≤ 0) :
    (halfAddResidualStateAfter X Y N d (K + 1)).T.EmitsDigit := by
  let T := (halfAddResidualStateAfter X Y N d (K + 1)).T
  let n1 : ℤ := T.a + T.b + T.c + T.d
  let d1 : ℤ := T.e + T.f + T.g + T.h
  let n2 : ℤ := -T.a + T.b - T.c + T.d
  let d2 : ℤ := -T.e + T.f - T.g + T.h
  let n3 : ℤ := -T.a - T.b + T.c + T.d
  let d3 : ℤ := -T.e - T.f + T.g + T.h
  let n4 : ℤ := T.a - T.b - T.c + T.d
  let d4 : ℤ := T.e - T.f - T.g + T.h
  have hnp : Tensor.hasNoPole d1 d2 d3 d4 = true := by
    simpa [T, d1, d2, d3, d4] using halfAddResidualStateAfter_hasNoPole_bool X Y N d (K + 1)
  have hnp' :
      Tensor.hasNoPole
        (T.e + T.f + T.g + T.h)
        (-T.e + T.f - T.g + T.h)
        (-T.e - T.f + T.g + T.h)
        (T.e - T.f - T.g + T.h) = true := by
    simpa [d1, d2, d3, d4] using hnp
  rcases halfAddResidualStateAfter_corner_mem_baseI_of_Xstep X Y N d hstep K with
    ⟨hr1, hr2, hr3, hr4⟩
  rcases hnonpos with ⟨hr1hi, hr2hi, hr3hi, hr4hi⟩
  have hratio1 : Tensor.apply T 1 1 = (n1 : ℝ) / d1 := by
    simpa [T, n1, d1] using halfAddResidualStateAfter_corner_ratio_11 X Y N d (K + 1)
  have hratio2 : Tensor.apply T 1 (-1) = (n2 : ℝ) / d2 := by
    simpa [T, n2, d2] using halfAddResidualStateAfter_corner_ratio_1m X Y N d (K + 1)
  have hratio3 : Tensor.apply T (-1) 1 = (n3 : ℝ) / d3 := by
    simpa [T, n3, d3] using halfAddResidualStateAfter_corner_ratio_m1 X Y N d (K + 1)
  have hratio4 : Tensor.apply T (-1) (-1) = (n4 : ℝ) / d4 := by
    simpa [T, n4, d4] using halfAddResidualStateAfter_corner_ratio_mm X Y N d (K + 1)
  rcases halfAddResidualStateAfter_corner_denom_sign_cases X Y N d (K + 1) with hden | hden
  · have h1 : Tensor.inDigitNeg n1 d1 = true := by
      apply Tensor.inDigitNeg_of_ratio_pos n1 d1 hden.1
      · simpa [T, hratio1] using hr1.1
      · simpa [T, hratio1] using hr1hi
    have h2 : Tensor.inDigitNeg n2 d2 = true := by
      apply Tensor.inDigitNeg_of_ratio_pos n2 d2 hden.2.1
      · simpa [T, hratio2] using hr2.1
      · simpa [T, hratio2] using hr2hi
    have h3 : Tensor.inDigitNeg n3 d3 = true := by
      apply Tensor.inDigitNeg_of_ratio_pos n3 d3 hden.2.2.1
      · simpa [T, hratio3] using hr3.1
      · simpa [T, hratio3] using hr3hi
    have h4 : Tensor.inDigitNeg n4 d4 = true := by
      apply Tensor.inDigitNeg_of_ratio_pos n4 d4 hden.2.2.2
      · simpa [T, hratio4] using hr4.1
      · simpa [T, hratio4] using hr4hi
    have h1' : Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    have hnegAll :
        ((Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      exact ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    simp [Tensor.cornerValues, hnp', hnegAll]
  · have h1 : Tensor.inDigitNeg n1 d1 = true := by
      apply Tensor.inDigitNeg_of_ratio_neg n1 d1 hden.1
      · simpa [T, hratio1] using hr1.1
      · simpa [T, hratio1] using hr1hi
    have h2 : Tensor.inDigitNeg n2 d2 = true := by
      apply Tensor.inDigitNeg_of_ratio_neg n2 d2 hden.2.1
      · simpa [T, hratio2] using hr2.1
      · simpa [T, hratio2] using hr2hi
    have h3 : Tensor.inDigitNeg n3 d3 = true := by
      apply Tensor.inDigitNeg_of_ratio_neg n3 d3 hden.2.2.1
      · simpa [T, hratio3] using hr3.1
      · simpa [T, hratio3] using hr3hi
    have h4 : Tensor.inDigitNeg n4 d4 = true := by
      apply Tensor.inDigitNeg_of_ratio_neg n4 d4 hden.2.2.2
      · simpa [T, hratio4] using hr4.1
      · simpa [T, hratio4] using hr4hi
    have h1' : Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    have hnegAll :
        ((Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      exact ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    simp [Tensor.cornerValues, hnp', hnegAll]

theorem halfAddResidualStateAfter_emitsDigit_eventually_of_Xstep
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorXStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorXStateAfter X Y N with
          T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∃ K0 : ℕ, ∀ K ≥ K0, (halfAddResidualStateAfter X Y N d (K + 1)).T.EmitsDigit := by
  rcases halfAddResidualStateAfter_corner_digit_trichotomy_eventually X Y N d with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  have hK' : K + 1 ≥ K0 := le_trans hK (Nat.le_succ _)
  rcases hK0 (K + 1) hK' with hpos | hneg | hmid
  · exact halfAddResidualStateAfter_emitsDigit_of_nonneg_Xstep X Y N d K hstep hpos
  · exact halfAddResidualStateAfter_emitsDigit_of_nonpos_Xstep X Y N d K hstep hneg
  · exact halfAddResidualStateAfter_emitsDigit_of_mid X Y N d (K + 1) hmid

theorem halfAddResidualStateAfter_productivity_spec_of_Xstep
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorXStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorXStateAfter X Y N with
          T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∃ K : ℕ, (halfAddResidualStateAfter X Y N d (K + 1)).T.ProductiveOnBase := by
  rcases halfAddResidualStateAfter_safeEventually X Y N d with ⟨Ksafe, hsafe⟩
  rcases halfAddResidualStateAfter_emitsDigit_eventually_of_Xstep X Y N d hstep with
    ⟨Kemit, hemit⟩
  refine ⟨max Ksafe Kemit, ?_⟩
  refine ⟨(hsafe (max Ksafe Kemit + 1) (le_trans (Nat.le_max_left _ _) (Nat.le_succ _))).1,
    (hsafe (max Ksafe Kemit + 1) (le_trans (Nat.le_max_left _ _) (Nat.le_succ _))).2, ?_⟩
  exact hemit (max Ksafe Kemit) (Nat.le_max_right _ _)

theorem halfAddResidualStateAfter_emitsDigit_eventually_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorStateAfter X Y N with
          T := (halfAddTensorStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∃ K0 : ℕ, ∀ K ≥ K0, (halfAddResidualStateAfter X Y N d K).T.EmitsDigit := by
  rcases halfAddResidualStateAfter_corner_digit_trichotomy_eventually X Y N d with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  rcases hK0 K hK with hpos | hneg | hmid
  · exact halfAddResidualStateAfter_emitsDigit_of_nonneg X Y N d K hstep hpos
  · exact halfAddResidualStateAfter_emitsDigit_of_nonpos X Y N d K hstep hneg
  · exact halfAddResidualStateAfter_emitsDigit_of_mid X Y N d K hmid

theorem halfAddResidualStateAfter_productivity_spec_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorStateAfter X Y N with
          T := (halfAddTensorStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∃ K : ℕ, (halfAddResidualStateAfter X Y N d K).T.ProductiveOnBase := by
  rcases halfAddResidualStateAfter_safeEventually X Y N d with ⟨Ksafe, hsafe⟩
  rcases halfAddResidualStateAfter_emitsDigit_eventually_of_step X Y N d hstep with
    ⟨Kemit, hemit⟩
  refine ⟨max Ksafe Kemit, ?_⟩
  refine ⟨(hsafe (max Ksafe Kemit) (Nat.le_max_left _ _)).1,
    (hsafe (max Ksafe Kemit) (Nat.le_max_left _ _)).2, ?_⟩
  exact hemit (max Ksafe Kemit) (Nat.le_max_right _ _)

theorem halfAddTensorStateAfter_hasNoPole_bool (X Y : MobiusReal) (N : ℕ) :
    let T := Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N
    Tensor.hasNoPole
      (T.e + T.f + T.g + T.h)
      (-T.e + T.f - T.g + T.h)
      (-T.e - T.f + T.g + T.h)
      (T.e - T.f - T.g + T.h) = true := by
  rw [absorbBoth_n_halfAdd_eq_avgTensor]
  dsimp [avgTensor]
  convert
    avgTensor_hasNoPole_bool (pairedPrefix X.stream N) (pairedPrefix Y.stream N)
      (pairedPrefix_noPoleOnBase X N) (pairedPrefix_noPoleOnBase Y N) using 1
  ring_nf

theorem halfAddTensorStateAfter_corner_denom_sign_cases (X Y : MobiusReal) (N : ℕ) :
    let T := Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N
    let d1 : ℤ := T.e + T.f + T.g + T.h
    let d2 : ℤ := -T.e + T.f - T.g + T.h
    let d3 : ℤ := -T.e - T.f + T.g + T.h
    let d4 : ℤ := T.e - T.f - T.g + T.h
    (0 < d1 ∧ 0 < d2 ∧ 0 < d3 ∧ 0 < d4) ∨
      (d1 < 0 ∧ d2 < 0 ∧ d3 < 0 ∧ d4 < 0) := by
  rw [absorbBoth_n_halfAdd_eq_avgTensor]
  dsimp [avgTensor]
  rcases LFT.endpoint_sign_cases (pairedPrefix X.stream N) (pairedPrefix_noPoleOnBase X N) with hX | hX
  · rcases LFT.endpoint_sign_cases (pairedPrefix Y.stream N) (pairedPrefix_noPoleOnBase Y N) with hY | hY
    · left
      constructor
      · have : 0 < 2 * ((pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            ((pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) := by
          nlinarith [hX.1, hY.1]
        convert this using 1
        ring_nf
      constructor
      · have : 0 < 2 * ((pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            (-(pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) := by
          nlinarith [hX.1, hY.2]
        convert this using 1
        ring_nf
      constructor
      · have : 0 < 2 * (-(pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            ((pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) := by
          nlinarith [hX.2, hY.1]
        convert this using 1
        ring_nf
      · have : 0 < 2 * (-(pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            (-(pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) := by
          nlinarith [hX.2, hY.2]
        convert this using 1
        ring_nf
    · right
      constructor
      · have : 2 * ((pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            ((pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) < 0 := by
          nlinarith [hX.1, hY.1]
        convert this using 1
        ring_nf
      constructor
      · have : 2 * ((pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            (-(pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) < 0 := by
          nlinarith [hX.1, hY.2]
        convert this using 1
        ring_nf
      constructor
      · have : 2 * (-(pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            ((pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) < 0 := by
          nlinarith [hX.2, hY.1]
        convert this using 1
        ring_nf
      · have : 2 * (-(pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            (-(pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) < 0 := by
          nlinarith [hX.2, hY.2]
        convert this using 1
        ring_nf
  · rcases LFT.endpoint_sign_cases (pairedPrefix Y.stream N) (pairedPrefix_noPoleOnBase Y N) with hY | hY
    · right
      constructor
      · have : 2 * ((pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            ((pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) < 0 := by
          nlinarith [hX.1, hY.1]
        convert this using 1
        ring_nf
      constructor
      · have : 2 * ((pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            (-(pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) < 0 := by
          nlinarith [hX.1, hY.2]
        convert this using 1
        ring_nf
      constructor
      · have : 2 * (-(pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            ((pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) < 0 := by
          nlinarith [hX.2, hY.1]
        convert this using 1
        ring_nf
      · have : 2 * (-(pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            (-(pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) < 0 := by
          nlinarith [hX.2, hY.2]
        convert this using 1
        ring_nf
    · left
      constructor
      · have : 0 < 2 * ((pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            ((pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) := by
          nlinarith [hX.1, hY.1]
        convert this using 1
        ring_nf
      constructor
      · have : 0 < 2 * ((pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            (-(pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) := by
          nlinarith [hX.1, hY.2]
        convert this using 1
        ring_nf
      constructor
      · have : 0 < 2 * (-(pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            ((pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) := by
          nlinarith [hX.2, hY.1]
        convert this using 1
        ring_nf
      · have : 0 < 2 * (-(pairedPrefix X.stream N).c + (pairedPrefix X.stream N).d) *
            (-(pairedPrefix Y.stream N).c + (pairedPrefix Y.stream N).d) := by
          nlinarith [hX.2, hY.2]
        convert this using 1
        ring_nf

theorem halfAddTensorStateAfter_corner_ratio_11 (X Y : MobiusReal) (N : ℕ) :
    let T := Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N
    let n1 : ℤ := T.a + T.b + T.c + T.d
    let d1 : ℤ := T.e + T.f + T.g + T.h
    Tensor.apply T 1 1 = (n1 : ℝ) / d1 := by
  simp [Tensor.apply]

theorem halfAddTensorStateAfter_corner_ratio_1m (X Y : MobiusReal) (N : ℕ) :
    let T := Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N
    let n2 : ℤ := -T.a + T.b - T.c + T.d
    let d2 : ℤ := -T.e + T.f - T.g + T.h
    Tensor.apply T 1 (-1) = (n2 : ℝ) / d2 := by
  simp [Tensor.apply]
  ring_nf

theorem halfAddTensorStateAfter_corner_ratio_m1 (X Y : MobiusReal) (N : ℕ) :
    let T := Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N
    let n3 : ℤ := -T.a - T.b + T.c + T.d
    let d3 : ℤ := -T.e - T.f + T.g + T.h
    Tensor.apply T (-1) 1 = (n3 : ℝ) / d3 := by
  simp [Tensor.apply]
  ring_nf

theorem halfAddTensorStateAfter_corner_ratio_mm (X Y : MobiusReal) (N : ℕ) :
    let T := Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N
    let n4 : ℤ := T.a - T.b - T.c + T.d
    let d4 : ℤ := T.e - T.f - T.g + T.h
    Tensor.apply T (-1) (-1) = (n4 : ℝ) / d4 := by
  simp [Tensor.apply]
  ring_nf

theorem halfAddTensorStateAfter_corner_digit_trichotomy_eventually (X Y : MobiusReal) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      let T := Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N
      let r₁ := Tensor.apply T 1 1
      let r₂ := Tensor.apply T 1 (-1)
      let r₃ := Tensor.apply T (-1) 1
      let r₄ := Tensor.apply T (-1) (-1)
      (0 ≤ r₁ ∧ 0 ≤ r₂ ∧ 0 ≤ r₃ ∧ 0 ≤ r₄) ∨
        (r₁ ≤ 0 ∧ r₂ ≤ 0 ∧ r₃ ≤ 0 ∧ r₄ ≤ 0) ∨
        ((-1 / 2 : ℝ) ≤ r₁ ∧ r₁ ≤ (1 / 2 : ℝ) ∧
          (-1 / 2 : ℝ) ≤ r₂ ∧ r₂ ≤ (1 / 2 : ℝ) ∧
          (-1 / 2 : ℝ) ≤ r₃ ∧ r₃ ≤ (1 / 2 : ℝ) ∧
          (-1 / 2 : ℝ) ≤ r₄ ∧ r₄ ≤ (1 / 2 : ℝ)) := by
  rcases halfAddTensorStateAfter_diff_lt X Y (ε := (1 / 2 : ℝ)) (by norm_num) with
    ⟨N0, hN0⟩
  refine ⟨N0, ?_⟩
  intro N hN
  dsimp
  have h1 : (1 : ℝ) ∈ baseI := by constructor <;> norm_num
  have hm1 : (-1 : ℝ) ∈ baseI := by constructor <;> norm_num
  rcases halfAddTensorStateAfter_corner_mem_baseI X Y N with
    ⟨hr₁, hr₂, hr₃, hr₄⟩
  have h12 :
      |Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 1 -
        Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 (-1)| < (1 / 2 : ℝ) :=
    hN0 N hN 1 h1 1 h1 1 h1 (-1) hm1
  have h13 :
      |Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 1 -
        Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) 1| < (1 / 2 : ℝ) :=
    hN0 N hN 1 h1 (-1) hm1 1 h1 1 h1
  have h14 :
      |Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 1 -
        Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) (-1)| < (1 / 2 : ℝ) :=
    hN0 N hN 1 h1 (-1) hm1 1 h1 (-1) hm1
  have h23 :
      |Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 (-1) -
        Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) 1| < (1 / 2 : ℝ) :=
    hN0 N hN 1 h1 (-1) hm1 (-1) hm1 1 h1
  have h24 :
      |Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 (-1) -
        Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) (-1)| < (1 / 2 : ℝ) :=
    hN0 N hN 1 h1 (-1) hm1 (-1) hm1 (-1) hm1
  have h34 :
      |Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) 1 -
        Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) (-1)| < (1 / 2 : ℝ) :=
    hN0 N hN (-1) hm1 (-1) hm1 1 h1 (-1) hm1
  simpa using
    four_values_digit_trichotomy
      (Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 1)
      (Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 (-1))
      (Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) 1)
      (Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) (-1))
      hr₁ hr₂ hr₃ hr₄ h12 h13 h14 h23 h24 h34


theorem halfAddInit_safe (X Y : MobiusReal) :
    GeneralTrace.SafeAt X Y halfAddInitState := by
  simp [halfAddInitState, GeneralTrace.SafeAt, Tensor.denAt, halfAddTensor]

theorem halfAddInit_stateValue (X Y : MobiusReal) :
    GeneralTrace.stateValue X Y halfAddInitState = (X.val + Y.val) / 2 := by
  simp [halfAddInitState, GeneralTrace.stateValue, halfAddTensor_valueAt, MobiusReal.drop]

theorem vmStep_emit_of_emitsDigit {s : VMState} (h : s.T.EmitsDigit) :
    ∃ d, VMStep s (some d) { s with T := s.T.emit d } := by
  rcases h with hneg | hrest
  · exact ⟨digitNeg, VMStep.emitNeg hneg⟩
  · rcases hrest with hzero | hpos
    · exact ⟨digitZero, VMStep.emitZero hzero⟩
    · exact ⟨digitPos, VMStep.emitPos hpos⟩

theorem vmStepXY_emit_of_emitsDigit (X Y : MobiusReal) {s : VMState} (h : s.T.EmitsDigit) :
    ∃ d, GeneralTrace.VMStepXY X Y s (some d) { s with T := s.T.emit d } := by
  rcases h with hneg | hrest
  · exact ⟨digitNeg, GeneralTrace.VMStepXY.emitNeg hneg⟩
  · rcases hrest with hzero | hpos
    · exact ⟨digitZero, GeneralTrace.VMStepXY.emitZero hzero⟩
    · exact ⟨digitPos, GeneralTrace.VMStepXY.emitPos hpos⟩

theorem stateValue_emit_mem_baseI
    (X Y : MobiusReal) {s s' : VMState} {d : LFT}
    (h : GeneralTrace.VMStepXY X Y s (some d) s')
    (hs : GeneralTrace.SafeAt X Y s) (hs' : GeneralTrace.SafeAt X Y s') :
    GeneralTrace.stateValue X Y s' ∈ baseI := by
  cases h with
  | emitNeg hor =>
      have hx : (MobiusReal.drop X s.idx_x).val ∈ baseI := GeneralTrace.drop_val_mem_baseI X s.idx_x
      have hy : (MobiusReal.drop Y s.idx_y).val ∈ baseI := GeneralTrace.drop_val_mem_baseI Y s.idx_y
      have hold :
          -1 ≤ GeneralTrace.stateValue X Y s ∧ GeneralTrace.stateValue X Y s ≤ 0 := by
        simpa [GeneralTrace.stateValue, Tensor.valueAt] using
          (Tensor.emitNeg_sound (T := s.T)
            (x := (MobiusReal.drop X s.idx_x).val) (y := (MobiusReal.drop Y s.idx_y).val)
            hx.1 hx.2 hy.1 hy.2 hor)
      have hstep :
          GeneralTrace.stateValue X Y s =
            LFT.apply digitNeg (GeneralTrace.stateValue X Y { s with T := s.T.emit digitNeg }) := by
        simpa using
          (GeneralTrace.stateValue_step_some (X := X) (Y := Y)
            (s := s) (s' := { s with T := s.T.emit digitNeg })
            (h := GeneralTrace.VMStepXY.emitNeg (X := X) (Y := Y) (s := s) hor) hs hs')
      constructor
      · have heq : GeneralTrace.stateValue X Y s =
            ((GeneralTrace.stateValue X Y { s with T := s.T.emit digitNeg }) - 1) / 2 := by
            simpa [digitNeg, LFT.apply] using hstep
        nlinarith [hold.1, hold.2, heq]
      · have heq : GeneralTrace.stateValue X Y s =
            ((GeneralTrace.stateValue X Y { s with T := s.T.emit digitNeg }) - 1) / 2 := by
            simpa [digitNeg, LFT.apply] using hstep
        nlinarith [hold.1, hold.2, heq]
  | emitZero hor =>
      have hx : (MobiusReal.drop X s.idx_x).val ∈ baseI := GeneralTrace.drop_val_mem_baseI X s.idx_x
      have hy : (MobiusReal.drop Y s.idx_y).val ∈ baseI := GeneralTrace.drop_val_mem_baseI Y s.idx_y
      have hold :
          (-1 / 2 : ℝ) ≤ GeneralTrace.stateValue X Y s ∧
            GeneralTrace.stateValue X Y s ≤ (1 / 2 : ℝ) := by
        simpa [GeneralTrace.stateValue, Tensor.valueAt] using
          (Tensor.emitZero_sound (T := s.T)
            (x := (MobiusReal.drop X s.idx_x).val) (y := (MobiusReal.drop Y s.idx_y).val)
            hx.1 hx.2 hy.1 hy.2 hor)
      have hstep :
          GeneralTrace.stateValue X Y s =
            LFT.apply digitZero (GeneralTrace.stateValue X Y { s with T := s.T.emit digitZero }) := by
        simpa using
          (GeneralTrace.stateValue_step_some (X := X) (Y := Y)
            (s := s) (s' := { s with T := s.T.emit digitZero })
            (h := GeneralTrace.VMStepXY.emitZero (X := X) (Y := Y) (s := s) hor) hs hs')
      constructor
      · have heq : GeneralTrace.stateValue X Y s =
            (GeneralTrace.stateValue X Y { s with T := s.T.emit digitZero }) / 2 := by
            simpa [digitZero, LFT.apply] using hstep
        nlinarith [hold.1, hold.2, heq]
      · have heq : GeneralTrace.stateValue X Y s =
            (GeneralTrace.stateValue X Y { s with T := s.T.emit digitZero }) / 2 := by
            simpa [digitZero, LFT.apply] using hstep
        nlinarith [hold.1, hold.2, heq]
  | emitPos hor =>
      have hx : (MobiusReal.drop X s.idx_x).val ∈ baseI := GeneralTrace.drop_val_mem_baseI X s.idx_x
      have hy : (MobiusReal.drop Y s.idx_y).val ∈ baseI := GeneralTrace.drop_val_mem_baseI Y s.idx_y
      have hold :
          0 ≤ GeneralTrace.stateValue X Y s ∧ GeneralTrace.stateValue X Y s ≤ 1 := by
        simpa [GeneralTrace.stateValue, Tensor.valueAt] using
          (Tensor.emitPos_sound (T := s.T)
            (x := (MobiusReal.drop X s.idx_x).val) (y := (MobiusReal.drop Y s.idx_y).val)
            hx.1 hx.2 hy.1 hy.2 hor)
      have hstep :
          GeneralTrace.stateValue X Y s =
            LFT.apply digitPos (GeneralTrace.stateValue X Y { s with T := s.T.emit digitPos }) := by
        simpa using
          (GeneralTrace.stateValue_step_some (X := X) (Y := Y)
            (s := s) (s' := { s with T := s.T.emit digitPos })
            (h := GeneralTrace.VMStepXY.emitPos (X := X) (Y := Y) (s := s) hor) hs hs')
      constructor
      · have heq : GeneralTrace.stateValue X Y s =
            ((GeneralTrace.stateValue X Y { s with T := s.T.emit digitPos }) + 1) / 2 := by
            simpa [digitPos, LFT.apply] using hstep
        nlinarith [hold.1, hold.2, heq]
      · have heq : GeneralTrace.stateValue X Y s =
            ((GeneralTrace.stateValue X Y { s with T := s.T.emit digitPos }) + 1) / 2 := by
            simpa [digitPos, LFT.apply] using hstep
        nlinarith [hold.1, hold.2, heq]

theorem safeVMRun_singleton_residual_mem_baseI
    (X Y : MobiusReal) {s t : VMState} {d : LFT}
    (hRun : SafeVMRun X Y s [d] t) :
    GeneralTrace.stateValue X Y t ∈ baseI := by
  have hgen :
      ∀ {s t : VMState} {es : List LFT},
        SafeVMRun X Y s es t → es.length = 1 → GeneralTrace.stateValue X Y t ∈ baseI := by
    intro s t es hRun'
    induction hRun' with
    | refl s hs =>
        intro hlen
        simp at hlen
    | stepNone h hs hs' ht ih =>
        intro hlen
        exact ih hlen
    | stepSome h hs hs' ht ih =>
        intro hlen
        have hmem := stateValue_emit_mem_baseI X Y h hs hs'
        have hEq := by
          simpa [List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen), emittedValue] using
            (vm_soundness_prefix _ _ X Y _ ht)
        simpa [hEq] using hmem
  exact hgen hRun (by simp)

theorem safeVMRun_pair_residual_mem_baseI
    (X Y : MobiusReal) {s t : VMState} {d₁ d₂ : LFT}
    (hRun : SafeVMRun X Y s [d₁, d₂] t) :
    GeneralTrace.stateValue X Y t ∈ baseI := by
  have hgen :
      ∀ {s t : VMState} {es : List LFT},
        SafeVMRun X Y s es t → es.length = 2 → GeneralTrace.stateValue X Y t ∈ baseI := by
    intro s t es hRun'
    induction hRun' with
    | refl s hs =>
        intro hlen
        simp at hlen
    | stepNone h hs hs' ht ih =>
        intro hlen
        exact ih hlen
    | stepSome h hs hs' ht ih =>
        intro hlen
        rename_i s s' t d ds
        have hlen' : ds.length = 1 := by
          simpa using Nat.succ.inj hlen
        cases ds with
        | nil =>
            simp at hlen'
        | cons d ds' =>
            cases ds' with
            | nil =>
                simpa using safeVMRun_singleton_residual_mem_baseI X Y ht
            | cons d' ds'' =>
                simp at hlen'
  exact hgen hRun (by simp)

theorem safe_end_of_safeVMRun (X Y : MobiusReal) {s t : VMState} {ds : List LFT}
    (hRun : SafeVMRun X Y s ds t) :
    GeneralTrace.SafeAt X Y t := by
  induction hRun with
  | refl s hs => exact hs
  | stepNone h hs hs' ht ih => exact ih
  | stepSome h hs hs' ht ih => exact ih

theorem safeVMRun_append (X Y : MobiusReal) {s u t : VMState} {ds es : List LFT}
    (h₁ : SafeVMRun X Y s ds u) (h₂ : SafeVMRun X Y u es t) :
    SafeVMRun X Y s (ds ++ es) t := by
  induction h₁ generalizing es t with
  | refl s hs =>
      simpa using h₂
  | stepNone h hs hs' ht ih =>
      exact SafeVMRun.stepNone h hs hs' (ih h₂)
  | stepSome h hs hs' ht ih =>
      simpa [List.cons_append] using SafeVMRun.stepSome h hs hs' (ih h₂)

theorem safeVMRun_append_nil (X Y : MobiusReal) {s u t : VMState}
    (h₁ : SafeVMRun X Y s [] u) (h₂ : SafeVMRun X Y u [] t) :
    SafeVMRun X Y s [] t := by
  simpa using safeVMRun_append X Y h₁ h₂

theorem halfAddTensorStateAfter_absorbX_step
    (X Y : MobiusReal) (N : ℕ)
    (h : (halfAddTensorStateAfter X Y N).T.oracle = Tensor.EmitDecision.absorb) :
    GeneralTrace.VMStepXY X Y (halfAddTensorStateAfter X Y N) none
      (halfAddTensorXStateAfter X Y N) := by
  simpa [halfAddTensorStateAfter, halfAddTensorXStateAfter] using
    (GeneralTrace.VMStepXY.absorbX (X := X) (Y := Y) (s := halfAddTensorStateAfter X Y N) h rfl)

theorem halfAddTensorXStateAfter_absorbY_step
    (X Y : MobiusReal) (N : ℕ)
    (h : (halfAddTensorXStateAfter X Y N).T.oracle = Tensor.EmitDecision.absorb) :
    GeneralTrace.VMStepXY X Y (halfAddTensorXStateAfter X Y N) none
      (halfAddTensorStateAfter X Y (N + 1)) := by
  simpa [halfAddTensorStateAfter, halfAddTensorXStateAfter, Tensor.absorbBoth_n] using
    (GeneralTrace.VMStepXY.absorbY (X := X) (Y := Y) (s := halfAddTensorXStateAfter X Y N) h rfl)

theorem halfAddResidualStateAfter_absorbX_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (h : (halfAddResidualStateAfter X Y N d K).T.oracle = Tensor.EmitDecision.absorb) :
    GeneralTrace.VMStepXY X Y (halfAddResidualStateAfter X Y N d K) none
      (halfAddResidualXStateAfter X Y N d K) := by
  have hstream : (MobiusReal.drop X N).stream K = X.stream (N + K) := by
    simp [MobiusReal.drop, Nat.add_comm]
  simpa [halfAddResidualStateAfter, halfAddResidualXStateAfter, hstream] using
    (GeneralTrace.VMStepXY.absorbX (X := X) (Y := Y)
      (s := halfAddResidualStateAfter X Y N d K) h rfl)

theorem halfAddResidualXStateAfter_absorbY_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (h : (halfAddResidualXStateAfter X Y N d K).T.oracle = Tensor.EmitDecision.absorb) :
    GeneralTrace.VMStepXY X Y (halfAddResidualXStateAfter X Y N d K) none
      (halfAddResidualStateAfter X Y N d (K + 1)) := by
  have hstream : (MobiusReal.drop Y N).stream K = Y.stream (N + K) := by
    simp [MobiusReal.drop, Nat.add_comm]
  simpa [halfAddResidualStateAfter, halfAddResidualXStateAfter, Tensor.absorbBoth_n, hstream] using
    (GeneralTrace.VMStepXY.absorbY (X := X) (Y := Y)
      (s := halfAddResidualXStateAfter X Y N d K) h rfl)

theorem halfAddResidual_pair_reachable
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (hs : GeneralTrace.SafeAt X Y (halfAddResidualStateAfter X Y N d K))
    (habs : (halfAddResidualStateAfter X Y N d K).T.oracle = Tensor.EmitDecision.absorb)
    (habsX : (halfAddResidualXStateAfter X Y N d K).T.oracle = Tensor.EmitDecision.absorb) :
    SafeVMRun X Y (halfAddResidualStateAfter X Y N d K) []
      (halfAddResidualStateAfter X Y N d (K + 1)) := by
  have hstepX : GeneralTrace.VMStepXY X Y (halfAddResidualStateAfter X Y N d K) none
      (halfAddResidualXStateAfter X Y N d K) :=
    halfAddResidualStateAfter_absorbX_step X Y N d K habs
  have hsX : GeneralTrace.SafeAt X Y (halfAddResidualXStateAfter X Y N d K) :=
    safe_step (X := X) (Y := Y) hstepX hs
  have hstepY : GeneralTrace.VMStepXY X Y (halfAddResidualXStateAfter X Y N d K) none
      (halfAddResidualStateAfter X Y N d (K + 1)) :=
    halfAddResidualXStateAfter_absorbY_step X Y N d K habsX
  have hsY : GeneralTrace.SafeAt X Y (halfAddResidualStateAfter X Y N d (K + 1)) :=
    safe_step (X := X) (Y := Y) hstepY hsX
  exact SafeVMRun.stepNone hstepX hs hsX <|
    SafeVMRun.stepNone hstepY hsX hsY <|
      SafeVMRun.refl _ hsY

theorem halfAddResidualXStateAfter_reachable
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (hreach : SafeVMRun X Y halfAddInitState [digit_to_LFT d]
      (halfAddResidualStateAfter X Y N d K))
    (habs : (halfAddResidualStateAfter X Y N d K).T.oracle = Tensor.EmitDecision.absorb) :
    SafeVMRun X Y halfAddInitState [digit_to_LFT d]
      (halfAddResidualXStateAfter X Y N d K) := by
  have hsK : GeneralTrace.SafeAt X Y (halfAddResidualStateAfter X Y N d K) :=
    safe_end_of_safeVMRun X Y hreach
  have hstepX : GeneralTrace.VMStepXY X Y (halfAddResidualStateAfter X Y N d K) none
      (halfAddResidualXStateAfter X Y N d K) :=
    halfAddResidualStateAfter_absorbX_step X Y N d K habs
  have hsX : GeneralTrace.SafeAt X Y (halfAddResidualXStateAfter X Y N d K) :=
    safe_step (X := X) (Y := Y) hstepX hsK
  exact safeVMRun_append X Y hreach
    (SafeVMRun.stepNone hstepX hsK hsX (SafeVMRun.refl _ hsX))

theorem halfAddResidualStateAfter_reachable
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (hreach0 : SafeVMRun X Y halfAddInitState [digit_to_LFT d]
      (halfAddResidualStateAfter X Y N d 0))
    (habs : ∀ k, k < K →
      (halfAddResidualStateAfter X Y N d k).T.oracle = Tensor.EmitDecision.absorb)
    (habsX : ∀ k, k < K →
      (halfAddResidualXStateAfter X Y N d k).T.oracle = Tensor.EmitDecision.absorb) :
    SafeVMRun X Y halfAddInitState [digit_to_LFT d]
      (halfAddResidualStateAfter X Y N d K) := by
  induction K with
  | zero =>
      simpa using hreach0
  | succ K ih =>
      have hrunK : SafeVMRun X Y halfAddInitState [digit_to_LFT d]
          (halfAddResidualStateAfter X Y N d K) := by
        apply ih
        · intro k hk
          exact habs k (lt_trans hk (Nat.lt_succ_self K))
        · intro k hk
          exact habsX k (lt_trans hk (Nat.lt_succ_self K))
      have hsK : GeneralTrace.SafeAt X Y (halfAddResidualStateAfter X Y N d K) :=
        safe_end_of_safeVMRun X Y hrunK
      have hpair : SafeVMRun X Y (halfAddResidualStateAfter X Y N d K) []
          (halfAddResidualStateAfter X Y N d (K + 1)) :=
        halfAddResidual_pair_reachable X Y N d K hsK
          (habs K (Nat.lt_succ_self K))
          (habsX K (Nat.lt_succ_self K))
      exact safeVMRun_append X Y hrunK hpair

theorem halfAddResidual_prefix_absorb_or_emits_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hreach0 : SafeVMRun X Y halfAddInitState [digit_to_LFT d]
      (halfAddResidualStateAfter X Y N d 0))
    (K : ℕ) :
    (∃ s : VMState, ∃ d₂, SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂] s) ∨
      ((∀ k, k < K → (halfAddResidualStateAfter X Y N d k).T.oracle = Tensor.EmitDecision.absorb) ∧
        (∀ k, k < K → (halfAddResidualXStateAfter X Y N d k).T.oracle = Tensor.EmitDecision.absorb) ∧
        SafeVMRun X Y halfAddInitState [digit_to_LFT d]
          (halfAddResidualStateAfter X Y N d K)) := by
  induction K with
  | zero =>
      right
      refine ⟨?_, ?_, hreach0⟩
      · intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
      · intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
  | succ K ih =>
      rcases ih with hemit | ⟨habs, habsX, hreachK⟩
      · exact Or.inl hemit
      · have hsK : GeneralTrace.SafeAt X Y (halfAddResidualStateAfter X Y N d K) :=
          safe_end_of_safeVMRun X Y hreachK
        cases hstate : (halfAddResidualStateAfter X Y N d K).T.oracle with
        | neg =>
            have hEmit : (halfAddResidualStateAfter X Y N d K).T.EmitsDigit := by
              exact Or.inl hstate
            rcases vmStepXY_emit_of_emitsDigit X Y
              (s := halfAddResidualStateAfter X Y N d K) hEmit with ⟨d₂, hstep⟩
            have hsK' : GeneralTrace.SafeAt X Y { halfAddResidualStateAfter X Y N d K with
                T := (halfAddResidualStateAfter X Y N d K).T.emit d₂ } :=
              safe_step (X := X) (Y := Y) hstep hsK
            have hrun : SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
                { halfAddResidualStateAfter X Y N d K with
                    T := (halfAddResidualStateAfter X Y N d K).T.emit d₂ } :=
              safeVMRun_append X Y hreachK
                (SafeVMRun.stepSome hstep hsK hsK' (SafeVMRun.refl _ hsK'))
            exact Or.inl ⟨_, d₂, hrun⟩
        | zero =>
            have hEmit : (halfAddResidualStateAfter X Y N d K).T.EmitsDigit := by
              exact Or.inr (Or.inl hstate)
            rcases vmStepXY_emit_of_emitsDigit X Y
              (s := halfAddResidualStateAfter X Y N d K) hEmit with ⟨d₂, hstep⟩
            have hsK' : GeneralTrace.SafeAt X Y { halfAddResidualStateAfter X Y N d K with
                T := (halfAddResidualStateAfter X Y N d K).T.emit d₂ } :=
              safe_step (X := X) (Y := Y) hstep hsK
            have hrun : SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
                { halfAddResidualStateAfter X Y N d K with
                    T := (halfAddResidualStateAfter X Y N d K).T.emit d₂ } :=
              safeVMRun_append X Y hreachK
                (SafeVMRun.stepSome hstep hsK hsK' (SafeVMRun.refl _ hsK'))
            exact Or.inl ⟨_, d₂, hrun⟩
        | pos =>
            have hEmit : (halfAddResidualStateAfter X Y N d K).T.EmitsDigit := by
              exact Or.inr (Or.inr hstate)
            rcases vmStepXY_emit_of_emitsDigit X Y
              (s := halfAddResidualStateAfter X Y N d K) hEmit with ⟨d₂, hstep⟩
            have hsK' : GeneralTrace.SafeAt X Y { halfAddResidualStateAfter X Y N d K with
                T := (halfAddResidualStateAfter X Y N d K).T.emit d₂ } :=
              safe_step (X := X) (Y := Y) hstep hsK
            have hrun : SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
                { halfAddResidualStateAfter X Y N d K with
                    T := (halfAddResidualStateAfter X Y N d K).T.emit d₂ } :=
              safeVMRun_append X Y hreachK
                (SafeVMRun.stepSome hstep hsK hsK' (SafeVMRun.refl _ hsK'))
            exact Or.inl ⟨_, d₂, hrun⟩
        | absorb =>
            have hreachX : SafeVMRun X Y halfAddInitState [digit_to_LFT d]
                (halfAddResidualXStateAfter X Y N d K) :=
              halfAddResidualXStateAfter_reachable X Y N d K hreachK hstate
            cases hstateX : (halfAddResidualXStateAfter X Y N d K).T.oracle with
            | neg =>
                have hEmitX : (halfAddResidualXStateAfter X Y N d K).T.EmitsDigit := by
                  exact Or.inl hstateX
                have hsX : GeneralTrace.SafeAt X Y (halfAddResidualXStateAfter X Y N d K) :=
                  safe_end_of_safeVMRun X Y hreachX
                rcases vmStepXY_emit_of_emitsDigit X Y
                  (s := halfAddResidualXStateAfter X Y N d K) hEmitX with ⟨d₂, hstep⟩
                have hsX' : GeneralTrace.SafeAt X Y { halfAddResidualXStateAfter X Y N d K with
                    T := (halfAddResidualXStateAfter X Y N d K).T.emit d₂ } :=
                  safe_step (X := X) (Y := Y) hstep hsX
                have hrun : SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
                    { halfAddResidualXStateAfter X Y N d K with
                        T := (halfAddResidualXStateAfter X Y N d K).T.emit d₂ } :=
                  safeVMRun_append X Y hreachX
                    (SafeVMRun.stepSome hstep hsX hsX' (SafeVMRun.refl _ hsX'))
                exact Or.inl ⟨_, d₂, hrun⟩
            | zero =>
                have hEmitX : (halfAddResidualXStateAfter X Y N d K).T.EmitsDigit := by
                  exact Or.inr (Or.inl hstateX)
                have hsX : GeneralTrace.SafeAt X Y (halfAddResidualXStateAfter X Y N d K) :=
                  safe_end_of_safeVMRun X Y hreachX
                rcases vmStepXY_emit_of_emitsDigit X Y
                  (s := halfAddResidualXStateAfter X Y N d K) hEmitX with ⟨d₂, hstep⟩
                have hsX' : GeneralTrace.SafeAt X Y { halfAddResidualXStateAfter X Y N d K with
                    T := (halfAddResidualXStateAfter X Y N d K).T.emit d₂ } :=
                  safe_step (X := X) (Y := Y) hstep hsX
                have hrun : SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
                    { halfAddResidualXStateAfter X Y N d K with
                        T := (halfAddResidualXStateAfter X Y N d K).T.emit d₂ } :=
                  safeVMRun_append X Y hreachX
                    (SafeVMRun.stepSome hstep hsX hsX' (SafeVMRun.refl _ hsX'))
                exact Or.inl ⟨_, d₂, hrun⟩
            | pos =>
                have hEmitX : (halfAddResidualXStateAfter X Y N d K).T.EmitsDigit := by
                  exact Or.inr (Or.inr hstateX)
                have hsX : GeneralTrace.SafeAt X Y (halfAddResidualXStateAfter X Y N d K) :=
                  safe_end_of_safeVMRun X Y hreachX
                rcases vmStepXY_emit_of_emitsDigit X Y
                  (s := halfAddResidualXStateAfter X Y N d K) hEmitX with ⟨d₂, hstep⟩
                have hsX' : GeneralTrace.SafeAt X Y { halfAddResidualXStateAfter X Y N d K with
                    T := (halfAddResidualXStateAfter X Y N d K).T.emit d₂ } :=
                  safe_step (X := X) (Y := Y) hstep hsX
                have hrun : SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
                    { halfAddResidualXStateAfter X Y N d K with
                        T := (halfAddResidualXStateAfter X Y N d K).T.emit d₂ } :=
                  safeVMRun_append X Y hreachX
                    (SafeVMRun.stepSome hstep hsX hsX' (SafeVMRun.refl _ hsX'))
                exact Or.inl ⟨_, d₂, hrun⟩
            | absorb =>
                have hpair : SafeVMRun X Y (halfAddResidualStateAfter X Y N d K) []
                    (halfAddResidualStateAfter X Y N d (K + 1)) :=
                  halfAddResidual_pair_reachable X Y N d K hsK hstate hstateX
                have hreachSucc : SafeVMRun X Y halfAddInitState [digit_to_LFT d]
                    (halfAddResidualStateAfter X Y N d (K + 1)) :=
                  safeVMRun_append X Y hreachK hpair
                exact Or.inr ⟨
                  (fun k hk =>
                    if hkK : k < K then
                      habs k hkK
                    else
                      by
                        have hkEq : k = K := Nat.eq_of_lt_succ_of_not_lt hk hkK
                        simpa [hkEq] using hstate),
                  (fun k hk =>
                    if hkK : k < K then
                      habsX k hkK
                    else
                      by
                        have hkEq : k = K := Nat.eq_of_lt_succ_of_not_lt hk hkK
                        simpa [hkEq] using hstateX),
                  hreachSucc⟩

theorem halfAddResidual_prefix_absorb_or_emits_of_Xstep
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hreach1 : SafeVMRun X Y halfAddInitState [digit_to_LFT d]
      (halfAddResidualStateAfter X Y N d 1))
    (K : ℕ) :
    (∃ s : VMState, ∃ d₂, SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂] s) ∨
      ((∀ k, k < K → (halfAddResidualStateAfter X Y N d (k + 1)).T.oracle =
          Tensor.EmitDecision.absorb) ∧
        (∀ k, k < K → (halfAddResidualXStateAfter X Y N d (k + 1)).T.oracle =
          Tensor.EmitDecision.absorb) ∧
        SafeVMRun X Y halfAddInitState [digit_to_LFT d]
          (halfAddResidualStateAfter X Y N d (K + 1))) := by
  induction K with
  | zero =>
      right
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
      · intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
      · simpa using hreach1
  | succ K ih =>
      rcases ih with hemit | ⟨habs, habsX, hreachK1⟩
      · exact Or.inl hemit
      · have hsK1 : GeneralTrace.SafeAt X Y (halfAddResidualStateAfter X Y N d (K + 1)) :=
          safe_end_of_safeVMRun X Y hreachK1
        cases hstate : (halfAddResidualStateAfter X Y N d (K + 1)).T.oracle with
        | neg =>
            have hEmit : (halfAddResidualStateAfter X Y N d (K + 1)).T.EmitsDigit := by
              exact Or.inl hstate
            rcases vmStepXY_emit_of_emitsDigit X Y
              (s := halfAddResidualStateAfter X Y N d (K + 1)) hEmit with ⟨d₂, hstep⟩
            have hsK1' : GeneralTrace.SafeAt X Y
                { halfAddResidualStateAfter X Y N d (K + 1) with
                    T := (halfAddResidualStateAfter X Y N d (K + 1)).T.emit d₂ } :=
              safe_step (X := X) (Y := Y) hstep hsK1
            have hrun : SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
                { halfAddResidualStateAfter X Y N d (K + 1) with
                    T := (halfAddResidualStateAfter X Y N d (K + 1)).T.emit d₂ } :=
              safeVMRun_append X Y hreachK1
                (SafeVMRun.stepSome hstep hsK1 hsK1' (SafeVMRun.refl _ hsK1'))
            exact Or.inl ⟨_, d₂, hrun⟩
        | zero =>
            have hEmit : (halfAddResidualStateAfter X Y N d (K + 1)).T.EmitsDigit := by
              exact Or.inr (Or.inl hstate)
            rcases vmStepXY_emit_of_emitsDigit X Y
              (s := halfAddResidualStateAfter X Y N d (K + 1)) hEmit with ⟨d₂, hstep⟩
            have hsK1' : GeneralTrace.SafeAt X Y
                { halfAddResidualStateAfter X Y N d (K + 1) with
                    T := (halfAddResidualStateAfter X Y N d (K + 1)).T.emit d₂ } :=
              safe_step (X := X) (Y := Y) hstep hsK1
            have hrun : SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
                { halfAddResidualStateAfter X Y N d (K + 1) with
                    T := (halfAddResidualStateAfter X Y N d (K + 1)).T.emit d₂ } :=
              safeVMRun_append X Y hreachK1
                (SafeVMRun.stepSome hstep hsK1 hsK1' (SafeVMRun.refl _ hsK1'))
            exact Or.inl ⟨_, d₂, hrun⟩
        | pos =>
            have hEmit : (halfAddResidualStateAfter X Y N d (K + 1)).T.EmitsDigit := by
              exact Or.inr (Or.inr hstate)
            rcases vmStepXY_emit_of_emitsDigit X Y
              (s := halfAddResidualStateAfter X Y N d (K + 1)) hEmit with ⟨d₂, hstep⟩
            have hsK1' : GeneralTrace.SafeAt X Y
                { halfAddResidualStateAfter X Y N d (K + 1) with
                    T := (halfAddResidualStateAfter X Y N d (K + 1)).T.emit d₂ } :=
              safe_step (X := X) (Y := Y) hstep hsK1
            have hrun : SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
                { halfAddResidualStateAfter X Y N d (K + 1) with
                    T := (halfAddResidualStateAfter X Y N d (K + 1)).T.emit d₂ } :=
              safeVMRun_append X Y hreachK1
                (SafeVMRun.stepSome hstep hsK1 hsK1' (SafeVMRun.refl _ hsK1'))
            exact Or.inl ⟨_, d₂, hrun⟩
        | absorb =>
            have hreachX1 : SafeVMRun X Y halfAddInitState [digit_to_LFT d]
                (halfAddResidualXStateAfter X Y N d (K + 1)) :=
              halfAddResidualXStateAfter_reachable X Y N d (K + 1) hreachK1 hstate
            cases hstateX : (halfAddResidualXStateAfter X Y N d (K + 1)).T.oracle with
            | neg =>
                have hEmitX : (halfAddResidualXStateAfter X Y N d (K + 1)).T.EmitsDigit := by
                  exact Or.inl hstateX
                have hsX1 : GeneralTrace.SafeAt X Y
                    (halfAddResidualXStateAfter X Y N d (K + 1)) :=
                  safe_end_of_safeVMRun X Y hreachX1
                rcases vmStepXY_emit_of_emitsDigit X Y
                  (s := halfAddResidualXStateAfter X Y N d (K + 1)) hEmitX with ⟨d₂, hstep⟩
                have hsX1' : GeneralTrace.SafeAt X Y
                    { halfAddResidualXStateAfter X Y N d (K + 1) with
                        T := (halfAddResidualXStateAfter X Y N d (K + 1)).T.emit d₂ } :=
                  safe_step (X := X) (Y := Y) hstep hsX1
                have hrun : SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
                    { halfAddResidualXStateAfter X Y N d (K + 1) with
                        T := (halfAddResidualXStateAfter X Y N d (K + 1)).T.emit d₂ } :=
                  safeVMRun_append X Y hreachX1
                    (SafeVMRun.stepSome hstep hsX1 hsX1' (SafeVMRun.refl _ hsX1'))
                exact Or.inl ⟨_, d₂, hrun⟩
            | zero =>
                have hEmitX : (halfAddResidualXStateAfter X Y N d (K + 1)).T.EmitsDigit := by
                  exact Or.inr (Or.inl hstateX)
                have hsX1 : GeneralTrace.SafeAt X Y
                    (halfAddResidualXStateAfter X Y N d (K + 1)) :=
                  safe_end_of_safeVMRun X Y hreachX1
                rcases vmStepXY_emit_of_emitsDigit X Y
                  (s := halfAddResidualXStateAfter X Y N d (K + 1)) hEmitX with ⟨d₂, hstep⟩
                have hsX1' : GeneralTrace.SafeAt X Y
                    { halfAddResidualXStateAfter X Y N d (K + 1) with
                        T := (halfAddResidualXStateAfter X Y N d (K + 1)).T.emit d₂ } :=
                  safe_step (X := X) (Y := Y) hstep hsX1
                have hrun : SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
                    { halfAddResidualXStateAfter X Y N d (K + 1) with
                        T := (halfAddResidualXStateAfter X Y N d (K + 1)).T.emit d₂ } :=
                  safeVMRun_append X Y hreachX1
                    (SafeVMRun.stepSome hstep hsX1 hsX1' (SafeVMRun.refl _ hsX1'))
                exact Or.inl ⟨_, d₂, hrun⟩
            | pos =>
                have hEmitX : (halfAddResidualXStateAfter X Y N d (K + 1)).T.EmitsDigit := by
                  exact Or.inr (Or.inr hstateX)
                have hsX1 : GeneralTrace.SafeAt X Y
                    (halfAddResidualXStateAfter X Y N d (K + 1)) :=
                  safe_end_of_safeVMRun X Y hreachX1
                rcases vmStepXY_emit_of_emitsDigit X Y
                  (s := halfAddResidualXStateAfter X Y N d (K + 1)) hEmitX with ⟨d₂, hstep⟩
                have hsX1' : GeneralTrace.SafeAt X Y
                    { halfAddResidualXStateAfter X Y N d (K + 1) with
                        T := (halfAddResidualXStateAfter X Y N d (K + 1)).T.emit d₂ } :=
                  safe_step (X := X) (Y := Y) hstep hsX1
                have hrun : SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
                    { halfAddResidualXStateAfter X Y N d (K + 1) with
                        T := (halfAddResidualXStateAfter X Y N d (K + 1)).T.emit d₂ } :=
                  safeVMRun_append X Y hreachX1
                    (SafeVMRun.stepSome hstep hsX1 hsX1' (SafeVMRun.refl _ hsX1'))
                exact Or.inl ⟨_, d₂, hrun⟩
            | absorb =>
                have hpair : SafeVMRun X Y (halfAddResidualStateAfter X Y N d (K + 1)) []
                    (halfAddResidualStateAfter X Y N d (K + 2)) :=
                  halfAddResidual_pair_reachable X Y N d (K + 1) hsK1 hstate hstateX
                have hreachSucc : SafeVMRun X Y halfAddInitState [digit_to_LFT d]
                    (halfAddResidualStateAfter X Y N d (K + 2)) :=
                  safeVMRun_append X Y hreachK1 hpair
                exact Or.inr ⟨
                  (fun k hk =>
                    if hkK : k < K then
                      by simpa [Nat.add_assoc] using habs k hkK
                    else
                      by
                        have hkEq : k = K := Nat.eq_of_lt_succ_of_not_lt hk hkK
                        simpa [hkEq, Nat.add_assoc] using hstate),
                  (fun k hk =>
                    if hkK : k < K then
                      by simpa [Nat.add_assoc] using habsX k hkK
                    else
                      by
                        have hkEq : k = K := Nat.eq_of_lt_succ_of_not_lt hk hkK
                        simpa [hkEq, Nat.add_assoc] using hstateX),
                  by simpa [Nat.add_assoc] using hreachSucc⟩

theorem halfAddResidualStateAfter_reachable_emitsStep
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (hreach : SafeVMRun X Y halfAddInitState [digit_to_LFT d]
      (halfAddResidualStateAfter X Y N d K))
    (hK : (halfAddResidualStateAfter X Y N d K).T.EmitsDigit) :
    ∃ d₂,
      SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
        { halfAddResidualStateAfter X Y N d K with
            T := (halfAddResidualStateAfter X Y N d K).T.emit d₂ } := by
  have hsK : GeneralTrace.SafeAt X Y (halfAddResidualStateAfter X Y N d K) :=
    safe_end_of_safeVMRun X Y hreach
  rcases vmStepXY_emit_of_emitsDigit X Y
    (s := halfAddResidualStateAfter X Y N d K) hK with ⟨d₂, hstep⟩
  have hsK' : GeneralTrace.SafeAt X Y { halfAddResidualStateAfter X Y N d K with
      T := (halfAddResidualStateAfter X Y N d K).T.emit d₂ } :=
    safe_step (X := X) (Y := Y) hstep hsK
  exact ⟨d₂, safeVMRun_append X Y hreach
    (SafeVMRun.stepSome hstep hsK hsK' (SafeVMRun.refl _ hsK'))⟩

theorem halfAddTensor_balanced_first_emit_reaches_two_digits
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hreach : SafeVMRun X Y halfAddInitState [] (halfAddTensorStateAfter X Y N))
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      (halfAddResidualStateAfter X Y N d 0)) :
    ∃ s : VMState, ∃ d₂, SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂] s := by
  have hsN : GeneralTrace.SafeAt X Y (halfAddTensorStateAfter X Y N) :=
    safe_end_of_safeVMRun X Y hreach
  have hs0 : GeneralTrace.SafeAt X Y (halfAddResidualStateAfter X Y N d 0) :=
    safe_step (X := X) (Y := Y) hstep hsN
  have hreach0 : SafeVMRun X Y halfAddInitState [digit_to_LFT d]
      (halfAddResidualStateAfter X Y N d 0) :=
    safeVMRun_append X Y hreach
      (SafeVMRun.stepSome hstep hsN hs0 (SafeVMRun.refl _ hs0))
  rcases halfAddResidualStateAfter_productivity_spec_of_step X Y N d hstep with ⟨K, hK⟩
  rcases halfAddResidual_prefix_absorb_or_emits_of_step X Y N d hreach0 K with
    hemit | ⟨habs, habsX, hreachK⟩
  · exact hemit
  · rcases halfAddResidualStateAfter_reachable_emitsStep X Y N d K hreachK hK.emitsDigit with
      ⟨d₂, hrun⟩
    exact ⟨_, d₂, hrun⟩

theorem halfAddTensorX_emit_absorbY_reaches_residual_one
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hreach : SafeVMRun X Y halfAddInitState [] (halfAddTensorXStateAfter X Y N))
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorXStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorXStateAfter X Y N with
          T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) })
    (habs : ({ halfAddTensorXStateAfter X Y N with
        T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }).T.oracle =
          Tensor.EmitDecision.absorb) :
    SafeVMRun X Y halfAddInitState [digit_to_LFT d]
      (halfAddResidualStateAfter X Y N d 1) := by
  let s₁ : VMState := { halfAddTensorXStateAfter X Y N with
    T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }
  have hsX : GeneralTrace.SafeAt X Y (halfAddTensorXStateAfter X Y N) :=
    safe_end_of_safeVMRun X Y hreach
  have hs₁ : GeneralTrace.SafeAt X Y s₁ := by
    simpa [s₁] using safe_step (X := X) (Y := Y) hstep hsX
  have hreachEmit : SafeVMRun X Y halfAddInitState [digit_to_LFT d] s₁ := by
    simpa [s₁] using safeVMRun_append X Y hreach
      (SafeVMRun.stepSome hstep hsX hs₁ (SafeVMRun.refl _ hs₁))
  have hstepY_raw : GeneralTrace.VMStepXY X Y s₁ none
      { T := s₁.T.absorbY (Y.stream N), idx_x := s₁.idx_x, idx_y := s₁.idx_y + 1,
        absorb_x_next := true } := by
    simpa [s₁, halfAddTensorXStateAfter] using
      (GeneralTrace.VMStepXY.absorbY (X := X) (Y := Y) (s := s₁) habs rfl)
  have hTEq : s₁.T.absorbY (Y.stream N) = (halfAddResidualStateAfter X Y N d 1).T := by
    simpa [s₁] using (halfAddResidualStateAfter_one_eq_from_Xstep X Y N d).symm
  have hstateEq :
      { T := s₁.T.absorbY (Y.stream N), idx_x := s₁.idx_x, idx_y := s₁.idx_y + 1,
        absorb_x_next := true } = halfAddResidualStateAfter X Y N d 1 := by
    simp [s₁, halfAddTensorXStateAfter, halfAddResidualStateAfter, Tensor.absorbBoth_n]
    simpa [halfAddResidualStateAfter, Tensor.absorbBoth_n] using hTEq
  have hstepY : GeneralTrace.VMStepXY X Y s₁ none (halfAddResidualStateAfter X Y N d 1) := by
    simpa [hstateEq] using hstepY_raw
  have hs1 : GeneralTrace.SafeAt X Y (halfAddResidualStateAfter X Y N d 1) :=
    safe_step (X := X) (Y := Y) hstepY hs₁
  exact safeVMRun_append X Y hreachEmit
    (SafeVMRun.stepNone hstepY hs₁ hs1 (SafeVMRun.refl _ hs1))

theorem halfAddTensorX_first_emit_reaches_two_digits
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hreach : SafeVMRun X Y halfAddInitState [] (halfAddTensorXStateAfter X Y N))
    (hstep : GeneralTrace.VMStepXY X Y
      (halfAddTensorXStateAfter X Y N)
      (some (digit_to_LFT d))
      { halfAddTensorXStateAfter X Y N with
          T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∃ s : VMState, ∃ d₂, SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂] s := by
  let s₁ : VMState := { halfAddTensorXStateAfter X Y N with
    T := (halfAddTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }
  have hsX : GeneralTrace.SafeAt X Y (halfAddTensorXStateAfter X Y N) :=
    safe_end_of_safeVMRun X Y hreach
  have hs₁ : GeneralTrace.SafeAt X Y s₁ := by
    simpa [s₁] using safe_step (X := X) (Y := Y) hstep hsX
  have hreachEmit : SafeVMRun X Y halfAddInitState [digit_to_LFT d] s₁ := by
    simpa [s₁] using safeVMRun_append X Y hreach
      (SafeVMRun.stepSome hstep hsX hs₁ (SafeVMRun.refl _ hs₁))
  cases hstate : s₁.T.oracle with
  | neg =>
      have hEmit : s₁.T.EmitsDigit := by
        exact Or.inl hstate
      rcases vmStepXY_emit_of_emitsDigit X Y (s := s₁) hEmit with ⟨d₂, hstep₂⟩
      have hs₂ : GeneralTrace.SafeAt X Y { s₁ with T := s₁.T.emit d₂ } :=
        safe_step (X := X) (Y := Y) hstep₂ hs₁
      have hrun : SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
          { s₁ with T := s₁.T.emit d₂ } :=
        safeVMRun_append X Y hreachEmit
          (SafeVMRun.stepSome hstep₂ hs₁ hs₂ (SafeVMRun.refl _ hs₂))
      exact ⟨_, d₂, hrun⟩
  | zero =>
      have hEmit : s₁.T.EmitsDigit := by
        exact Or.inr (Or.inl hstate)
      rcases vmStepXY_emit_of_emitsDigit X Y (s := s₁) hEmit with ⟨d₂, hstep₂⟩
      have hs₂ : GeneralTrace.SafeAt X Y { s₁ with T := s₁.T.emit d₂ } :=
        safe_step (X := X) (Y := Y) hstep₂ hs₁
      have hrun : SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
          { s₁ with T := s₁.T.emit d₂ } :=
        safeVMRun_append X Y hreachEmit
          (SafeVMRun.stepSome hstep₂ hs₁ hs₂ (SafeVMRun.refl _ hs₂))
      exact ⟨_, d₂, hrun⟩
  | pos =>
      have hEmit : s₁.T.EmitsDigit := by
        exact Or.inr (Or.inr hstate)
      rcases vmStepXY_emit_of_emitsDigit X Y (s := s₁) hEmit with ⟨d₂, hstep₂⟩
      have hs₂ : GeneralTrace.SafeAt X Y { s₁ with T := s₁.T.emit d₂ } :=
        safe_step (X := X) (Y := Y) hstep₂ hs₁
      have hrun : SafeVMRun X Y halfAddInitState [digit_to_LFT d, d₂]
          { s₁ with T := s₁.T.emit d₂ } :=
        safeVMRun_append X Y hreachEmit
          (SafeVMRun.stepSome hstep₂ hs₁ hs₂ (SafeVMRun.refl _ hs₂))
      exact ⟨_, d₂, hrun⟩
  | absorb =>
      have hreach1 : SafeVMRun X Y halfAddInitState [digit_to_LFT d]
          (halfAddResidualStateAfter X Y N d 1) :=
        halfAddTensorX_emit_absorbY_reaches_residual_one X Y N d hreach hstep hstate
      rcases halfAddResidualStateAfter_productivity_spec_of_Xstep X Y N d hstep with ⟨K, hK⟩
      rcases halfAddResidual_prefix_absorb_or_emits_of_Xstep X Y N d hreach1 K with
        hemit | ⟨habs, habsX, hreachK1⟩
      · exact hemit
      · have hreachK : SafeVMRun X Y halfAddInitState [digit_to_LFT d]
            (halfAddResidualStateAfter X Y N d (K + 1)) := by
          simpa [Nat.add_comm] using hreachK1
        rcases halfAddResidualStateAfter_reachable_emitsStep X Y N d (K + 1)
          hreachK hK.emitsDigit with ⟨d₂, hrun⟩
        exact ⟨_, d₂, hrun⟩

theorem halfAddTensor_pair_reachable
    (X Y : MobiusReal) (N : ℕ)
    (hs : GeneralTrace.SafeAt X Y (halfAddTensorStateAfter X Y N))
    (habs : (halfAddTensorStateAfter X Y N).T.oracle = Tensor.EmitDecision.absorb)
    (habsX : (halfAddTensorXStateAfter X Y N).T.oracle = Tensor.EmitDecision.absorb) :
    SafeVMRun X Y (halfAddTensorStateAfter X Y N) [] (halfAddTensorStateAfter X Y (N + 1)) := by
  have hstepX : GeneralTrace.VMStepXY X Y (halfAddTensorStateAfter X Y N) none
      (halfAddTensorXStateAfter X Y N) :=
    halfAddTensorStateAfter_absorbX_step X Y N habs
  have hsX : GeneralTrace.SafeAt X Y (halfAddTensorXStateAfter X Y N) :=
    safe_step (X := X) (Y := Y) hstepX hs
  have hstepY : GeneralTrace.VMStepXY X Y (halfAddTensorXStateAfter X Y N) none
      (halfAddTensorStateAfter X Y (N + 1)) :=
    halfAddTensorXStateAfter_absorbY_step X Y N habsX
  have hsY : GeneralTrace.SafeAt X Y (halfAddTensorStateAfter X Y (N + 1)) :=
    safe_step (X := X) (Y := Y) hstepY hsX
  exact SafeVMRun.stepNone hstepX hs hsX <|
    SafeVMRun.stepNone hstepY hsX hsY <|
      SafeVMRun.refl _ hsY

theorem halfAddTensorXStateAfter_reachable
    (X Y : MobiusReal) (N : ℕ)
    (hreach : SafeVMRun X Y halfAddInitState [] (halfAddTensorStateAfter X Y N))
    (habs : (halfAddTensorStateAfter X Y N).T.oracle = Tensor.EmitDecision.absorb) :
    SafeVMRun X Y halfAddInitState [] (halfAddTensorXStateAfter X Y N) := by
  have hsN : GeneralTrace.SafeAt X Y (halfAddTensorStateAfter X Y N) :=
    safe_end_of_safeVMRun X Y hreach
  have hstepX : GeneralTrace.VMStepXY X Y (halfAddTensorStateAfter X Y N) none
      (halfAddTensorXStateAfter X Y N) :=
    halfAddTensorStateAfter_absorbX_step X Y N habs
  have hsX : GeneralTrace.SafeAt X Y (halfAddTensorXStateAfter X Y N) :=
    safe_step (X := X) (Y := Y) hstepX hsN
  exact safeVMRun_append X Y hreach
    (SafeVMRun.stepNone hstepX hsN hsX (SafeVMRun.refl _ hsX))

theorem halfAddTensorStateAfter_reachable
    (X Y : MobiusReal) (N : ℕ)
    (habs : ∀ k, k < N →
      (halfAddTensorStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb)
    (habsX : ∀ k, k < N →
      (halfAddTensorXStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb) :
    SafeVMRun X Y halfAddInitState [] (halfAddTensorStateAfter X Y N) := by
  induction N with
  | zero =>
      simpa [halfAddInitState, halfAddTensorStateAfter] using
        (SafeVMRun.refl (X := X) (Y := Y) halfAddInitState (halfAddInit_safe X Y))
  | succ N ih =>
      have hrunN : SafeVMRun X Y halfAddInitState [] (halfAddTensorStateAfter X Y N) := by
        apply ih
        · intro k hk
          exact habs k (lt_trans hk (Nat.lt_succ_self N))
        · intro k hk
          exact habsX k (lt_trans hk (Nat.lt_succ_self N))
      have hsN : GeneralTrace.SafeAt X Y (halfAddTensorStateAfter X Y N) :=
        safe_end_of_safeVMRun X Y hrunN
      have hpair : SafeVMRun X Y (halfAddTensorStateAfter X Y N) []
          (halfAddTensorStateAfter X Y (N + 1)) :=
        halfAddTensor_pair_reachable X Y N hsN
          (habs N (Nat.lt_succ_self N))
          (habsX N (Nat.lt_succ_self N))
      exact safeVMRun_append_nil X Y hrunN hpair

theorem halfAddTensorStateAfter_emitsDigit_of_nonneg
    (X Y : MobiusReal) (N : ℕ)
    (hnonneg :
      0 ≤ Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 1 ∧
      0 ≤ Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 (-1) ∧
      0 ≤ Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) 1 ∧
      0 ≤ Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) (-1)) :
    (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).EmitsDigit := by
  let T := Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N
  let n1 : ℤ := T.a + T.b + T.c + T.d
  let d1 : ℤ := T.e + T.f + T.g + T.h
  let n2 : ℤ := -T.a + T.b - T.c + T.d
  let d2 : ℤ := -T.e + T.f - T.g + T.h
  let n3 : ℤ := -T.a - T.b + T.c + T.d
  let d3 : ℤ := -T.e - T.f + T.g + T.h
  let n4 : ℤ := T.a - T.b - T.c + T.d
  let d4 : ℤ := T.e - T.f - T.g + T.h
  have hnp : Tensor.hasNoPole d1 d2 d3 d4 = true := by
    simpa [T, d1, d2, d3, d4] using halfAddTensorStateAfter_hasNoPole_bool X Y N
  have hnp' :
      Tensor.hasNoPole
        (T.e + T.f + T.g + T.h)
        (-T.e + T.f - T.g + T.h)
        (-T.e - T.f + T.g + T.h)
        (T.e - T.f - T.g + T.h) = true := by
    simpa [d1, d2, d3, d4] using hnp
  rcases halfAddTensorStateAfter_corner_mem_baseI X Y N with ⟨hr1, hr2, hr3, hr4⟩
  rcases hnonneg with ⟨hr1lo, hr2lo, hr3lo, hr4lo⟩
  have hratio1 : Tensor.apply T 1 1 = (n1 : ℝ) / d1 := by
    simpa [T, n1, d1] using halfAddTensorStateAfter_corner_ratio_11 X Y N
  have hratio2 : Tensor.apply T 1 (-1) = (n2 : ℝ) / d2 := by
    simpa [T, n2, d2] using halfAddTensorStateAfter_corner_ratio_1m X Y N
  have hratio3 : Tensor.apply T (-1) 1 = (n3 : ℝ) / d3 := by
    simpa [T, n3, d3] using halfAddTensorStateAfter_corner_ratio_m1 X Y N
  have hratio4 : Tensor.apply T (-1) (-1) = (n4 : ℝ) / d4 := by
    simpa [T, n4, d4] using halfAddTensorStateAfter_corner_ratio_mm X Y N
  rcases halfAddTensorStateAfter_corner_denom_sign_cases X Y N with hden | hden
  · have h1 : Tensor.inDigitPos n1 d1 = true := by
      apply Tensor.inDigitPos_of_ratio_pos n1 d1 hden.1
      · simpa [T, hratio1] using hr1lo
      · simpa [T, hratio1] using hr1.2
    have h2 : Tensor.inDigitPos n2 d2 = true := by
      apply Tensor.inDigitPos_of_ratio_pos n2 d2 hden.2.1
      · simpa [T, hratio2] using hr2lo
      · simpa [T, hratio2] using hr2.2
    have h3 : Tensor.inDigitPos n3 d3 = true := by
      apply Tensor.inDigitPos_of_ratio_pos n3 d3 hden.2.2.1
      · simpa [T, hratio3] using hr3lo
      · simpa [T, hratio3] using hr3.2
    have h4 : Tensor.inDigitPos n4 d4 = true := by
      apply Tensor.inDigitPos_of_ratio_pos n4 d4 hden.2.2.2
      · simpa [T, hratio4] using hr4lo
      · simpa [T, hratio4] using hr4.2
    have h1' : Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    have hposAll :
        ((Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      exact ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    by_cases hnegAll :
        ((Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
    · left
      simp [Tensor.cornerValues, hnp', hnegAll]
    · by_cases hzeroAll :
          ((Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
              Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
            Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
          Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
      · right
        left
        simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll]
      · right
        right
        simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll, hposAll]
  · have h1 : Tensor.inDigitPos n1 d1 = true := by
      apply Tensor.inDigitPos_of_ratio_neg n1 d1 hden.1
      · simpa [T, hratio1] using hr1lo
      · simpa [T, hratio1] using hr1.2
    have h2 : Tensor.inDigitPos n2 d2 = true := by
      apply Tensor.inDigitPos_of_ratio_neg n2 d2 hden.2.1
      · simpa [T, hratio2] using hr2lo
      · simpa [T, hratio2] using hr2.2
    have h3 : Tensor.inDigitPos n3 d3 = true := by
      apply Tensor.inDigitPos_of_ratio_neg n3 d3 hden.2.2.1
      · simpa [T, hratio3] using hr3lo
      · simpa [T, hratio3] using hr3.2
    have h4 : Tensor.inDigitPos n4 d4 = true := by
      apply Tensor.inDigitPos_of_ratio_neg n4 d4 hden.2.2.2
      · simpa [T, hratio4] using hr4lo
      · simpa [T, hratio4] using hr4.2
    have h1' : Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    have hposAll :
        ((Tensor.inDigitPos (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitPos (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitPos (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitPos (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      exact ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    by_cases hnegAll :
        ((Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
    · left
      simp [Tensor.cornerValues, hnp', hnegAll]
    · by_cases hzeroAll :
          ((Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
              Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
            Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
          Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
      · right
        left
        simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll]
      · right
        right
        simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll, hposAll]

theorem halfAddTensorStateAfter_emitsDigit_of_nonpos
    (X Y : MobiusReal) (N : ℕ)
    (hnonpos :
      Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 1 ≤ 0 ∧
      Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 (-1) ≤ 0 ∧
      Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) 1 ≤ 0 ∧
      Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) (-1) ≤ 0) :
    (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).EmitsDigit := by
  let T := Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N
  let n1 : ℤ := T.a + T.b + T.c + T.d
  let d1 : ℤ := T.e + T.f + T.g + T.h
  let n2 : ℤ := -T.a + T.b - T.c + T.d
  let d2 : ℤ := -T.e + T.f - T.g + T.h
  let n3 : ℤ := -T.a - T.b + T.c + T.d
  let d3 : ℤ := -T.e - T.f + T.g + T.h
  let n4 : ℤ := T.a - T.b - T.c + T.d
  let d4 : ℤ := T.e - T.f - T.g + T.h
  have hnp : Tensor.hasNoPole d1 d2 d3 d4 = true := by
    simpa [T, d1, d2, d3, d4] using halfAddTensorStateAfter_hasNoPole_bool X Y N
  have hnp' :
      Tensor.hasNoPole
        (T.e + T.f + T.g + T.h)
        (-T.e + T.f - T.g + T.h)
        (-T.e - T.f + T.g + T.h)
        (T.e - T.f - T.g + T.h) = true := by
    simpa [d1, d2, d3, d4] using hnp
  rcases halfAddTensorStateAfter_corner_mem_baseI X Y N with ⟨hr1, hr2, hr3, hr4⟩
  rcases hnonpos with ⟨hr1hi, hr2hi, hr3hi, hr4hi⟩
  have hratio1 : Tensor.apply T 1 1 = (n1 : ℝ) / d1 := by
    simpa [T, n1, d1] using halfAddTensorStateAfter_corner_ratio_11 X Y N
  have hratio2 : Tensor.apply T 1 (-1) = (n2 : ℝ) / d2 := by
    simpa [T, n2, d2] using halfAddTensorStateAfter_corner_ratio_1m X Y N
  have hratio3 : Tensor.apply T (-1) 1 = (n3 : ℝ) / d3 := by
    simpa [T, n3, d3] using halfAddTensorStateAfter_corner_ratio_m1 X Y N
  have hratio4 : Tensor.apply T (-1) (-1) = (n4 : ℝ) / d4 := by
    simpa [T, n4, d4] using halfAddTensorStateAfter_corner_ratio_mm X Y N
  rcases halfAddTensorStateAfter_corner_denom_sign_cases X Y N with hden | hden
  · have h1 : Tensor.inDigitNeg n1 d1 = true := by
      apply Tensor.inDigitNeg_of_ratio_pos n1 d1 hden.1
      · simpa [T, hratio1] using hr1.1
      · simpa [T, hratio1] using hr1hi
    have h2 : Tensor.inDigitNeg n2 d2 = true := by
      apply Tensor.inDigitNeg_of_ratio_pos n2 d2 hden.2.1
      · simpa [T, hratio2] using hr2.1
      · simpa [T, hratio2] using hr2hi
    have h3 : Tensor.inDigitNeg n3 d3 = true := by
      apply Tensor.inDigitNeg_of_ratio_pos n3 d3 hden.2.2.1
      · simpa [T, hratio3] using hr3.1
      · simpa [T, hratio3] using hr3hi
    have h4 : Tensor.inDigitNeg n4 d4 = true := by
      apply Tensor.inDigitNeg_of_ratio_pos n4 d4 hden.2.2.2
      · simpa [T, hratio4] using hr4.1
      · simpa [T, hratio4] using hr4hi
    have h1' : Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    simp [Tensor.cornerValues, hnp', h1', h2', h3', h4']
  · have h1 : Tensor.inDigitNeg n1 d1 = true := by
      apply Tensor.inDigitNeg_of_ratio_neg n1 d1 hden.1
      · simpa [T, hratio1] using hr1.1
      · simpa [T, hratio1] using hr1hi
    have h2 : Tensor.inDigitNeg n2 d2 = true := by
      apply Tensor.inDigitNeg_of_ratio_neg n2 d2 hden.2.1
      · simpa [T, hratio2] using hr2.1
      · simpa [T, hratio2] using hr2hi
    have h3 : Tensor.inDigitNeg n3 d3 = true := by
      apply Tensor.inDigitNeg_of_ratio_neg n3 d3 hden.2.2.1
      · simpa [T, hratio3] using hr3.1
      · simpa [T, hratio3] using hr3hi
    have h4 : Tensor.inDigitNeg n4 d4 = true := by
      apply Tensor.inDigitNeg_of_ratio_neg n4 d4 hden.2.2.2
      · simpa [T, hratio4] using hr4.1
      · simpa [T, hratio4] using hr4hi
    have h1' : Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    simp [Tensor.cornerValues, hnp', h1', h2', h3', h4']

theorem halfAddTensorStateAfter_emitsDigit_of_mid
    (X Y : MobiusReal) (N : ℕ)
    (hmid :
      (-1 / 2 : ℝ) ≤ Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 1 ∧
        Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 1 ≤ (1 / 2 : ℝ) ∧
        (-1 / 2 : ℝ) ≤ Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 (-1) ∧
        Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) 1 (-1) ≤ (1 / 2 : ℝ) ∧
        (-1 / 2 : ℝ) ≤ Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) 1 ∧
        Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) 1 ≤ (1 / 2 : ℝ) ∧
        (-1 / 2 : ℝ) ≤ Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) (-1) ∧
        Tensor.apply (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N) (-1) (-1) ≤ (1 / 2 : ℝ)) :
    (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).EmitsDigit := by
  let T := Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N
  let n1 : ℤ := T.a + T.b + T.c + T.d
  let d1 : ℤ := T.e + T.f + T.g + T.h
  let n2 : ℤ := -T.a + T.b - T.c + T.d
  let d2 : ℤ := -T.e + T.f - T.g + T.h
  let n3 : ℤ := -T.a - T.b + T.c + T.d
  let d3 : ℤ := -T.e - T.f + T.g + T.h
  let n4 : ℤ := T.a - T.b - T.c + T.d
  let d4 : ℤ := T.e - T.f - T.g + T.h
  have hnp : Tensor.hasNoPole d1 d2 d3 d4 = true := by
    simpa [T, d1, d2, d3, d4] using halfAddTensorStateAfter_hasNoPole_bool X Y N
  have hnp' :
      Tensor.hasNoPole
        (T.e + T.f + T.g + T.h)
        (-T.e + T.f - T.g + T.h)
        (-T.e - T.f + T.g + T.h)
        (T.e - T.f - T.g + T.h) = true := by
    simpa [d1, d2, d3, d4] using hnp
  rcases hmid with ⟨hr1lo, hr1hi, hr2lo, hr2hi, hr3lo, hr3hi, hr4lo, hr4hi⟩
  have hratio1 : Tensor.apply T 1 1 = (n1 : ℝ) / d1 := by
    simpa [T, n1, d1] using halfAddTensorStateAfter_corner_ratio_11 X Y N
  have hratio2 : Tensor.apply T 1 (-1) = (n2 : ℝ) / d2 := by
    simpa [T, n2, d2] using halfAddTensorStateAfter_corner_ratio_1m X Y N
  have hratio3 : Tensor.apply T (-1) 1 = (n3 : ℝ) / d3 := by
    simpa [T, n3, d3] using halfAddTensorStateAfter_corner_ratio_m1 X Y N
  have hratio4 : Tensor.apply T (-1) (-1) = (n4 : ℝ) / d4 := by
    simpa [T, n4, d4] using halfAddTensorStateAfter_corner_ratio_mm X Y N
  have hr1lo' : (-(1 / 2 : ℝ)) ≤ (n1 : ℝ) / d1 := by
    have hsrc : (-((2 : ℝ)⁻¹)) ≤ Tensor.apply T 1 1 := by
      have : (-(1 / 2 : ℝ)) ≤ Tensor.apply T 1 1 := by
        have h : ((-1 : ℝ) / 2) ≤ Tensor.apply T 1 1 := by
          dsimp [T]
          exact hr1lo
        nlinarith
      norm_num at this ⊢
      exact this
    have htmp : (-((2 : ℝ)⁻¹)) ≤ (n1 : ℝ) / d1 := by
      rw [← hratio1]
      exact hsrc
    norm_num at htmp ⊢
    exact htmp
  have hr1hi' : (n1 : ℝ) / d1 ≤ (1 / 2 : ℝ) := by
    rw [← hratio1]
    simpa [T] using hr1hi
  have hr2lo' : (-(1 / 2 : ℝ)) ≤ (n2 : ℝ) / d2 := by
    have hsrc : (-((2 : ℝ)⁻¹)) ≤ Tensor.apply T 1 (-1) := by
      have : (-(1 / 2 : ℝ)) ≤ Tensor.apply T 1 (-1) := by
        have h : ((-1 : ℝ) / 2) ≤ Tensor.apply T 1 (-1) := by
          dsimp [T]
          exact hr2lo
        nlinarith
      norm_num at this ⊢
      exact this
    have htmp : (-((2 : ℝ)⁻¹)) ≤ (n2 : ℝ) / d2 := by
      rw [← hratio2]
      exact hsrc
    norm_num at htmp ⊢
    exact htmp
  have hr2hi' : (n2 : ℝ) / d2 ≤ (1 / 2 : ℝ) := by
    rw [← hratio2]
    simpa [T] using hr2hi
  have hr3lo' : (-(1 / 2 : ℝ)) ≤ (n3 : ℝ) / d3 := by
    have hsrc : (-((2 : ℝ)⁻¹)) ≤ Tensor.apply T (-1) 1 := by
      have : (-(1 / 2 : ℝ)) ≤ Tensor.apply T (-1) 1 := by
        have h : ((-1 : ℝ) / 2) ≤ Tensor.apply T (-1) 1 := by
          dsimp [T]
          exact hr3lo
        nlinarith
      norm_num at this ⊢
      exact this
    have htmp : (-((2 : ℝ)⁻¹)) ≤ (n3 : ℝ) / d3 := by
      rw [← hratio3]
      exact hsrc
    norm_num at htmp ⊢
    exact htmp
  have hr3hi' : (n3 : ℝ) / d3 ≤ (1 / 2 : ℝ) := by
    rw [← hratio3]
    simpa [T] using hr3hi
  have hr4lo' : (-(1 / 2 : ℝ)) ≤ (n4 : ℝ) / d4 := by
    have hsrc : (-((2 : ℝ)⁻¹)) ≤ Tensor.apply T (-1) (-1) := by
      have : (-(1 / 2 : ℝ)) ≤ Tensor.apply T (-1) (-1) := by
        have h : ((-1 : ℝ) / 2) ≤ Tensor.apply T (-1) (-1) := by
          dsimp [T]
          exact hr4lo
        nlinarith
      norm_num at this ⊢
      exact this
    have htmp : (-((2 : ℝ)⁻¹)) ≤ (n4 : ℝ) / d4 := by
      rw [← hratio4]
      exact hsrc
    norm_num at htmp ⊢
    exact htmp
  have hr4hi' : (n4 : ℝ) / d4 ≤ (1 / 2 : ℝ) := by
    rw [← hratio4]
    simpa [T] using hr4hi
  rcases halfAddTensorStateAfter_corner_denom_sign_cases X Y N with hden | hden
  · have h1 : Tensor.inDigitZero n1 d1 = true := by
      apply Tensor.inDigitZero_of_ratio_pos n1 d1 hden.1
      · exact hr1lo'
      · exact hr1hi'
    have h2 : Tensor.inDigitZero n2 d2 = true := by
      apply Tensor.inDigitZero_of_ratio_pos n2 d2 hden.2.1
      · exact hr2lo'
      · exact hr2hi'
    have h3 : Tensor.inDigitZero n3 d3 = true := by
      apply Tensor.inDigitZero_of_ratio_pos n3 d3 hden.2.2.1
      · exact hr3lo'
      · exact hr3hi'
    have h4 : Tensor.inDigitZero n4 d4 = true := by
      apply Tensor.inDigitZero_of_ratio_pos n4 d4 hden.2.2.2
      · exact hr4lo'
      · exact hr4hi'
    have h1' : Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    have hzeroAll :
        ((Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      exact ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    by_cases hnegAll :
        ((Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
    · left
      simp [Tensor.cornerValues, hnp', hnegAll]
    · right
      left
      simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll]
  · have h1 : Tensor.inDigitZero n1 d1 = true := by
      apply Tensor.inDigitZero_of_ratio_neg n1 d1 hden.1
      · exact hr1lo'
      · exact hr1hi'
    have h2 : Tensor.inDigitZero n2 d2 = true := by
      apply Tensor.inDigitZero_of_ratio_neg n2 d2 hden.2.1
      · exact hr2lo'
      · exact hr2hi'
    have h3 : Tensor.inDigitZero n3 d3 = true := by
      apply Tensor.inDigitZero_of_ratio_neg n3 d3 hden.2.2.1
      · exact hr3lo'
      · exact hr3hi'
    have h4 : Tensor.inDigitZero n4 d4 = true := by
      apply Tensor.inDigitZero_of_ratio_neg n4 d4 hden.2.2.2
      · exact hr4lo'
      · exact hr4hi'
    have h1' : Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true := by
      simpa [n1, d1] using h1
    have h2' : Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true := by
      simpa [n2, d2] using h2
    have h3' : Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true := by
      simpa [n3, d3] using h3
    have h4' : Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      simpa [n4, d4] using h4
    have hzeroAll :
        ((Tensor.inDigitZero (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitZero (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitZero (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitZero (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true := by
      exact ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩
    change T.oracle = Tensor.EmitDecision.neg ∨
      T.oracle = Tensor.EmitDecision.zero ∨
      T.oracle = Tensor.EmitDecision.pos
    unfold Tensor.oracle
    by_cases hnegAll :
        ((Tensor.inDigitNeg (T.a + T.b + T.c + T.d) (T.e + T.f + T.g + T.h) = true ∧
            Tensor.inDigitNeg (-T.a + T.b - T.c + T.d) (-T.e + T.f - T.g + T.h) = true) ∧
          Tensor.inDigitNeg (-T.a - T.b + T.c + T.d) (-T.e - T.f + T.g + T.h) = true) ∧
        Tensor.inDigitNeg (T.a - T.b - T.c + T.d) (T.e - T.f - T.g + T.h) = true
    · left
      simp [Tensor.cornerValues, hnp', hnegAll]
    · right
      left
      simp [Tensor.cornerValues, hnp', hnegAll, hzeroAll]

theorem halfAddTensorStateAfter_emitsDigit_eventually (X Y : MobiusReal) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).EmitsDigit := by
  rcases halfAddTensorStateAfter_corner_digit_trichotomy_eventually X Y with ⟨N0, hN0⟩
  refine ⟨N0, ?_⟩
  intro N hN
  rcases hN0 N hN with hpos | hneg | hmid
  · exact halfAddTensorStateAfter_emitsDigit_of_nonneg X Y N hpos
  · exact halfAddTensorStateAfter_emitsDigit_of_nonpos X Y N hneg
  · exact halfAddTensorStateAfter_emitsDigit_of_mid X Y N hmid

theorem halfAddTensor_productivity_spec (X Y : MobiusReal) :
    ∃ N : ℕ, (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).ProductiveOnBase := by
  rcases halfAddTensorStateAfter_safeEventually X Y with ⟨Nsafe, hsafe⟩
  rcases halfAddTensorStateAfter_emitsDigit_eventually X Y with ⟨Nemit, hemit⟩
  refine ⟨max Nsafe Nemit, ?_⟩
  refine ⟨(hsafe (max Nsafe Nemit) (Nat.le_max_left _ _)).1,
    (hsafe (max Nsafe Nemit) (Nat.le_max_left _ _)).2, ?_⟩
  exact hemit (max Nsafe Nemit) (Nat.le_max_right _ _)

theorem halfAddTensor_eventually_emitsDigit (X Y : MobiusReal) :
    ∃ N : ℕ, (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).EmitsDigit := by
  rcases halfAddTensor_productivity_spec X Y with ⟨N, hN⟩
  exact ⟨N, hN.emitsDigit⟩

/--
Compatibility alias for the old axiom-backed name.
For `halfAddTensor`, this now follows from the proved productivity theorem above.
-/
theorem halfAddTensor_productivity_spec_axiom (X Y : MobiusReal) :
    ∃ N : ℕ, (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).ProductiveOnBase :=
  halfAddTensor_productivity_spec X Y

/--
Compatibility alias for the old axiom-backed name.
-/
theorem halfAddTensor_eventually_emitsDigit_axiom (X Y : MobiusReal) :
    ∃ N : ℕ, (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).EmitsDigit := by
  exact halfAddTensor_eventually_emitsDigit X Y

/--
Existence of an emitting absorbed state; this is not a reachability theorem.
-/
theorem halfAddTensor_productiveState_emitsStep (X Y : MobiusReal) :
    ∃ N d,
      VMStep (halfAddTensorStateAfter X Y N) (some d)
        { halfAddTensorStateAfter X Y N with
            T := (halfAddTensorStateAfter X Y N).T.emit d } := by
  rcases halfAddTensor_eventually_emitsDigit X Y with ⟨N, hN⟩
  exact ⟨N, (vmStep_emit_of_emitsDigit (s := halfAddTensorStateAfter X Y N) hN).choose,
    (vmStep_emit_of_emitsDigit (s := halfAddTensorStateAfter X Y N) hN).choose_spec⟩

/--
Compatibility alias for the old axiom-backed name.
-/
theorem halfAddTensor_productiveState_emitsStep_axiom (X Y : MobiusReal) :
    ∃ N d,
      VMStep (halfAddTensorStateAfter X Y N) (some d)
        { halfAddTensorStateAfter X Y N with
            T := (halfAddTensorStateAfter X Y N).T.emit d } := by
  exact halfAddTensor_productiveState_emitsStep X Y

theorem halfAddTensor_prefix_absorb_or_emits
    (X Y : MobiusReal) (N : ℕ) :
    (∃ s : VMState, ∃ d, SafeVMRun X Y halfAddInitState [d] s) ∨
      ((∀ k, k < N → (halfAddTensorStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb) ∧
        (∀ k, k < N → (halfAddTensorXStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb) ∧
        SafeVMRun X Y halfAddInitState [] (halfAddTensorStateAfter X Y N)) := by
  induction N with
  | zero =>
      right
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
      · intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
      · simpa [halfAddInitState, halfAddTensorStateAfter] using
          (SafeVMRun.refl (X := X) (Y := Y) halfAddInitState (halfAddInit_safe X Y))
  | succ N ih =>
      rcases ih with hemit | ⟨habs, habsX, hreachN⟩
      · exact Or.inl hemit
      · have hsN : GeneralTrace.SafeAt X Y (halfAddTensorStateAfter X Y N) :=
          safe_end_of_safeVMRun X Y hreachN
        cases hstate : (halfAddTensorStateAfter X Y N).T.oracle with
        | neg =>
            have hEmit : (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).EmitsDigit := by
              exact Or.inl hstate
            rcases vmStepXY_emit_of_emitsDigit X Y (s := halfAddTensorStateAfter X Y N) hEmit with
              ⟨d, hstep⟩
            have hsN' : GeneralTrace.SafeAt X Y { halfAddTensorStateAfter X Y N with
                T := (halfAddTensorStateAfter X Y N).T.emit d } :=
              safe_step (X := X) (Y := Y) hstep hsN
            have hrun : SafeVMRun X Y halfAddInitState [d]
                { halfAddTensorStateAfter X Y N with
                    T := (halfAddTensorStateAfter X Y N).T.emit d } :=
              safeVMRun_append X Y hreachN
                (SafeVMRun.stepSome hstep hsN hsN' (SafeVMRun.refl _ hsN'))
            exact Or.inl ⟨_, d, hrun⟩
        | zero =>
            have hEmit : (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).EmitsDigit := by
              exact Or.inr (Or.inl hstate)
            rcases vmStepXY_emit_of_emitsDigit X Y (s := halfAddTensorStateAfter X Y N) hEmit with
              ⟨d, hstep⟩
            have hsN' : GeneralTrace.SafeAt X Y { halfAddTensorStateAfter X Y N with
                T := (halfAddTensorStateAfter X Y N).T.emit d } :=
              safe_step (X := X) (Y := Y) hstep hsN
            have hrun : SafeVMRun X Y halfAddInitState [d]
                { halfAddTensorStateAfter X Y N with
                    T := (halfAddTensorStateAfter X Y N).T.emit d } :=
              safeVMRun_append X Y hreachN
                (SafeVMRun.stepSome hstep hsN hsN' (SafeVMRun.refl _ hsN'))
            exact Or.inl ⟨_, d, hrun⟩
        | pos =>
            have hEmit : (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).EmitsDigit := by
              exact Or.inr (Or.inr hstate)
            rcases vmStepXY_emit_of_emitsDigit X Y (s := halfAddTensorStateAfter X Y N) hEmit with
              ⟨d, hstep⟩
            have hsN' : GeneralTrace.SafeAt X Y { halfAddTensorStateAfter X Y N with
                T := (halfAddTensorStateAfter X Y N).T.emit d } :=
              safe_step (X := X) (Y := Y) hstep hsN
            have hrun : SafeVMRun X Y halfAddInitState [d]
                { halfAddTensorStateAfter X Y N with
                    T := (halfAddTensorStateAfter X Y N).T.emit d } :=
              safeVMRun_append X Y hreachN
                (SafeVMRun.stepSome hstep hsN hsN' (SafeVMRun.refl _ hsN'))
            exact Or.inl ⟨_, d, hrun⟩
        | absorb =>
            have hreachX : SafeVMRun X Y halfAddInitState [] (halfAddTensorXStateAfter X Y N) :=
              halfAddTensorXStateAfter_reachable X Y N hreachN hstate
            cases hstateX : (halfAddTensorXStateAfter X Y N).T.oracle with
            | neg =>
                have hEmitX : (halfAddTensorXStateAfter X Y N).T.EmitsDigit := by
                  exact Or.inl hstateX
                have hsX : GeneralTrace.SafeAt X Y (halfAddTensorXStateAfter X Y N) :=
                  safe_end_of_safeVMRun X Y hreachX
                rcases vmStepXY_emit_of_emitsDigit X Y (s := halfAddTensorXStateAfter X Y N) hEmitX with
                  ⟨d, hstep⟩
                have hsX' : GeneralTrace.SafeAt X Y { halfAddTensorXStateAfter X Y N with
                    T := (halfAddTensorXStateAfter X Y N).T.emit d } :=
                  safe_step (X := X) (Y := Y) hstep hsX
                have hrun : SafeVMRun X Y halfAddInitState [d]
                    { halfAddTensorXStateAfter X Y N with
                        T := (halfAddTensorXStateAfter X Y N).T.emit d } :=
                  safeVMRun_append X Y hreachX
                    (SafeVMRun.stepSome hstep hsX hsX' (SafeVMRun.refl _ hsX'))
                exact Or.inl ⟨_, d, hrun⟩
            | zero =>
                have hEmitX : (halfAddTensorXStateAfter X Y N).T.EmitsDigit := by
                  exact Or.inr (Or.inl hstateX)
                have hsX : GeneralTrace.SafeAt X Y (halfAddTensorXStateAfter X Y N) :=
                  safe_end_of_safeVMRun X Y hreachX
                rcases vmStepXY_emit_of_emitsDigit X Y (s := halfAddTensorXStateAfter X Y N) hEmitX with
                  ⟨d, hstep⟩
                have hsX' : GeneralTrace.SafeAt X Y { halfAddTensorXStateAfter X Y N with
                    T := (halfAddTensorXStateAfter X Y N).T.emit d } :=
                  safe_step (X := X) (Y := Y) hstep hsX
                have hrun : SafeVMRun X Y halfAddInitState [d]
                    { halfAddTensorXStateAfter X Y N with
                        T := (halfAddTensorXStateAfter X Y N).T.emit d } :=
                  safeVMRun_append X Y hreachX
                    (SafeVMRun.stepSome hstep hsX hsX' (SafeVMRun.refl _ hsX'))
                exact Or.inl ⟨_, d, hrun⟩
            | pos =>
                have hEmitX : (halfAddTensorXStateAfter X Y N).T.EmitsDigit := by
                  exact Or.inr (Or.inr hstateX)
                have hsX : GeneralTrace.SafeAt X Y (halfAddTensorXStateAfter X Y N) :=
                  safe_end_of_safeVMRun X Y hreachX
                rcases vmStepXY_emit_of_emitsDigit X Y (s := halfAddTensorXStateAfter X Y N) hEmitX with
                  ⟨d, hstep⟩
                have hsX' : GeneralTrace.SafeAt X Y { halfAddTensorXStateAfter X Y N with
                    T := (halfAddTensorXStateAfter X Y N).T.emit d } :=
                  safe_step (X := X) (Y := Y) hstep hsX
                have hrun : SafeVMRun X Y halfAddInitState [d]
                    { halfAddTensorXStateAfter X Y N with
                        T := (halfAddTensorXStateAfter X Y N).T.emit d } :=
                  safeVMRun_append X Y hreachX
                    (SafeVMRun.stepSome hstep hsX hsX' (SafeVMRun.refl _ hsX'))
                exact Or.inl ⟨_, d, hrun⟩
            | absorb =>
                have hpair : SafeVMRun X Y (halfAddTensorStateAfter X Y N) []
                    (halfAddTensorStateAfter X Y (N + 1)) :=
                  halfAddTensor_pair_reachable X Y N hsN hstate hstateX
                have hreachSucc : SafeVMRun X Y halfAddInitState []
                    (halfAddTensorStateAfter X Y (N + 1)) :=
                  safeVMRun_append_nil X Y hreachN hpair
                exact Or.inr ⟨
                  (fun k hk =>
                    if hkN : k < N then
                      habs k hkN
                    else
                      by
                        have hkEq : k = N := Nat.eq_of_lt_succ_of_not_lt hk hkN
                        simpa [hkEq] using hstate),
                  (fun k hk =>
                    if hkN : k < N then
                      habsX k hkN
                    else
                      by
                        have hkEq : k = N := Nat.eq_of_lt_succ_of_not_lt hk hkN
                        simpa [hkEq] using hstateX),
                  hreachSucc⟩

theorem halfAddTensor_prefix_absorb_or_emits_classified
    (X Y : MobiusReal) (N : ℕ) :
    (∃ M : ℕ, ∃ d : Digit,
        SafeVMRun X Y halfAddInitState [] (halfAddTensorStateAfter X Y M) ∧
        GeneralTrace.VMStepXY X Y
          (halfAddTensorStateAfter X Y M)
          (some (digit_to_LFT d))
          (halfAddResidualStateAfter X Y M d 0)) ∨
      (∃ M : ℕ, ∃ d : Digit,
        SafeVMRun X Y halfAddInitState [] (halfAddTensorXStateAfter X Y M) ∧
        GeneralTrace.VMStepXY X Y
          (halfAddTensorXStateAfter X Y M)
          (some (digit_to_LFT d))
          { halfAddTensorXStateAfter X Y M with
              T := (halfAddTensorXStateAfter X Y M).T.emit (digit_to_LFT d) }) ∨
      ((∀ k, k < N → (halfAddTensorStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb) ∧
        (∀ k, k < N → (halfAddTensorXStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb) ∧
        SafeVMRun X Y halfAddInitState [] (halfAddTensorStateAfter X Y N)) := by
  induction N with
  | zero =>
      right
      right
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
      · intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
      · simpa [halfAddInitState, halfAddTensorStateAfter] using
          (SafeVMRun.refl (X := X) (Y := Y) halfAddInitState (halfAddInit_safe X Y))
  | succ N ih =>
      rcases ih with hbal | hx | ⟨habs, habsX, hreachN⟩
      · exact Or.inl hbal
      · exact Or.inr (Or.inl hx)
      · have hsN : GeneralTrace.SafeAt X Y (halfAddTensorStateAfter X Y N) :=
          safe_end_of_safeVMRun X Y hreachN
        cases hstate : (halfAddTensorStateAfter X Y N).T.oracle with
        | neg =>
            have hstep' : GeneralTrace.VMStepXY X Y
                (halfAddTensorStateAfter X Y N)
                (some (digit_to_LFT .neg))
                (halfAddResidualStateAfter X Y N .neg 0) := by
              simpa [halfAddResidualStateAfter_zero] using
                (GeneralTrace.VMStepXY.emitNeg (X := X) (Y := Y)
                  (s := halfAddTensorStateAfter X Y N) hstate)
            exact Or.inl ⟨N, .neg, hreachN, hstep'⟩
        | zero =>
            have hstep' : GeneralTrace.VMStepXY X Y
                (halfAddTensorStateAfter X Y N)
                (some (digit_to_LFT .zero))
                (halfAddResidualStateAfter X Y N .zero 0) := by
              simpa [halfAddResidualStateAfter_zero] using
                (GeneralTrace.VMStepXY.emitZero (X := X) (Y := Y)
                  (s := halfAddTensorStateAfter X Y N) hstate)
            exact Or.inl ⟨N, .zero, hreachN, hstep'⟩
        | pos =>
            have hstep' : GeneralTrace.VMStepXY X Y
                (halfAddTensorStateAfter X Y N)
                (some (digit_to_LFT .pos))
                (halfAddResidualStateAfter X Y N .pos 0) := by
              simpa [halfAddResidualStateAfter_zero] using
                (GeneralTrace.VMStepXY.emitPos (X := X) (Y := Y)
                  (s := halfAddTensorStateAfter X Y N) hstate)
            exact Or.inl ⟨N, .pos, hreachN, hstep'⟩
        | absorb =>
            have hreachX : SafeVMRun X Y halfAddInitState [] (halfAddTensorXStateAfter X Y N) :=
              halfAddTensorXStateAfter_reachable X Y N hreachN hstate
            cases hstateX : (halfAddTensorXStateAfter X Y N).T.oracle with
            | neg =>
                exact Or.inr (Or.inl ⟨N, .neg, hreachX, by
                  simpa using
                    (GeneralTrace.VMStepXY.emitNeg (X := X) (Y := Y)
                      (s := halfAddTensorXStateAfter X Y N) hstateX)⟩)
            | zero =>
                exact Or.inr (Or.inl ⟨N, .zero, hreachX, by
                  simpa using
                    (GeneralTrace.VMStepXY.emitZero (X := X) (Y := Y)
                      (s := halfAddTensorXStateAfter X Y N) hstateX)⟩)
            | pos =>
                exact Or.inr (Or.inl ⟨N, .pos, hreachX, by
                  simpa using
                    (GeneralTrace.VMStepXY.emitPos (X := X) (Y := Y)
                      (s := halfAddTensorXStateAfter X Y N) hstateX)⟩)
            | absorb =>
                have hpair : SafeVMRun X Y (halfAddTensorStateAfter X Y N) []
                    (halfAddTensorStateAfter X Y (N + 1)) :=
                  halfAddTensor_pair_reachable X Y N hsN hstate hstateX
                have hreachSucc : SafeVMRun X Y halfAddInitState []
                    (halfAddTensorStateAfter X Y (N + 1)) :=
                  safeVMRun_append_nil X Y hreachN hpair
                exact Or.inr (Or.inr ⟨
                  (fun k hk =>
                    if hkN : k < N then
                      habs k hkN
                    else
                      by
                        have hkEq : k = N := Nat.eq_of_lt_succ_of_not_lt hk hkN
                        simpa [hkEq] using hstate),
                  (fun k hk =>
                    if hkN : k < N then
                      habsX k hkN
                    else
                      by
                        have hkEq : k = N := Nat.eq_of_lt_succ_of_not_lt hk hkN
                        simpa [hkEq] using hstateX),
                  hreachSucc⟩)

theorem halfAddTensor_scheduler_emitsStep
    (X Y : MobiusReal) :
    ∃ s : VMState, ∃ d, SafeVMRun X Y halfAddInitState [d] s := by
  rcases halfAddTensor_eventually_emitsDigit X Y with ⟨N, hN⟩
  rcases halfAddTensor_prefix_absorb_or_emits X Y N with hemit | ⟨habs, habsX, hreachN⟩
  · exact hemit
  · have hsN : GeneralTrace.SafeAt X Y (halfAddTensorStateAfter X Y N) :=
      safe_end_of_safeVMRun X Y hreachN
    rcases vmStepXY_emit_of_emitsDigit X Y (s := halfAddTensorStateAfter X Y N) hN with ⟨d, hstep⟩
    have hsN' : GeneralTrace.SafeAt X Y { halfAddTensorStateAfter X Y N with
        T := (halfAddTensorStateAfter X Y N).T.emit d } :=
      safe_step (X := X) (Y := Y) hstep hsN
    have hrun : SafeVMRun X Y halfAddInitState [d]
        { halfAddTensorStateAfter X Y N with
            T := (halfAddTensorStateAfter X Y N).T.emit d } :=
      safeVMRun_append X Y hreachN
        (SafeVMRun.stepSome hstep hsN hsN' (SafeVMRun.refl _ hsN'))
    exact ⟨_, d, hrun⟩

theorem halfAddTensor_scheduler_reaches_two_digits
    (X Y : MobiusReal) :
    ∃ s : VMState, ∃ d₁ d₂, SafeVMRun X Y halfAddInitState [digit_to_LFT d₁, d₂] s := by
  rcases halfAddTensor_eventually_emitsDigit X Y with ⟨N, hN⟩
  rcases halfAddTensor_prefix_absorb_or_emits_classified X Y N with
    hbal | hx | ⟨habs, habsX, hreachN⟩
  · rcases hbal with ⟨M, d₁, hreachM, hstepM⟩
    rcases halfAddTensor_balanced_first_emit_reaches_two_digits X Y M d₁ hreachM hstepM with
      ⟨s, d₂, hrun⟩
    exact ⟨s, d₁, d₂, hrun⟩
  · rcases hx with ⟨M, d₁, hreachX, hstepX⟩
    rcases halfAddTensorX_first_emit_reaches_two_digits X Y M d₁ hreachX hstepX with
      ⟨s, d₂, hrun⟩
    exact ⟨s, d₁, d₂, hrun⟩
  · have hsN : GeneralTrace.SafeAt X Y (halfAddTensorStateAfter X Y N) :=
      safe_end_of_safeVMRun X Y hreachN
    rcases hN with hneg | hrest
    · have hstep' : GeneralTrace.VMStepXY X Y
          (halfAddTensorStateAfter X Y N)
          (some (digit_to_LFT .neg))
          (halfAddResidualStateAfter X Y N .neg 0) := by
        simpa [halfAddResidualStateAfter_zero] using
          (GeneralTrace.VMStepXY.emitNeg (X := X) (Y := Y)
            (s := halfAddTensorStateAfter X Y N) hneg)
      rcases halfAddTensor_balanced_first_emit_reaches_two_digits X Y N .neg hreachN hstep' with
        ⟨s, d₂, hrun⟩
      exact ⟨s, .neg, d₂, hrun⟩
    · rcases hrest with hzero | hpos
      · have hstep' : GeneralTrace.VMStepXY X Y
            (halfAddTensorStateAfter X Y N)
            (some (digit_to_LFT .zero))
            (halfAddResidualStateAfter X Y N .zero 0) := by
          simpa [halfAddResidualStateAfter_zero] using
            (GeneralTrace.VMStepXY.emitZero (X := X) (Y := Y)
              (s := halfAddTensorStateAfter X Y N) hzero)
        rcases halfAddTensor_balanced_first_emit_reaches_two_digits X Y N .zero hreachN hstep' with
          ⟨s, d₂, hrun⟩
        exact ⟨s, .zero, d₂, hrun⟩
      · have hstep' : GeneralTrace.VMStepXY X Y
            (halfAddTensorStateAfter X Y N)
            (some (digit_to_LFT .pos))
            (halfAddResidualStateAfter X Y N .pos 0) := by
          simpa [halfAddResidualStateAfter_zero] using
            (GeneralTrace.VMStepXY.emitPos (X := X) (Y := Y)
              (s := halfAddTensorStateAfter X Y N) hpos)
        rcases halfAddTensor_balanced_first_emit_reaches_two_digits X Y N .pos hreachN hstep' with
          ⟨s, d₂, hrun⟩
        exact ⟨s, .pos, d₂, hrun⟩

theorem halfAddTensor_scheduler_emitsStep_mem_baseI
    (X Y : MobiusReal) :
    ∃ s : VMState, ∃ d,
      SafeVMRun X Y halfAddInitState [d] s ∧
      GeneralTrace.stateValue X Y s ∈ baseI := by
  rcases halfAddTensor_scheduler_emitsStep X Y with ⟨s, d, hrun⟩
  exact ⟨s, d, hrun, safeVMRun_singleton_residual_mem_baseI X Y hrun⟩

theorem halfAddTensor_run_eventually_emits (X Y : MobiusReal) :
    ∃ fuel, (run X Y fuel halfAddInitState).1 ≠ [] := by
  rcases halfAddTensor_scheduler_emitsStep X Y with ⟨s, d, hrun⟩
  rcases Computable.Mobius.safeVMRun_realized_by_run X Y hrun with ⟨fuel, hstate, hds⟩
  refine ⟨fuel, ?_⟩
  intro hnil
  have : ((run X Y fuel halfAddInitState).1.map digit_to_LFT) = [] := by
    simp [hnil]
  rw [hds] at this
  have hlen := congrArg List.length this
  simp at hlen

theorem halfAddTensor_run_reaches_first_digit (X Y : MobiusReal) :
    ∃ fuel d s, run X Y fuel halfAddInitState = ([d], s) := by
  rcases halfAddTensor_scheduler_emitsStep X Y with ⟨s, d, hrun⟩
  rcases Computable.Mobius.safeVMRun_realized_by_run X Y hrun with ⟨fuel, hstate, hds⟩
  set out := (run X Y fuel halfAddInitState).1
  have houtMap : out.map digit_to_LFT = [d] := by
    simpa [out] using hds
  cases hout : out with
  | nil =>
      have hlen := congrArg List.length houtMap
      simp [hout] at hlen
  | cons d0 ds =>
      cases hds0 : ds with
      | nil =>
          refine ⟨fuel, d0, (run X Y fuel halfAddInitState).2, ?_⟩
          have hout' : (run X Y fuel halfAddInitState).1 = [d0] := by
            simp [out, hout, hds0]
          exact Prod.ext hout' rfl
      | cons d1 ds' =>
          have hlen : List.length (out.map digit_to_LFT) = List.length [d] := by
            simp [houtMap]
          simp [out, hout, hds0] at hlen

theorem halfAddTensor_run_reaches_first_digit_mem_baseI (X Y : MobiusReal) :
    ∃ fuel d s,
      run X Y fuel halfAddInitState = ([d], s) ∧
      GeneralTrace.stateValue X Y s ∈ baseI := by
  rcases halfAddTensor_run_reaches_first_digit X Y with ⟨fuel, d, s, hrun⟩
  have hsafeRun : SafeVMRun X Y halfAddInitState [digit_to_LFT d] s := by
    simpa [hrun] using run_safeVMRun X Y fuel halfAddInitState (halfAddInit_safe X Y)
  exact ⟨fuel, d, s, hrun, safeVMRun_singleton_residual_mem_baseI X Y hsafeRun⟩

theorem halfAddTensor_run_first_digit_sound (X Y : MobiusReal) :
    ∃ fuel d s,
      run X Y fuel halfAddInitState = ([d], s) ∧
      (X.val + Y.val) / 2 = LFT.apply (digit_to_LFT d) (GeneralTrace.stateValue X Y s) := by
  rcases halfAddTensor_run_reaches_first_digit X Y with ⟨fuel, d, s, hrun⟩
  have hsafeRun : SafeVMRun X Y halfAddInitState [digit_to_LFT d] s := by
    simpa [hrun] using run_safeVMRun X Y fuel halfAddInitState (halfAddInit_safe X Y)
  have hprefix :
      GeneralTrace.stateValue X Y halfAddInitState =
        LFT.apply (digit_to_LFT d) (GeneralTrace.stateValue X Y s) := by
    simpa using vm_soundness_prefix_one halfAddInitState s X Y (digit_to_LFT d) hsafeRun
  refine ⟨fuel, d, s, hrun, ?_⟩
  calc
    (X.val + Y.val) / 2 = GeneralTrace.stateValue X Y halfAddInitState := by
      symm
      exact halfAddInit_stateValue X Y
    _ = LFT.apply (digit_to_LFT d) (GeneralTrace.stateValue X Y s) := hprefix

theorem halfAddTensor_run_first_digit_sound_mem_baseI (X Y : MobiusReal) :
    ∃ fuel d s,
      run X Y fuel halfAddInitState = ([d], s) ∧
      (X.val + Y.val) / 2 = LFT.apply (digit_to_LFT d) (GeneralTrace.stateValue X Y s) ∧
      GeneralTrace.stateValue X Y s ∈ baseI := by
  rcases halfAddTensor_run_reaches_first_digit_mem_baseI X Y with ⟨fuel, d, s, hrun, hs⟩
  have hsafeRun : SafeVMRun X Y halfAddInitState [digit_to_LFT d] s := by
    simpa [hrun] using run_safeVMRun X Y fuel halfAddInitState (halfAddInit_safe X Y)
  have hprefix :
      GeneralTrace.stateValue X Y halfAddInitState =
        LFT.apply (digit_to_LFT d) (GeneralTrace.stateValue X Y s) := by
    simpa using vm_soundness_prefix_one halfAddInitState s X Y (digit_to_LFT d) hsafeRun
  refine ⟨fuel, d, s, hrun, ?_, hs⟩
  calc
    (X.val + Y.val) / 2 = GeneralTrace.stateValue X Y halfAddInitState := by
      symm
      exact halfAddInit_stateValue X Y
    _ = LFT.apply (digit_to_LFT d) (GeneralTrace.stateValue X Y s) := hprefix

theorem halfAddTensor_run_first_digit_stable (X Y : MobiusReal) :
    ∃ fuel0 d, ∀ fuel, fuel0 ≤ fuel →
      ∃ tail, (run X Y fuel halfAddInitState).1 = d :: tail := by
  rcases halfAddTensor_run_reaches_first_digit X Y with ⟨fuel0, d, s, hrun0⟩
  refine ⟨fuel0, d, ?_⟩
  intro fuel hle
  rcases emittedPrefix_prefix_of_le X Y hle halfAddInitState with ⟨ds, hds⟩
  refine ⟨ds, ?_⟩
  simpa [emittedPrefix, hrun0] using hds

theorem halfAddTensor_run_reaches_two_digits (X Y : MobiusReal) :
    ∃ fuel d₁ d₂ s, run X Y fuel halfAddInitState = ([d₁, d₂], s) := by
  rcases halfAddTensor_scheduler_reaches_two_digits X Y with ⟨s, d₁, d₂LFT, hrun⟩
  rcases Computable.Mobius.safeVMRun_realized_by_run X Y hrun with ⟨fuel, hstate, hds⟩
  set out := (run X Y fuel halfAddInitState).1
  have houtMap : out.map digit_to_LFT = [digit_to_LFT d₁, d₂LFT] := by
    simpa [out] using hds
  cases hout : out with
  | nil =>
      have hlen := congrArg List.length houtMap
      simp [hout] at hlen
  | cons d0 ds =>
      cases hds0 : ds with
      | nil =>
          have hlen := congrArg List.length houtMap
          simp [hout, hds0] at hlen
      | cons d1 ds' =>
          cases hds1 : ds' with
          | nil =>
              refine ⟨fuel, d0, d1, (run X Y fuel halfAddInitState).2, ?_⟩
              have hout' : (run X Y fuel halfAddInitState).1 = [d0, d1] := by
                simp [out, hout, hds0, hds1]
              exact Prod.ext hout' rfl
          | cons d2 ds'' =>
              have hlen := congrArg List.length houtMap
              simp [hout, hds0, hds1] at hlen

theorem halfAddTensor_run_two_digits_sound (X Y : MobiusReal) :
    ∃ fuel d₁ d₂ s,
      run X Y fuel halfAddInitState = ([d₁, d₂], s) ∧
      (X.val + Y.val) / 2 =
        LFT.apply (digit_to_LFT d₁)
          (LFT.apply (digit_to_LFT d₂) (GeneralTrace.stateValue X Y s)) := by
  rcases halfAddTensor_run_reaches_two_digits X Y with ⟨fuel, d₁, d₂, s, hrun⟩
  have hsafeRun : SafeVMRun X Y halfAddInitState [digit_to_LFT d₁, digit_to_LFT d₂] s := by
    simpa [hrun] using run_safeVMRun X Y fuel halfAddInitState (halfAddInit_safe X Y)
  have hprefix :
      GeneralTrace.stateValue X Y halfAddInitState =
        LFT.apply (digit_to_LFT d₁)
          (LFT.apply (digit_to_LFT d₂) (GeneralTrace.stateValue X Y s)) := by
    simpa using
      vm_soundness_prefix_two halfAddInitState s X Y (digit_to_LFT d₁) (digit_to_LFT d₂) hsafeRun
  refine ⟨fuel, d₁, d₂, s, hrun, ?_⟩
  calc
    (X.val + Y.val) / 2 = GeneralTrace.stateValue X Y halfAddInitState := by
      symm
      exact halfAddInit_stateValue X Y
    _ = LFT.apply (digit_to_LFT d₁)
          (LFT.apply (digit_to_LFT d₂) (GeneralTrace.stateValue X Y s)) := hprefix

theorem halfAddTensor_run_reaches_two_digits_mem_baseI (X Y : MobiusReal) :
    ∃ fuel d₁ d₂ s,
      run X Y fuel halfAddInitState = ([d₁, d₂], s) ∧
      GeneralTrace.stateValue X Y s ∈ baseI := by
  rcases halfAddTensor_run_reaches_two_digits X Y with ⟨fuel, d₁, d₂, s, hrun⟩
  have hsafeRun : SafeVMRun X Y halfAddInitState [digit_to_LFT d₁, digit_to_LFT d₂] s := by
    simpa [hrun] using run_safeVMRun X Y fuel halfAddInitState (halfAddInit_safe X Y)
  exact ⟨fuel, d₁, d₂, s, hrun, safeVMRun_pair_residual_mem_baseI X Y hsafeRun⟩

theorem halfAddTensor_run_two_digits_sound_mem_baseI (X Y : MobiusReal) :
    ∃ fuel d₁ d₂ s,
      run X Y fuel halfAddInitState = ([d₁, d₂], s) ∧
      (X.val + Y.val) / 2 =
        LFT.apply (digit_to_LFT d₁)
          (LFT.apply (digit_to_LFT d₂) (GeneralTrace.stateValue X Y s)) ∧
      GeneralTrace.stateValue X Y s ∈ baseI := by
  rcases halfAddTensor_run_reaches_two_digits_mem_baseI X Y with ⟨fuel, d₁, d₂, s, hrun, hs⟩
  have hsafeRun : SafeVMRun X Y halfAddInitState [digit_to_LFT d₁, digit_to_LFT d₂] s := by
    simpa [hrun] using run_safeVMRun X Y fuel halfAddInitState (halfAddInit_safe X Y)
  have hprefix :
      GeneralTrace.stateValue X Y halfAddInitState =
        LFT.apply (digit_to_LFT d₁)
          (LFT.apply (digit_to_LFT d₂) (GeneralTrace.stateValue X Y s)) := by
    simpa using
      vm_soundness_prefix_two halfAddInitState s X Y (digit_to_LFT d₁) (digit_to_LFT d₂) hsafeRun
  refine ⟨fuel, d₁, d₂, s, hrun, ?_, hs⟩
  calc
    (X.val + Y.val) / 2 = GeneralTrace.stateValue X Y halfAddInitState := by
      symm
      exact halfAddInit_stateValue X Y
    _ = LFT.apply (digit_to_LFT d₁)
          (LFT.apply (digit_to_LFT d₂) (GeneralTrace.stateValue X Y s)) := hprefix

theorem halfAddTensor_run_two_digits_stable (X Y : MobiusReal) :
    ∃ fuel0 d₁ d₂, ∀ fuel, fuel0 ≤ fuel →
      ∃ tail, (run X Y fuel halfAddInitState).1 = d₁ :: d₂ :: tail := by
  rcases halfAddTensor_run_reaches_two_digits X Y with ⟨fuel0, d₁, d₂, s, hrun0⟩
  refine ⟨fuel0, d₁, d₂, ?_⟩
  intro fuel hle
  rcases emittedPrefix_prefix_of_le X Y hle halfAddInitState with ⟨ds, hds⟩
  refine ⟨ds, ?_⟩
  simpa [emittedPrefix, hrun0] using hds

theorem halfAddTensor_reachable_emitsStep
    (X Y : MobiusReal) (N : ℕ)
    (hreach : SafeVMRun X Y halfAddInitState [] (halfAddTensorStateAfter X Y N))
    (hN : (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).EmitsDigit) :
    ∃ d,
      SafeVMRun X Y halfAddInitState [d]
        { halfAddTensorStateAfter X Y N with
            T := (halfAddTensorStateAfter X Y N).T.emit d } := by
  have hsN : GeneralTrace.SafeAt X Y (halfAddTensorStateAfter X Y N) :=
    safe_end_of_safeVMRun X Y hreach
  rcases vmStepXY_emit_of_emitsDigit X Y (s := halfAddTensorStateAfter X Y N) hN with ⟨d, hstep⟩
  have hsN' : GeneralTrace.SafeAt X Y { halfAddTensorStateAfter X Y N with
      T := (halfAddTensorStateAfter X Y N).T.emit d } :=
    safe_step (X := X) (Y := Y) hstep hsN
  exact ⟨d, safeVMRun_append X Y hreach
    (SafeVMRun.stepSome hstep hsN hsN' (SafeVMRun.refl _ hsN'))⟩

theorem halfAddTensor_reachable_emitsStep_mem_baseI
    (X Y : MobiusReal) (N : ℕ)
    (hreach : SafeVMRun X Y halfAddInitState [] (halfAddTensorStateAfter X Y N))
    (hN : (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).EmitsDigit) :
    ∃ d,
      SafeVMRun X Y halfAddInitState [d]
        { halfAddTensorStateAfter X Y N with
            T := (halfAddTensorStateAfter X Y N).T.emit d } ∧
      GeneralTrace.stateValue X Y { halfAddTensorStateAfter X Y N with
          T := (halfAddTensorStateAfter X Y N).T.emit d } ∈ baseI := by
  have hsN : GeneralTrace.SafeAt X Y (halfAddTensorStateAfter X Y N) :=
    safe_end_of_safeVMRun X Y hreach
  rcases vmStepXY_emit_of_emitsDigit X Y (s := halfAddTensorStateAfter X Y N) hN with ⟨d, hstep⟩
  have hsN' : GeneralTrace.SafeAt X Y { halfAddTensorStateAfter X Y N with
      T := (halfAddTensorStateAfter X Y N).T.emit d } :=
    safe_step (X := X) (Y := Y) hstep hsN
  refine ⟨d, safeVMRun_append X Y hreach
    (SafeVMRun.stepSome hstep hsN hsN' (SafeVMRun.refl _ hsN')), ?_⟩
  exact stateValue_emit_mem_baseI X Y hstep hsN hsN'

theorem halfAddTensorX_reachable_emitsStep
    (X Y : MobiusReal) (N : ℕ)
    (hreach : SafeVMRun X Y halfAddInitState [] (halfAddTensorXStateAfter X Y N))
    (hN : (halfAddTensorXStateAfter X Y N).T.EmitsDigit) :
    ∃ d,
      SafeVMRun X Y halfAddInitState [d]
        { halfAddTensorXStateAfter X Y N with
            T := (halfAddTensorXStateAfter X Y N).T.emit d } := by
  have hsN : GeneralTrace.SafeAt X Y (halfAddTensorXStateAfter X Y N) :=
    safe_end_of_safeVMRun X Y hreach
  rcases vmStepXY_emit_of_emitsDigit X Y (s := halfAddTensorXStateAfter X Y N) hN with ⟨d, hstep⟩
  have hsN' : GeneralTrace.SafeAt X Y { halfAddTensorXStateAfter X Y N with
      T := (halfAddTensorXStateAfter X Y N).T.emit d } :=
    safe_step (X := X) (Y := Y) hstep hsN
  exact ⟨d, safeVMRun_append X Y hreach
    (SafeVMRun.stepSome hstep hsN hsN' (SafeVMRun.refl _ hsN'))⟩

theorem halfAddTensorX_reachable_emitsStep_mem_baseI
    (X Y : MobiusReal) (N : ℕ)
    (hreach : SafeVMRun X Y halfAddInitState [] (halfAddTensorXStateAfter X Y N))
    (hN : (halfAddTensorXStateAfter X Y N).T.EmitsDigit) :
    ∃ d,
      SafeVMRun X Y halfAddInitState [d]
        { halfAddTensorXStateAfter X Y N with
            T := (halfAddTensorXStateAfter X Y N).T.emit d } ∧
      GeneralTrace.stateValue X Y { halfAddTensorXStateAfter X Y N with
          T := (halfAddTensorXStateAfter X Y N).T.emit d } ∈ baseI := by
  have hsN : GeneralTrace.SafeAt X Y (halfAddTensorXStateAfter X Y N) :=
    safe_end_of_safeVMRun X Y hreach
  rcases vmStepXY_emit_of_emitsDigit X Y (s := halfAddTensorXStateAfter X Y N) hN with ⟨d, hstep⟩
  have hsN' : GeneralTrace.SafeAt X Y { halfAddTensorXStateAfter X Y N with
      T := (halfAddTensorXStateAfter X Y N).T.emit d } :=
    safe_step (X := X) (Y := Y) hstep hsN
  refine ⟨d, safeVMRun_append X Y hreach
    (SafeVMRun.stepSome hstep hsN hsN' (SafeVMRun.refl _ hsN')), ?_⟩
  exact stateValue_emit_mem_baseI X Y hstep hsN hsN'

theorem halfAddTensor_reachable_emitsStep_of_absorb_prefix
    (X Y : MobiusReal) (N : ℕ)
    (habs : ∀ k, k < N →
      (halfAddTensorStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb)
    (habsX : ∀ k, k < N →
      (halfAddTensorXStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb)
    (hN : (Tensor.absorbBoth_n halfAddTensor X.stream Y.stream N).EmitsDigit) :
    ∃ d,
      SafeVMRun X Y halfAddInitState [d]
        { halfAddTensorStateAfter X Y N with
            T := (halfAddTensorStateAfter X Y N).T.emit d } := by
  have hreach := halfAddTensorStateAfter_reachable X Y N habs habsX
  exact halfAddTensor_reachable_emitsStep X Y N hreach hN

theorem halfAddTensorX_reachable_emitsStep_of_absorb_prefix
    (X Y : MobiusReal) (N : ℕ)
    (habs : ∀ k, k ≤ N →
      (halfAddTensorStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb)
    (habsX : ∀ k, k < N →
      (halfAddTensorXStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb)
    (hN : (halfAddTensorXStateAfter X Y N).T.EmitsDigit) :
    ∃ d,
      SafeVMRun X Y halfAddInitState [d]
        { halfAddTensorXStateAfter X Y N with
            T := (halfAddTensorXStateAfter X Y N).T.emit d } := by
  have hreachN : SafeVMRun X Y halfAddInitState [] (halfAddTensorStateAfter X Y N) :=
    halfAddTensorStateAfter_reachable X Y N
      (fun k hk => habs k (Nat.le_of_lt hk)) habsX
  have hreachX : SafeVMRun X Y halfAddInitState [] (halfAddTensorXStateAfter X Y N) :=
    halfAddTensorXStateAfter_reachable X Y N hreachN (habs N le_rfl)
  exact halfAddTensorX_reachable_emitsStep X Y N hreachX hN

theorem halfAddTensor_soundness_infinite
    (X Y : MobiusReal) (out : DigitStream)
    (σ : ℕ → VMState) (ℓ : ℕ → Option LFT)
    (hσ0 : σ 0 = halfAddInitState)
    (hstep : ∀ i, GeneralTrace.VMStepXY X Y (σ i) (ℓ i) (σ (i + 1)))
    (hsafe : ∀ i, GeneralTrace.SafeAt X Y (σ i))
    (sched : GeneralTrace.EmitSchedule ℓ out) :
    (MobiusReal.fromStream out).val = (X.val + Y.val) / 2 := by
  calc
    (MobiusReal.fromStream out).val = GeneralTrace.stateValue X Y halfAddInitState := by
      exact vm_soundness_infinite X Y halfAddInitState out σ ℓ hσ0 hstep hsafe sched
    _ = (X.val + Y.val) / 2 := halfAddInit_stateValue X Y

theorem addOutput_soundness_infinite
    (X Y : MobiusReal) (out : DigitStream)
    (σ : ℕ → VMState) (ℓ : ℕ → Option LFT)
    (hσ0 : σ 0 = halfAddInitState)
    (hstep : ∀ i, GeneralTrace.VMStepXY X Y (σ i) (ℓ i) (σ (i + 1)))
    (hsafe : ∀ i, GeneralTrace.SafeAt X Y (σ i))
    (sched : GeneralTrace.EmitSchedule ℓ out) :
    2 * (MobiusReal.fromStream out).val = X.val + Y.val := by
  have hhalf := halfAddTensor_soundness_infinite X Y out σ ℓ hσ0 hstep hsafe sched
  linarith

theorem addOutput_toReal_soundness_infinite
    (X Y : MobiusReal) (out : DigitStream)
    (σ : ℕ → VMState) (ℓ : ℕ → Option LFT)
    (hσ0 : σ 0 = halfAddInitState)
    (hstep : ∀ i, GeneralTrace.VMStepXY X Y (σ i) (ℓ i) (σ (i + 1)))
    (hsafe : ∀ i, GeneralTrace.SafeAt X Y (σ i))
    (sched : GeneralTrace.EmitSchedule ℓ out) :
    Computable.CReal.toReal (toCRealScaled 1 out) = X.val + Y.val := by
  calc
    Computable.CReal.toReal (toCRealScaled 1 out)
        = 2 * (MobiusReal.fromStream out).val :=
          DigitStream.toReal_toCRealScaled_one out
    _ = X.val + Y.val := addOutput_soundness_infinite X Y out σ ℓ hσ0 hstep hsafe sched

end Mobius
end Computable
