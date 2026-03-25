import HopfieldNet.CReals.Mobius.Runtime
import HopfieldNet.CReals.Mobius.CRealBridge

namespace Computable
namespace Mobius

set_option autoImplicit false

/-- Initial VM state for the bounded multiplication tensor on `[-1,1]^2`. -/
def mulInitState : VMState where
  T := mulTensor
  idx_x := 0
  idx_y := 0
  absorb_x_next := true

theorem mulInit_safe (X Y : MobiusReal) :
    GeneralTrace.SafeAt X Y mulInitState := by
  simp [mulInitState, GeneralTrace.SafeAt, Tensor.denAt, mulTensor]

theorem mulInit_stateValue (X Y : MobiusReal) :
    GeneralTrace.stateValue X Y mulInitState = X.val * Y.val := by
  simp [mulInitState, GeneralTrace.stateValue, mulTensor_valueAt, MobiusReal.drop]

theorem mulInit_stateValue_mem_baseI (X Y : MobiusReal) :
    GeneralTrace.stateValue X Y mulInitState ∈ baseI := by
  have hx : X.val ∈ baseI := MobiusReal.val_mem_baseI X
  have hy : Y.val ∈ baseI := MobiusReal.val_mem_baseI Y
  rw [mulInit_stateValue]
  have hxa : |X.val| ≤ (1 : ℝ) := abs_le.2 ⟨hx.1, hx.2⟩
  have hya : |Y.val| ≤ (1 : ℝ) := abs_le.2 ⟨hy.1, hy.2⟩
  have hmul : |X.val * Y.val| ≤ (1 : ℝ) := by
    calc
      |X.val * Y.val| = |X.val| * |Y.val| := by simp [abs_mul]
      _ ≤ 1 * 1 := by gcongr
      _ = (1 : ℝ) := by ring
  exact abs_le.1 (by simpa using hmul)

private theorem Tensor.ext
    {T S : Tensor}
    (ha : T.a = S.a) (hb : T.b = S.b) (hc : T.c = S.c) (hd : T.d = S.d)
    (he : T.e = S.e) (hf : T.f = S.f) (hg : T.g = S.g) (hh : T.h = S.h) :
    T = S := by
  cases T
  cases S
  simp_all

/-- Tensor representing the product `LFT.apply M x * LFT.apply N y`. -/
def mulPrefixTensor (M N : LFT) : Tensor where
  a := M.a * N.a
  b := M.a * N.b
  c := M.b * N.a
  d := M.b * N.b
  e := M.c * N.c
  f := M.c * N.d
  g := M.d * N.c
  h := M.d * N.d

@[simp] theorem mulPrefixTensor_id_id :
    mulPrefixTensor LFT.id LFT.id = mulTensor := by
  apply Tensor.ext <;> simp [mulPrefixTensor, mulTensor, LFT.id]

theorem mulPrefixTensor_absorbX_absorbY (M N Px Py : LFT) :
    ((mulPrefixTensor M N).absorbX Px).absorbY Py =
      mulPrefixTensor (M.comp Px) (N.comp Py) := by
  apply Tensor.ext <;>
    simp [mulPrefixTensor, Tensor.absorbX, Tensor.absorbY, LFT.comp] <;> ring

theorem mulPrefixTensor_absorbX (M N Px : LFT) :
    (mulPrefixTensor M N).absorbX Px = mulPrefixTensor (M.comp Px) N := by
  apply Tensor.ext <;>
    simp [mulPrefixTensor, Tensor.absorbX, LFT.comp] <;> ring

theorem mulPrefixTensor_absorbY (M N Py : LFT) :
    (mulPrefixTensor M N).absorbY Py = mulPrefixTensor M (N.comp Py) := by
  apply Tensor.ext <;>
    simp [mulPrefixTensor, Tensor.absorbY, LFT.comp] <;> ring

theorem absorbBoth_n_mulPrefixTensor_eq (M N : LFT) (sx sy : LFTStream) :
    ∀ K, Tensor.absorbBoth_n (mulPrefixTensor M N) sx sy K =
      mulPrefixTensor (M.comp (pairedPrefix sx K)) (N.comp (pairedPrefix sy K))
  | 0 => by
      apply Tensor.ext <;> simp [Tensor.absorbBoth_n, pairedPrefix, mulPrefixTensor, LFT.comp, LFT.id]
  | K + 1 => by
      calc
        Tensor.absorbBoth_n (mulPrefixTensor M N) sx sy (K + 1)
            = ((Tensor.absorbBoth_n (mulPrefixTensor M N) sx sy K).absorbX (sx K)).absorbY (sy K) := by
                simp [Tensor.absorbBoth_n]
        _ = ((mulPrefixTensor (M.comp (pairedPrefix sx K)) (N.comp (pairedPrefix sy K))).absorbX (sx K)).absorbY (sy K) := by
              rw [absorbBoth_n_mulPrefixTensor_eq (M := M) (N := N) (sx := sx) (sy := sy) K]
        _ = mulPrefixTensor ((M.comp (pairedPrefix sx K)).comp (sx K))
              ((N.comp (pairedPrefix sy K)).comp (sy K)) := by
                simpa using mulPrefixTensor_absorbX_absorbY
                  (M.comp (pairedPrefix sx K)) (N.comp (pairedPrefix sy K)) (sx K) (sy K)
        _ = mulPrefixTensor (M.comp (pairedPrefix sx (K + 1))) (N.comp (pairedPrefix sy (K + 1))) := by
              simp [pairedPrefix, LFT.comp_assoc]

theorem absorbBoth_n_mulTensor_eq (sx sy : LFTStream) :
    ∀ N, Tensor.absorbBoth_n mulTensor sx sy N =
      mulPrefixTensor (pairedPrefix sx N) (pairedPrefix sy N)
  | 0 => by
      simp [pairedPrefix, Tensor.absorbBoth_n, mulPrefixTensor_id_id]
  | N + 1 => by
      calc
        Tensor.absorbBoth_n mulTensor sx sy (N + 1)
            = ((Tensor.absorbBoth_n mulTensor sx sy N).absorbX (sx N)).absorbY (sy N) := by
                simp [Tensor.absorbBoth_n]
        _ = ((mulPrefixTensor (pairedPrefix sx N) (pairedPrefix sy N)).absorbX (sx N)).absorbY (sy N) := by
              rw [absorbBoth_n_mulTensor_eq sx sy N]
        _ = mulPrefixTensor ((pairedPrefix sx N).comp (sx N)) ((pairedPrefix sy N).comp (sy N)) := by
              simpa using mulPrefixTensor_absorbX_absorbY
                (pairedPrefix sx N) (pairedPrefix sy N) (sx N) (sy N)
        _ = mulPrefixTensor (pairedPrefix sx (N + 1)) (pairedPrefix sy (N + 1)) := by
              simp [pairedPrefix]

def mulTensorStateAfter (X Y : MobiusReal) (N : ℕ) : VMState where
  T := Tensor.absorbBoth_n mulTensor X.stream Y.stream N
  idx_x := N
  idx_y := N
  absorb_x_next := true

def mulTensorXStateAfter (X Y : MobiusReal) (N : ℕ) : VMState where
  T := (Tensor.absorbBoth_n mulTensor X.stream Y.stream N).absorbX (X.stream N)
  idx_x := N + 1
  idx_y := N
  absorb_x_next := false

theorem mulTensorXStateAfter_eq_mulPrefixTensor
    (X Y : MobiusReal) (N : ℕ) :
    (mulTensorXStateAfter X Y N).T =
      mulPrefixTensor ((pairedPrefix X.stream N).comp (X.stream N)) (pairedPrefix Y.stream N) := by
  rw [mulTensorXStateAfter, absorbBoth_n_mulTensor_eq]
  simpa using mulPrefixTensor_absorbX (pairedPrefix X.stream N) (pairedPrefix Y.stream N) (X.stream N)

theorem mulPrefixTensor_apply (M N : LFT) (x y : ℝ) :
    Tensor.apply (mulPrefixTensor M N) x y = LFT.apply M x * LFT.apply N y := by
  set numM : ℝ := (M.a : ℝ) * x + (M.b : ℝ)
  set denM : ℝ := (M.c : ℝ) * x + (M.d : ℝ)
  set numN : ℝ := (N.a : ℝ) * y + (N.b : ℝ)
  set denN : ℝ := (N.c : ℝ) * y + (N.d : ℝ)
  have hTensor :
      Tensor.apply (mulPrefixTensor M N) x y = (numM * numN) / (denM * denN) := by
    simp [Tensor.apply, mulPrefixTensor, numM, denM, numN, denN]
    ring_nf
  have hProd :
      LFT.apply M x * LFT.apply N y = (numM * numN) / (denM * denN) := by
    by_cases hdm : denM = 0
    · by_cases hdn : denN = 0
      · simp [LFT.apply, numM, denM, numN, denN, hdm, hdn]
      · simp [LFT.apply, numM, denM, numN, denN, hdm]
    · by_cases hdn : denN = 0
      · simp [LFT.apply, numM, denM, numN, denN, hdn]
      · simp [LFT.apply, numM, denM, numN, denN]
        field_simp [hdm, hdn]
  rw [hTensor, hProd]

theorem mul_mem_baseI {a b : ℝ} (ha : a ∈ baseI) (hb : b ∈ baseI) :
    a * b ∈ baseI := by
  have haa : |a| ≤ (1 : ℝ) := abs_le.2 ⟨ha.1, ha.2⟩
  have hba : |b| ≤ (1 : ℝ) := abs_le.2 ⟨hb.1, hb.2⟩
  have hmul : |a * b| ≤ (1 : ℝ) := by
    calc
      |a * b| = |a| * |b| := by simp [abs_mul]
      _ ≤ 1 * 1 := by gcongr
      _ = (1 : ℝ) := by ring
  exact abs_le.1 (by simpa using hmul)

theorem mul_diff_le_sum_of_mem_baseI {a b c d : ℝ}
    (hb : b ∈ baseI) (hc : c ∈ baseI) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  have hbabs : |b| ≤ (1 : ℝ) := abs_le.2 ⟨hb.1, hb.2⟩
  have hcabs : |c| ≤ (1 : ℝ) := abs_le.2 ⟨hc.1, hc.2⟩
  calc
    |a * b - c * d|
        = |b * (a - c) + c * (b - d)| := by ring_nf
    _ ≤ |b * (a - c)| + |c * (b - d)| := abs_add_le _ _
    _ = |b| * |a - c| + |c| * |b - d| := by simp [abs_mul]
    _ ≤ 1 * |a - c| + 1 * |b - d| := by gcongr
    _ = |a - c| + |b - d| := by ring

theorem mulPrefixTensor_hasNoPoleOnBase (M N : LFT)
    (hM : M.NoPoleOnBase) (hN : N.NoPoleOnBase) :
    (mulPrefixTensor M N).HasNoPoleOnBase := by
  intro x hx y hy
  have hMx := LFT.denom_ne_zero_of_NoPoleOnBase M hx hM
  have hNy := LFT.denom_ne_zero_of_NoPoleOnBase N hy hN
  intro h0
  set AX : ℝ := ((M.c : ℝ) * x + (M.d : ℝ))
  set AY : ℝ := ((N.c : ℝ) * y + (N.d : ℝ))
  have h0' : AX * AY = 0 := by
    subst AX AY
    convert h0 using 1
    simp [Tensor.denAt, mulPrefixTensor]
    ring_nf
  rcases mul_eq_zero.mp h0' with hX | hY
  · exact hMx hX
  · exact hNy hY

theorem mulPrefixTensor_mapsBaseI (M N : LFT)
    (hMMaps : Set.MapsTo (fun x => LFT.apply M x) baseI baseI)
    (hNMaps : Set.MapsTo (fun y => LFT.apply N y) baseI baseI) :
    (mulPrefixTensor M N).MapsBaseI := by
  intro x hx y hy
  rw [mulPrefixTensor_apply M N x y]
  exact mul_mem_baseI (hMMaps hx) (hNMaps hy)

theorem GeneralTrace.safeAt_of_tensor_hasNoPoleOnBase
    (X Y : MobiusReal) (s : VMState) (hT : s.T.HasNoPoleOnBase) :
    GeneralTrace.SafeAt X Y s := by
  exact hT _ (GeneralTrace.drop_val_mem_baseI X s.idx_x)
    _ (GeneralTrace.drop_val_mem_baseI Y s.idx_y)

theorem mulTensorStateAfter_apply (X Y : MobiusReal) (N : ℕ) (x y : ℝ) :
    Tensor.apply (Tensor.absorbBoth_n mulTensor X.stream Y.stream N) x y =
      LFT.apply (pairedPrefix X.stream N) x * LFT.apply (pairedPrefix Y.stream N) y := by
  rw [absorbBoth_n_mulTensor_eq]
  exact mulPrefixTensor_apply (pairedPrefix X.stream N) (pairedPrefix Y.stream N) x y

theorem mulTensorStateAfter_mapsBaseI (X Y : MobiusReal) (N : ℕ) :
    (Tensor.absorbBoth_n mulTensor X.stream Y.stream N).MapsBaseI := by
  rw [absorbBoth_n_mulTensor_eq]
  exact mulPrefixTensor_mapsBaseI
    (pairedPrefix X.stream N) (pairedPrefix Y.stream N)
    (pairedPrefix_maps_base X N) (pairedPrefix_maps_base Y N)

theorem mulTensorStateAfter_hasNoPoleOnBase (X Y : MobiusReal) (N : ℕ) :
    (Tensor.absorbBoth_n mulTensor X.stream Y.stream N).HasNoPoleOnBase := by
  rw [absorbBoth_n_mulTensor_eq]
  exact mulPrefixTensor_hasNoPoleOnBase
    (pairedPrefix X.stream N) (pairedPrefix Y.stream N)
    (pairedPrefix_noPoleOnBase X N) (pairedPrefix_noPoleOnBase Y N)

theorem mulTensorXStateAfter_hasNoPoleOnBase (X Y : MobiusReal) (N : ℕ) :
    (mulTensorXStateAfter X Y N).T.HasNoPoleOnBase := by
  rw [mulTensorXStateAfter_eq_mulPrefixTensor]
  exact mulPrefixTensor_hasNoPoleOnBase
    ((pairedPrefix X.stream N).comp (X.stream N)) (pairedPrefix Y.stream N)
    (by simpa [pairedPrefix] using pairedPrefix_noPoleOnBase X (N + 1))
    (pairedPrefix_noPoleOnBase Y N)

theorem mulTensorStateAfter_safe (X Y : MobiusReal) (N : ℕ) :
    GeneralTrace.SafeAt X Y (mulTensorStateAfter X Y N) := by
  exact GeneralTrace.safeAt_of_tensor_hasNoPoleOnBase X Y
    (mulTensorStateAfter X Y N) (mulTensorStateAfter_hasNoPoleOnBase X Y N)

theorem mulTensorXStateAfter_safe (X Y : MobiusReal) (N : ℕ) :
    GeneralTrace.SafeAt X Y (mulTensorXStateAfter X Y N) := by
  exact GeneralTrace.safeAt_of_tensor_hasNoPoleOnBase X Y
    (mulTensorXStateAfter X Y N) (mulTensorXStateAfter_hasNoPoleOnBase X Y N)

theorem mulTensorStateAfter_diff_lt
    (X Y : MobiusReal) {ε : ℝ} (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ x ∈ baseI, ∀ w ∈ baseI, ∀ y ∈ baseI, ∀ z ∈ baseI,
      |Tensor.apply (Tensor.absorbBoth_n mulTensor X.stream Y.stream N) x y -
        Tensor.apply (Tensor.absorbBoth_n mulTensor X.stream Y.stream N) w z| < ε := by
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
          |LFT.apply (pairedPrefix X.stream (n + 1)) x -
              LFT.apply (pairedPrefix X.stream (n + 1)) w| < ε / 2 := by
        rw [pairedPrefix_eq_partialComp]
        exact hdx0
      have hdy :
          |LFT.apply (pairedPrefix Y.stream (n + 1)) y -
              LFT.apply (pairedPrefix Y.stream (n + 1)) z| < ε / 2 := by
        rw [pairedPrefix_eq_partialComp]
        exact hdy0
      have hXw : LFT.apply (pairedPrefix X.stream (n + 1)) w ∈ baseI :=
        pairedPrefix_maps_base X (n + 1) hw
      have hYy : LFT.apply (pairedPrefix Y.stream (n + 1)) y ∈ baseI :=
        pairedPrefix_maps_base Y (n + 1) hy
      rw [mulTensorStateAfter_apply X Y (n + 1) x y, mulTensorStateAfter_apply X Y (n + 1) w z]
      have hsplit :
          |LFT.apply (pairedPrefix X.stream (n + 1)) x * LFT.apply (pairedPrefix Y.stream (n + 1)) y -
              LFT.apply (pairedPrefix X.stream (n + 1)) w * LFT.apply (pairedPrefix Y.stream (n + 1)) z|
            ≤ |LFT.apply (pairedPrefix X.stream (n + 1)) x -
                LFT.apply (pairedPrefix X.stream (n + 1)) w| +
              |LFT.apply (pairedPrefix Y.stream (n + 1)) y -
                LFT.apply (pairedPrefix Y.stream (n + 1)) z| := by
        exact mul_diff_le_sum_of_mem_baseI hYy hXw
      have hsum :
          |LFT.apply (pairedPrefix X.stream (n + 1)) x -
              LFT.apply (pairedPrefix X.stream (n + 1)) w| +
            |LFT.apply (pairedPrefix Y.stream (n + 1)) y -
              LFT.apply (pairedPrefix Y.stream (n + 1)) z| < ε := by
        nlinarith
      exact lt_of_le_of_lt hsplit hsum

theorem mulTensorStateAfter_width_le_eventually
    (X Y : MobiusReal) {ε : ℝ} (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      tensorWidth (Tensor.absorbBoth_n mulTensor X.stream Y.stream N) ≤ ε := by
  rcases mulTensorStateAfter_diff_lt X Y hε with ⟨N0, hN0⟩
  refine ⟨N0, ?_⟩
  intro N hN
  unfold tensorWidth
  exact csSup_le
    (Tensor.widthSet_nonempty (Tensor.absorbBoth_n mulTensor X.stream Y.stream N))
    (by
      intro d hd
      rcases hd with ⟨x, y, w, z, hx, hy, hw, hz, rfl⟩
      exact le_of_lt (hN0 N hN x hx w hw y hy z hz))

theorem mulTensorStateAfter_width_lt_half_eventually (X Y : MobiusReal) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      tensorWidth (Tensor.absorbBoth_n mulTensor X.stream Y.stream N) < (1 / 2 : ℝ) := by
  rcases mulTensorStateAfter_width_le_eventually X Y
    (ε := (1 / 4 : ℝ)) (by norm_num) with ⟨N0, hN0⟩
  refine ⟨N0, ?_⟩
  intro N hN
  have hwidth : tensorWidth (Tensor.absorbBoth_n mulTensor X.stream Y.stream N) ≤ (1 / 4 : ℝ) :=
    hN0 N hN
  linarith

theorem mulTensorStateAfter_safeEventually (X Y : MobiusReal) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      (Tensor.absorbBoth_n mulTensor X.stream Y.stream N).HasNoPoleOnBase ∧
        tensorWidth (Tensor.absorbBoth_n mulTensor X.stream Y.stream N) < (1 / 2 : ℝ) := by
  rcases mulTensorStateAfter_width_lt_half_eventually X Y with ⟨N0, hN0⟩
  refine ⟨N0, ?_⟩
  intro N hN
  exact ⟨mulTensorStateAfter_hasNoPoleOnBase X Y N, hN0 N hN⟩

theorem mulTensor_productivity_spec (X Y : MobiusReal) :
    ∃ N, (Tensor.absorbBoth_n mulTensor X.stream Y.stream N).ProductiveOnBase := by
  rcases mulTensorStateAfter_safeEventually X Y with ⟨N0, hN0⟩
  refine ⟨N0, ?_⟩
  exact Tensor.productiveOnBase_of_hasNoPoleOnBase_of_mapsBaseI_of_width_lt_half
    (T := Tensor.absorbBoth_n mulTensor X.stream Y.stream N0)
    (mulTensorStateAfter_hasNoPoleOnBase X Y N0)
    (mulTensorStateAfter_mapsBaseI X Y N0)
    (hN0 N0 le_rfl).2

theorem mulTensor_eventually_emitsDigit (X Y : MobiusReal) :
    ∃ N, (Tensor.absorbBoth_n mulTensor X.stream Y.stream N).EmitsDigit := by
  rcases mulTensor_productivity_spec X Y with ⟨N, hN⟩
  exact ⟨N, hN.2.2⟩

theorem mulTensorStateAfter_absorbX_step
    (X Y : MobiusReal) (N : ℕ)
    (h : (mulTensorStateAfter X Y N).T.oracle = Tensor.EmitDecision.absorb) :
    GeneralTrace.VMStepXY X Y (mulTensorStateAfter X Y N) none
      (mulTensorXStateAfter X Y N) := by
  simpa [mulTensorStateAfter, mulTensorXStateAfter] using
    (GeneralTrace.VMStepXY.absorbX (X := X) (Y := Y) (s := mulTensorStateAfter X Y N) h rfl)

theorem mulTensorXStateAfter_absorbY_step
    (X Y : MobiusReal) (N : ℕ)
    (h : (mulTensorXStateAfter X Y N).T.oracle = Tensor.EmitDecision.absorb) :
    GeneralTrace.VMStepXY X Y (mulTensorXStateAfter X Y N) none
      (mulTensorStateAfter X Y (N + 1)) := by
  simpa [mulTensorStateAfter, mulTensorXStateAfter, Tensor.absorbBoth_n] using
    (GeneralTrace.VMStepXY.absorbY (X := X) (Y := Y) (s := mulTensorXStateAfter X Y N) h rfl)

theorem mulTensor_pair_reachable
    (X Y : MobiusReal) (N : ℕ)
    (hs : GeneralTrace.SafeAt X Y (mulTensorStateAfter X Y N))
    (habs : (mulTensorStateAfter X Y N).T.oracle = Tensor.EmitDecision.absorb)
    (habsX : (mulTensorXStateAfter X Y N).T.oracle = Tensor.EmitDecision.absorb) :
    SafeVMRun X Y (mulTensorStateAfter X Y N) [] (mulTensorStateAfter X Y (N + 1)) := by
  have hstepX : GeneralTrace.VMStepXY X Y (mulTensorStateAfter X Y N) none
      (mulTensorXStateAfter X Y N) :=
    mulTensorStateAfter_absorbX_step X Y N habs
  have hsX : GeneralTrace.SafeAt X Y (mulTensorXStateAfter X Y N) :=
    safe_step (X := X) (Y := Y) hstepX hs
  have hstepY : GeneralTrace.VMStepXY X Y (mulTensorXStateAfter X Y N) none
      (mulTensorStateAfter X Y (N + 1)) :=
    mulTensorXStateAfter_absorbY_step X Y N habsX
  have hsY : GeneralTrace.SafeAt X Y (mulTensorStateAfter X Y (N + 1)) :=
    safe_step (X := X) (Y := Y) hstepY hsX
  exact SafeVMRun.stepNone hstepX hs hsX <|
    SafeVMRun.stepNone hstepY hsX hsY <|
      SafeVMRun.refl _ hsY

theorem mulTensorXStateAfter_reachable
    (X Y : MobiusReal) (N : ℕ)
    (hreach : SafeVMRun X Y mulInitState [] (mulTensorStateAfter X Y N))
    (habs : (mulTensorStateAfter X Y N).T.oracle = Tensor.EmitDecision.absorb) :
    SafeVMRun X Y mulInitState [] (mulTensorXStateAfter X Y N) := by
  have hsN : GeneralTrace.SafeAt X Y (mulTensorStateAfter X Y N) :=
    safe_end_of_safeVMRun X Y hreach
  have hstepX : GeneralTrace.VMStepXY X Y (mulTensorStateAfter X Y N) none
      (mulTensorXStateAfter X Y N) :=
    mulTensorStateAfter_absorbX_step X Y N habs
  have hsX : GeneralTrace.SafeAt X Y (mulTensorXStateAfter X Y N) :=
    safe_step (X := X) (Y := Y) hstepX hsN
  exact safeVMRun_append X Y hreach
    (SafeVMRun.stepNone hstepX hsN hsX (SafeVMRun.refl _ hsX))

theorem mulTensorStateAfter_reachable
    (X Y : MobiusReal) (N : ℕ)
    (habs : ∀ k, k < N →
      (mulTensorStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb)
    (habsX : ∀ k, k < N →
      (mulTensorXStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb) :
    SafeVMRun X Y mulInitState [] (mulTensorStateAfter X Y N) := by
  induction N with
  | zero =>
      simpa [mulInitState, mulTensorStateAfter] using
        (SafeVMRun.refl (X := X) (Y := Y) mulInitState (mulInit_safe X Y))
  | succ N ih =>
      have hrunN : SafeVMRun X Y mulInitState [] (mulTensorStateAfter X Y N) := by
        apply ih
        · intro k hk
          exact habs k (lt_trans hk (Nat.lt_succ_self N))
        · intro k hk
          exact habsX k (lt_trans hk (Nat.lt_succ_self N))
      have hsN : GeneralTrace.SafeAt X Y (mulTensorStateAfter X Y N) :=
        safe_end_of_safeVMRun X Y hrunN
      have hpair : SafeVMRun X Y (mulTensorStateAfter X Y N) []
          (mulTensorStateAfter X Y (N + 1)) :=
        mulTensor_pair_reachable X Y N hsN
          (habs N (Nat.lt_succ_self N))
          (habsX N (Nat.lt_succ_self N))
      exact safeVMRun_append_nil X Y hrunN hpair

theorem mulTensor_prefix_absorb_or_emits
    (X Y : MobiusReal) (N : ℕ) :
    (∃ s : VMState, ∃ d, SafeVMRun X Y mulInitState [d] s) ∨
      ((∀ k, k < N → (mulTensorStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb) ∧
        (∀ k, k < N → (mulTensorXStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb) ∧
        SafeVMRun X Y mulInitState [] (mulTensorStateAfter X Y N)) := by
  induction N with
  | zero =>
      right
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
      · intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
      · simpa [mulInitState, mulTensorStateAfter] using
          (SafeVMRun.refl (X := X) (Y := Y) mulInitState (mulInit_safe X Y))
  | succ N ih =>
      rcases ih with hemit | ⟨habs, habsX, hreachN⟩
      · exact Or.inl hemit
      · have hsN : GeneralTrace.SafeAt X Y (mulTensorStateAfter X Y N) :=
          safe_end_of_safeVMRun X Y hreachN
        cases hstate : (mulTensorStateAfter X Y N).T.oracle with
        | neg =>
            have hEmit : (Tensor.absorbBoth_n mulTensor X.stream Y.stream N).EmitsDigit := by
              exact Or.inl hstate
            rcases vmStepXY_emit_of_emitsDigit X Y (s := mulTensorStateAfter X Y N) hEmit with
              ⟨d, hstep⟩
            have hsN' : GeneralTrace.SafeAt X Y { mulTensorStateAfter X Y N with
                T := (mulTensorStateAfter X Y N).T.emit d } :=
              safe_step (X := X) (Y := Y) hstep hsN
            have hrun : SafeVMRun X Y mulInitState [d]
                { mulTensorStateAfter X Y N with
                    T := (mulTensorStateAfter X Y N).T.emit d } :=
              safeVMRun_append X Y hreachN
                (SafeVMRun.stepSome hstep hsN hsN' (SafeVMRun.refl _ hsN'))
            exact Or.inl ⟨_, d, hrun⟩
        | zero =>
            have hEmit : (Tensor.absorbBoth_n mulTensor X.stream Y.stream N).EmitsDigit := by
              exact Or.inr (Or.inl hstate)
            rcases vmStepXY_emit_of_emitsDigit X Y (s := mulTensorStateAfter X Y N) hEmit with
              ⟨d, hstep⟩
            have hsN' : GeneralTrace.SafeAt X Y { mulTensorStateAfter X Y N with
                T := (mulTensorStateAfter X Y N).T.emit d } :=
              safe_step (X := X) (Y := Y) hstep hsN
            have hrun : SafeVMRun X Y mulInitState [d]
                { mulTensorStateAfter X Y N with
                    T := (mulTensorStateAfter X Y N).T.emit d } :=
              safeVMRun_append X Y hreachN
                (SafeVMRun.stepSome hstep hsN hsN' (SafeVMRun.refl _ hsN'))
            exact Or.inl ⟨_, d, hrun⟩
        | pos =>
            have hEmit : (Tensor.absorbBoth_n mulTensor X.stream Y.stream N).EmitsDigit := by
              exact Or.inr (Or.inr hstate)
            rcases vmStepXY_emit_of_emitsDigit X Y (s := mulTensorStateAfter X Y N) hEmit with
              ⟨d, hstep⟩
            have hsN' : GeneralTrace.SafeAt X Y { mulTensorStateAfter X Y N with
                T := (mulTensorStateAfter X Y N).T.emit d } :=
              safe_step (X := X) (Y := Y) hstep hsN
            have hrun : SafeVMRun X Y mulInitState [d]
                { mulTensorStateAfter X Y N with
                    T := (mulTensorStateAfter X Y N).T.emit d } :=
              safeVMRun_append X Y hreachN
                (SafeVMRun.stepSome hstep hsN hsN' (SafeVMRun.refl _ hsN'))
            exact Or.inl ⟨_, d, hrun⟩
        | absorb =>
            have hreachX : SafeVMRun X Y mulInitState [] (mulTensorXStateAfter X Y N) :=
              mulTensorXStateAfter_reachable X Y N hreachN hstate
            cases hstateX : (mulTensorXStateAfter X Y N).T.oracle with
            | neg =>
                have hEmitX : (mulTensorXStateAfter X Y N).T.EmitsDigit := by
                  exact Or.inl hstateX
                have hsX : GeneralTrace.SafeAt X Y (mulTensorXStateAfter X Y N) :=
                  safe_end_of_safeVMRun X Y hreachX
                rcases vmStepXY_emit_of_emitsDigit X Y (s := mulTensorXStateAfter X Y N) hEmitX with
                  ⟨d, hstep⟩
                have hsX' : GeneralTrace.SafeAt X Y { mulTensorXStateAfter X Y N with
                    T := (mulTensorXStateAfter X Y N).T.emit d } :=
                  safe_step (X := X) (Y := Y) hstep hsX
                have hrun : SafeVMRun X Y mulInitState [d]
                    { mulTensorXStateAfter X Y N with
                        T := (mulTensorXStateAfter X Y N).T.emit d } :=
                  safeVMRun_append X Y hreachX
                    (SafeVMRun.stepSome hstep hsX hsX' (SafeVMRun.refl _ hsX'))
                exact Or.inl ⟨_, d, hrun⟩
            | zero =>
                have hEmitX : (mulTensorXStateAfter X Y N).T.EmitsDigit := by
                  exact Or.inr (Or.inl hstateX)
                have hsX : GeneralTrace.SafeAt X Y (mulTensorXStateAfter X Y N) :=
                  safe_end_of_safeVMRun X Y hreachX
                rcases vmStepXY_emit_of_emitsDigit X Y (s := mulTensorXStateAfter X Y N) hEmitX with
                  ⟨d, hstep⟩
                have hsX' : GeneralTrace.SafeAt X Y { mulTensorXStateAfter X Y N with
                    T := (mulTensorXStateAfter X Y N).T.emit d } :=
                  safe_step (X := X) (Y := Y) hstep hsX
                have hrun : SafeVMRun X Y mulInitState [d]
                    { mulTensorXStateAfter X Y N with
                        T := (mulTensorXStateAfter X Y N).T.emit d } :=
                  safeVMRun_append X Y hreachX
                    (SafeVMRun.stepSome hstep hsX hsX' (SafeVMRun.refl _ hsX'))
                exact Or.inl ⟨_, d, hrun⟩
            | pos =>
                have hEmitX : (mulTensorXStateAfter X Y N).T.EmitsDigit := by
                  exact Or.inr (Or.inr hstateX)
                have hsX : GeneralTrace.SafeAt X Y (mulTensorXStateAfter X Y N) :=
                  safe_end_of_safeVMRun X Y hreachX
                rcases vmStepXY_emit_of_emitsDigit X Y (s := mulTensorXStateAfter X Y N) hEmitX with
                  ⟨d, hstep⟩
                have hsX' : GeneralTrace.SafeAt X Y { mulTensorXStateAfter X Y N with
                    T := (mulTensorXStateAfter X Y N).T.emit d } :=
                  safe_step (X := X) (Y := Y) hstep hsX
                have hrun : SafeVMRun X Y mulInitState [d]
                    { mulTensorXStateAfter X Y N with
                        T := (mulTensorXStateAfter X Y N).T.emit d } :=
                  safeVMRun_append X Y hreachX
                    (SafeVMRun.stepSome hstep hsX hsX' (SafeVMRun.refl _ hsX'))
                exact Or.inl ⟨_, d, hrun⟩
            | absorb =>
                have hpair : SafeVMRun X Y (mulTensorStateAfter X Y N) []
                    (mulTensorStateAfter X Y (N + 1)) :=
                  mulTensor_pair_reachable X Y N hsN hstate hstateX
                have hreachSucc : SafeVMRun X Y mulInitState []
                    (mulTensorStateAfter X Y (N + 1)) :=
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

theorem mulTensor_scheduler_emitsStep
    (X Y : MobiusReal) :
    ∃ s : VMState, ∃ d, SafeVMRun X Y mulInitState [d] s := by
  rcases mulTensor_eventually_emitsDigit X Y with ⟨N, hN⟩
  rcases mulTensor_prefix_absorb_or_emits X Y N with hemit | ⟨habs, habsX, hreachN⟩
  · exact hemit
  · have hsN : GeneralTrace.SafeAt X Y (mulTensorStateAfter X Y N) :=
      safe_end_of_safeVMRun X Y hreachN
    rcases vmStepXY_emit_of_emitsDigit X Y (s := mulTensorStateAfter X Y N) hN with ⟨d, hstep⟩
    have hsN' : GeneralTrace.SafeAt X Y { mulTensorStateAfter X Y N with
        T := (mulTensorStateAfter X Y N).T.emit d } :=
      safe_step (X := X) (Y := Y) hstep hsN
    have hrun : SafeVMRun X Y mulInitState [d]
        { mulTensorStateAfter X Y N with
            T := (mulTensorStateAfter X Y N).T.emit d } :=
      safeVMRun_append X Y hreachN
        (SafeVMRun.stepSome hstep hsN hsN' (SafeVMRun.refl _ hsN'))
    exact ⟨_, d, hrun⟩

theorem mulTensor_run_eventually_emits (X Y : MobiusReal) :
    ∃ fuel, (run X Y fuel mulInitState).1 ≠ [] := by
  rcases mulTensor_scheduler_emitsStep X Y with ⟨s, d, hrun⟩
  rcases Computable.Mobius.safeVMRun_realized_by_run X Y hrun with ⟨fuel, hstate, hds⟩
  refine ⟨fuel, ?_⟩
  intro hnil
  have : ((run X Y fuel mulInitState).1.map digit_to_LFT) = [] := by
    simp [hnil]
  rw [hds] at this
  have hlen := congrArg List.length this
  simp at hlen

private def digitBias : Digit → ℤ
  | .neg => 1
  | .zero => 0
  | .pos => -1

private def digitDecision : Digit → Tensor.EmitDecision
  | .neg => Tensor.EmitDecision.neg
  | .zero => Tensor.EmitDecision.zero
  | .pos => Tensor.EmitDecision.pos

/-- Tensor representing the affine product `(u : ℝ) * (M x * N y) + v`. -/
def affineMulTensor (u v : ℤ) (M N : LFT) : Tensor where
  a := u * M.a * N.a + v * M.c * N.c
  b := u * M.a * N.b + v * M.c * N.d
  c := u * M.b * N.a + v * M.d * N.c
  d := u * M.b * N.b + v * M.d * N.d
  e := M.c * N.c
  f := M.c * N.d
  g := M.d * N.c
  h := M.d * N.d

@[simp] theorem affineMulTensor_one_zero (M N : LFT) :
    affineMulTensor 1 0 M N = mulPrefixTensor M N := by
  apply Tensor.ext <;> simp [affineMulTensor, mulPrefixTensor]

theorem affineMulTensor_absorbX_absorbY (u v : ℤ) (M N Px Py : LFT) :
    ((affineMulTensor u v M N).absorbX Px).absorbY Py =
      affineMulTensor u v (M.comp Px) (N.comp Py) := by
  apply Tensor.ext <;>
    simp [affineMulTensor, Tensor.absorbX, Tensor.absorbY, LFT.comp] <;> ring

theorem affineMulTensor_absorbX (u v : ℤ) (M N Px : LFT) :
    (affineMulTensor u v M N).absorbX Px = affineMulTensor u v (M.comp Px) N := by
  apply Tensor.ext <;>
    simp [affineMulTensor, Tensor.absorbX, LFT.comp] <;> ring

theorem affineMulTensor_absorbY (u v : ℤ) (M N Py : LFT) :
    (affineMulTensor u v M N).absorbY Py = affineMulTensor u v M (N.comp Py) := by
  apply Tensor.ext <;>
    simp [affineMulTensor, Tensor.absorbY, LFT.comp] <;> ring

theorem absorbBoth_n_affineMulTensor_eq
    (u v : ℤ) (M N : LFT) (sx sy : LFTStream) :
    ∀ K, Tensor.absorbBoth_n (affineMulTensor u v M N) sx sy K =
      affineMulTensor u v (M.comp (pairedPrefix sx K)) (N.comp (pairedPrefix sy K))
  | 0 => by
      apply Tensor.ext <;>
        simp [Tensor.absorbBoth_n, pairedPrefix, affineMulTensor, LFT.comp, LFT.id]
  | K + 1 => by
      calc
        Tensor.absorbBoth_n (affineMulTensor u v M N) sx sy (K + 1)
            = ((Tensor.absorbBoth_n (affineMulTensor u v M N) sx sy K).absorbX (sx K)).absorbY (sy K) := by
                simp [Tensor.absorbBoth_n]
        _ = ((affineMulTensor u v (M.comp (pairedPrefix sx K)) (N.comp (pairedPrefix sy K))).absorbX (sx K)).absorbY (sy K) := by
              rw [absorbBoth_n_affineMulTensor_eq (u := u) (v := v) (M := M) (N := N) (sx := sx) (sy := sy) K]
        _ = affineMulTensor u v ((M.comp (pairedPrefix sx K)).comp (sx K))
              ((N.comp (pairedPrefix sy K)).comp (sy K)) := by
                simpa using affineMulTensor_absorbX_absorbY
                  u v (M.comp (pairedPrefix sx K)) (N.comp (pairedPrefix sy K)) (sx K) (sy K)
        _ = affineMulTensor u v (M.comp (pairedPrefix sx (K + 1))) (N.comp (pairedPrefix sy (K + 1))) := by
              simp [pairedPrefix, LFT.comp_assoc]

theorem affineMulTensor_apply (u v : ℤ) (M N : LFT) (x y : ℝ)
    (hx : ((M.c : ℝ) * x + (M.d : ℝ)) ≠ 0)
    (hy : ((N.c : ℝ) * y + (N.d : ℝ)) ≠ 0) :
    Tensor.apply (affineMulTensor u v M N) x y =
      (u : ℝ) * LFT.apply M x * LFT.apply N y + (v : ℝ) := by
  set AX : ℝ := ((M.a : ℝ) * x + (M.b : ℝ))
  set DX : ℝ := ((M.c : ℝ) * x + (M.d : ℝ))
  set AY : ℝ := ((N.a : ℝ) * y + (N.b : ℝ))
  set DY : ℝ := ((N.c : ℝ) * y + (N.d : ℝ))
  have hDX : DX ≠ 0 := by simpa [DX] using hx
  have hDY : DY ≠ 0 := by simpa [DY] using hy
  have hD : DX * DY ≠ 0 := mul_ne_zero hDX hDY
  have hTensor :
      Tensor.apply (affineMulTensor u v M N) x y =
        ((u : ℝ) * AX * AY + (v : ℝ) * DX * DY) / (DX * DY) := by
    simp [Tensor.apply, affineMulTensor, AX, DX, AY, DY]
    ring_nf
  have hSplit :
      (((u : ℝ) * AX * AY + (v : ℝ) * DX * DY) / (DX * DY)) =
        ((u : ℝ) * AX * AY) / (DX * DY) + (v : ℝ) := by
    field_simp [hD]
  have hProd :
      ((u : ℝ) * AX * AY) / (DX * DY) =
        (u : ℝ) * (AX / DX) * (AY / DY) := by
    field_simp [hDX, hDY]
  calc
    Tensor.apply (affineMulTensor u v M N) x y
        = ((u : ℝ) * AX * AY + (v : ℝ) * DX * DY) / (DX * DY) := hTensor
    _ = ((u : ℝ) * AX * AY) / (DX * DY) + (v : ℝ) := hSplit
    _ = (u : ℝ) * (AX / DX) * (AY / DY) + (v : ℝ) := by rw [hProd]
    _ = (u : ℝ) * LFT.apply M x * LFT.apply N y + (v : ℝ) := by
          simp [LFT.apply, AX, DX, AY, DY]

theorem affineMulTensor_hasNoPoleOnBase (u v : ℤ) (M N : LFT)
    (hM : M.NoPoleOnBase) (hN : N.NoPoleOnBase) :
    (affineMulTensor u v M N).HasNoPoleOnBase := by
  intro x hx y hy
  have hMx := LFT.denom_ne_zero_of_NoPoleOnBase M hx hM
  have hNy := LFT.denom_ne_zero_of_NoPoleOnBase N hy hN
  intro h0
  set AX : ℝ := ((M.c : ℝ) * x + (M.d : ℝ))
  set AY : ℝ := ((N.c : ℝ) * y + (N.d : ℝ))
  have h0' : AX * AY = 0 := by
    subst AX AY
    convert h0 using 1
    simp [Tensor.denAt, affineMulTensor]
    ring_nf
  rcases mul_eq_zero.mp h0' with hX | hY
  · exact hMx hX
  · exact hNy hY

theorem affineMulTensor_emit_digit (u v : ℤ) (M N : LFT) (d : Digit) :
    (affineMulTensor u v M N).emit (digit_to_LFT d) =
      affineMulTensor (2 * u) (2 * v + digitBias d) M N := by
  cases d <;> apply Tensor.ext <;>
    simp [affineMulTensor, digitBias, digit_to_LFT, digitNeg, digitZero, digitPos,
      Tensor.emit] <;> ring_nf

theorem mulTensorStateAfter_emit_eq_affineMulTensor
    (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    (mulTensorStateAfter X Y N).T.emit (digit_to_LFT d) =
      affineMulTensor 2 (digitBias d) (pairedPrefix X.stream N) (pairedPrefix Y.stream N) := by
  rw [mulTensorStateAfter, absorbBoth_n_mulTensor_eq, ← affineMulTensor_one_zero]
  simpa using affineMulTensor_emit_digit 1 0 (pairedPrefix X.stream N) (pairedPrefix Y.stream N) d

theorem mulTensorXStateAfter_emit_eq_affineMulTensor
    (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    (mulTensorXStateAfter X Y N).T.emit (digit_to_LFT d) =
      affineMulTensor 2 (digitBias d)
        ((pairedPrefix X.stream N).comp (X.stream N))
        (pairedPrefix Y.stream N) := by
  rw [mulTensorXStateAfter_eq_mulPrefixTensor, ← affineMulTensor_one_zero]
  simpa using affineMulTensor_emit_digit
    1 0 ((pairedPrefix X.stream N).comp (X.stream N)) (pairedPrefix Y.stream N) d

def mulResidualStateAfter (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) : VMState where
  T := Tensor.absorbBoth_n
    ((mulTensorStateAfter X Y N).T.emit (digit_to_LFT d))
    (MobiusReal.drop X N).stream (MobiusReal.drop Y N).stream K
  idx_x := N + K
  idx_y := N + K
  absorb_x_next := true

def mulResidualXStateAfter (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) : VMState where
  T := (mulResidualStateAfter X Y N d K).T.absorbX ((MobiusReal.drop X N).stream K)
  idx_x := N + K + 1
  idx_y := N + K
  absorb_x_next := false

@[simp] theorem mulResidualStateAfter_zero (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    mulResidualStateAfter X Y N d 0 =
      { mulTensorStateAfter X Y N with
          T := (mulTensorStateAfter X Y N).T.emit (digit_to_LFT d) } := by
  simp [mulResidualStateAfter, mulTensorStateAfter, Tensor.absorbBoth_n]

theorem mulResidualStateAfter_eq_affineMulTensor
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    (mulResidualStateAfter X Y N d K).T =
      affineMulTensor 2 (digitBias d)
        ((pairedPrefix X.stream N).comp (pairedPrefix (MobiusReal.drop X N).stream K))
        ((pairedPrefix Y.stream N).comp (pairedPrefix (MobiusReal.drop Y N).stream K)) := by
  unfold mulResidualStateAfter
  rw [mulTensorStateAfter_emit_eq_affineMulTensor]
  simpa [LFT.comp_assoc] using
    absorbBoth_n_affineMulTensor_eq
      2 (digitBias d)
      (pairedPrefix X.stream N) (pairedPrefix Y.stream N)
      (MobiusReal.drop X N).stream (MobiusReal.drop Y N).stream K

theorem mulResidualStateAfter_eq_affineMulTensor'
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    (mulResidualStateAfter X Y N d K).T =
      affineMulTensor 2 (digitBias d)
        (pairedPrefix X.stream (N + K))
        (pairedPrefix Y.stream (N + K)) := by
  rw [mulResidualStateAfter_eq_affineMulTensor]
  simp [MobiusReal.drop, pairedPrefix_append_shift]

theorem mulResidualXStateAfter_eq_affineMulTensor
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    (mulResidualXStateAfter X Y N d K).T =
      affineMulTensor 2 (digitBias d)
        (pairedPrefix X.stream (N + K + 1))
        (pairedPrefix Y.stream (N + K)) := by
  rw [mulResidualXStateAfter, mulResidualStateAfter_eq_affineMulTensor']
  have hdrop : (MobiusReal.drop X N).stream K = X.stream (N + K) := by
    simp [MobiusReal.drop, Nat.add_comm]
  rw [hdrop, affineMulTensor_absorbX]
  simp [pairedPrefix]

theorem mulResidualStateAfter_hasNoPoleOnBase
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    (mulResidualStateAfter X Y N d K).T.HasNoPoleOnBase := by
  rw [mulResidualStateAfter_eq_affineMulTensor']
  exact affineMulTensor_hasNoPoleOnBase 2 (digitBias d)
    (pairedPrefix X.stream (N + K)) (pairedPrefix Y.stream (N + K))
    (pairedPrefix_noPoleOnBase X (N + K))
    (pairedPrefix_noPoleOnBase Y (N + K))

theorem mulResidualXStateAfter_hasNoPoleOnBase
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) :
    (mulResidualXStateAfter X Y N d K).T.HasNoPoleOnBase := by
  rw [mulResidualXStateAfter_eq_affineMulTensor]
  exact affineMulTensor_hasNoPoleOnBase 2 (digitBias d)
    (pairedPrefix X.stream (N + K + 1)) (pairedPrefix Y.stream (N + K))
    (pairedPrefix_noPoleOnBase X (N + K + 1))
    (pairedPrefix_noPoleOnBase Y (N + K))

theorem mulTensorStateAfter_emit_hasNoPoleOnBase
    (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    ({ mulTensorStateAfter X Y N with
        T := (mulTensorStateAfter X Y N).T.emit (digit_to_LFT d) }).T.HasNoPoleOnBase := by
  simpa [mulResidualStateAfter_zero] using mulResidualStateAfter_hasNoPoleOnBase X Y N d 0

theorem mulTensorXStateAfter_emit_hasNoPoleOnBase
    (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    ({ mulTensorXStateAfter X Y N with
        T := (mulTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }).T.HasNoPoleOnBase := by
  rw [mulTensorXStateAfter_emit_eq_affineMulTensor]
  exact affineMulTensor_hasNoPoleOnBase 2 (digitBias d)
    ((pairedPrefix X.stream N).comp (X.stream N))
    (pairedPrefix Y.stream N)
    (by simpa [pairedPrefix] using pairedPrefix_noPoleOnBase X (N + 1))
    (pairedPrefix_noPoleOnBase Y N)

theorem mulResidualStateAfter_apply
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ) {x y : ℝ}
    (hx : x ∈ baseI) (hy : y ∈ baseI) :
    Tensor.apply (mulResidualStateAfter X Y N d K).T x y =
      (2 : ℝ) * LFT.apply (pairedPrefix X.stream (N + K)) x *
        LFT.apply (pairedPrefix Y.stream (N + K)) y + (digitBias d : ℝ) := by
  rw [mulResidualStateAfter_eq_affineMulTensor']
  exact affineMulTensor_apply 2 (digitBias d)
    (pairedPrefix X.stream (N + K)) (pairedPrefix Y.stream (N + K)) x y
    (pairedPrefix_denom_ne_zero X (N + K) hx)
    (pairedPrefix_denom_ne_zero Y (N + K) hy)

theorem mulResidualStateAfter_diff_lt
    (X Y : MobiusReal) (N : ℕ) (d : Digit) {ε : ℝ} (hε : 0 < ε) :
    ∃ K0 : ℕ, ∀ K ≥ K0, ∀ x ∈ baseI, ∀ w ∈ baseI, ∀ y ∈ baseI, ∀ z ∈ baseI,
      |Tensor.apply (mulResidualStateAfter X Y N d K).T x y -
        Tensor.apply (mulResidualStateAfter X Y N d K).T w z| < ε := by
  have hε4 : 0 < ε / 4 := by linarith
  rcases X.contractive.shrinks_to_zero (ε / 4) hε4 with ⟨NX, hNX⟩
  rcases Y.contractive.shrinks_to_zero (ε / 4) hε4 with ⟨NY, hNY⟩
  refine ⟨max NX NY + 1, ?_⟩
  intro K hK x hx w hw y hy z hz
  have hKN : K ≤ N + K := by omega
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
          |LFT.apply (partialComp X.stream n) x - LFT.apply (partialComp X.stream n) w| < ε / 4 := by
        simpa [partialComp] using hNX n hnX 0 x hx w hw
      have hdy0 :
          |LFT.apply (partialComp Y.stream n) y - LFT.apply (partialComp Y.stream n) z| < ε / 4 := by
        simpa [partialComp] using hNY n hnY 0 y hy z hz
      have hdx :
          |LFT.apply (pairedPrefix X.stream (N + K)) x - LFT.apply (pairedPrefix X.stream (N + K)) w| < ε / 4 := by
        rw [hsum, pairedPrefix_eq_partialComp]
        exact hdx0
      have hdy :
          |LFT.apply (pairedPrefix Y.stream (N + K)) y - LFT.apply (pairedPrefix Y.stream (N + K)) z| < ε / 4 := by
        rw [hsum, pairedPrefix_eq_partialComp]
        exact hdy0
      have hXw : LFT.apply (pairedPrefix X.stream (N + K)) w ∈ baseI :=
        pairedPrefix_maps_base X (N + K) hw
      have hYy : LFT.apply (pairedPrefix Y.stream (N + K)) y ∈ baseI :=
        pairedPrefix_maps_base Y (N + K) hy
      rw [mulResidualStateAfter_apply X Y N d K hx hy,
        mulResidualStateAfter_apply X Y N d K hw hz]
      have hsplit :
          |(2 : ℝ) * LFT.apply (pairedPrefix X.stream (N + K)) x *
              LFT.apply (pairedPrefix Y.stream (N + K)) y + (digitBias d : ℝ) -
            ((2 : ℝ) * LFT.apply (pairedPrefix X.stream (N + K)) w *
              LFT.apply (pairedPrefix Y.stream (N + K)) z + (digitBias d : ℝ))|
            ≤ (2 : ℝ) *
              (|LFT.apply (pairedPrefix X.stream (N + K)) x -
                  LFT.apply (pairedPrefix X.stream (N + K)) w| +
                |LFT.apply (pairedPrefix Y.stream (N + K)) y -
                  LFT.apply (pairedPrefix Y.stream (N + K)) z|) := by
        calc
          |(2 : ℝ) * LFT.apply (pairedPrefix X.stream (N + K)) x *
                LFT.apply (pairedPrefix Y.stream (N + K)) y + (digitBias d : ℝ) -
              ((2 : ℝ) * LFT.apply (pairedPrefix X.stream (N + K)) w *
                LFT.apply (pairedPrefix Y.stream (N + K)) z + (digitBias d : ℝ))|
              = |(2 : ℝ) *
                  (LFT.apply (pairedPrefix X.stream (N + K)) x *
                    LFT.apply (pairedPrefix Y.stream (N + K)) y -
                    LFT.apply (pairedPrefix X.stream (N + K)) w *
                      LFT.apply (pairedPrefix Y.stream (N + K)) z)| := by
                    ring_nf
          _ = (2 : ℝ) *
                |LFT.apply (pairedPrefix X.stream (N + K)) x *
                    LFT.apply (pairedPrefix Y.stream (N + K)) y -
                    LFT.apply (pairedPrefix X.stream (N + K)) w *
                      LFT.apply (pairedPrefix Y.stream (N + K)) z| := by
                    simp [abs_mul]
          _ ≤ (2 : ℝ) *
                (|LFT.apply (pairedPrefix X.stream (N + K)) x -
                    LFT.apply (pairedPrefix X.stream (N + K)) w| +
                  |LFT.apply (pairedPrefix Y.stream (N + K)) y -
                    LFT.apply (pairedPrefix Y.stream (N + K)) z|) := by
                    gcongr
                    exact mul_diff_le_sum_of_mem_baseI hYy hXw
      have hsum' :
          (2 : ℝ) *
            (|LFT.apply (pairedPrefix X.stream (N + K)) x -
                LFT.apply (pairedPrefix X.stream (N + K)) w| +
              |LFT.apply (pairedPrefix Y.stream (N + K)) y -
                LFT.apply (pairedPrefix Y.stream (N + K)) z|) < ε := by
        nlinarith
      exact lt_of_le_of_lt hsplit hsum'

theorem mulResidualStateAfter_width_le_eventually
    (X Y : MobiusReal) (N : ℕ) (d : Digit) {ε : ℝ} (hε : 0 < ε) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      tensorWidth (mulResidualStateAfter X Y N d K).T ≤ ε := by
  rcases mulResidualStateAfter_diff_lt X Y N d hε with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  unfold tensorWidth
  exact csSup_le
    (Tensor.widthSet_nonempty (mulResidualStateAfter X Y N d K).T)
    (by
      intro r hr
      rcases hr with ⟨x, y, w, z, hx, hy, hw, hz, rfl⟩
      exact le_of_lt (hK0 K hK x hx w hw y hy z hz))

theorem mulResidualStateAfter_width_lt_half_eventually
    (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      tensorWidth (mulResidualStateAfter X Y N d K).T < (1 / 2 : ℝ) := by
  rcases mulResidualStateAfter_width_le_eventually X Y N d
    (ε := (1 / 4 : ℝ)) (by norm_num) with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  have hwidth : tensorWidth (mulResidualStateAfter X Y N d K).T ≤ (1 / 4 : ℝ) := hK0 K hK
  linarith

theorem mulResidualStateAfter_safeEventually
    (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (mulResidualStateAfter X Y N d K).T.HasNoPoleOnBase ∧
        tensorWidth (mulResidualStateAfter X Y N d K).T < (1 / 2 : ℝ) := by
  rcases mulResidualStateAfter_width_lt_half_eventually X Y N d with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  exact ⟨mulResidualStateAfter_hasNoPoleOnBase X Y N d K, hK0 K hK⟩

theorem Tensor.emit_mapsBaseI_of_oracle
    (T : Tensor) (d : Digit)
    (hOldNoPole : T.HasNoPoleOnBase)
    (hNewNoPole : (T.emit (digit_to_LFT d)).HasNoPoleOnBase)
    (horacle : T.oracle = digitDecision d) :
    (T.emit (digit_to_LFT d)).MapsBaseI := by
  intro x hx y hy
  let T' : Tensor := T.emit (digit_to_LFT d)
  have hdenOld : Tensor.denAt T x y ≠ 0 := hOldNoPole x hx y hy
  have hdenNew : Tensor.denAt T' x y ≠ 0 := by
    simpa [T'] using hNewNoPole x hx y hy
  cases d with
  | neg =>
      have hold : -1 ≤ Tensor.apply T x y ∧ Tensor.apply T x y ≤ 0 := by
        simpa [digitDecision] using Tensor.emitNeg_sound (T := T)
          (x := x) (y := y) hx.1 hx.2 hy.1 hy.2 horacle
      have hlft : ((digitNeg.c : ℝ) * Tensor.valueAt T' x y + (digitNeg.d : ℝ)) ≠ 0 := by
        simp [digitNeg]
      have hEq : Tensor.apply T x y = LFT.apply digitNeg (Tensor.apply T' x y) := by
        simpa [Tensor.valueAt, T'] using
          (Tensor.emit_invariant (T := T) (D := digitNeg)
            (x := x) (y := y) hdenNew hdenOld hlft)
      constructor
      · have heq : Tensor.apply T x y = ((Tensor.apply T' x y) - 1) / 2 := by
          simpa [digitNeg, LFT.apply] using hEq
        nlinarith [hold.1, heq]
      · have heq : Tensor.apply T x y = ((Tensor.apply T' x y) - 1) / 2 := by
          simpa [digitNeg, LFT.apply] using hEq
        nlinarith [hold.2, heq]
  | zero =>
      have hold : (-1 / 2 : ℝ) ≤ Tensor.apply T x y ∧ Tensor.apply T x y ≤ (1 / 2 : ℝ) := by
        simpa [digitDecision] using Tensor.emitZero_sound (T := T)
          (x := x) (y := y) hx.1 hx.2 hy.1 hy.2 horacle
      have hlft : ((digitZero.c : ℝ) * Tensor.valueAt T' x y + (digitZero.d : ℝ)) ≠ 0 := by
        simp [digitZero]
      have hEq : Tensor.apply T x y = LFT.apply digitZero (Tensor.apply T' x y) := by
        simpa [Tensor.valueAt, T'] using
          (Tensor.emit_invariant (T := T) (D := digitZero)
            (x := x) (y := y) hdenNew hdenOld hlft)
      constructor
      · have heq : Tensor.apply T x y = (Tensor.apply T' x y) / 2 := by
          simpa [digitZero, LFT.apply] using hEq
        nlinarith [hold.1, heq]
      · have heq : Tensor.apply T x y = (Tensor.apply T' x y) / 2 := by
          simpa [digitZero, LFT.apply] using hEq
        nlinarith [hold.2, heq]
  | pos =>
      have hold : 0 ≤ Tensor.apply T x y ∧ Tensor.apply T x y ≤ 1 := by
        simpa [digitDecision] using Tensor.emitPos_sound (T := T)
          (x := x) (y := y) hx.1 hx.2 hy.1 hy.2 horacle
      have hlft : ((digitPos.c : ℝ) * Tensor.valueAt T' x y + (digitPos.d : ℝ)) ≠ 0 := by
        simp [digitPos]
      have hEq : Tensor.apply T x y = LFT.apply digitPos (Tensor.apply T' x y) := by
        simpa [Tensor.valueAt, T'] using
          (Tensor.emit_invariant (T := T) (D := digitPos)
            (x := x) (y := y) hdenNew hdenOld hlft)
      constructor
      · have heq : Tensor.apply T x y = ((Tensor.apply T' x y) + 1) / 2 := by
          simpa [digitPos, LFT.apply] using hEq
        nlinarith [hold.1, heq]
      · have heq : Tensor.apply T x y = ((Tensor.apply T' x y) + 1) / 2 := by
          simpa [digitPos, LFT.apply] using hEq
        nlinarith [hold.2, heq]

theorem mulTensorStateAfter_emit_mapsBaseI_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (mulTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      { mulTensorStateAfter X Y N with
          T := (mulTensorStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ({ mulTensorStateAfter X Y N with
        T := (mulTensorStateAfter X Y N).T.emit (digit_to_LFT d) }).T.MapsBaseI := by
  cases d with
  | neg =>
      have horacle :
          (mulTensorStateAfter X Y N).T.oracle = Tensor.EmitDecision.neg := by
        exact GeneralTrace.oracle_eq_of_step_neg X Y (by simpa [digit_to_LFT] using hstep)
      simpa [digitDecision, digit_to_LFT] using
        (Tensor.emit_mapsBaseI_of_oracle
          (T := (mulTensorStateAfter X Y N).T)
          (d := .neg)
          (mulTensorStateAfter_hasNoPoleOnBase X Y N)
          (mulTensorStateAfter_emit_hasNoPoleOnBase X Y N .neg)
          horacle)
  | zero =>
      have horacle :
          (mulTensorStateAfter X Y N).T.oracle = Tensor.EmitDecision.zero := by
        exact GeneralTrace.oracle_eq_of_step_zero X Y (by simpa [digit_to_LFT] using hstep)
      simpa [digitDecision, digit_to_LFT] using
        (Tensor.emit_mapsBaseI_of_oracle
          (T := (mulTensorStateAfter X Y N).T)
          (d := .zero)
          (mulTensorStateAfter_hasNoPoleOnBase X Y N)
          (mulTensorStateAfter_emit_hasNoPoleOnBase X Y N .zero)
          horacle)
  | pos =>
      have horacle :
          (mulTensorStateAfter X Y N).T.oracle = Tensor.EmitDecision.pos := by
        exact GeneralTrace.oracle_eq_of_step_pos X Y (by simpa [digit_to_LFT] using hstep)
      simpa [digitDecision, digit_to_LFT] using
        (Tensor.emit_mapsBaseI_of_oracle
          (T := (mulTensorStateAfter X Y N).T)
          (d := .pos)
          (mulTensorStateAfter_hasNoPoleOnBase X Y N)
          (mulTensorStateAfter_emit_hasNoPoleOnBase X Y N .pos)
          horacle)

theorem mulTensorXStateAfter_emit_mapsBaseI_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (mulTensorXStateAfter X Y N)
      (some (digit_to_LFT d))
      { mulTensorXStateAfter X Y N with
          T := (mulTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ({ mulTensorXStateAfter X Y N with
        T := (mulTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }).T.MapsBaseI := by
  cases d with
  | neg =>
      have horacle :
          (mulTensorXStateAfter X Y N).T.oracle = Tensor.EmitDecision.neg := by
        exact GeneralTrace.oracle_eq_of_step_neg X Y (by simpa [digit_to_LFT] using hstep)
      simpa [digitDecision, digit_to_LFT] using
        (Tensor.emit_mapsBaseI_of_oracle
          (T := (mulTensorXStateAfter X Y N).T)
          (d := .neg)
          (mulTensorXStateAfter_hasNoPoleOnBase X Y N)
          (mulTensorXStateAfter_emit_hasNoPoleOnBase X Y N .neg)
          horacle)
  | zero =>
      have horacle :
          (mulTensorXStateAfter X Y N).T.oracle = Tensor.EmitDecision.zero := by
        exact GeneralTrace.oracle_eq_of_step_zero X Y (by simpa [digit_to_LFT] using hstep)
      simpa [digitDecision, digit_to_LFT] using
        (Tensor.emit_mapsBaseI_of_oracle
          (T := (mulTensorXStateAfter X Y N).T)
          (d := .zero)
          (mulTensorXStateAfter_hasNoPoleOnBase X Y N)
          (mulTensorXStateAfter_emit_hasNoPoleOnBase X Y N .zero)
          horacle)
  | pos =>
      have horacle :
          (mulTensorXStateAfter X Y N).T.oracle = Tensor.EmitDecision.pos := by
        exact GeneralTrace.oracle_eq_of_step_pos X Y (by simpa [digit_to_LFT] using hstep)
      simpa [digitDecision, digit_to_LFT] using
        (Tensor.emit_mapsBaseI_of_oracle
          (T := (mulTensorXStateAfter X Y N).T)
          (d := .pos)
          (mulTensorXStateAfter_hasNoPoleOnBase X Y N)
          (mulTensorXStateAfter_emit_hasNoPoleOnBase X Y N .pos)
          horacle)

theorem mulResidualStateAfter_zero_mapsBaseI_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (mulTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      { mulTensorStateAfter X Y N with
          T := (mulTensorStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    (mulResidualStateAfter X Y N d 0).T.MapsBaseI := by
  simpa [mulResidualStateAfter_zero] using
    mulTensorStateAfter_emit_mapsBaseI_of_step X Y N d hstep

theorem mulResidualStateAfter_one_eq_from_Xstep
    (X Y : MobiusReal) (N : ℕ) (d : Digit) :
    (mulResidualStateAfter X Y N d 1).T =
      ({ mulTensorXStateAfter X Y N with
          T := (mulTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }).T.absorbY (Y.stream N) := by
  rw [mulResidualStateAfter_eq_affineMulTensor']
  rw [mulTensorXStateAfter_emit_eq_affineMulTensor]
  rw [affineMulTensor_absorbY]
  simp [pairedPrefix]

theorem mulResidualStateAfter_mapsBaseI_pair_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (mulTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      { mulTensorStateAfter X Y N with
          T := (mulTensorStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∀ K,
      (mulResidualStateAfter X Y N d K).T.MapsBaseI ∧
      (mulResidualXStateAfter X Y N d K).T.MapsBaseI
  | 0 => by
      refine ⟨mulResidualStateAfter_zero_mapsBaseI_of_step X Y N d hstep, ?_⟩
      exact Tensor.mapsBaseI_absorbX
        ((mulResidualStateAfter X Y N d 0).T)
        ((MobiusReal.drop X N).stream 0)
        (mulResidualStateAfter_zero_mapsBaseI_of_step X Y N d hstep)
        (mulResidualStateAfter_hasNoPoleOnBase X Y N d 0)
        (mulResidualXStateAfter_hasNoPoleOnBase X Y N d 0)
        (IsContractive.maps_base_step (MobiusReal.drop X N).contractive 0)
        (IsContractive.no_poles_step (MobiusReal.drop X N).contractive 0)
  | K + 1 => by
      rcases mulResidualStateAfter_mapsBaseI_pair_of_step X Y N d hstep K with
        ⟨hStateK, hXK⟩
      have hStateSucc :
          (mulResidualStateAfter X Y N d (K + 1)).T.MapsBaseI := by
        have hEq :
            (mulResidualStateAfter X Y N d (K + 1)).T =
              (mulResidualXStateAfter X Y N d K).T.absorbY ((MobiusReal.drop Y N).stream K) := by
          simp [mulResidualStateAfter, mulResidualXStateAfter, Tensor.absorbBoth_n]
        rw [hEq]
        exact Tensor.mapsBaseI_absorbY
          ((mulResidualXStateAfter X Y N d K).T)
          ((MobiusReal.drop Y N).stream K)
          hXK
          (mulResidualXStateAfter_hasNoPoleOnBase X Y N d K)
          (mulResidualStateAfter_hasNoPoleOnBase X Y N d (K + 1))
          (IsContractive.maps_base_step (MobiusReal.drop Y N).contractive K)
          (IsContractive.no_poles_step (MobiusReal.drop Y N).contractive K)
      have hXSucc :
          (mulResidualXStateAfter X Y N d (K + 1)).T.MapsBaseI := by
        exact Tensor.mapsBaseI_absorbX
          ((mulResidualStateAfter X Y N d (K + 1)).T)
          ((MobiusReal.drop X N).stream (K + 1))
          hStateSucc
          (mulResidualStateAfter_hasNoPoleOnBase X Y N d (K + 1))
          (mulResidualXStateAfter_hasNoPoleOnBase X Y N d (K + 1))
          (IsContractive.maps_base_step (MobiusReal.drop X N).contractive (K + 1))
          (IsContractive.no_poles_step (MobiusReal.drop X N).contractive (K + 1))
      exact ⟨hStateSucc, hXSucc⟩

theorem mulResidualStateAfter_mapsBaseI_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (mulTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      { mulTensorStateAfter X Y N with
          T := (mulTensorStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∀ K, (mulResidualStateAfter X Y N d K).T.MapsBaseI :=
  fun K => (mulResidualStateAfter_mapsBaseI_pair_of_step X Y N d hstep K).1

theorem mulResidualStateAfter_mapsBaseI_pair_of_Xstep
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (mulTensorXStateAfter X Y N)
      (some (digit_to_LFT d))
      { mulTensorXStateAfter X Y N with
          T := (mulTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∀ K,
      (mulResidualStateAfter X Y N d (K + 1)).T.MapsBaseI ∧
      (mulResidualXStateAfter X Y N d (K + 1)).T.MapsBaseI
  | 0 => by
      let s' : VMState := { mulTensorXStateAfter X Y N with
        T := (mulTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }
      have hState1 :
          (mulResidualStateAfter X Y N d 1).T.MapsBaseI := by
        have hNoPole1 : (s'.T.absorbY (Y.stream N)).HasNoPoleOnBase := by
          rw [← mulResidualStateAfter_one_eq_from_Xstep X Y N d]
          exact mulResidualStateAfter_hasNoPoleOnBase X Y N d 1
        rw [mulResidualStateAfter_one_eq_from_Xstep]
        exact Tensor.mapsBaseI_absorbY s'.T (Y.stream N)
          (mulTensorXStateAfter_emit_mapsBaseI_of_step X Y N d hstep)
          (by simpa [s'] using mulTensorXStateAfter_emit_hasNoPoleOnBase X Y N d)
          hNoPole1
          (IsContractive.maps_base_step Y.contractive N)
          (IsContractive.no_poles_step Y.contractive N)
      refine ⟨hState1, ?_⟩
      exact Tensor.mapsBaseI_absorbX
        ((mulResidualStateAfter X Y N d 1).T)
        ((MobiusReal.drop X N).stream 1)
        hState1
        (mulResidualStateAfter_hasNoPoleOnBase X Y N d 1)
        (mulResidualXStateAfter_hasNoPoleOnBase X Y N d 1)
        (IsContractive.maps_base_step (MobiusReal.drop X N).contractive 1)
        (IsContractive.no_poles_step (MobiusReal.drop X N).contractive 1)
  | K + 1 => by
      rcases mulResidualStateAfter_mapsBaseI_pair_of_Xstep X Y N d hstep K with
        ⟨hStateK, hXK⟩
      have hStateSucc :
          (mulResidualStateAfter X Y N d (K + 2)).T.MapsBaseI := by
        have hEq :
            (mulResidualStateAfter X Y N d (K + 2)).T =
              (mulResidualXStateAfter X Y N d (K + 1)).T.absorbY
                ((MobiusReal.drop Y N).stream (K + 1)) := by
          simp [mulResidualStateAfter, mulResidualXStateAfter, Tensor.absorbBoth_n]
        rw [hEq]
        exact Tensor.mapsBaseI_absorbY
          ((mulResidualXStateAfter X Y N d (K + 1)).T)
          ((MobiusReal.drop Y N).stream (K + 1))
          hXK
          (mulResidualXStateAfter_hasNoPoleOnBase X Y N d (K + 1))
          (mulResidualStateAfter_hasNoPoleOnBase X Y N d (K + 2))
          (IsContractive.maps_base_step (MobiusReal.drop Y N).contractive (K + 1))
          (IsContractive.no_poles_step (MobiusReal.drop Y N).contractive (K + 1))
      have hXSucc :
          (mulResidualXStateAfter X Y N d (K + 2)).T.MapsBaseI := by
        exact Tensor.mapsBaseI_absorbX
          ((mulResidualStateAfter X Y N d (K + 2)).T)
          ((MobiusReal.drop X N).stream (K + 2))
          hStateSucc
          (mulResidualStateAfter_hasNoPoleOnBase X Y N d (K + 2))
          (mulResidualXStateAfter_hasNoPoleOnBase X Y N d (K + 2))
          (IsContractive.maps_base_step (MobiusReal.drop X N).contractive (K + 2))
          (IsContractive.no_poles_step (MobiusReal.drop X N).contractive (K + 2))
      exact ⟨hStateSucc, hXSucc⟩

theorem mulResidualStateAfter_emitsDigit_eventually_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (mulTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      { mulTensorStateAfter X Y N with
          T := (mulTensorStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∃ K0 : ℕ, ∀ K ≥ K0, (mulResidualStateAfter X Y N d K).T.EmitsDigit := by
  rcases mulResidualStateAfter_safeEventually X Y N d with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  have hsafe := hK0 K hK
  exact Tensor.emitsDigit_of_hasNoPoleOnBase_of_mapsBaseI_of_width_lt_half
    (T := (mulResidualStateAfter X Y N d K).T)
    hsafe.1
    (mulResidualStateAfter_mapsBaseI_of_step X Y N d hstep K)
    hsafe.2

theorem mulResidualStateAfter_productivity_spec_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (mulTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      { mulTensorStateAfter X Y N with
          T := (mulTensorStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∃ K : ℕ, (mulResidualStateAfter X Y N d K).T.ProductiveOnBase := by
  rcases mulResidualStateAfter_safeEventually X Y N d with ⟨Ksafe, hsafe⟩
  refine ⟨Ksafe, ?_⟩
  have hsafe' := hsafe Ksafe le_rfl
  exact Tensor.productiveOnBase_of_hasNoPoleOnBase_of_mapsBaseI_of_width_lt_half
    (T := (mulResidualStateAfter X Y N d Ksafe).T)
    hsafe'.1
    (mulResidualStateAfter_mapsBaseI_of_step X Y N d hstep Ksafe)
    hsafe'.2

theorem mulResidualStateAfter_emitsDigit_eventually_of_Xstep
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (mulTensorXStateAfter X Y N)
      (some (digit_to_LFT d))
      { mulTensorXStateAfter X Y N with
          T := (mulTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∃ K0 : ℕ, ∀ K ≥ K0, (mulResidualStateAfter X Y N d (K + 1)).T.EmitsDigit := by
  rcases mulResidualStateAfter_safeEventually X Y N d with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  have hK' : K + 1 ≥ K0 := le_trans hK (Nat.le_succ _)
  have hsafe := hK0 (K + 1) hK'
  exact Tensor.emitsDigit_of_hasNoPoleOnBase_of_mapsBaseI_of_width_lt_half
    (T := (mulResidualStateAfter X Y N d (K + 1)).T)
    hsafe.1
    ((mulResidualStateAfter_mapsBaseI_pair_of_Xstep X Y N d hstep K).1)
    hsafe.2

theorem mulResidualStateAfter_productivity_spec_of_Xstep
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hstep : GeneralTrace.VMStepXY X Y
      (mulTensorXStateAfter X Y N)
      (some (digit_to_LFT d))
      { mulTensorXStateAfter X Y N with
          T := (mulTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∃ K : ℕ, (mulResidualStateAfter X Y N d (K + 1)).T.ProductiveOnBase := by
  rcases mulResidualStateAfter_safeEventually X Y N d with ⟨Ksafe, hsafe⟩
  refine ⟨Ksafe, ?_⟩
  have hsafe' := hsafe (Ksafe + 1) (Nat.le_succ _)
  exact Tensor.productiveOnBase_of_hasNoPoleOnBase_of_mapsBaseI_of_width_lt_half
    (T := (mulResidualStateAfter X Y N d (Ksafe + 1)).T)
    hsafe'.1
    ((mulResidualStateAfter_mapsBaseI_pair_of_Xstep X Y N d hstep Ksafe).1)
    hsafe'.2

theorem mulResidualStateAfter_absorbX_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (h : (mulResidualStateAfter X Y N d K).T.oracle = Tensor.EmitDecision.absorb) :
    GeneralTrace.VMStepXY X Y (mulResidualStateAfter X Y N d K) none
      (mulResidualXStateAfter X Y N d K) := by
  have hstream : (MobiusReal.drop X N).stream K = X.stream (N + K) := by
    simp [MobiusReal.drop, Nat.add_comm]
  simpa [mulResidualStateAfter, mulResidualXStateAfter, hstream] using
    (GeneralTrace.VMStepXY.absorbX (X := X) (Y := Y)
      (s := mulResidualStateAfter X Y N d K) h rfl)

theorem mulResidualXStateAfter_absorbY_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (h : (mulResidualXStateAfter X Y N d K).T.oracle = Tensor.EmitDecision.absorb) :
    GeneralTrace.VMStepXY X Y (mulResidualXStateAfter X Y N d K) none
      (mulResidualStateAfter X Y N d (K + 1)) := by
  have hstream : (MobiusReal.drop Y N).stream K = Y.stream (N + K) := by
    simp [MobiusReal.drop, Nat.add_comm]
  simpa [mulResidualStateAfter, mulResidualXStateAfter, Tensor.absorbBoth_n, hstream] using
    (GeneralTrace.VMStepXY.absorbY (X := X) (Y := Y)
      (s := mulResidualXStateAfter X Y N d K) h rfl)

theorem mulResidual_pair_reachable
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (hs : GeneralTrace.SafeAt X Y (mulResidualStateAfter X Y N d K))
    (habs : (mulResidualStateAfter X Y N d K).T.oracle = Tensor.EmitDecision.absorb)
    (habsX : (mulResidualXStateAfter X Y N d K).T.oracle = Tensor.EmitDecision.absorb) :
    SafeVMRun X Y (mulResidualStateAfter X Y N d K) []
      (mulResidualStateAfter X Y N d (K + 1)) := by
  have hstepX : GeneralTrace.VMStepXY X Y (mulResidualStateAfter X Y N d K) none
      (mulResidualXStateAfter X Y N d K) :=
    mulResidualStateAfter_absorbX_step X Y N d K habs
  have hsX : GeneralTrace.SafeAt X Y (mulResidualXStateAfter X Y N d K) :=
    safe_step (X := X) (Y := Y) hstepX hs
  have hstepY : GeneralTrace.VMStepXY X Y (mulResidualXStateAfter X Y N d K) none
      (mulResidualStateAfter X Y N d (K + 1)) :=
    mulResidualXStateAfter_absorbY_step X Y N d K habsX
  have hsY : GeneralTrace.SafeAt X Y (mulResidualStateAfter X Y N d (K + 1)) :=
    safe_step (X := X) (Y := Y) hstepY hsX
  exact SafeVMRun.stepNone hstepX hs hsX <|
    SafeVMRun.stepNone hstepY hsX hsY <|
      SafeVMRun.refl _ hsY

theorem mulResidualXStateAfter_reachable
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (hreach : SafeVMRun X Y mulInitState [digit_to_LFT d]
      (mulResidualStateAfter X Y N d K))
    (habs : (mulResidualStateAfter X Y N d K).T.oracle = Tensor.EmitDecision.absorb) :
    SafeVMRun X Y mulInitState [digit_to_LFT d]
      (mulResidualXStateAfter X Y N d K) := by
  have hsK : GeneralTrace.SafeAt X Y (mulResidualStateAfter X Y N d K) :=
    safe_end_of_safeVMRun X Y hreach
  have hstepX : GeneralTrace.VMStepXY X Y (mulResidualStateAfter X Y N d K) none
      (mulResidualXStateAfter X Y N d K) :=
    mulResidualStateAfter_absorbX_step X Y N d K habs
  have hsX : GeneralTrace.SafeAt X Y (mulResidualXStateAfter X Y N d K) :=
    safe_step (X := X) (Y := Y) hstepX hsK
  exact safeVMRun_append X Y hreach
    (SafeVMRun.stepNone hstepX hsK hsX (SafeVMRun.refl _ hsX))

theorem mulResidualStateAfter_reachable
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (hreach0 : SafeVMRun X Y mulInitState [digit_to_LFT d]
      (mulResidualStateAfter X Y N d 0))
    (habs : ∀ k, k < K →
      (mulResidualStateAfter X Y N d k).T.oracle = Tensor.EmitDecision.absorb)
    (habsX : ∀ k, k < K →
      (mulResidualXStateAfter X Y N d k).T.oracle = Tensor.EmitDecision.absorb) :
    SafeVMRun X Y mulInitState [digit_to_LFT d]
      (mulResidualStateAfter X Y N d K) := by
  induction K with
  | zero =>
      simpa using hreach0
  | succ K ih =>
      have hrunK : SafeVMRun X Y mulInitState [digit_to_LFT d]
          (mulResidualStateAfter X Y N d K) := by
        apply ih
        · intro k hk
          exact habs k (lt_trans hk (Nat.lt_succ_self K))
        · intro k hk
          exact habsX k (lt_trans hk (Nat.lt_succ_self K))
      have hsK : GeneralTrace.SafeAt X Y (mulResidualStateAfter X Y N d K) :=
        safe_end_of_safeVMRun X Y hrunK
      have hpair : SafeVMRun X Y (mulResidualStateAfter X Y N d K) []
          (mulResidualStateAfter X Y N d (K + 1)) :=
        mulResidual_pair_reachable X Y N d K hsK
          (habs K (Nat.lt_succ_self K))
          (habsX K (Nat.lt_succ_self K))
      exact safeVMRun_append X Y hrunK hpair

theorem mulResidual_prefix_absorb_or_emits_of_step
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hreach0 : SafeVMRun X Y mulInitState [digit_to_LFT d]
      (mulResidualStateAfter X Y N d 0))
    (K : ℕ) :
    (∃ s : VMState, ∃ d₂, SafeVMRun X Y mulInitState [digit_to_LFT d, d₂] s) ∨
      ((∀ k, k < K → (mulResidualStateAfter X Y N d k).T.oracle = Tensor.EmitDecision.absorb) ∧
        (∀ k, k < K → (mulResidualXStateAfter X Y N d k).T.oracle = Tensor.EmitDecision.absorb) ∧
        SafeVMRun X Y mulInitState [digit_to_LFT d]
          (mulResidualStateAfter X Y N d K)) := by
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
      · have hsK : GeneralTrace.SafeAt X Y (mulResidualStateAfter X Y N d K) :=
          safe_end_of_safeVMRun X Y hreachK
        cases hstate : (mulResidualStateAfter X Y N d K).T.oracle with
        | neg =>
            have hEmit : (mulResidualStateAfter X Y N d K).T.EmitsDigit := by
              exact Or.inl hstate
            rcases vmStepXY_emit_of_emitsDigit X Y
              (s := mulResidualStateAfter X Y N d K) hEmit with ⟨d₂, hstep⟩
            have hsK' : GeneralTrace.SafeAt X Y { mulResidualStateAfter X Y N d K with
                T := (mulResidualStateAfter X Y N d K).T.emit d₂ } :=
              safe_step (X := X) (Y := Y) hstep hsK
            have hrun : SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
                { mulResidualStateAfter X Y N d K with
                    T := (mulResidualStateAfter X Y N d K).T.emit d₂ } :=
              safeVMRun_append X Y hreachK
                (SafeVMRun.stepSome hstep hsK hsK' (SafeVMRun.refl _ hsK'))
            exact Or.inl ⟨_, d₂, hrun⟩
        | zero =>
            have hEmit : (mulResidualStateAfter X Y N d K).T.EmitsDigit := by
              exact Or.inr (Or.inl hstate)
            rcases vmStepXY_emit_of_emitsDigit X Y
              (s := mulResidualStateAfter X Y N d K) hEmit with ⟨d₂, hstep⟩
            have hsK' : GeneralTrace.SafeAt X Y { mulResidualStateAfter X Y N d K with
                T := (mulResidualStateAfter X Y N d K).T.emit d₂ } :=
              safe_step (X := X) (Y := Y) hstep hsK
            have hrun : SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
                { mulResidualStateAfter X Y N d K with
                    T := (mulResidualStateAfter X Y N d K).T.emit d₂ } :=
              safeVMRun_append X Y hreachK
                (SafeVMRun.stepSome hstep hsK hsK' (SafeVMRun.refl _ hsK'))
            exact Or.inl ⟨_, d₂, hrun⟩
        | pos =>
            have hEmit : (mulResidualStateAfter X Y N d K).T.EmitsDigit := by
              exact Or.inr (Or.inr hstate)
            rcases vmStepXY_emit_of_emitsDigit X Y
              (s := mulResidualStateAfter X Y N d K) hEmit with ⟨d₂, hstep⟩
            have hsK' : GeneralTrace.SafeAt X Y { mulResidualStateAfter X Y N d K with
                T := (mulResidualStateAfter X Y N d K).T.emit d₂ } :=
              safe_step (X := X) (Y := Y) hstep hsK
            have hrun : SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
                { mulResidualStateAfter X Y N d K with
                    T := (mulResidualStateAfter X Y N d K).T.emit d₂ } :=
              safeVMRun_append X Y hreachK
                (SafeVMRun.stepSome hstep hsK hsK' (SafeVMRun.refl _ hsK'))
            exact Or.inl ⟨_, d₂, hrun⟩
        | absorb =>
            have hreachX : SafeVMRun X Y mulInitState [digit_to_LFT d]
                (mulResidualXStateAfter X Y N d K) :=
              mulResidualXStateAfter_reachable X Y N d K hreachK hstate
            cases hstateX : (mulResidualXStateAfter X Y N d K).T.oracle with
            | neg =>
                have hEmitX : (mulResidualXStateAfter X Y N d K).T.EmitsDigit := by
                  exact Or.inl hstateX
                have hsX : GeneralTrace.SafeAt X Y (mulResidualXStateAfter X Y N d K) :=
                  safe_end_of_safeVMRun X Y hreachX
                rcases vmStepXY_emit_of_emitsDigit X Y
                  (s := mulResidualXStateAfter X Y N d K) hEmitX with ⟨d₂, hstep⟩
                have hsX' : GeneralTrace.SafeAt X Y { mulResidualXStateAfter X Y N d K with
                    T := (mulResidualXStateAfter X Y N d K).T.emit d₂ } :=
                  safe_step (X := X) (Y := Y) hstep hsX
                have hrun : SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
                    { mulResidualXStateAfter X Y N d K with
                        T := (mulResidualXStateAfter X Y N d K).T.emit d₂ } :=
                  safeVMRun_append X Y hreachX
                    (SafeVMRun.stepSome hstep hsX hsX' (SafeVMRun.refl _ hsX'))
                exact Or.inl ⟨_, d₂, hrun⟩
            | zero =>
                have hEmitX : (mulResidualXStateAfter X Y N d K).T.EmitsDigit := by
                  exact Or.inr (Or.inl hstateX)
                have hsX : GeneralTrace.SafeAt X Y (mulResidualXStateAfter X Y N d K) :=
                  safe_end_of_safeVMRun X Y hreachX
                rcases vmStepXY_emit_of_emitsDigit X Y
                  (s := mulResidualXStateAfter X Y N d K) hEmitX with ⟨d₂, hstep⟩
                have hsX' : GeneralTrace.SafeAt X Y { mulResidualXStateAfter X Y N d K with
                    T := (mulResidualXStateAfter X Y N d K).T.emit d₂ } :=
                  safe_step (X := X) (Y := Y) hstep hsX
                have hrun : SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
                    { mulResidualXStateAfter X Y N d K with
                        T := (mulResidualXStateAfter X Y N d K).T.emit d₂ } :=
                  safeVMRun_append X Y hreachX
                    (SafeVMRun.stepSome hstep hsX hsX' (SafeVMRun.refl _ hsX'))
                exact Or.inl ⟨_, d₂, hrun⟩
            | pos =>
                have hEmitX : (mulResidualXStateAfter X Y N d K).T.EmitsDigit := by
                  exact Or.inr (Or.inr hstateX)
                have hsX : GeneralTrace.SafeAt X Y (mulResidualXStateAfter X Y N d K) :=
                  safe_end_of_safeVMRun X Y hreachX
                rcases vmStepXY_emit_of_emitsDigit X Y
                  (s := mulResidualXStateAfter X Y N d K) hEmitX with ⟨d₂, hstep⟩
                have hsX' : GeneralTrace.SafeAt X Y { mulResidualXStateAfter X Y N d K with
                    T := (mulResidualXStateAfter X Y N d K).T.emit d₂ } :=
                  safe_step (X := X) (Y := Y) hstep hsX
                have hrun : SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
                    { mulResidualXStateAfter X Y N d K with
                        T := (mulResidualXStateAfter X Y N d K).T.emit d₂ } :=
                  safeVMRun_append X Y hreachX
                    (SafeVMRun.stepSome hstep hsX hsX' (SafeVMRun.refl _ hsX'))
                exact Or.inl ⟨_, d₂, hrun⟩
            | absorb =>
                have hpair : SafeVMRun X Y (mulResidualStateAfter X Y N d K) []
                    (mulResidualStateAfter X Y N d (K + 1)) :=
                  mulResidual_pair_reachable X Y N d K hsK hstate hstateX
                have hreachSucc : SafeVMRun X Y mulInitState [digit_to_LFT d]
                    (mulResidualStateAfter X Y N d (K + 1)) :=
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

theorem mulResidual_prefix_absorb_or_emits_of_Xstep
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hreach1 : SafeVMRun X Y mulInitState [digit_to_LFT d]
      (mulResidualStateAfter X Y N d 1))
    (K : ℕ) :
    (∃ s : VMState, ∃ d₂, SafeVMRun X Y mulInitState [digit_to_LFT d, d₂] s) ∨
      ((∀ k, k < K → (mulResidualStateAfter X Y N d (k + 1)).T.oracle =
          Tensor.EmitDecision.absorb) ∧
        (∀ k, k < K → (mulResidualXStateAfter X Y N d (k + 1)).T.oracle =
          Tensor.EmitDecision.absorb) ∧
        SafeVMRun X Y mulInitState [digit_to_LFT d]
          (mulResidualStateAfter X Y N d (K + 1))) := by
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
      · have hsK1 : GeneralTrace.SafeAt X Y (mulResidualStateAfter X Y N d (K + 1)) :=
          safe_end_of_safeVMRun X Y hreachK1
        cases hstate : (mulResidualStateAfter X Y N d (K + 1)).T.oracle with
        | neg =>
            have hEmit : (mulResidualStateAfter X Y N d (K + 1)).T.EmitsDigit := by
              exact Or.inl hstate
            rcases vmStepXY_emit_of_emitsDigit X Y
              (s := mulResidualStateAfter X Y N d (K + 1)) hEmit with ⟨d₂, hstep⟩
            have hsK1' : GeneralTrace.SafeAt X Y
                { mulResidualStateAfter X Y N d (K + 1) with
                    T := (mulResidualStateAfter X Y N d (K + 1)).T.emit d₂ } :=
              safe_step (X := X) (Y := Y) hstep hsK1
            have hrun : SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
                { mulResidualStateAfter X Y N d (K + 1) with
                    T := (mulResidualStateAfter X Y N d (K + 1)).T.emit d₂ } :=
              safeVMRun_append X Y hreachK1
                (SafeVMRun.stepSome hstep hsK1 hsK1' (SafeVMRun.refl _ hsK1'))
            exact Or.inl ⟨_, d₂, hrun⟩
        | zero =>
            have hEmit : (mulResidualStateAfter X Y N d (K + 1)).T.EmitsDigit := by
              exact Or.inr (Or.inl hstate)
            rcases vmStepXY_emit_of_emitsDigit X Y
              (s := mulResidualStateAfter X Y N d (K + 1)) hEmit with ⟨d₂, hstep⟩
            have hsK1' : GeneralTrace.SafeAt X Y
                { mulResidualStateAfter X Y N d (K + 1) with
                    T := (mulResidualStateAfter X Y N d (K + 1)).T.emit d₂ } :=
              safe_step (X := X) (Y := Y) hstep hsK1
            have hrun : SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
                { mulResidualStateAfter X Y N d (K + 1) with
                    T := (mulResidualStateAfter X Y N d (K + 1)).T.emit d₂ } :=
              safeVMRun_append X Y hreachK1
                (SafeVMRun.stepSome hstep hsK1 hsK1' (SafeVMRun.refl _ hsK1'))
            exact Or.inl ⟨_, d₂, hrun⟩
        | pos =>
            have hEmit : (mulResidualStateAfter X Y N d (K + 1)).T.EmitsDigit := by
              exact Or.inr (Or.inr hstate)
            rcases vmStepXY_emit_of_emitsDigit X Y
              (s := mulResidualStateAfter X Y N d (K + 1)) hEmit with ⟨d₂, hstep⟩
            have hsK1' : GeneralTrace.SafeAt X Y
                { mulResidualStateAfter X Y N d (K + 1) with
                    T := (mulResidualStateAfter X Y N d (K + 1)).T.emit d₂ } :=
              safe_step (X := X) (Y := Y) hstep hsK1
            have hrun : SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
                { mulResidualStateAfter X Y N d (K + 1) with
                    T := (mulResidualStateAfter X Y N d (K + 1)).T.emit d₂ } :=
              safeVMRun_append X Y hreachK1
                (SafeVMRun.stepSome hstep hsK1 hsK1' (SafeVMRun.refl _ hsK1'))
            exact Or.inl ⟨_, d₂, hrun⟩
        | absorb =>
            have hreachX1 : SafeVMRun X Y mulInitState [digit_to_LFT d]
                (mulResidualXStateAfter X Y N d (K + 1)) :=
              mulResidualXStateAfter_reachable X Y N d (K + 1) hreachK1 hstate
            cases hstateX : (mulResidualXStateAfter X Y N d (K + 1)).T.oracle with
            | neg =>
                have hEmitX : (mulResidualXStateAfter X Y N d (K + 1)).T.EmitsDigit := by
                  exact Or.inl hstateX
                have hsX1 : GeneralTrace.SafeAt X Y
                    (mulResidualXStateAfter X Y N d (K + 1)) :=
                  safe_end_of_safeVMRun X Y hreachX1
                rcases vmStepXY_emit_of_emitsDigit X Y
                  (s := mulResidualXStateAfter X Y N d (K + 1)) hEmitX with ⟨d₂, hstep⟩
                have hsX1' : GeneralTrace.SafeAt X Y
                    { mulResidualXStateAfter X Y N d (K + 1) with
                        T := (mulResidualXStateAfter X Y N d (K + 1)).T.emit d₂ } :=
                  safe_step (X := X) (Y := Y) hstep hsX1
                have hrun : SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
                    { mulResidualXStateAfter X Y N d (K + 1) with
                        T := (mulResidualXStateAfter X Y N d (K + 1)).T.emit d₂ } :=
                  safeVMRun_append X Y hreachX1
                    (SafeVMRun.stepSome hstep hsX1 hsX1' (SafeVMRun.refl _ hsX1'))
                exact Or.inl ⟨_, d₂, hrun⟩
            | zero =>
                have hEmitX : (mulResidualXStateAfter X Y N d (K + 1)).T.EmitsDigit := by
                  exact Or.inr (Or.inl hstateX)
                have hsX1 : GeneralTrace.SafeAt X Y
                    (mulResidualXStateAfter X Y N d (K + 1)) :=
                  safe_end_of_safeVMRun X Y hreachX1
                rcases vmStepXY_emit_of_emitsDigit X Y
                  (s := mulResidualXStateAfter X Y N d (K + 1)) hEmitX with ⟨d₂, hstep⟩
                have hsX1' : GeneralTrace.SafeAt X Y
                    { mulResidualXStateAfter X Y N d (K + 1) with
                        T := (mulResidualXStateAfter X Y N d (K + 1)).T.emit d₂ } :=
                  safe_step (X := X) (Y := Y) hstep hsX1
                have hrun : SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
                    { mulResidualXStateAfter X Y N d (K + 1) with
                        T := (mulResidualXStateAfter X Y N d (K + 1)).T.emit d₂ } :=
                  safeVMRun_append X Y hreachX1
                    (SafeVMRun.stepSome hstep hsX1 hsX1' (SafeVMRun.refl _ hsX1'))
                exact Or.inl ⟨_, d₂, hrun⟩
            | pos =>
                have hEmitX : (mulResidualXStateAfter X Y N d (K + 1)).T.EmitsDigit := by
                  exact Or.inr (Or.inr hstateX)
                have hsX1 : GeneralTrace.SafeAt X Y
                    (mulResidualXStateAfter X Y N d (K + 1)) :=
                  safe_end_of_safeVMRun X Y hreachX1
                rcases vmStepXY_emit_of_emitsDigit X Y
                  (s := mulResidualXStateAfter X Y N d (K + 1)) hEmitX with ⟨d₂, hstep⟩
                have hsX1' : GeneralTrace.SafeAt X Y
                    { mulResidualXStateAfter X Y N d (K + 1) with
                        T := (mulResidualXStateAfter X Y N d (K + 1)).T.emit d₂ } :=
                  safe_step (X := X) (Y := Y) hstep hsX1
                have hrun : SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
                    { mulResidualXStateAfter X Y N d (K + 1) with
                        T := (mulResidualXStateAfter X Y N d (K + 1)).T.emit d₂ } :=
                  safeVMRun_append X Y hreachX1
                    (SafeVMRun.stepSome hstep hsX1 hsX1' (SafeVMRun.refl _ hsX1'))
                exact Or.inl ⟨_, d₂, hrun⟩
            | absorb =>
                have hpair : SafeVMRun X Y (mulResidualStateAfter X Y N d (K + 1)) []
                    (mulResidualStateAfter X Y N d (K + 2)) :=
                  mulResidual_pair_reachable X Y N d (K + 1) hsK1 hstate hstateX
                have hreachSucc : SafeVMRun X Y mulInitState [digit_to_LFT d]
                    (mulResidualStateAfter X Y N d (K + 2)) :=
                  safeVMRun_append X Y hreachK1 hpair
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
                  by simpa [Nat.add_assoc] using hreachSucc⟩

theorem mulResidualStateAfter_reachable_emitsStep
    (X Y : MobiusReal) (N : ℕ) (d : Digit) (K : ℕ)
    (hreach : SafeVMRun X Y mulInitState [digit_to_LFT d]
      (mulResidualStateAfter X Y N d K))
    (hK : (mulResidualStateAfter X Y N d K).T.EmitsDigit) :
    ∃ d₂,
      SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
        { mulResidualStateAfter X Y N d K with
            T := (mulResidualStateAfter X Y N d K).T.emit d₂ } := by
  have hsK : GeneralTrace.SafeAt X Y (mulResidualStateAfter X Y N d K) :=
    safe_end_of_safeVMRun X Y hreach
  rcases vmStepXY_emit_of_emitsDigit X Y
    (s := mulResidualStateAfter X Y N d K) hK with ⟨d₂, hstep⟩
  have hsK' : GeneralTrace.SafeAt X Y { mulResidualStateAfter X Y N d K with
      T := (mulResidualStateAfter X Y N d K).T.emit d₂ } :=
    safe_step (X := X) (Y := Y) hstep hsK
  exact ⟨d₂, safeVMRun_append X Y hreach
    (SafeVMRun.stepSome hstep hsK hsK' (SafeVMRun.refl _ hsK'))⟩

theorem mulTensor_balanced_first_emit_reaches_two_digits
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hreach : SafeVMRun X Y mulInitState [] (mulTensorStateAfter X Y N))
    (hstep : GeneralTrace.VMStepXY X Y
      (mulTensorStateAfter X Y N)
      (some (digit_to_LFT d))
      (mulResidualStateAfter X Y N d 0)) :
    ∃ s : VMState, ∃ d₂, SafeVMRun X Y mulInitState [digit_to_LFT d, d₂] s := by
  have hsN : GeneralTrace.SafeAt X Y (mulTensorStateAfter X Y N) :=
    safe_end_of_safeVMRun X Y hreach
  have hs0 : GeneralTrace.SafeAt X Y (mulResidualStateAfter X Y N d 0) :=
    safe_step (X := X) (Y := Y) hstep hsN
  have hreach0 : SafeVMRun X Y mulInitState [digit_to_LFT d]
      (mulResidualStateAfter X Y N d 0) :=
    safeVMRun_append X Y hreach
      (SafeVMRun.stepSome hstep hsN hs0 (SafeVMRun.refl _ hs0))
  rcases mulResidualStateAfter_productivity_spec_of_step X Y N d hstep with ⟨K, hK⟩
  rcases mulResidual_prefix_absorb_or_emits_of_step X Y N d hreach0 K with
    hemit | ⟨habs, habsX, hreachK⟩
  · exact hemit
  · rcases mulResidualStateAfter_reachable_emitsStep X Y N d K hreachK hK.emitsDigit with
      ⟨d₂, hrun⟩
    exact ⟨_, d₂, hrun⟩

theorem mulTensorX_emit_absorbY_reaches_residual_one
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hreach : SafeVMRun X Y mulInitState [] (mulTensorXStateAfter X Y N))
    (hstep : GeneralTrace.VMStepXY X Y
      (mulTensorXStateAfter X Y N)
      (some (digit_to_LFT d))
      { mulTensorXStateAfter X Y N with
          T := (mulTensorXStateAfter X Y N).T.emit (digit_to_LFT d) })
    (habs : ({ mulTensorXStateAfter X Y N with
        T := (mulTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }).T.oracle =
          Tensor.EmitDecision.absorb) :
    SafeVMRun X Y mulInitState [digit_to_LFT d]
      (mulResidualStateAfter X Y N d 1) := by
  let s₁ : VMState := { mulTensorXStateAfter X Y N with
    T := (mulTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }
  have hsX : GeneralTrace.SafeAt X Y (mulTensorXStateAfter X Y N) :=
    safe_end_of_safeVMRun X Y hreach
  have hs₁ : GeneralTrace.SafeAt X Y s₁ := by
    simpa [s₁] using safe_step (X := X) (Y := Y) hstep hsX
  have hreachEmit : SafeVMRun X Y mulInitState [digit_to_LFT d] s₁ := by
    simpa [s₁] using safeVMRun_append X Y hreach
      (SafeVMRun.stepSome hstep hsX hs₁ (SafeVMRun.refl _ hs₁))
  have hstepY_raw : GeneralTrace.VMStepXY X Y s₁ none
      { T := s₁.T.absorbY (Y.stream N), idx_x := s₁.idx_x, idx_y := s₁.idx_y + 1,
        absorb_x_next := true } := by
    simpa [s₁, mulTensorXStateAfter] using
      (GeneralTrace.VMStepXY.absorbY (X := X) (Y := Y) (s := s₁) habs rfl)
  have hTEq : s₁.T.absorbY (Y.stream N) = (mulResidualStateAfter X Y N d 1).T := by
    simpa [s₁] using (mulResidualStateAfter_one_eq_from_Xstep X Y N d).symm
  have hstateEq :
      { T := s₁.T.absorbY (Y.stream N), idx_x := s₁.idx_x, idx_y := s₁.idx_y + 1,
        absorb_x_next := true } = mulResidualStateAfter X Y N d 1 := by
    simp [s₁, mulTensorXStateAfter, mulResidualStateAfter, Tensor.absorbBoth_n]
    simpa [mulResidualStateAfter, Tensor.absorbBoth_n] using hTEq
  have hstepY : GeneralTrace.VMStepXY X Y s₁ none (mulResidualStateAfter X Y N d 1) := by
    simpa [hstateEq] using hstepY_raw
  have hs1 : GeneralTrace.SafeAt X Y (mulResidualStateAfter X Y N d 1) :=
    safe_step (X := X) (Y := Y) hstepY hs₁
  exact safeVMRun_append X Y hreachEmit
    (SafeVMRun.stepNone hstepY hs₁ hs1 (SafeVMRun.refl _ hs1))

theorem mulTensorX_first_emit_reaches_two_digits
    (X Y : MobiusReal) (N : ℕ) (d : Digit)
    (hreach : SafeVMRun X Y mulInitState [] (mulTensorXStateAfter X Y N))
    (hstep : GeneralTrace.VMStepXY X Y
      (mulTensorXStateAfter X Y N)
      (some (digit_to_LFT d))
      { mulTensorXStateAfter X Y N with
          T := (mulTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }) :
    ∃ s : VMState, ∃ d₂, SafeVMRun X Y mulInitState [digit_to_LFT d, d₂] s := by
  let s₁ : VMState := { mulTensorXStateAfter X Y N with
    T := (mulTensorXStateAfter X Y N).T.emit (digit_to_LFT d) }
  have hsX : GeneralTrace.SafeAt X Y (mulTensorXStateAfter X Y N) :=
    safe_end_of_safeVMRun X Y hreach
  have hs₁ : GeneralTrace.SafeAt X Y s₁ := by
    simpa [s₁] using safe_step (X := X) (Y := Y) hstep hsX
  have hreachEmit : SafeVMRun X Y mulInitState [digit_to_LFT d] s₁ := by
    simpa [s₁] using safeVMRun_append X Y hreach
      (SafeVMRun.stepSome hstep hsX hs₁ (SafeVMRun.refl _ hs₁))
  cases hstate : s₁.T.oracle with
  | neg =>
      have hEmit : s₁.T.EmitsDigit := by
        exact Or.inl hstate
      rcases vmStepXY_emit_of_emitsDigit X Y (s := s₁) hEmit with ⟨d₂, hstep₂⟩
      have hs₂ : GeneralTrace.SafeAt X Y { s₁ with T := s₁.T.emit d₂ } :=
        safe_step (X := X) (Y := Y) hstep₂ hs₁
      have hrun : SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
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
      have hrun : SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
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
      have hrun : SafeVMRun X Y mulInitState [digit_to_LFT d, d₂]
          { s₁ with T := s₁.T.emit d₂ } :=
        safeVMRun_append X Y hreachEmit
          (SafeVMRun.stepSome hstep₂ hs₁ hs₂ (SafeVMRun.refl _ hs₂))
      exact ⟨_, d₂, hrun⟩
  | absorb =>
      have hreach1 : SafeVMRun X Y mulInitState [digit_to_LFT d]
          (mulResidualStateAfter X Y N d 1) :=
        mulTensorX_emit_absorbY_reaches_residual_one X Y N d hreach hstep hstate
      rcases mulResidualStateAfter_productivity_spec_of_Xstep X Y N d hstep with ⟨K, hK⟩
      rcases mulResidual_prefix_absorb_or_emits_of_Xstep X Y N d hreach1 K with
        hemit | ⟨habs, habsX, hreachK1⟩
      · exact hemit
      · have hreachK : SafeVMRun X Y mulInitState [digit_to_LFT d]
            (mulResidualStateAfter X Y N d (K + 1)) := by
          simpa [Nat.add_comm] using hreachK1
        rcases mulResidualStateAfter_reachable_emitsStep X Y N d (K + 1)
          hreachK hK.emitsDigit with ⟨d₂, hrun⟩
        exact ⟨_, d₂, hrun⟩

theorem mulTensor_prefix_absorb_or_emits_classified
    (X Y : MobiusReal) (N : ℕ) :
    (∃ M : ℕ, ∃ d : Digit,
        SafeVMRun X Y mulInitState [] (mulTensorStateAfter X Y M) ∧
        GeneralTrace.VMStepXY X Y
          (mulTensorStateAfter X Y M)
          (some (digit_to_LFT d))
          (mulResidualStateAfter X Y M d 0)) ∨
      (∃ M : ℕ, ∃ d : Digit,
        SafeVMRun X Y mulInitState [] (mulTensorXStateAfter X Y M) ∧
        GeneralTrace.VMStepXY X Y
          (mulTensorXStateAfter X Y M)
          (some (digit_to_LFT d))
          { mulTensorXStateAfter X Y M with
              T := (mulTensorXStateAfter X Y M).T.emit (digit_to_LFT d) }) ∨
      ((∀ k, k < N → (mulTensorStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb) ∧
        (∀ k, k < N → (mulTensorXStateAfter X Y k).T.oracle = Tensor.EmitDecision.absorb) ∧
        SafeVMRun X Y mulInitState [] (mulTensorStateAfter X Y N)) := by
  induction N with
  | zero =>
      right
      right
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
      · intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
      · simpa [mulInitState, mulTensorStateAfter] using
          (SafeVMRun.refl (X := X) (Y := Y) mulInitState (mulInit_safe X Y))
  | succ N ih =>
      rcases ih with hbal | hx | ⟨habs, habsX, hreachN⟩
      · exact Or.inl hbal
      · exact Or.inr (Or.inl hx)
      · have hsN : GeneralTrace.SafeAt X Y (mulTensorStateAfter X Y N) :=
          safe_end_of_safeVMRun X Y hreachN
        cases hstate : (mulTensorStateAfter X Y N).T.oracle with
        | neg =>
            have hstep' : GeneralTrace.VMStepXY X Y
                (mulTensorStateAfter X Y N)
                (some (digit_to_LFT .neg))
                (mulResidualStateAfter X Y N .neg 0) := by
              simpa [mulResidualStateAfter_zero] using
                (GeneralTrace.VMStepXY.emitNeg (X := X) (Y := Y)
                  (s := mulTensorStateAfter X Y N) hstate)
            exact Or.inl ⟨N, .neg, hreachN, hstep'⟩
        | zero =>
            have hstep' : GeneralTrace.VMStepXY X Y
                (mulTensorStateAfter X Y N)
                (some (digit_to_LFT .zero))
                (mulResidualStateAfter X Y N .zero 0) := by
              simpa [mulResidualStateAfter_zero] using
                (GeneralTrace.VMStepXY.emitZero (X := X) (Y := Y)
                  (s := mulTensorStateAfter X Y N) hstate)
            exact Or.inl ⟨N, .zero, hreachN, hstep'⟩
        | pos =>
            have hstep' : GeneralTrace.VMStepXY X Y
                (mulTensorStateAfter X Y N)
                (some (digit_to_LFT .pos))
                (mulResidualStateAfter X Y N .pos 0) := by
              simpa [mulResidualStateAfter_zero] using
                (GeneralTrace.VMStepXY.emitPos (X := X) (Y := Y)
                  (s := mulTensorStateAfter X Y N) hstate)
            exact Or.inl ⟨N, .pos, hreachN, hstep'⟩
        | absorb =>
            have hreachX : SafeVMRun X Y mulInitState [] (mulTensorXStateAfter X Y N) :=
              mulTensorXStateAfter_reachable X Y N hreachN hstate
            cases hstateX : (mulTensorXStateAfter X Y N).T.oracle with
            | neg =>
                exact Or.inr (Or.inl ⟨N, .neg, hreachX, by
                  simpa using
                    (GeneralTrace.VMStepXY.emitNeg (X := X) (Y := Y)
                      (s := mulTensorXStateAfter X Y N) hstateX)⟩)
            | zero =>
                exact Or.inr (Or.inl ⟨N, .zero, hreachX, by
                  simpa using
                    (GeneralTrace.VMStepXY.emitZero (X := X) (Y := Y)
                      (s := mulTensorXStateAfter X Y N) hstateX)⟩)
            | pos =>
                exact Or.inr (Or.inl ⟨N, .pos, hreachX, by
                  simpa using
                    (GeneralTrace.VMStepXY.emitPos (X := X) (Y := Y)
                      (s := mulTensorXStateAfter X Y N) hstateX)⟩)
            | absorb =>
                have hpair : SafeVMRun X Y (mulTensorStateAfter X Y N) []
                    (mulTensorStateAfter X Y (N + 1)) :=
                  mulTensor_pair_reachable X Y N hsN hstate hstateX
                have hreachSucc : SafeVMRun X Y mulInitState []
                    (mulTensorStateAfter X Y (N + 1)) :=
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

theorem mulTensor_scheduler_reaches_two_digits
    (X Y : MobiusReal) :
    ∃ s : VMState, ∃ d₁ d₂, SafeVMRun X Y mulInitState [digit_to_LFT d₁, d₂] s := by
  rcases mulTensor_eventually_emitsDigit X Y with ⟨N, hN⟩
  rcases mulTensor_prefix_absorb_or_emits_classified X Y N with
    hbal | hx | ⟨habs, habsX, hreachN⟩
  · rcases hbal with ⟨M, d₁, hreachM, hstepM⟩
    rcases mulTensor_balanced_first_emit_reaches_two_digits X Y M d₁ hreachM hstepM with
      ⟨s, d₂, hrun⟩
    exact ⟨s, d₁, d₂, hrun⟩
  · rcases hx with ⟨M, d₁, hreachX, hstepX⟩
    rcases mulTensorX_first_emit_reaches_two_digits X Y M d₁ hreachX hstepX with
      ⟨s, d₂, hrun⟩
    exact ⟨s, d₁, d₂, hrun⟩
  · have hsN : GeneralTrace.SafeAt X Y (mulTensorStateAfter X Y N) :=
      safe_end_of_safeVMRun X Y hreachN
    rcases hN with hneg | hrest
    · have hstep' : GeneralTrace.VMStepXY X Y
          (mulTensorStateAfter X Y N)
          (some (digit_to_LFT .neg))
          (mulResidualStateAfter X Y N .neg 0) := by
        simpa [mulResidualStateAfter_zero] using
          (GeneralTrace.VMStepXY.emitNeg (X := X) (Y := Y)
            (s := mulTensorStateAfter X Y N) hneg)
      rcases mulTensor_balanced_first_emit_reaches_two_digits X Y N .neg hreachN hstep' with
        ⟨s, d₂, hrun⟩
      exact ⟨s, .neg, d₂, hrun⟩
    · rcases hrest with hzero | hpos
      · have hstep' : GeneralTrace.VMStepXY X Y
            (mulTensorStateAfter X Y N)
            (some (digit_to_LFT .zero))
            (mulResidualStateAfter X Y N .zero 0) := by
          simpa [mulResidualStateAfter_zero] using
            (GeneralTrace.VMStepXY.emitZero (X := X) (Y := Y)
              (s := mulTensorStateAfter X Y N) hzero)
        rcases mulTensor_balanced_first_emit_reaches_two_digits X Y N .zero hreachN hstep' with
          ⟨s, d₂, hrun⟩
        exact ⟨s, .zero, d₂, hrun⟩
      · have hstep' : GeneralTrace.VMStepXY X Y
            (mulTensorStateAfter X Y N)
            (some (digit_to_LFT .pos))
            (mulResidualStateAfter X Y N .pos 0) := by
          simpa [mulResidualStateAfter_zero] using
            (GeneralTrace.VMStepXY.emitPos (X := X) (Y := Y)
              (s := mulTensorStateAfter X Y N) hpos)
        rcases mulTensor_balanced_first_emit_reaches_two_digits X Y N .pos hreachN hstep' with
          ⟨s, d₂, hrun⟩
        exact ⟨s, .pos, d₂, hrun⟩

theorem mulTensor_scheduler_reaches_two_digits_mem_baseI
    (X Y : MobiusReal) :
    ∃ s : VMState, ∃ d₁ d₂,
      SafeVMRun X Y mulInitState [digit_to_LFT d₁, d₂] s ∧
      GeneralTrace.stateValue X Y s ∈ baseI := by
  rcases mulTensor_scheduler_reaches_two_digits X Y with ⟨s, d₁, d₂, hrun⟩
  exact ⟨s, d₁, d₂, hrun, safeVMRun_pair_residual_mem_baseI X Y hrun⟩

theorem mulTensor_run_reaches_two_digits (X Y : MobiusReal) :
    ∃ fuel d₁ d₂ s, run X Y fuel mulInitState = ([d₁, d₂], s) := by
  rcases mulTensor_scheduler_reaches_two_digits X Y with ⟨s, d₁, d₂LFT, hrun⟩
  rcases Computable.Mobius.safeVMRun_realized_by_run X Y hrun with ⟨fuel, hstate, hds⟩
  set out := (run X Y fuel mulInitState).1
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
              refine ⟨fuel, d0, d1, (run X Y fuel mulInitState).2, ?_⟩
              have hout' : (run X Y fuel mulInitState).1 = [d0, d1] := by
                simp [out, hout, hds0, hds1]
              exact Prod.ext hout' rfl
          | cons d2 ds'' =>
              have hlen := congrArg List.length houtMap
              simp [hout, hds0, hds1] at hlen

theorem mulTensor_run_two_digits_sound (X Y : MobiusReal) :
    ∃ fuel d₁ d₂ s,
      run X Y fuel mulInitState = ([d₁, d₂], s) ∧
      X.val * Y.val =
        LFT.apply (digit_to_LFT d₁)
          (LFT.apply (digit_to_LFT d₂) (GeneralTrace.stateValue X Y s)) := by
  rcases mulTensor_run_reaches_two_digits X Y with ⟨fuel, d₁, d₂, s, hrun⟩
  have hsafeRun : SafeVMRun X Y mulInitState [digit_to_LFT d₁, digit_to_LFT d₂] s := by
    simpa [hrun] using run_safeVMRun X Y fuel mulInitState (mulInit_safe X Y)
  have hprefix :
      GeneralTrace.stateValue X Y mulInitState =
        LFT.apply (digit_to_LFT d₁)
          (LFT.apply (digit_to_LFT d₂) (GeneralTrace.stateValue X Y s)) := by
    simpa using
      vm_soundness_prefix_two mulInitState s X Y (digit_to_LFT d₁) (digit_to_LFT d₂) hsafeRun
  refine ⟨fuel, d₁, d₂, s, hrun, ?_⟩
  calc
    X.val * Y.val = GeneralTrace.stateValue X Y mulInitState := by
      symm
      exact mulInit_stateValue X Y
    _ = LFT.apply (digit_to_LFT d₁)
          (LFT.apply (digit_to_LFT d₂) (GeneralTrace.stateValue X Y s)) := hprefix

theorem mulTensor_run_reaches_two_digits_mem_baseI (X Y : MobiusReal) :
    ∃ fuel d₁ d₂ s,
      run X Y fuel mulInitState = ([d₁, d₂], s) ∧
      GeneralTrace.stateValue X Y s ∈ baseI := by
  rcases mulTensor_run_reaches_two_digits X Y with ⟨fuel, d₁, d₂, s, hrun⟩
  have hsafeRun : SafeVMRun X Y mulInitState [digit_to_LFT d₁, digit_to_LFT d₂] s := by
    simpa [hrun] using run_safeVMRun X Y fuel mulInitState (mulInit_safe X Y)
  exact ⟨fuel, d₁, d₂, s, hrun, safeVMRun_pair_residual_mem_baseI X Y hsafeRun⟩

theorem mulTensor_run_two_digits_sound_mem_baseI (X Y : MobiusReal) :
    ∃ fuel d₁ d₂ s,
      run X Y fuel mulInitState = ([d₁, d₂], s) ∧
      X.val * Y.val =
        LFT.apply (digit_to_LFT d₁)
          (LFT.apply (digit_to_LFT d₂) (GeneralTrace.stateValue X Y s)) ∧
      GeneralTrace.stateValue X Y s ∈ baseI := by
  rcases mulTensor_run_reaches_two_digits_mem_baseI X Y with ⟨fuel, d₁, d₂, s, hrun, hs⟩
  have hsafeRun : SafeVMRun X Y mulInitState [digit_to_LFT d₁, digit_to_LFT d₂] s := by
    simpa [hrun] using run_safeVMRun X Y fuel mulInitState (mulInit_safe X Y)
  have hprefix :
      GeneralTrace.stateValue X Y mulInitState =
        LFT.apply (digit_to_LFT d₁)
          (LFT.apply (digit_to_LFT d₂) (GeneralTrace.stateValue X Y s)) := by
    simpa using
      vm_soundness_prefix_two mulInitState s X Y (digit_to_LFT d₁) (digit_to_LFT d₂) hsafeRun
  refine ⟨fuel, d₁, d₂, s, hrun, ?_, hs⟩
  calc
    X.val * Y.val = GeneralTrace.stateValue X Y mulInitState := by
      symm
      exact mulInit_stateValue X Y
    _ = LFT.apply (digit_to_LFT d₁)
          (LFT.apply (digit_to_LFT d₂) (GeneralTrace.stateValue X Y s)) := hprefix

def affineMulStateAfter (X Y : MobiusReal) (u v : ℤ) (N K : ℕ) : VMState where
  T := Tensor.absorbBoth_n
    (affineMulTensor u v (pairedPrefix X.stream N) (pairedPrefix Y.stream N))
    (MobiusReal.drop X N).stream (MobiusReal.drop Y N).stream K
  idx_x := N + K
  idx_y := N + K
  absorb_x_next := true

def affineMulXStateAfter (X Y : MobiusReal) (u v : ℤ) (N K : ℕ) : VMState where
  T := (affineMulStateAfter X Y u v N K).T.absorbX ((MobiusReal.drop X N).stream K)
  idx_x := N + K + 1
  idx_y := N + K
  absorb_x_next := false

@[simp] theorem affineMulStateAfter_zero
    (X Y : MobiusReal) (u v : ℤ) (N : ℕ) :
    affineMulStateAfter X Y u v N 0 =
      { mulTensorStateAfter X Y N with
          T := affineMulTensor u v (pairedPrefix X.stream N) (pairedPrefix Y.stream N) } := by
  simp [affineMulStateAfter, mulTensorStateAfter, Tensor.absorbBoth_n]

theorem affineMulStateAfter_eq_affineMulTensor
    (X Y : MobiusReal) (u v : ℤ) (N K : ℕ) :
    (affineMulStateAfter X Y u v N K).T =
      affineMulTensor u v
        ((pairedPrefix X.stream N).comp (pairedPrefix (MobiusReal.drop X N).stream K))
        ((pairedPrefix Y.stream N).comp (pairedPrefix (MobiusReal.drop Y N).stream K)) := by
  unfold affineMulStateAfter
  simpa [LFT.comp_assoc] using
    absorbBoth_n_affineMulTensor_eq
      u v
      (pairedPrefix X.stream N) (pairedPrefix Y.stream N)
      (MobiusReal.drop X N).stream (MobiusReal.drop Y N).stream K

theorem affineMulStateAfter_eq_affineMulTensor'
    (X Y : MobiusReal) (u v : ℤ) (N K : ℕ) :
    (affineMulStateAfter X Y u v N K).T =
      affineMulTensor u v
        (pairedPrefix X.stream (N + K))
        (pairedPrefix Y.stream (N + K)) := by
  rw [affineMulStateAfter_eq_affineMulTensor]
  simp [MobiusReal.drop, pairedPrefix_append_shift]

theorem affineMulXStateAfter_eq_affineMulTensor
    (X Y : MobiusReal) (u v : ℤ) (N K : ℕ) :
    (affineMulXStateAfter X Y u v N K).T =
      affineMulTensor u v
        (pairedPrefix X.stream (N + K + 1))
        (pairedPrefix Y.stream (N + K)) := by
  rw [affineMulXStateAfter, affineMulStateAfter_eq_affineMulTensor']
  have hdrop : (MobiusReal.drop X N).stream K = X.stream (N + K) := by
    simp [MobiusReal.drop, Nat.add_comm]
  rw [hdrop, affineMulTensor_absorbX]
  simp [pairedPrefix]

theorem affineMulStateAfter_hasNoPoleOnBase
    (X Y : MobiusReal) (u v : ℤ) (N K : ℕ) :
    (affineMulStateAfter X Y u v N K).T.HasNoPoleOnBase := by
  rw [affineMulStateAfter_eq_affineMulTensor']
  exact affineMulTensor_hasNoPoleOnBase u v
    (pairedPrefix X.stream (N + K)) (pairedPrefix Y.stream (N + K))
    (pairedPrefix_noPoleOnBase X (N + K))
    (pairedPrefix_noPoleOnBase Y (N + K))

theorem affineMulXStateAfter_hasNoPoleOnBase
    (X Y : MobiusReal) (u v : ℤ) (N K : ℕ) :
    (affineMulXStateAfter X Y u v N K).T.HasNoPoleOnBase := by
  rw [affineMulXStateAfter_eq_affineMulTensor]
  exact affineMulTensor_hasNoPoleOnBase u v
    (pairedPrefix X.stream (N + K + 1)) (pairedPrefix Y.stream (N + K))
    (pairedPrefix_noPoleOnBase X (N + K + 1))
    (pairedPrefix_noPoleOnBase Y (N + K))

theorem affineMulStateAfter_safe
    (X Y : MobiusReal) (u v : ℤ) (N K : ℕ) :
    GeneralTrace.SafeAt X Y (affineMulStateAfter X Y u v N K) := by
  exact GeneralTrace.safeAt_of_tensor_hasNoPoleOnBase X Y
    (affineMulStateAfter X Y u v N K)
    (affineMulStateAfter_hasNoPoleOnBase X Y u v N K)

theorem affineMulXStateAfter_safe
    (X Y : MobiusReal) (u v : ℤ) (N K : ℕ) :
    GeneralTrace.SafeAt X Y (affineMulXStateAfter X Y u v N K) := by
  exact GeneralTrace.safeAt_of_tensor_hasNoPoleOnBase X Y
    (affineMulXStateAfter X Y u v N K)
    (affineMulXStateAfter_hasNoPoleOnBase X Y u v N K)

theorem affineMulStateAfter_apply
    (X Y : MobiusReal) (u v : ℤ) (N K : ℕ) {x y : ℝ}
    (hx : x ∈ baseI) (hy : y ∈ baseI) :
    Tensor.apply (affineMulStateAfter X Y u v N K).T x y =
      (u : ℝ) * LFT.apply (pairedPrefix X.stream (N + K)) x *
        LFT.apply (pairedPrefix Y.stream (N + K)) y + (v : ℝ) := by
  rw [affineMulStateAfter_eq_affineMulTensor']
  exact affineMulTensor_apply u v
    (pairedPrefix X.stream (N + K)) (pairedPrefix Y.stream (N + K)) x y
    (pairedPrefix_denom_ne_zero X (N + K) hx)
    (pairedPrefix_denom_ne_zero Y (N + K) hy)

theorem affineMulStateAfter_diff_lt
    (X Y : MobiusReal) (u v : ℤ) (N : ℕ)
    (hu : 0 < u) {ε : ℝ} (hε : 0 < ε) :
    ∃ K0 : ℕ, ∀ K ≥ K0, ∀ x ∈ baseI, ∀ w ∈ baseI, ∀ y ∈ baseI, ∀ z ∈ baseI,
      |Tensor.apply (affineMulStateAfter X Y u v N K).T x y -
        Tensor.apply (affineMulStateAfter X Y u v N K).T w z| < ε := by
  have huR : 0 < (u : ℝ) := by
    exact_mod_cast hu
  have hden : 0 < 2 * (u : ℝ) := by
    nlinarith
  have hεu : 0 < ε / (2 * (u : ℝ)) := div_pos hε hden
  rcases X.contractive.shrinks_to_zero (ε / (2 * (u : ℝ))) hεu with ⟨NX, hNX⟩
  rcases Y.contractive.shrinks_to_zero (ε / (2 * (u : ℝ))) hεu with ⟨NY, hNY⟩
  refine ⟨max NX NY + 1, ?_⟩
  intro K hK x hx w hw y hy z hz
  have hKN : K ≤ N + K := by omega
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
          |LFT.apply (partialComp X.stream n) x - LFT.apply (partialComp X.stream n) w|
            < ε / (2 * (u : ℝ)) := by
        simpa [partialComp] using hNX n hnX 0 x hx w hw
      have hdy0 :
          |LFT.apply (partialComp Y.stream n) y - LFT.apply (partialComp Y.stream n) z|
            < ε / (2 * (u : ℝ)) := by
        simpa [partialComp] using hNY n hnY 0 y hy z hz
      have hdx :
          |LFT.apply (pairedPrefix X.stream (N + K)) x -
              LFT.apply (pairedPrefix X.stream (N + K)) w| < ε / (2 * (u : ℝ)) := by
        rw [hsum, pairedPrefix_eq_partialComp]
        exact hdx0
      have hdy :
          |LFT.apply (pairedPrefix Y.stream (N + K)) y -
              LFT.apply (pairedPrefix Y.stream (N + K)) z| < ε / (2 * (u : ℝ)) := by
        rw [hsum, pairedPrefix_eq_partialComp]
        exact hdy0
      have hXw : LFT.apply (pairedPrefix X.stream (N + K)) w ∈ baseI :=
        pairedPrefix_maps_base X (N + K) hw
      have hYy : LFT.apply (pairedPrefix Y.stream (N + K)) y ∈ baseI :=
        pairedPrefix_maps_base Y (N + K) hy
      rw [affineMulStateAfter_apply X Y u v N K hx hy,
        affineMulStateAfter_apply X Y u v N K hw hz]
      have huAbs : |(u : ℝ)| = (u : ℝ) := abs_of_nonneg huR.le
      have hsplit :
          |(u : ℝ) * LFT.apply (pairedPrefix X.stream (N + K)) x *
              LFT.apply (pairedPrefix Y.stream (N + K)) y + (v : ℝ) -
            ((u : ℝ) * LFT.apply (pairedPrefix X.stream (N + K)) w *
              LFT.apply (pairedPrefix Y.stream (N + K)) z + (v : ℝ))|
            ≤ (u : ℝ) *
              (|LFT.apply (pairedPrefix X.stream (N + K)) x -
                  LFT.apply (pairedPrefix X.stream (N + K)) w| +
                |LFT.apply (pairedPrefix Y.stream (N + K)) y -
                  LFT.apply (pairedPrefix Y.stream (N + K)) z|) := by
        calc
          |(u : ℝ) * LFT.apply (pairedPrefix X.stream (N + K)) x *
                LFT.apply (pairedPrefix Y.stream (N + K)) y + (v : ℝ) -
              ((u : ℝ) * LFT.apply (pairedPrefix X.stream (N + K)) w *
                LFT.apply (pairedPrefix Y.stream (N + K)) z + (v : ℝ))|
              = |(u : ℝ) *
                  (LFT.apply (pairedPrefix X.stream (N + K)) x *
                    LFT.apply (pairedPrefix Y.stream (N + K)) y -
                    LFT.apply (pairedPrefix X.stream (N + K)) w *
                      LFT.apply (pairedPrefix Y.stream (N + K)) z)| := by
                    ring_nf
          _ = |(u : ℝ)| *
                |LFT.apply (pairedPrefix X.stream (N + K)) x *
                    LFT.apply (pairedPrefix Y.stream (N + K)) y -
                  LFT.apply (pairedPrefix X.stream (N + K)) w *
                    LFT.apply (pairedPrefix Y.stream (N + K)) z| := by
                  simp [abs_mul]
          _ = (u : ℝ) *
                |LFT.apply (pairedPrefix X.stream (N + K)) x *
                    LFT.apply (pairedPrefix Y.stream (N + K)) y -
                  LFT.apply (pairedPrefix X.stream (N + K)) w *
                    LFT.apply (pairedPrefix Y.stream (N + K)) z| := by
                  rw [huAbs]
          _ ≤ (u : ℝ) *
                (|LFT.apply (pairedPrefix X.stream (N + K)) x -
                    LFT.apply (pairedPrefix X.stream (N + K)) w| +
                  |LFT.apply (pairedPrefix Y.stream (N + K)) y -
                    LFT.apply (pairedPrefix Y.stream (N + K)) z|) := by
                  gcongr
                  exact mul_diff_le_sum_of_mem_baseI hYy hXw
      have hsum' :
          ε / (2 * (u : ℝ)) + ε / (2 * (u : ℝ)) >
            |LFT.apply (pairedPrefix X.stream (N + K)) x -
                LFT.apply (pairedPrefix X.stream (N + K)) w| +
              |LFT.apply (pairedPrefix Y.stream (N + K)) y -
                LFT.apply (pairedPrefix Y.stream (N + K)) z| := by
        nlinarith
      have huNe : (u : ℝ) ≠ 0 := ne_of_gt huR
      have hsum'' :
          |LFT.apply (pairedPrefix X.stream (N + K)) x -
              LFT.apply (pairedPrefix X.stream (N + K)) w| +
            |LFT.apply (pairedPrefix Y.stream (N + K)) y -
              LFT.apply (pairedPrefix Y.stream (N + K)) z| < ε / (u : ℝ) := by
        have hEq :
            ε / (2 * (u : ℝ)) + ε / (2 * (u : ℝ)) = ε / (u : ℝ) := by
          field_simp [huNe]
          ring
        rw [hEq] at hsum'
        exact hsum'
      have hmul :
          (u : ℝ) *
            (|LFT.apply (pairedPrefix X.stream (N + K)) x -
                LFT.apply (pairedPrefix X.stream (N + K)) w| +
              |LFT.apply (pairedPrefix Y.stream (N + K)) y -
                LFT.apply (pairedPrefix Y.stream (N + K)) z|) <
            (u : ℝ) * (ε / (u : ℝ)) :=
        mul_lt_mul_of_pos_left hsum'' huR
      have hscale :
          (u : ℝ) *
            (|LFT.apply (pairedPrefix X.stream (N + K)) x -
                LFT.apply (pairedPrefix X.stream (N + K)) w| +
              |LFT.apply (pairedPrefix Y.stream (N + K)) y -
                LFT.apply (pairedPrefix Y.stream (N + K)) z|) < ε := by
        have hEq : (u : ℝ) * (ε / (u : ℝ)) = ε := by
          field_simp [huNe]
        simpa [hEq] using hmul
      exact lt_of_le_of_lt hsplit hscale

theorem affineMulStateAfter_width_le_eventually
    (X Y : MobiusReal) (u v : ℤ) (N : ℕ)
    (hu : 0 < u) {ε : ℝ} (hε : 0 < ε) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      tensorWidth (affineMulStateAfter X Y u v N K).T ≤ ε := by
  rcases affineMulStateAfter_diff_lt X Y u v N hu hε with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  unfold tensorWidth
  exact csSup_le
    (Tensor.widthSet_nonempty (affineMulStateAfter X Y u v N K).T)
    (by
      intro r hr
      rcases hr with ⟨x, y, w, z, hx, hy, hw, hz, rfl⟩
      exact le_of_lt (hK0 K hK x hx w hw y hy z hz))

theorem affineMulStateAfter_width_lt_half_eventually
    (X Y : MobiusReal) (u v : ℤ) (N : ℕ) (hu : 0 < u) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      tensorWidth (affineMulStateAfter X Y u v N K).T < (1 / 2 : ℝ) := by
  rcases affineMulStateAfter_width_le_eventually X Y u v N hu
    (ε := (1 / 4 : ℝ)) (by norm_num) with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  have hwidth : tensorWidth (affineMulStateAfter X Y u v N K).T ≤ (1 / 4 : ℝ) := hK0 K hK
  linarith

theorem affineMulStateAfter_safeEventually
    (X Y : MobiusReal) (u v : ℤ) (N : ℕ) (hu : 0 < u) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (affineMulStateAfter X Y u v N K).T.HasNoPoleOnBase ∧
        tensorWidth (affineMulStateAfter X Y u v N K).T < (1 / 2 : ℝ) := by
  rcases affineMulStateAfter_width_lt_half_eventually X Y u v N hu with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  exact ⟨affineMulStateAfter_hasNoPoleOnBase X Y u v N K, hK0 K hK⟩

theorem affineMulStateAfter_one_eq_from_X
    (X Y : MobiusReal) (u v : ℤ) (N : ℕ) :
    (affineMulStateAfter X Y u v N 1).T =
      (affineMulXStateAfter X Y u v N 0).T.absorbY (Y.stream N) := by
  rw [affineMulStateAfter_eq_affineMulTensor']
  rw [affineMulXStateAfter_eq_affineMulTensor]
  rw [affineMulTensor_absorbY]
  simp [pairedPrefix]

theorem affineMulStateAfter_mapsBaseI_pair_of_zero
    (X Y : MobiusReal) (u v : ℤ) (N : ℕ)
    (h0Maps : (affineMulStateAfter X Y u v N 0).T.MapsBaseI) :
    ∀ K,
      (affineMulStateAfter X Y u v N K).T.MapsBaseI ∧
      (affineMulXStateAfter X Y u v N K).T.MapsBaseI
  | 0 => by
      refine ⟨h0Maps, ?_⟩
      exact Tensor.mapsBaseI_absorbX
        ((affineMulStateAfter X Y u v N 0).T)
        ((MobiusReal.drop X N).stream 0)
        h0Maps
        (affineMulStateAfter_hasNoPoleOnBase X Y u v N 0)
        (affineMulXStateAfter_hasNoPoleOnBase X Y u v N 0)
        (IsContractive.maps_base_step (MobiusReal.drop X N).contractive 0)
        (IsContractive.no_poles_step (MobiusReal.drop X N).contractive 0)
  | K + 1 => by
      rcases affineMulStateAfter_mapsBaseI_pair_of_zero X Y u v N h0Maps K with
        ⟨hStateK, hXK⟩
      have hStateSucc :
          (affineMulStateAfter X Y u v N (K + 1)).T.MapsBaseI := by
        have hEq :
            (affineMulStateAfter X Y u v N (K + 1)).T =
              (affineMulXStateAfter X Y u v N K).T.absorbY
                ((MobiusReal.drop Y N).stream K) := by
          simp [affineMulStateAfter, affineMulXStateAfter, Tensor.absorbBoth_n]
        rw [hEq]
        exact Tensor.mapsBaseI_absorbY
          ((affineMulXStateAfter X Y u v N K).T)
          ((MobiusReal.drop Y N).stream K)
          hXK
          (affineMulXStateAfter_hasNoPoleOnBase X Y u v N K)
          (affineMulStateAfter_hasNoPoleOnBase X Y u v N (K + 1))
          (IsContractive.maps_base_step (MobiusReal.drop Y N).contractive K)
          (IsContractive.no_poles_step (MobiusReal.drop Y N).contractive K)
      have hXSucc :
          (affineMulXStateAfter X Y u v N (K + 1)).T.MapsBaseI := by
        exact Tensor.mapsBaseI_absorbX
          ((affineMulStateAfter X Y u v N (K + 1)).T)
          ((MobiusReal.drop X N).stream (K + 1))
          hStateSucc
          (affineMulStateAfter_hasNoPoleOnBase X Y u v N (K + 1))
          (affineMulXStateAfter_hasNoPoleOnBase X Y u v N (K + 1))
          (IsContractive.maps_base_step (MobiusReal.drop X N).contractive (K + 1))
          (IsContractive.no_poles_step (MobiusReal.drop X N).contractive (K + 1))
      exact ⟨hStateSucc, hXSucc⟩

theorem affineMulStateAfter_mapsBaseI_of_zero
    (X Y : MobiusReal) (u v : ℤ) (N : ℕ)
    (h0Maps : (affineMulStateAfter X Y u v N 0).T.MapsBaseI) :
    ∀ K, (affineMulStateAfter X Y u v N K).T.MapsBaseI :=
  fun K => (affineMulStateAfter_mapsBaseI_pair_of_zero X Y u v N h0Maps K).1

theorem affineMulStateAfter_mapsBaseI_pair_of_Xzero
    (X Y : MobiusReal) (u v : ℤ) (N : ℕ)
    (hX0Maps : (affineMulXStateAfter X Y u v N 0).T.MapsBaseI) :
    ∀ K,
      (affineMulStateAfter X Y u v N (K + 1)).T.MapsBaseI ∧
      (affineMulXStateAfter X Y u v N (K + 1)).T.MapsBaseI
  | 0 => by
      have hState1 :
          (affineMulStateAfter X Y u v N 1).T.MapsBaseI := by
        have hNoPole1 :
            ((affineMulXStateAfter X Y u v N 0).T.absorbY (Y.stream N)).HasNoPoleOnBase := by
          rw [← affineMulStateAfter_one_eq_from_X X Y u v N]
          exact affineMulStateAfter_hasNoPoleOnBase X Y u v N 1
        rw [affineMulStateAfter_one_eq_from_X]
        exact Tensor.mapsBaseI_absorbY
          ((affineMulXStateAfter X Y u v N 0).T) (Y.stream N)
          hX0Maps
          (affineMulXStateAfter_hasNoPoleOnBase X Y u v N 0)
          hNoPole1
          (IsContractive.maps_base_step Y.contractive N)
          (IsContractive.no_poles_step Y.contractive N)
      refine ⟨hState1, ?_⟩
      exact Tensor.mapsBaseI_absorbX
        ((affineMulStateAfter X Y u v N 1).T)
        ((MobiusReal.drop X N).stream 1)
        hState1
        (affineMulStateAfter_hasNoPoleOnBase X Y u v N 1)
        (affineMulXStateAfter_hasNoPoleOnBase X Y u v N 1)
        (IsContractive.maps_base_step (MobiusReal.drop X N).contractive 1)
        (IsContractive.no_poles_step (MobiusReal.drop X N).contractive 1)
  | K + 1 => by
      rcases affineMulStateAfter_mapsBaseI_pair_of_Xzero X Y u v N hX0Maps K with
        ⟨hStateK, hXK⟩
      have hStateSucc :
          (affineMulStateAfter X Y u v N (K + 2)).T.MapsBaseI := by
        have hEq :
            (affineMulStateAfter X Y u v N (K + 2)).T =
              (affineMulXStateAfter X Y u v N (K + 1)).T.absorbY
                ((MobiusReal.drop Y N).stream (K + 1)) := by
          simp [affineMulStateAfter, affineMulXStateAfter, Tensor.absorbBoth_n]
        rw [hEq]
        exact Tensor.mapsBaseI_absorbY
          ((affineMulXStateAfter X Y u v N (K + 1)).T)
          ((MobiusReal.drop Y N).stream (K + 1))
          hXK
          (affineMulXStateAfter_hasNoPoleOnBase X Y u v N (K + 1))
          (affineMulStateAfter_hasNoPoleOnBase X Y u v N (K + 2))
          (IsContractive.maps_base_step (MobiusReal.drop Y N).contractive (K + 1))
          (IsContractive.no_poles_step (MobiusReal.drop Y N).contractive (K + 1))
      have hXSucc :
          (affineMulXStateAfter X Y u v N (K + 2)).T.MapsBaseI := by
        exact Tensor.mapsBaseI_absorbX
          ((affineMulStateAfter X Y u v N (K + 2)).T)
          ((MobiusReal.drop X N).stream (K + 2))
          hStateSucc
          (affineMulStateAfter_hasNoPoleOnBase X Y u v N (K + 2))
          (affineMulXStateAfter_hasNoPoleOnBase X Y u v N (K + 2))
          (IsContractive.maps_base_step (MobiusReal.drop X N).contractive (K + 2))
          (IsContractive.no_poles_step (MobiusReal.drop X N).contractive (K + 2))
      exact ⟨hStateSucc, hXSucc⟩

theorem affineMulStateAfter_emitsDigit_eventually_of_zero
    (X Y : MobiusReal) (u v : ℤ) (N : ℕ)
    (hu : 0 < u)
    (h0Maps : (affineMulStateAfter X Y u v N 0).T.MapsBaseI) :
    ∃ K0 : ℕ, ∀ K ≥ K0, (affineMulStateAfter X Y u v N K).T.EmitsDigit := by
  rcases affineMulStateAfter_safeEventually X Y u v N hu with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  have hsafe := hK0 K hK
  exact Tensor.emitsDigit_of_hasNoPoleOnBase_of_mapsBaseI_of_width_lt_half
    (T := (affineMulStateAfter X Y u v N K).T)
    hsafe.1
    (affineMulStateAfter_mapsBaseI_of_zero X Y u v N h0Maps K)
    hsafe.2

theorem affineMulStateAfter_productivity_spec_of_zero
    (X Y : MobiusReal) (u v : ℤ) (N : ℕ)
    (hu : 0 < u)
    (h0Maps : (affineMulStateAfter X Y u v N 0).T.MapsBaseI) :
    ∃ K : ℕ, (affineMulStateAfter X Y u v N K).T.ProductiveOnBase := by
  rcases affineMulStateAfter_safeEventually X Y u v N hu with ⟨Ksafe, hsafe⟩
  refine ⟨Ksafe, ?_⟩
  have hsafe' := hsafe Ksafe le_rfl
  exact Tensor.productiveOnBase_of_hasNoPoleOnBase_of_mapsBaseI_of_width_lt_half
    (T := (affineMulStateAfter X Y u v N Ksafe).T)
    hsafe'.1
    (affineMulStateAfter_mapsBaseI_of_zero X Y u v N h0Maps Ksafe)
    hsafe'.2

theorem affineMulStateAfter_emitsDigit_eventually_of_Xzero
    (X Y : MobiusReal) (u v : ℤ) (N : ℕ)
    (hu : 0 < u)
    (hX0Maps : (affineMulXStateAfter X Y u v N 0).T.MapsBaseI) :
    ∃ K0 : ℕ, ∀ K ≥ K0, (affineMulStateAfter X Y u v N (K + 1)).T.EmitsDigit := by
  rcases affineMulStateAfter_safeEventually X Y u v N hu with ⟨K0, hK0⟩
  refine ⟨K0, ?_⟩
  intro K hK
  have hK' : K + 1 ≥ K0 := le_trans hK (Nat.le_succ _)
  have hsafe := hK0 (K + 1) hK'
  exact Tensor.emitsDigit_of_hasNoPoleOnBase_of_mapsBaseI_of_width_lt_half
    (T := (affineMulStateAfter X Y u v N (K + 1)).T)
    hsafe.1
    ((affineMulStateAfter_mapsBaseI_pair_of_Xzero X Y u v N hX0Maps K).1)
    hsafe.2

theorem affineMulStateAfter_productivity_spec_of_Xzero
    (X Y : MobiusReal) (u v : ℤ) (N : ℕ)
    (hu : 0 < u)
    (hX0Maps : (affineMulXStateAfter X Y u v N 0).T.MapsBaseI) :
    ∃ K : ℕ, (affineMulStateAfter X Y u v N (K + 1)).T.ProductiveOnBase := by
  rcases affineMulStateAfter_safeEventually X Y u v N hu with ⟨Ksafe, hsafe⟩
  refine ⟨Ksafe, ?_⟩
  have hsafe' := hsafe (Ksafe + 1) (Nat.le_succ _)
  exact Tensor.productiveOnBase_of_hasNoPoleOnBase_of_mapsBaseI_of_width_lt_half
    (T := (affineMulStateAfter X Y u v N (Ksafe + 1)).T)
    hsafe'.1
    ((affineMulStateAfter_mapsBaseI_pair_of_Xzero X Y u v N hX0Maps Ksafe).1)
    hsafe'.2

/-- Executable prefix report for the bounded multiplication machine. -/
def mulPrefixResult (X Y : MobiusReal) (fuel : ℕ) : PrefixResult :=
  prefixResult X Y fuel mulInitState

theorem mulPrefix_eq_value_plus_residual
    (X Y : MobiusReal) (fuel : ℕ) :
    X.val * Y.val =
      (mulPrefixResult X Y fuel).approx +
        GeneralTrace.stateValue X Y (mulPrefixResult X Y fuel).state /
          2 ^ (mulPrefixResult X Y fuel).digits.length := by
  have hs : GeneralTrace.SafeAt X Y mulInitState := mulInit_safe X Y
  calc
    X.val * Y.val = GeneralTrace.stateValue X Y mulInitState := by
      symm
      exact mulInit_stateValue X Y
    _ =
      (mulPrefixResult X Y fuel).approx +
        GeneralTrace.stateValue X Y (mulPrefixResult X Y fuel).state /
          2 ^ (mulPrefixResult X Y fuel).digits.length := by
        simpa [mulPrefixResult] using
          prefixResult_stateValue_eq_approx_add_scaled X Y fuel mulInitState hs

theorem mulPrefix_error_le
    (X Y : MobiusReal) (fuel : ℕ)
    (hres : GeneralTrace.stateValue X Y (mulPrefixResult X Y fuel).state ∈ baseI) :
    |X.val * Y.val - (mulPrefixResult X Y fuel).approx| ≤
      (mulPrefixResult X Y fuel).errorBound := by
  have hs : GeneralTrace.SafeAt X Y mulInitState := mulInit_safe X Y
  calc
    |X.val * Y.val - (mulPrefixResult X Y fuel).approx|
      = |GeneralTrace.stateValue X Y mulInitState - (mulPrefixResult X Y fuel).approx| := by
          rw [mulInit_stateValue]
    _ ≤ (mulPrefixResult X Y fuel).errorBound := by
          simpa [mulPrefixResult] using
            prefixResult_error_le X Y fuel mulInitState hs hres

theorem mulPrefix_realized_by_safeRun
    (X Y : MobiusReal) (fuel : ℕ) :
    SafeVMRun X Y mulInitState
      ((mulPrefixResult X Y fuel).digits.map digit_to_LFT)
      (mulPrefixResult X Y fuel).state := by
  simpa [mulPrefixResult] using
    prefixResult_realized_by_safeRun X Y fuel mulInitState (mulInit_safe X Y)

theorem mulPrefix_toReal_eq_digitListApprox_add_scaled
    (X Y : DigitStream) (fuel : ℕ) :
    (MobiusReal.fromStream X).val * (MobiusReal.fromStream Y).val =
      (mulPrefixResult (MobiusReal.fromStream X) (MobiusReal.fromStream Y) fuel).approx +
        GeneralTrace.stateValue
            (MobiusReal.fromStream X)
            (MobiusReal.fromStream Y)
            (mulPrefixResult (MobiusReal.fromStream X) (MobiusReal.fromStream Y) fuel).state /
          2 ^ (mulPrefixResult (MobiusReal.fromStream X) (MobiusReal.fromStream Y) fuel).digits.length := by
  simpa using
    mulPrefix_eq_value_plus_residual (MobiusReal.fromStream X) (MobiusReal.fromStream Y) fuel

end Mobius
end Computable
