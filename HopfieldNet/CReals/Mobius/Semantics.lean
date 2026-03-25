import HopfieldNet.CReals.Mobius.Basic

/-!
# Möbius streams: semantic bridge (experimental)

This file adds the **semantic layer** for the Möbius-stream machine:

- a (classical) denotation `MobiusReal.val : ℝ`, defined as a `lim` of partial compositions
- algebraic invariance lemmas showing that VM micro-steps (`absorbX`, `emit`) preserve real meaning
- the canonical initial tensors for `add`, `mul`, `sub`, `div`

The deeper “nested interval / uniqueness” theorem is intentionally deferred: `Filter.lim` is defined
without assuming convergence, so this file can provide a stable API while we later prove the
contractive streams really converge to a unique real.
-/

namespace Computable
namespace Mobius

/-! ## Denotation -/

noncomputable def MobiusReal.val (x : MobiusReal) : ℝ :=
  lim (Filter.map (fun n => LFT.apply (partialComp x.stream n) 0) Filter.atTop)

/-! ## Tensor semantics and invariance -/

namespace Tensor

noncomputable def valueAt (T : Tensor) (x y : ℝ) : ℝ :=
  Tensor.apply T x y

theorem absorbX_invariant (T : Tensor) (M : LFT) (x y : ℝ)
    (h_lft_den : ((M.c : ℝ) * x + (M.d : ℝ)) ≠ 0)
    (h_den_old :
        ((T.e : ℝ) * (LFT.apply M x) * y + (T.f : ℝ) * (LFT.apply M x) + (T.g : ℝ) * y + (T.h : ℝ)) ≠ 0)
    (h_den_new :
        (((T.absorbX M).e : ℝ) * x * y + ((T.absorbX M).f : ℝ) * x + ((T.absorbX M).g : ℝ) * y +
              ((T.absorbX M).h : ℝ)) ≠ 0) :
    T.valueAt (LFT.apply M x) y = (T.absorbX M).valueAt x y := by
  -- Expand the LFT application to `u / v` (choosing `v` in the syntactic normal form `x*c + d`).
  set u : ℝ := x * (M.a : ℝ) + (M.b : ℝ)
  set v : ℝ := x * (M.c : ℝ) + (M.d : ℝ)
  have hv : v ≠ 0 := by
    simpa [v, mul_comm, add_comm, add_left_comm, add_assoc] using h_lft_den
  have hx' : LFT.apply M x = u / v := by
    simp [LFT.apply, u, v, mul_comm]
  have h_den_old' : Tensor.denAt T (u / v) y ≠ 0 := by
    simpa [Tensor.denAt, hx', u, v] using h_den_old
  have h_den_new' : Tensor.denAt (T.absorbX M) x y ≠ 0 := by
    simpa [Tensor.denAt] using h_den_new
  -- Key algebraic identity: absorbing is substitution `x ↦ u/v`, clearing the common denominator `v`.
  have h_num :
      Tensor.numAt (T.absorbX M) x y = v * Tensor.numAt T (u / v) y := by
    -- unfold and clear the (small) denominator coming from `u / v`
    simp [Tensor.numAt, u, v, Tensor.absorbX]
    field_simp [hv]
    ring_nf
  have h_den :
      Tensor.denAt (T.absorbX M) x y = v * Tensor.denAt T (u / v) y := by
    simp [Tensor.denAt, u, v, Tensor.absorbX]
    field_simp [hv]
    ring_nf
  -- Now cancel the common factor `v`.
  unfold Tensor.valueAt
  calc
    Tensor.apply T (LFT.apply M x) y
        = Tensor.numAt T (u / v) y / Tensor.denAt T (u / v) y := by
            -- use `hx'` to avoid commutativity normal-form issues
            simp [Tensor.apply, hx', Tensor.numAt, Tensor.denAt]
    _ = (v * Tensor.numAt T (u / v) y) / (v * Tensor.denAt T (u / v) y) := by
            field_simp [hv, h_den_old']
            -- `field_simp` closes this step after normalization.
    _ = Tensor.numAt (T.absorbX M) x y / Tensor.denAt (T.absorbX M) x y := by
            simp [h_num, h_den]
    _ = Tensor.apply (T.absorbX M) x y := by
            simp [Tensor.apply, Tensor.numAt, Tensor.denAt]

theorem absorbY_invariant (T : Tensor) (M : LFT) (x y : ℝ)
    (h_lft_den : ((M.c : ℝ) * y + (M.d : ℝ)) ≠ 0)
    (h_den_old :
        ((T.e : ℝ) * x * (LFT.apply M y) + (T.f : ℝ) * x + (T.g : ℝ) * (LFT.apply M y) + (T.h : ℝ)) ≠ 0)
    (_h_den_new :
        (((T.absorbY M).e : ℝ) * x * y + ((T.absorbY M).f : ℝ) * x + ((T.absorbY M).g : ℝ) * y +
              ((T.absorbY M).h : ℝ)) ≠ 0) :
    T.valueAt x (LFT.apply M y) = (T.absorbY M).valueAt x y := by
  set u : ℝ := y * (M.a : ℝ) + (M.b : ℝ)
  set v : ℝ := y * (M.c : ℝ) + (M.d : ℝ)
  have hv : v ≠ 0 := by
    simpa [v, mul_comm, add_comm, add_left_comm, add_assoc] using h_lft_den
  have hy' : LFT.apply M y = u / v := by
    simp [LFT.apply, u, v, mul_comm]
  have h_den_old' : Tensor.denAt T x (u / v) ≠ 0 := by
    simpa [Tensor.denAt, hy', u, v] using h_den_old
  have h_num :
      Tensor.numAt (T.absorbY M) x y = v * Tensor.numAt T x (u / v) := by
    simp [Tensor.numAt, u, v, Tensor.absorbY]
    field_simp [hv]
    ring_nf
  have h_den :
      Tensor.denAt (T.absorbY M) x y = v * Tensor.denAt T x (u / v) := by
    simp [Tensor.denAt, u, v, Tensor.absorbY]
    field_simp [hv]
    ring_nf
  unfold Tensor.valueAt
  calc
    Tensor.apply T x (LFT.apply M y)
        = Tensor.numAt T x (u / v) / Tensor.denAt T x (u / v) := by
            simp [Tensor.apply, hy', Tensor.numAt, Tensor.denAt]
    _ = (v * Tensor.numAt T x (u / v)) / (v * Tensor.denAt T x (u / v)) := by
            field_simp [hv, h_den_old']
    _ = Tensor.numAt (T.absorbY M) x y / Tensor.denAt (T.absorbY M) x y := by
            simp [h_num, h_den]
    _ = Tensor.apply (T.absorbY M) x y := by
            simp [Tensor.apply, Tensor.numAt, Tensor.denAt]

theorem emit_invariant (T : Tensor) (D : LFT) (x y : ℝ)
    (h_den_new :
        (((T.emit D).e : ℝ) * x * y + ((T.emit D).f : ℝ) * x + ((T.emit D).g : ℝ) * y + ((T.emit D).h : ℝ)) ≠ 0)
    (h_den_old :
        ((T.e : ℝ) * x * y + (T.f : ℝ) * x + (T.g : ℝ) * y + (T.h : ℝ)) ≠ 0)
    (h_lft_den : ((D.c : ℝ) * ((T.emit D).valueAt x y) + (D.d : ℝ)) ≠ 0) :
    T.valueAt x y = LFT.apply D ((T.emit D).valueAt x y) := by
  -- Work with `num/den` for both tensors.
  let N : ℝ := Tensor.numAt T x y
  let D0 : ℝ := Tensor.denAt T x y
  let N' : ℝ := Tensor.numAt (T.emit D) x y
  let D' : ℝ := Tensor.denAt (T.emit D) x y
  have hD0 : D0 ≠ 0 := by
    simpa [D0, Tensor.denAt] using h_den_old
  have hD' : D' ≠ 0 := by
    simpa [D', Tensor.denAt] using h_den_new
  -- Outer LFT denominator nonzero, rewritten to `N'/D'`.
  have hOuter : ((D.c : ℝ) * (N' / D') + (D.d : ℝ)) ≠ 0 := by
    simpa [Tensor.valueAt, apply_eq, N', D'] using h_lft_den
  -- `emit` computes the inverse-LFT update on the pair `(N, D0)`.
  have hN' : N' = (D.d : ℝ) * N - (D.b : ℝ) * D0 := by
    simp [N', N, D0, Tensor.numAt, Tensor.denAt, Tensor.emit]
    ring_nf
  have hD'formula : D' = -(D.c : ℝ) * N + (D.a : ℝ) * D0 := by
    simp [D', N, D0, Tensor.numAt, Tensor.denAt, Tensor.emit]
    ring_nf
  -- Determinant of `D` is nonzero over `ℝ`.
  have hdet : ((D.a * D.d - D.b * D.c : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast D.det_neq_zero
  unfold Tensor.valueAt
  -- Rewrite both tensor applications as `num/den`, then do explicit fraction algebra.
  have hT : Tensor.apply T x y = N / D0 := by simp [Tensor.apply, Tensor.numAt, Tensor.denAt, N, D0]
  have hEmit : Tensor.apply (T.emit D) x y = N' / D' := by simp [Tensor.apply, Tensor.numAt, Tensor.denAt, N', D']
  -- Reduce the goal to a rational identity.
  simp [hT, hEmit, LFT.apply]
  -- Turn the nested `N'/D'` into a single fraction.
  have hLFT :
      ((D.a : ℝ) * (N' / D') + (D.b : ℝ)) / ((D.c : ℝ) * (N' / D') + (D.d : ℝ)) =
        ((D.a : ℝ) * N' + (D.b : ℝ) * D') / ((D.c : ℝ) * N' + (D.d : ℝ) * D') := by
    field_simp [hD', hOuter]
  rw [hLFT]
  -- Substitute the `emit` update equations; the determinant cancels.
  simp [hN', hD'formula]
  -- Collapse the linear combinations to determinant multiples (avoid fragile `simp` matching).
  set A : ℝ :=
    (D.a : ℝ) * (↑D.d * N - ↑D.b * D0) + (D.b : ℝ) * (-(↑D.c * N) + ↑D.a * D0)
  set B : ℝ :=
    (D.c : ℝ) * (↑D.d * N - ↑D.b * D0) + (D.d : ℝ) * (-(↑D.c * N) + ↑D.a * D0)
  have hA : A = ((D.a * D.d - D.b * D.c : ℤ) : ℝ) * N := by
    subst A
    push_cast
    ring_nf
  have hB : B = ((D.a * D.d - D.b * D.c : ℤ) : ℝ) * D0 := by
    subst B
    push_cast
    ring_nf
  -- Reduce to cancelling a common nonzero factor.
  -- Goal is now `N / D0 = (det*N)/(det*D0)`.
  change N / D0 = A / B
  simp [hA, hB]
  have hdet' : (↑D.a * ↑D.d - ↑D.b * ↑D.c : ℝ) ≠ 0 := by
    have h := hdet
    push_cast at h
    simpa using h
  field_simp [hdet', hD0]

private lemma normalizeFactor_dvd_a (T : Tensor) : ((T.normalizeFactor : ℤ) ∣ T.a) := by
  rw [Tensor.normalizeFactor, ← Int.dvd_natAbs]
  exact Int.ofNat_dvd.mpr <|
    (Nat.gcd_dvd_left _ _).trans <| (Nat.gcd_dvd_left _ _).trans <| Nat.gcd_dvd_left _ _

private lemma normalizeFactor_dvd_b (T : Tensor) : ((T.normalizeFactor : ℤ) ∣ T.b) := by
  rw [Tensor.normalizeFactor, ← Int.dvd_natAbs]
  exact Int.ofNat_dvd.mpr <|
    (Nat.gcd_dvd_left _ _).trans <| (Nat.gcd_dvd_left _ _).trans <| Nat.gcd_dvd_right _ _

private lemma normalizeFactor_dvd_c (T : Tensor) : ((T.normalizeFactor : ℤ) ∣ T.c) := by
  rw [Tensor.normalizeFactor, ← Int.dvd_natAbs]
  exact Int.ofNat_dvd.mpr <|
    (Nat.gcd_dvd_left _ _).trans <| (Nat.gcd_dvd_right _ _).trans <| Nat.gcd_dvd_left _ _

private lemma normalizeFactor_dvd_d (T : Tensor) : ((T.normalizeFactor : ℤ) ∣ T.d) := by
  rw [Tensor.normalizeFactor, ← Int.dvd_natAbs]
  exact Int.ofNat_dvd.mpr <|
    (Nat.gcd_dvd_left _ _).trans <| (Nat.gcd_dvd_right _ _).trans <| Nat.gcd_dvd_right _ _

private lemma normalizeFactor_dvd_e (T : Tensor) : ((T.normalizeFactor : ℤ) ∣ T.e) := by
  rw [Tensor.normalizeFactor, ← Int.dvd_natAbs]
  exact Int.ofNat_dvd.mpr <|
    (Nat.gcd_dvd_right _ _).trans <| (Nat.gcd_dvd_left _ _).trans <| Nat.gcd_dvd_left _ _

private lemma normalizeFactor_dvd_f (T : Tensor) : ((T.normalizeFactor : ℤ) ∣ T.f) := by
  rw [Tensor.normalizeFactor, ← Int.dvd_natAbs]
  exact Int.ofNat_dvd.mpr <|
    (Nat.gcd_dvd_right _ _).trans <| (Nat.gcd_dvd_left _ _).trans <| Nat.gcd_dvd_right _ _

private lemma normalizeFactor_dvd_g (T : Tensor) : ((T.normalizeFactor : ℤ) ∣ T.g) := by
  rw [Tensor.normalizeFactor, ← Int.dvd_natAbs]
  exact Int.ofNat_dvd.mpr <|
    (Nat.gcd_dvd_right _ _).trans <| (Nat.gcd_dvd_right _ _).trans <| Nat.gcd_dvd_left _ _

private lemma normalizeFactor_dvd_h (T : Tensor) : ((T.normalizeFactor : ℤ) ∣ T.h) := by
  rw [Tensor.normalizeFactor, ← Int.dvd_natAbs]
  exact Int.ofNat_dvd.mpr <|
    (Nat.gcd_dvd_right _ _).trans <| (Nat.gcd_dvd_right _ _).trans <| Nat.gcd_dvd_right _ _

private lemma numAt_eq_scale_mul_numAt_divideBy
    (T : Tensor) (gZ : ℤ)
    (ha : gZ ∣ T.a) (hb : gZ ∣ T.b) (hc : gZ ∣ T.c) (hd : gZ ∣ T.d)
    (x y : ℝ) :
    Tensor.numAt T x y = (gZ : ℝ) * Tensor.numAt (T.divideBy gZ) x y := by
  have ha' := congrArg (fun z : ℤ => (z : ℝ)) (Int.ediv_mul_cancel ha)
  have hb' := congrArg (fun z : ℤ => (z : ℝ)) (Int.ediv_mul_cancel hb)
  have hc' := congrArg (fun z : ℤ => (z : ℝ)) (Int.ediv_mul_cancel hc)
  have hd' := congrArg (fun z : ℤ => (z : ℝ)) (Int.ediv_mul_cancel hd)
  simp [Tensor.numAt, Tensor.divideBy] at ha' hb' hc' hd' ⊢
  rw [← ha', ← hb', ← hc', ← hd']
  ring

private lemma denAt_eq_scale_mul_denAt_divideBy
    (T : Tensor) (gZ : ℤ)
    (he : gZ ∣ T.e) (hf : gZ ∣ T.f) (hg : gZ ∣ T.g) (hh : gZ ∣ T.h)
    (x y : ℝ) :
    Tensor.denAt T x y = (gZ : ℝ) * Tensor.denAt (T.divideBy gZ) x y := by
  have he' := congrArg (fun z : ℤ => (z : ℝ)) (Int.ediv_mul_cancel he)
  have hf' := congrArg (fun z : ℤ => (z : ℝ)) (Int.ediv_mul_cancel hf)
  have hg' := congrArg (fun z : ℤ => (z : ℝ)) (Int.ediv_mul_cancel hg)
  have hh' := congrArg (fun z : ℤ => (z : ℝ)) (Int.ediv_mul_cancel hh)
  simp [Tensor.denAt, Tensor.divideBy] at he' hf' hg' hh' ⊢
  rw [← he', ← hf', ← hg', ← hh']
  ring

theorem divideBy_invariant (T : Tensor) (gZ : ℤ) (hgZ : gZ ≠ 0)
    (ha : gZ ∣ T.a) (hb : gZ ∣ T.b) (hc : gZ ∣ T.c) (hd : gZ ∣ T.d)
    (he : gZ ∣ T.e) (hf : gZ ∣ T.f) (hg : gZ ∣ T.g) (hh : gZ ∣ T.h)
    (x y : ℝ) :
    Tensor.apply T x y = Tensor.apply (T.divideBy gZ) x y := by
  have hgR : (gZ : ℝ) ≠ 0 := by exact_mod_cast hgZ
  have hnum := numAt_eq_scale_mul_numAt_divideBy T gZ ha hb hc hd x y
  have hden := denAt_eq_scale_mul_denAt_divideBy T gZ he hf hg hh x y
  rw [Tensor.apply_eq, Tensor.apply_eq]
  rw [hnum, hden]
  field_simp [hgR]

theorem normalize_invariant (T : Tensor) (x y : ℝ) :
    Tensor.apply T x y = Tensor.apply T.normalize x y := by
  unfold Tensor.normalize
  by_cases hg : T.normalizeFactor ≤ 1
  · simp [hg]
  · have hgNat : T.normalizeFactor ≠ 0 := by
      intro h0
      have : T.normalizeFactor ≤ 1 := by simp [h0]
      exact hg this
    have hgZ : ((T.normalizeFactor : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast hgNat
    simpa [hg, Tensor.divideBy] using
      divideBy_invariant T (T.normalizeFactor : ℤ) hgZ
        (normalizeFactor_dvd_a T) (normalizeFactor_dvd_b T)
        (normalizeFactor_dvd_c T) (normalizeFactor_dvd_d T)
        (normalizeFactor_dvd_e T) (normalizeFactor_dvd_f T)
        (normalizeFactor_dvd_g T) (normalizeFactor_dvd_h T) x y

theorem normalize_valueAt (T : Tensor) (x y : ℝ) :
    Tensor.valueAt T x y = Tensor.valueAt T.normalize x y := by
  simpa [Tensor.valueAt] using normalize_invariant T x y

theorem denAt_ne_zero_normalize_iff (T : Tensor) (x y : ℝ) :
    Tensor.denAt T x y ≠ 0 ↔ Tensor.denAt T.normalize x y ≠ 0 := by
  unfold Tensor.normalize
  by_cases hg : T.normalizeFactor ≤ 1
  · simp [hg]
  · have hgNat : T.normalizeFactor ≠ 0 := by
      intro h0
      have : T.normalizeFactor ≤ 1 := by simp [h0]
      exact hg this
    have hgZ : ((T.normalizeFactor : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast hgNat
    have hgR : (((T.normalizeFactor : ℕ) : ℤ) : ℝ) ≠ 0 := by
      exact_mod_cast hgZ
    have hden :
        Tensor.denAt T x y =
          (((T.normalizeFactor : ℕ) : ℤ) : ℝ) *
            Tensor.denAt (T.divideBy (T.normalizeFactor : ℤ)) x y := by
      simpa [Tensor.divideBy] using
        denAt_eq_scale_mul_denAt_divideBy T (T.normalizeFactor : ℤ)
          (normalizeFactor_dvd_e T) (normalizeFactor_dvd_f T)
          (normalizeFactor_dvd_g T) (normalizeFactor_dvd_h T) x y
    constructor
    · intro hT
      have hdiv : Tensor.denAt (T.divideBy (T.normalizeFactor : ℤ)) x y ≠ 0 := by
        intro hzero
        apply hT
        rw [hden]
        simp [hzero]
      simpa [hg] using hdiv
    · intro hnorm
      have hdiv : Tensor.denAt (T.divideBy (T.normalizeFactor : ℤ)) x y ≠ 0 := by
        simpa [hg] using hnorm
      rw [hden]
      exact mul_ne_zero hgR hdiv

end Tensor

/-! ## Canonical arithmetic tensors -/

def addTensor : Tensor where
  a := 0; b := 1; c := 1; d := 0
  e := 0; f := 0; g := 0; h := 1

/-- Averaged addition tensor, denoting `(x + y) / 2` on `[-1,1]^2`. -/
def halfAddTensor : Tensor where
  a := 0; b := 1; c := 1; d := 0
  e := 0; f := 0; g := 0; h := 2

def mulTensor : Tensor where
  a := 1; b := 0; c := 0; d := 0
  e := 0; f := 0; g := 0; h := 1

def subTensor : Tensor where
  a := 0; b := 1; c := -1; d := 0
  e := 0; f := 0; g := 0; h := 1

def divTensor : Tensor where
  a := 0; b := 1; c := 0; d := 0
  e := 0; f := 0; g := 1; h := 0

@[simp] theorem addTensor_valueAt (x y : ℝ) :
    Tensor.valueAt addTensor x y = x + y := by
  simp [Tensor.valueAt, Tensor.apply, addTensor]

@[simp] theorem halfAddTensor_valueAt (x y : ℝ) :
    Tensor.valueAt halfAddTensor x y = (x + y) / 2 := by
  simp [Tensor.valueAt, Tensor.apply, halfAddTensor]

@[simp] theorem mulTensor_valueAt (x y : ℝ) :
    Tensor.valueAt mulTensor x y = x * y := by
  simp [Tensor.valueAt, Tensor.apply, mulTensor]

@[simp] theorem subTensor_valueAt (x y : ℝ) :
    Tensor.valueAt subTensor x y = x - y := by
  simp [Tensor.valueAt, Tensor.apply, subTensor, sub_eq_add_neg]

@[simp] theorem divTensor_valueAt (x y : ℝ) :
    Tensor.valueAt divTensor x y = x / y := by
  simp [Tensor.valueAt, Tensor.apply, divTensor]

end Mobius
end Computable
