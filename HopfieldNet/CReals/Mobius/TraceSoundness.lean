import HopfieldNet.CReals.Mobius.VMTraceSoundness
namespace Computable
namespace Mobius

open scoped BigOperators

/-! ## Trace soundness (VM → ℝ) -/

/-! ### Stream shifting -/

/-! ### VM traces tied to fixed inputs -/

/-!
`VMRun X Y s ds s'` means: starting at `s`, the VM makes finitely many steps tied to inputs `X,Y`
and emits exactly the list `ds` (in chronological order), ending at `s'`.

Absorption steps do not contribute to `ds`.
-/
inductive SafeVMRun (X Y : MobiusReal) : VMState → List LFT → VMState → Prop
  | refl (s : VMState) (hs : GeneralTrace.SafeAt X Y s) : SafeVMRun X Y s [] s
  | stepNone {s s' t : VMState} {ds : List LFT}
      (h : GeneralTrace.VMStepXY X Y s none s')
      (hs : GeneralTrace.SafeAt X Y s)
      (hs' : GeneralTrace.SafeAt X Y s')
      (ht : SafeVMRun X Y s' ds t) :
      SafeVMRun X Y s ds t
  | stepSome {s s' t : VMState} {d : LFT} {ds : List LFT}
      (h : GeneralTrace.VMStepXY X Y s (some d) s')
      (hs : GeneralTrace.SafeAt X Y s)
      (hs' : GeneralTrace.SafeAt X Y s')
      (ht : SafeVMRun X Y s' ds t) :
      SafeVMRun X Y s (d :: ds) t

noncomputable def emittedValue (ds : List LFT) (r : ℝ) : ℝ :=
  ds.foldr (fun D acc => LFT.apply D acc) r

@[simp] theorem emittedValue_nil (r : ℝ) :
    emittedValue [] r = r := rfl

@[simp] theorem emittedValue_cons (d : LFT) (ds : List LFT) (r : ℝ) :
    emittedValue (d :: ds) r = LFT.apply d (emittedValue ds r) := rfl

@[simp] lemma digit_to_LFT_apply (d : Digit) (x : ℝ) :
    LFT.apply (digit_to_LFT d) x = (x + d.toRat) / 2 := by
  cases d <;> simp [digit_to_LFT, digitNeg, digitZero, digitPos, LFT.apply, mul_comm]

/-- Real value represented by a finite digit prefix, with zero residual tail. -/
noncomputable def digitListApprox : List Digit → ℝ
  | [] => 0
  | d :: ds => (d.toRat : ℝ) / 2 + digitListApprox ds / 2

@[simp] theorem digitListApprox_nil : digitListApprox [] = 0 := rfl

@[simp] theorem digitListApprox_cons (d : Digit) (ds : List Digit) :
    digitListApprox (d :: ds) = (d.toRat : ℝ) / 2 + digitListApprox ds / 2 := rfl

private lemma div_pow_two_succ (r : ℝ) (n : ℕ) :
    (r / 2 ^ n) / 2 = r / 2 ^ (n + 1) := by
  have hpow : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  field_simp [pow_succ, hpow]
  ring

theorem emittedValue_map_digit_to_LFT_eq_digitListApprox_add_scaled :
    ∀ (ds : List Digit) (r : ℝ),
      emittedValue (ds.map digit_to_LFT) r =
        digitListApprox ds + r / 2 ^ ds.length
  | [], r => by
      simp [digitListApprox]
  | d :: ds, r => by
      calc
        emittedValue ((d :: ds).map digit_to_LFT) r
            = LFT.apply (digit_to_LFT d) (emittedValue (ds.map digit_to_LFT) r) := by
                simp [emittedValue]
        _ = (emittedValue (ds.map digit_to_LFT) r + d.toRat) / 2 := by
              rw [digit_to_LFT_apply]
        _ = ((digitListApprox ds + r / 2 ^ ds.length) + d.toRat) / 2 := by
              rw [emittedValue_map_digit_to_LFT_eq_digitListApprox_add_scaled ds r]
        _ = (d.toRat : ℝ) / 2 + digitListApprox ds / 2 + (r / 2 ^ ds.length) / 2 := by
              ring
        _ = (d.toRat : ℝ) / 2 + digitListApprox ds / 2 + r / 2 ^ (ds.length + 1) := by
              rw [div_pow_two_succ]
        _ = digitListApprox (d :: ds) + r / 2 ^ (List.length (d :: ds)) := by
              simp [digitListApprox]

theorem emittedValue_map_digit_to_LFT_sub_digitListApprox_abs_le
    (ds : List Digit) {r : ℝ} (hr : r ∈ baseI) :
    |emittedValue (ds.map digit_to_LFT) r - digitListApprox ds| ≤
      (1 : ℝ) / 2 ^ ds.length := by
  have hrabs : |r| ≤ (1 : ℝ) := by
    exact abs_le.mpr ⟨hr.1, hr.2⟩
  calc
    |emittedValue (ds.map digit_to_LFT) r - digitListApprox ds|
        = |r / 2 ^ ds.length| := by
            rw [emittedValue_map_digit_to_LFT_eq_digitListApprox_add_scaled]
            congr 1
            ring
    _ = |r| * ((1 : ℝ) / 2 ^ ds.length) := by
          simp [div_eq_mul_inv, abs_mul]
    _ ≤ 1 * ((1 : ℝ) / 2 ^ ds.length) := by
          gcongr
    _ = (1 : ℝ) / 2 ^ ds.length := by ring

theorem safe_step
    (X Y : MobiusReal) {s s' : VMState} {o : Option LFT}
    (h : GeneralTrace.VMStepXY X Y s o s')
    (hs : GeneralTrace.SafeAt X Y s) :
    GeneralTrace.SafeAt X Y s' := by
  cases h with
  | emitNeg hor =>
      simpa [GeneralTrace.SafeAt, Tensor.denAt, Tensor.emit, digitNeg] using hs
  | emitZero hor =>
      simpa [GeneralTrace.SafeAt, Tensor.denAt, Tensor.emit, digitZero] using hs
  | emitPos hor =>
      simpa [GeneralTrace.SafeAt, Tensor.denAt, Tensor.emit, digitPos] using hs
  | absorbX hor hx =>
      set M : LFT := X.stream s.idx_x
      set xTail : ℝ := (MobiusReal.drop X (s.idx_x + 1)).val
      set yVal : ℝ := (MobiusReal.drop Y s.idx_y).val
      have hxTail : xTail ∈ baseI := by
        simpa [xTail] using GeneralTrace.drop_val_mem_baseI X (s.idx_x + 1)
      have hMNoPole : M.NoPoleOnBase := by
        simpa [M, partialCompFrom] using X.contractive.no_poles_from s.idx_x 0
      have hMden : ((M.c : ℝ) * xTail + (M.d : ℝ)) ≠ 0 := by
        exact LFT.denom_ne_zero_of_NoPoleOnBase M (x := xTail) hxTail hMNoPole
      have hdrop :
          (MobiusReal.drop X s.idx_x).val = LFT.apply M xTail := by
        simpa [M, xTail, MobiusReal.drop, Nat.add_assoc] using (MobiusReal.val_drop_succ X s.idx_x)
      have hsOld :
          Tensor.denAt s.T (LFT.apply M xTail) yVal ≠ 0 := by
        simpa [GeneralTrace.SafeAt, hdrop, yVal] using hs
      set u : ℝ := xTail * (M.a : ℝ) + (M.b : ℝ)
      set v : ℝ := xTail * (M.c : ℝ) + (M.d : ℝ)
      have hv : v ≠ 0 := by
        simpa [v, mul_comm, add_comm, add_left_comm, add_assoc] using hMden
      have hx' : LFT.apply M xTail = u / v := by
        simp [LFT.apply, u, v, mul_comm]
      have hsOld' : Tensor.denAt s.T (u / v) yVal ≠ 0 := by
        simpa [Tensor.denAt, hx', u, v] using hsOld
      have hden :
          Tensor.denAt (s.T.absorbX M) xTail yVal = v * Tensor.denAt s.T (u / v) yVal := by
        simp [Tensor.denAt, u, v, Tensor.absorbX]
        field_simp [hv]
        ring_nf
      have hsNew : Tensor.denAt (s.T.absorbX M) xTail yVal ≠ 0 := by
        rw [hden]
        exact mul_ne_zero hv hsOld'
      simpa [GeneralTrace.SafeAt, xTail, yVal] using hsNew
  | absorbY hor hy =>
      set M : LFT := Y.stream s.idx_y
      set xVal : ℝ := (MobiusReal.drop X s.idx_x).val
      set yTail : ℝ := (MobiusReal.drop Y (s.idx_y + 1)).val
      have hyTail : yTail ∈ baseI := by
        simpa [yTail] using GeneralTrace.drop_val_mem_baseI Y (s.idx_y + 1)
      have hMNoPole : M.NoPoleOnBase := by
        simpa [M, partialCompFrom] using Y.contractive.no_poles_from s.idx_y 0
      have hMden : ((M.c : ℝ) * yTail + (M.d : ℝ)) ≠ 0 := by
        exact LFT.denom_ne_zero_of_NoPoleOnBase M (x := yTail) hyTail hMNoPole
      have hdrop :
          (MobiusReal.drop Y s.idx_y).val = LFT.apply M yTail := by
        simpa [M, yTail, MobiusReal.drop, Nat.add_assoc] using (MobiusReal.val_drop_succ Y s.idx_y)
      have hsOld :
          Tensor.denAt s.T xVal (LFT.apply M yTail) ≠ 0 := by
        simpa [GeneralTrace.SafeAt, hdrop, xVal] using hs
      set u : ℝ := yTail * (M.a : ℝ) + (M.b : ℝ)
      set v : ℝ := yTail * (M.c : ℝ) + (M.d : ℝ)
      have hv : v ≠ 0 := by
        simpa [v, mul_comm, add_comm, add_left_comm, add_assoc] using hMden
      have hy' : LFT.apply M yTail = u / v := by
        simp [LFT.apply, u, v, mul_comm]
      have hsOld' : Tensor.denAt s.T xVal (u / v) ≠ 0 := by
        simpa [Tensor.denAt, hy', u, v] using hsOld
      have hden :
          Tensor.denAt (s.T.absorbY M) xVal yTail = v * Tensor.denAt s.T xVal (u / v) := by
        simp [Tensor.denAt, u, v, Tensor.absorbY]
        field_simp [hv]
        ring_nf
      have hsNew : Tensor.denAt (s.T.absorbY M) xVal yTail ≠ 0 := by
        rw [hden]
        exact mul_ne_zero hv hsOld'
      simpa [GeneralTrace.SafeAt, xVal, yTail] using hsNew

/-!
### VM soundness (finite prefix form)

This is the core “invariant along a run” statement. The full infinite `vm_soundness` theorem
will be proved by taking limits once we connect:

- the emitted digit stream (as a `MobiusReal`) to `partialComp`,
- and the residual tensor/state sequence to a shrinking nested-interval denotation.

For now we provide the fully proved *finite* semantic equation.
-/
theorem vm_soundness_prefix
    (s₀ s₁ : VMState) (X Y : MobiusReal) (ds : List LFT)
    (hRun : SafeVMRun X Y s₀ ds s₁) :
    GeneralTrace.stateValue X Y s₀ =
      emittedValue ds (GeneralTrace.stateValue X Y s₁) := by
  induction hRun with
  | refl s hs =>
      simp [emittedValue]
  | stepNone h hs hs' ht ih =>
      exact (GeneralTrace.stateValue_step_none (X := X) (Y := Y) h hs hs').trans ih
  | stepSome h hs hs' ht ih =>
      have hstep := GeneralTrace.stateValue_step_some (X := X) (Y := Y) h hs hs'
      cases h with
      | emitNeg hor =>
          exact hstep.trans <| by
            simpa [emittedValue] using congrArg (fun r => LFT.apply digitNeg r) ih
      | emitZero hor =>
          exact hstep.trans <| by
            simpa [emittedValue] using congrArg (fun r => LFT.apply digitZero r) ih
      | emitPos hor =>
          exact hstep.trans <| by
            simpa [emittedValue] using congrArg (fun r => LFT.apply digitPos r) ih

theorem vm_soundness_prefix_one
    (s₀ s₁ : VMState) (X Y : MobiusReal) (d : LFT)
    (hRun : SafeVMRun X Y s₀ [d] s₁) :
    GeneralTrace.stateValue X Y s₀ =
      LFT.apply d (GeneralTrace.stateValue X Y s₁) := by
  simpa [emittedValue] using vm_soundness_prefix s₀ s₁ X Y [d] hRun

theorem vm_soundness_prefix_two
    (s₀ s₂ : VMState) (X Y : MobiusReal) (d₁ d₂ : LFT)
    (hRun : SafeVMRun X Y s₀ [d₁, d₂] s₂) :
    GeneralTrace.stateValue X Y s₀ =
      LFT.apply d₁ (LFT.apply d₂ (GeneralTrace.stateValue X Y s₂)) := by
  simpa [emittedValue] using vm_soundness_prefix s₀ s₂ X Y [d₁, d₂] hRun

/-!
### VM soundness (full infinite trace form)

This packages the general absorb-aware theorem from `VMTraceSoundness` in the API layer of this
file. The finite prefix theorem above is the local inductive invariant; the theorem below combines
it with the shrinking-image denotation argument for the emitted digit stream.
-/
theorem vm_soundness_infinite
    (X Y : MobiusReal) (s₀ : VMState) (out : DigitStream)
    (σ : ℕ → VMState) (ℓ : ℕ → Option LFT)
    (hσ0 : σ 0 = s₀)
    (hstep : ∀ i, GeneralTrace.VMStepXY X Y (σ i) (ℓ i) (σ (i + 1)))
    (hsafe : ∀ i, GeneralTrace.SafeAt X Y (σ i))
    (sched : GeneralTrace.EmitSchedule ℓ out) :
    (MobiusReal.fromStream out).val = GeneralTrace.stateValue X Y s₀ := by
  exact GeneralTrace.vm_soundness_with_absorb
    (X := X) (Y := Y) (s₀ := s₀) (out := out)
    (σ := σ) (ℓ := ℓ) hσ0 hstep hsafe sched

end Mobius
end Computable

