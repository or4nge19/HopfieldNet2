import HopfieldNet.CReals.Mobius.TraceSoundness

namespace Computable
namespace Mobius

def stepStreams (sx sy : LFTStream) (s : VMState) : Option Digit × VMState :=
  match s.T.oracle with
  | .neg =>
      (some .neg, { s with T := s.T.emit digitNeg })
  | .zero =>
      (some .zero, { s with T := s.T.emit digitZero })
  | .pos =>
      (some .pos, { s with T := s.T.emit digitPos })
  | .absorb =>
      if s.absorb_x_next then
        (none, { s with
          T := s.T.absorbX (sx s.idx_x)
          idx_x := s.idx_x + 1
          absorb_x_next := false })
      else
        (none, { s with
          T := s.T.absorbY (sy s.idx_y)
          idx_y := s.idx_y + 1
          absorb_x_next := true })

def step (X Y : MobiusReal) (s : VMState) : Option Digit × VMState :=
  stepStreams X.stream Y.stream s

def runSteps (sx sy : LFTStream) : ℕ → VMState → List Digit × VMState
  | 0, s => ([], s)
  | n + 1, s =>
      let out := stepStreams sx sy s
      let tail := runSteps sx sy n out.2
      match out.1 with
      | none => tail
      | some d => (d :: tail.1, tail.2)

def run (X Y : MobiusReal) (fuel : ℕ) (s : VMState) : List Digit × VMState :=
  runSteps X.stream Y.stream fuel s

def emittedPrefix (X Y : MobiusReal) (fuel : ℕ) (s : VMState) : List Digit :=
  (run X Y fuel s).1

def finalState (X Y : MobiusReal) (fuel : ℕ) (s : VMState) : VMState :=
  (run X Y fuel s).2

theorem runSteps_add (sx sy : LFTStream) (n m : ℕ) (s : VMState) :
    runSteps sx sy (n + m) s =
      let r1 := runSteps sx sy n s
      let r2 := runSteps sx sy m r1.2
      (r1.1 ++ r2.1, r2.2) := by
  induction n generalizing s with
  | zero =>
      simp [runSteps]
  | succ n ih =>
      rw [Nat.succ_add, runSteps]
      set out := stepStreams sx sy s
      have ih' := ih out.2
      cases hout : out.1 with
      | none =>
          simpa [out, hout, runSteps, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih'
      | some d =>
          simpa [out, hout, runSteps, List.cons_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            congrArg (fun p : List Digit × VMState => (d :: p.1, p.2)) ih'

theorem stepStreams_spec (sx sy : LFTStream) (s : VMState) :
    let out := stepStreams sx sy s
    VMStep s (Option.map digit_to_LFT out.1) out.2 := by
  unfold stepStreams
  cases hor : s.T.oracle with
  | neg =>
      simp [hor, digit_to_LFT, VMStep.emitNeg]
  | zero =>
      simp [hor, digit_to_LFT, VMStep.emitZero]
  | pos =>
      simp [hor, digit_to_LFT, VMStep.emitPos]
  | absorb =>
      by_cases hx : s.absorb_x_next = true
      · simp [hor, hx, VMStep.absorbX]
      · have hy : s.absorb_x_next = false := by
          cases hbool : s.absorb_x_next <;> simp_all
        simp [hor, hy, VMStep.absorbY]

theorem step_spec (X Y : MobiusReal) (s : VMState) :
    let out := step X Y s
    GeneralTrace.VMStepXY X Y s (Option.map digit_to_LFT out.1) out.2 := by
  unfold step stepStreams
  cases hor : s.T.oracle with
  | neg =>
      simp [hor, digit_to_LFT, GeneralTrace.VMStepXY.emitNeg]
  | zero =>
      simp [hor, digit_to_LFT, GeneralTrace.VMStepXY.emitZero]
  | pos =>
      simp [hor, digit_to_LFT, GeneralTrace.VMStepXY.emitPos]
  | absorb =>
      by_cases hx : s.absorb_x_next = true
      · simp [hor, hx, GeneralTrace.VMStepXY.absorbX]
      · have hy : s.absorb_x_next = false := by
          cases hbool : s.absorb_x_next <;> simp_all
        simp [hor, hy, GeneralTrace.VMStepXY.absorbY]

theorem runSteps_safeVMRun (X Y : MobiusReal) :
    ∀ fuel s, GeneralTrace.SafeAt X Y s →
      SafeVMRun X Y s
        (((runSteps X.stream Y.stream fuel s).1).map digit_to_LFT)
        ((runSteps X.stream Y.stream fuel s).2)
  | 0, s, hs => by
      simpa [runSteps] using (SafeVMRun.refl (X := X) (Y := Y) s hs)
  | fuel + 1, s, hs => by
      dsimp [runSteps]
      let out := stepStreams X.stream Y.stream s
      have hstep : GeneralTrace.VMStepXY X Y s (Option.map digit_to_LFT out.1) out.2 := by
        simpa [step, out] using (step_spec X Y s)
      have hs' : GeneralTrace.SafeAt X Y out.2 := by
        exact safe_step (X := X) (Y := Y) hstep hs
      have htail :
          SafeVMRun X Y out.2
            (((runSteps X.stream Y.stream fuel out.2).1).map digit_to_LFT)
            ((runSteps X.stream Y.stream fuel out.2).2) :=
        runSteps_safeVMRun X Y fuel out.2 hs'
      cases hout : out.1 with
      | none =>
          simpa [out, hout] using
            (SafeVMRun.stepNone (X := X) (Y := Y)
              (by simpa [hout] using hstep) hs hs' htail)
      | some d =>
          simpa [out, hout] using
            (SafeVMRun.stepSome (X := X) (Y := Y)
              (by simpa [hout] using hstep) hs hs' htail)

theorem run_safeVMRun (X Y : MobiusReal) (fuel : ℕ) (s : VMState)
    (hs : GeneralTrace.SafeAt X Y s) :
    SafeVMRun X Y s ((run X Y fuel s).1.map digit_to_LFT) (run X Y fuel s).2 := by
  simpa [run] using runSteps_safeVMRun X Y fuel s hs

theorem run_soundness_prefix (X Y : MobiusReal) (fuel : ℕ) (s : VMState)
    (hs : GeneralTrace.SafeAt X Y s) :
    GeneralTrace.stateValue X Y s =
      emittedValue ((run X Y fuel s).1.map digit_to_LFT)
        (GeneralTrace.stateValue X Y ((run X Y fuel s).2)) := by
  exact vm_soundness_prefix s (run X Y fuel s).2 X Y ((run X Y fuel s).1.map digit_to_LFT)
    (run_safeVMRun X Y fuel s hs)

theorem run_soundness_prefix_digitListApprox
    (X Y : MobiusReal) (fuel : ℕ) (s : VMState)
    (hs : GeneralTrace.SafeAt X Y s) :
    GeneralTrace.stateValue X Y s =
      digitListApprox ((run X Y fuel s).1) +
        GeneralTrace.stateValue X Y ((run X Y fuel s).2) /
          2 ^ ((run X Y fuel s).1.length) := by
  calc
    GeneralTrace.stateValue X Y s
        = emittedValue ((run X Y fuel s).1.map digit_to_LFT)
            (GeneralTrace.stateValue X Y ((run X Y fuel s).2)) :=
          run_soundness_prefix X Y fuel s hs
    _ = digitListApprox ((run X Y fuel s).1) +
          GeneralTrace.stateValue X Y ((run X Y fuel s).2) /
            2 ^ ((run X Y fuel s).1.length) :=
          emittedValue_map_digit_to_LFT_eq_digitListApprox_add_scaled
            ((run X Y fuel s).1) (GeneralTrace.stateValue X Y ((run X Y fuel s).2))

theorem run_soundness_prefix_digitListApprox_error
    (X Y : MobiusReal) (fuel : ℕ) (s : VMState)
    (hs : GeneralTrace.SafeAt X Y s)
    (hres : GeneralTrace.stateValue X Y ((run X Y fuel s).2) ∈ baseI) :
    |GeneralTrace.stateValue X Y s - digitListApprox ((run X Y fuel s).1)| ≤
      (1 : ℝ) / 2 ^ ((run X Y fuel s).1.length) := by
  rw [run_soundness_prefix X Y fuel s hs]
  exact emittedValue_map_digit_to_LFT_sub_digitListApprox_abs_le
    ((run X Y fuel s).1) hres

theorem run_add (X Y : MobiusReal) (m n : ℕ) (s : VMState) :
    run X Y (m + n) s =
      let r1 := run X Y m s
      let r2 := run X Y n r1.2
      (r1.1 ++ r2.1, r2.2) := by
  simpa [run] using runSteps_add X.stream Y.stream m n s

theorem emittedPrefix_add (X Y : MobiusReal) (m n : ℕ) (s : VMState) :
    emittedPrefix X Y (m + n) s =
      emittedPrefix X Y m s ++ emittedPrefix X Y n (finalState X Y m s) := by
  simpa [emittedPrefix, finalState, run_add] using congrArg Prod.fst (run_add X Y m n s)

theorem finalState_add (X Y : MobiusReal) (m n : ℕ) (s : VMState) :
    finalState X Y (m + n) s =
      finalState X Y n (finalState X Y m s) := by
  simpa [finalState, run_add] using congrArg Prod.snd (run_add X Y m n s)

theorem emittedPrefix_prefix_of_le (X Y : MobiusReal) {m n : ℕ} (h : m ≤ n) (s : VMState) :
    ∃ ds, emittedPrefix X Y n s = emittedPrefix X Y m s ++ ds := by
  rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
  refine ⟨emittedPrefix X Y k (finalState X Y m s), ?_⟩
  simpa [emittedPrefix_add]

theorem safeVMRun_realized_by_run (X Y : MobiusReal) :
    ∀ {s t : VMState} {ds : List LFT}, SafeVMRun X Y s ds t →
      ∃ fuel, (run X Y fuel s).2 = t ∧ ((run X Y fuel s).1.map digit_to_LFT = ds)
  | s, _, _, SafeVMRun.refl _ _ => by
      refine ⟨0, ?_, ?_⟩ <;> simp [run, runSteps]
  | s, _, _, SafeVMRun.stepNone h hs hs' ht => by
      rcases safeVMRun_realized_by_run X Y ht with ⟨fuel, hstate, hds⟩
      cases h with
      | absorbX hor hx =>
          refine ⟨fuel + 1, ?_, ?_⟩
          · simpa [run, runSteps, step, stepStreams, hor, hx] using hstate
          · simpa [run, runSteps, step, stepStreams, hor, hx] using hds
      | absorbY hor hy =>
          refine ⟨fuel + 1, ?_, ?_⟩
          · simpa [run, runSteps, step, stepStreams, hor, hy] using hstate
          · simpa [run, runSteps, step, stepStreams, hor, hy] using hds
  | s, _, _, SafeVMRun.stepSome h hs hs' ht => by
      rcases safeVMRun_realized_by_run X Y ht with ⟨fuel, hstate, hds⟩
      cases h with
      | emitNeg hor =>
          refine ⟨fuel + 1, ?_, ?_⟩
          · simpa [run, runSteps, step, stepStreams, hor] using hstate
          · simpa [run, runSteps, step, stepStreams, hor, digit_to_LFT] using hds
      | emitZero hor =>
          refine ⟨fuel + 1, ?_, ?_⟩
          · simpa [run, runSteps, step, stepStreams, hor] using hstate
          · simpa [run, runSteps, step, stepStreams, hor, digit_to_LFT] using hds
      | emitPos hor =>
          refine ⟨fuel + 1, ?_, ?_⟩
          · simpa [run, runSteps, step, stepStreams, hor] using hstate
          · simpa [run, runSteps, step, stepStreams, hor, digit_to_LFT] using hds

end Mobius
end Computable
