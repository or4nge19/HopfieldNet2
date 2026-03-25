import HopfieldNet.CReals.Mobius.Productivity
import HopfieldNet.CReals.Mobius.Eval

namespace Computable
namespace Mobius

set_option autoImplicit false

/--
`PrefixResult` packages the computable runner output in a theorem-friendly format:
the emitted digit prefix together with the residual VM state.
-/
structure PrefixResult where
  digits : List Digit
  state : VMState

namespace PrefixResult

noncomputable def approx (r : PrefixResult) : ℝ :=
  digitListApprox r.digits

noncomputable def errorBound (r : PrefixResult) : ℝ :=
  (1 : ℝ) / 2 ^ r.digits.length

end PrefixResult

/-- Run the executable Möbius VM for `fuel` steps from an arbitrary starting state. -/
def prefixResult (X Y : MobiusReal) (fuel : ℕ) (s : VMState) : PrefixResult :=
  let r := run X Y fuel s
  ⟨r.1, r.2⟩

/--
Run the normalization-aware executable Möbius VM for `fuel` steps from an arbitrary starting state.

This preserves denotation exactly while periodically dividing out common gcd factors in the residual
tensor after each machine step.
-/
def normalizedPrefixResult (X Y : MobiusReal) (fuel : ℕ) (s : VMState) : PrefixResult :=
  let r := runNormalized X Y fuel s
  ⟨r.1, r.2⟩

@[simp] theorem prefixResult_digits (X Y : MobiusReal) (fuel : ℕ) (s : VMState) :
    (prefixResult X Y fuel s).digits = (run X Y fuel s).1 := rfl

@[simp] theorem prefixResult_state (X Y : MobiusReal) (fuel : ℕ) (s : VMState) :
    (prefixResult X Y fuel s).state = (run X Y fuel s).2 := rfl

@[simp] theorem normalizedPrefixResult_digits (X Y : MobiusReal) (fuel : ℕ) (s : VMState) :
    (normalizedPrefixResult X Y fuel s).digits = (runNormalized X Y fuel s).1 := rfl

@[simp] theorem normalizedPrefixResult_state (X Y : MobiusReal) (fuel : ℕ) (s : VMState) :
    (normalizedPrefixResult X Y fuel s).state = (runNormalized X Y fuel s).2 := rfl

theorem prefixResult_stateValue_eq_approx_add_scaled
    (X Y : MobiusReal) (fuel : ℕ) (s : VMState)
    (hs : GeneralTrace.SafeAt X Y s) :
    GeneralTrace.stateValue X Y s =
      (prefixResult X Y fuel s).approx +
        GeneralTrace.stateValue X Y (prefixResult X Y fuel s).state /
          2 ^ (prefixResult X Y fuel s).digits.length := by
  simpa [prefixResult, PrefixResult.approx] using
    run_soundness_prefix_digitListApprox X Y fuel s hs

theorem prefixResult_error_le
    (X Y : MobiusReal) (fuel : ℕ) (s : VMState)
    (hs : GeneralTrace.SafeAt X Y s)
    (hres : GeneralTrace.stateValue X Y (prefixResult X Y fuel s).state ∈ baseI) :
    |GeneralTrace.stateValue X Y s - (prefixResult X Y fuel s).approx| ≤
      (prefixResult X Y fuel s).errorBound := by
  simpa [prefixResult, PrefixResult.approx, PrefixResult.errorBound] using
    run_soundness_prefix_digitListApprox_error X Y fuel s hs hres

theorem prefixResult_realized_by_safeRun
    (X Y : MobiusReal) (fuel : ℕ) (s : VMState)
    (hs : GeneralTrace.SafeAt X Y s) :
    SafeVMRun X Y s ((prefixResult X Y fuel s).digits.map digit_to_LFT) (prefixResult X Y fuel s).state := by
  simpa [prefixResult] using run_safeVMRun X Y fuel s hs

theorem normalizedPrefixResult_stateValue_eq_approx_add_scaled
    (X Y : MobiusReal) (fuel : ℕ) (s : VMState)
    (hs : GeneralTrace.SafeAt X Y s) :
    GeneralTrace.stateValue X Y s =
      (normalizedPrefixResult X Y fuel s).approx +
        GeneralTrace.stateValue X Y (normalizedPrefixResult X Y fuel s).state /
          2 ^ (normalizedPrefixResult X Y fuel s).digits.length := by
  simpa [normalizedPrefixResult, PrefixResult.approx] using
    runNormalized_soundness_prefix_digitListApprox X Y fuel s hs

theorem normalizedPrefixResult_error_le
    (X Y : MobiusReal) (fuel : ℕ) (s : VMState)
    (hs : GeneralTrace.SafeAt X Y s)
    (hres : GeneralTrace.stateValue X Y (normalizedPrefixResult X Y fuel s).state ∈ baseI) :
    |GeneralTrace.stateValue X Y s - (normalizedPrefixResult X Y fuel s).approx| ≤
      (normalizedPrefixResult X Y fuel s).errorBound := by
  simpa [normalizedPrefixResult, PrefixResult.approx, PrefixResult.errorBound] using
    runNormalized_soundness_prefix_digitListApprox_error X Y fuel s hs hres

/-- Executable prefix report for the existing half-add machine. -/
def halfAddPrefixResult (X Y : MobiusReal) (fuel : ℕ) : PrefixResult :=
  prefixResult X Y fuel halfAddInitState

theorem halfAddPrefix_eq_value_plus_residual
    (X Y : MobiusReal) (fuel : ℕ) :
    (X.val + Y.val) / 2 =
      (halfAddPrefixResult X Y fuel).approx +
        GeneralTrace.stateValue X Y (halfAddPrefixResult X Y fuel).state /
          2 ^ (halfAddPrefixResult X Y fuel).digits.length := by
  have hs : GeneralTrace.SafeAt X Y halfAddInitState := halfAddInit_safe X Y
  calc
    (X.val + Y.val) / 2 = GeneralTrace.stateValue X Y halfAddInitState := by
      symm
      exact halfAddInit_stateValue X Y
    _ =
      (halfAddPrefixResult X Y fuel).approx +
        GeneralTrace.stateValue X Y (halfAddPrefixResult X Y fuel).state /
          2 ^ (halfAddPrefixResult X Y fuel).digits.length := by
        simpa [halfAddPrefixResult] using
          prefixResult_stateValue_eq_approx_add_scaled X Y fuel halfAddInitState hs

theorem halfAddPrefix_error_le
    (X Y : MobiusReal) (fuel : ℕ)
    (hres : GeneralTrace.stateValue X Y (halfAddPrefixResult X Y fuel).state ∈ baseI) :
    |(X.val + Y.val) / 2 - (halfAddPrefixResult X Y fuel).approx| ≤
      (halfAddPrefixResult X Y fuel).errorBound := by
  have hs : GeneralTrace.SafeAt X Y halfAddInitState := halfAddInit_safe X Y
  calc
    |(X.val + Y.val) / 2 - (halfAddPrefixResult X Y fuel).approx|
      = |GeneralTrace.stateValue X Y halfAddInitState - (halfAddPrefixResult X Y fuel).approx| := by
          rw [halfAddInit_stateValue]
    _ ≤ (halfAddPrefixResult X Y fuel).errorBound := by
          simpa [halfAddPrefixResult] using
            prefixResult_error_le X Y fuel halfAddInitState hs hres

end Mobius
end Computable
