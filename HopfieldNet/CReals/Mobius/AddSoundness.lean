import HopfieldNet.CReals.Mobius.Productivity
import HopfieldNet.CReals.Mobius.CRealBridge

namespace Computable
namespace Mobius

theorem halfAddOutput_toReal_soundness_infinite
    (X Y out : DigitStream)
    (σ : ℕ → VMState) (ℓ : ℕ → Option LFT)
    (hσ0 : σ 0 = halfAddInitState)
    (hstep :
      ∀ i,
        GeneralTrace.VMStepXY
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream Y)
          (σ i) (ℓ i) (σ (i + 1)))
    (hsafe :
      ∀ i,
        GeneralTrace.SafeAt
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream Y)
          (σ i))
    (sched : GeneralTrace.EmitSchedule ℓ out) :
    Computable.CReal.toReal (toCReal out) =
      ((MobiusReal.fromStream X).val + (MobiusReal.fromStream Y).val) / 2 := by
  calc
    Computable.CReal.toReal (toCReal out)
        = (MobiusReal.fromStream out).val := DigitStream.toReal_toCReal out
    _ = ((MobiusReal.fromStream X).val + (MobiusReal.fromStream Y).val) / 2 :=
          halfAddTensor_soundness_infinite
            (X := MobiusReal.fromStream X)
            (Y := MobiusReal.fromStream Y)
            (out := out) (σ := σ) (ℓ := ℓ) hσ0 hstep hsafe sched

theorem addOutput_toCReal_soundness_infinite
    (X Y out : DigitStream)
    (σ : ℕ → VMState) (ℓ : ℕ → Option LFT)
    (hσ0 : σ 0 = halfAddInitState)
    (hstep :
      ∀ i,
        GeneralTrace.VMStepXY
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream Y)
          (σ i) (ℓ i) (σ (i + 1)))
    (hsafe :
      ∀ i,
        GeneralTrace.SafeAt
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream Y)
          (σ i))
    (sched : GeneralTrace.EmitSchedule ℓ out) :
    toCRealScaled 1 out = toCReal X + toCReal Y := by
  apply Computable.CReal.toReal_injective
  calc
    Computable.CReal.toReal (toCRealScaled 1 out)
        = (MobiusReal.fromStream X).val + (MobiusReal.fromStream Y).val :=
          addOutput_toReal_soundness_infinite
            (X := MobiusReal.fromStream X)
            (Y := MobiusReal.fromStream Y)
            (out := out) (σ := σ) (ℓ := ℓ) hσ0 hstep hsafe sched
    _ = Computable.CReal.toReal (toCReal X) + Computable.CReal.toReal (toCReal Y) := by
          rw [DigitStream.toReal_toCReal, DigitStream.toReal_toCReal]
    _ = Computable.CReal.toReal (toCReal X + toCReal Y) := by
          simp [Computable.CReal.toReal_add]

theorem halfAddOutput_toCReal_soundness_infinite
    (X Y out : DigitStream)
    (σ : ℕ → VMState) (ℓ : ℕ → Option LFT)
    (hσ0 : σ 0 = halfAddInitState)
    (hstep :
      ∀ i,
        GeneralTrace.VMStepXY
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream Y)
          (σ i) (ℓ i) (σ (i + 1)))
    (hsafe :
      ∀ i,
        GeneralTrace.SafeAt
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream Y)
          (σ i))
    (sched : GeneralTrace.EmitSchedule ℓ out) :
    toCReal out = (toCReal X + toCReal Y) / Computable.CReal.two := by
  have hscaled :
      Computable.CReal.two * toCReal out = toCReal X + toCReal Y := by
    simpa [DigitStream.toCRealScaled_one_eq_two_mul] using
      addOutput_toCReal_soundness_infinite X Y out σ ℓ hσ0 hstep hsafe sched
  have h2 : Computable.CReal.two ≠ 0 := by
    exact Computable.CReal.two_ne_zero
  exact (eq_div_iff h2).2 (by simpa [mul_comm] using hscaled)

theorem halfAddOutput_add_self_toCReal_soundness_infinite
    (X Y out : DigitStream)
    (σ : ℕ → VMState) (ℓ : ℕ → Option LFT)
    (hσ0 : σ 0 = halfAddInitState)
    (hstep :
      ∀ i,
        GeneralTrace.VMStepXY
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream Y)
          (σ i) (ℓ i) (σ (i + 1)))
    (hsafe :
      ∀ i,
        GeneralTrace.SafeAt
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream Y)
          (σ i))
    (sched : GeneralTrace.EmitSchedule ℓ out) :
    toCReal out + toCReal out = toCReal X + toCReal Y := by
  calc
    toCReal out + toCReal out = toCRealScaled 1 out := by
          symm
          exact DigitStream.toCRealScaled_one_eq_add_self out
    _ = toCReal X + toCReal Y :=
          addOutput_toCReal_soundness_infinite X Y out σ ℓ hσ0 hstep hsafe sched

end Mobius
end Computable
