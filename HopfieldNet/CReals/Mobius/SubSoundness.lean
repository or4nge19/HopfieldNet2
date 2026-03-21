import HopfieldNet.CReals.Mobius.Productivity
import HopfieldNet.CReals.Mobius.CRealBridge

namespace Computable
namespace Mobius

theorem subOutput_soundness_infinite
    (X Y out : DigitStream)
    (σ : ℕ → VMState) (ℓ : ℕ → Option LFT)
    (hσ0 : σ 0 = halfAddInitState)
    (hstep :
      ∀ i,
        GeneralTrace.VMStepXY
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream (DigitStream.negStream Y))
          (σ i) (ℓ i) (σ (i + 1)))
    (hsafe :
      ∀ i,
        GeneralTrace.SafeAt
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream (DigitStream.negStream Y))
          (σ i))
    (sched : GeneralTrace.EmitSchedule ℓ out) :
    2 * (MobiusReal.fromStream out).val =
      (MobiusReal.fromStream X).val - (MobiusReal.fromStream Y).val := by
  have hadd :=
    addOutput_soundness_infinite
      (X := MobiusReal.fromStream X)
      (Y := MobiusReal.fromStream (DigitStream.negStream Y))
      (out := out) (σ := σ) (ℓ := ℓ) hσ0 hstep hsafe sched
  calc
    2 * (MobiusReal.fromStream out).val
        = (MobiusReal.fromStream X).val + (MobiusReal.fromStream (DigitStream.negStream Y)).val := hadd
    _ = (MobiusReal.fromStream X).val - (MobiusReal.fromStream Y).val := by
          rw [DigitStream.fromStream_val_negStream]
          ring

theorem subOutput_toReal_soundness_infinite
    (X Y out : DigitStream)
    (σ : ℕ → VMState) (ℓ : ℕ → Option LFT)
    (hσ0 : σ 0 = halfAddInitState)
    (hstep :
      ∀ i,
        GeneralTrace.VMStepXY
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream (DigitStream.negStream Y))
          (σ i) (ℓ i) (σ (i + 1)))
    (hsafe :
      ∀ i,
        GeneralTrace.SafeAt
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream (DigitStream.negStream Y))
          (σ i))
    (sched : GeneralTrace.EmitSchedule ℓ out) :
    Computable.CReal.toReal (toCRealScaled 1 out) =
      (MobiusReal.fromStream X).val - (MobiusReal.fromStream Y).val := by
  calc
    Computable.CReal.toReal (toCRealScaled 1 out)
        = 2 * (MobiusReal.fromStream out).val := DigitStream.toReal_toCRealScaled_one out
    _ = (MobiusReal.fromStream X).val - (MobiusReal.fromStream Y).val :=
          subOutput_soundness_infinite X Y out σ ℓ hσ0 hstep hsafe sched

theorem subOutput_toCReal_soundness_infinite
    (X Y out : DigitStream)
    (σ : ℕ → VMState) (ℓ : ℕ → Option LFT)
    (hσ0 : σ 0 = halfAddInitState)
    (hstep :
      ∀ i,
        GeneralTrace.VMStepXY
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream (DigitStream.negStream Y))
          (σ i) (ℓ i) (σ (i + 1)))
    (hsafe :
      ∀ i,
        GeneralTrace.SafeAt
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream (DigitStream.negStream Y))
          (σ i))
    (sched : GeneralTrace.EmitSchedule ℓ out) :
    toCRealScaled 1 out = toCReal X - toCReal Y := by
  apply Computable.CReal.toReal_injective
  calc
    Computable.CReal.toReal (toCRealScaled 1 out)
        = (MobiusReal.fromStream X).val - (MobiusReal.fromStream Y).val :=
          subOutput_toReal_soundness_infinite X Y out σ ℓ hσ0 hstep hsafe sched
    _ = Computable.CReal.toReal (toCReal X) - Computable.CReal.toReal (toCReal Y) := by
          rw [DigitStream.toReal_toCReal, DigitStream.toReal_toCReal]
    _ = Computable.CReal.toReal (toCReal X - toCReal Y) := by
          simp [sub_eq_add_neg, Computable.CReal.toReal_add, Computable.CReal.toReal_neg]

theorem halfSubOutput_toCReal_soundness_infinite
    (X Y out : DigitStream)
    (σ : ℕ → VMState) (ℓ : ℕ → Option LFT)
    (hσ0 : σ 0 = halfAddInitState)
    (hstep :
      ∀ i,
        GeneralTrace.VMStepXY
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream (DigitStream.negStream Y))
          (σ i) (ℓ i) (σ (i + 1)))
    (hsafe :
      ∀ i,
        GeneralTrace.SafeAt
          (MobiusReal.fromStream X)
          (MobiusReal.fromStream (DigitStream.negStream Y))
          (σ i))
    (sched : GeneralTrace.EmitSchedule ℓ out) :
    toCReal out = (toCReal X - toCReal Y) / Computable.CReal.two := by
  have hscaled :
      Computable.CReal.two * toCReal out = toCReal X - toCReal Y := by
    simpa [DigitStream.toCRealScaled_one_eq_two_mul] using
      subOutput_toCReal_soundness_infinite X Y out σ ℓ hσ0 hstep hsafe sched
  have h2 : Computable.CReal.two ≠ 0 := by
    exact Computable.CReal.two_ne_zero
  exact (eq_div_iff h2).2 (by simpa [mul_comm] using hscaled)

end Mobius
end Computable
