import HopfieldNet.CReals.Mobius.MulSoundness

namespace Computable
namespace Mobius

/--
Simple concrete digit streams for executable prefix experiments.
These examples exercise the computable runner directly on raw digit streams,
avoiding any noncomputable `MobiusReal` wrapper.
-/

def zeroVsZeroOut (fuel : ℕ) : List Digit :=
  (runSteps (lftStreamOfDigits DigitStream.zeroDigits) (lftStreamOfDigits DigitStream.zeroDigits) fuel halfAddInitState).1

def oneVsZeroOut (fuel : ℕ) : List Digit :=
  (runSteps (lftStreamOfDigits DigitStream.oneDigits) (lftStreamOfDigits DigitStream.zeroDigits) fuel halfAddInitState).1

def oneVsOneOut (fuel : ℕ) : List Digit :=
  (runSteps (lftStreamOfDigits DigitStream.oneDigits) (lftStreamOfDigits DigitStream.oneDigits) fuel halfAddInitState).1

def oneVsMinusOneOut (fuel : ℕ) : List Digit :=
  (runSteps (lftStreamOfDigits DigitStream.oneDigits) (lftStreamOfDigits DigitStream.minusOneDigits) fuel halfAddInitState).1

def zeroTimesZeroOut (fuel : ℕ) : List Digit :=
  (runSteps (lftStreamOfDigits DigitStream.zeroDigits) (lftStreamOfDigits DigitStream.zeroDigits) fuel mulInitState).1

def oneTimesZeroOut (fuel : ℕ) : List Digit :=
  (runSteps (lftStreamOfDigits DigitStream.oneDigits) (lftStreamOfDigits DigitStream.zeroDigits) fuel mulInitState).1

def oneTimesOneOutMul (fuel : ℕ) : List Digit :=
  (runSteps (lftStreamOfDigits DigitStream.oneDigits) (lftStreamOfDigits DigitStream.oneDigits) fuel mulInitState).1

def oneTimesMinusOneOutMul (fuel : ℕ) : List Digit :=
  (runSteps (lftStreamOfDigits DigitStream.oneDigits) (lftStreamOfDigits DigitStream.minusOneDigits) fuel mulInitState).1

/-
Concrete two-digit prefix snapshots for the executable runner.
The previous examples only displayed a raw output list after fixed fuel;
these now also show the first two digits explicitly.
-/
#eval! zeroVsZeroOut 12
#eval! (zeroVsZeroOut 12).take 2

#eval! oneVsZeroOut 12
#eval! (oneVsZeroOut 12).take 2

#eval! oneVsOneOut 12
#eval! (oneVsOneOut 12).take 2

#eval! oneVsMinusOneOut 12
#eval! (oneVsMinusOneOut 12).take 2

#eval! zeroTimesZeroOut 16
#eval! (zeroTimesZeroOut 16).take 3

#eval! oneTimesZeroOut 16
#eval! (oneTimesZeroOut 16).take 3

#eval! oneTimesOneOutMul 16
#eval! (oneTimesOneOutMul 16).take 3

#eval! oneTimesMinusOneOutMul 16
#eval! (oneTimesMinusOneOutMul 16).take 3

end Mobius
end Computable
