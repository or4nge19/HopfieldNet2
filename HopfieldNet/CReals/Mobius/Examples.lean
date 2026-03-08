import HopfieldNet.CReals.Mobius.Productivity

namespace Computable
namespace Mobius

/--
Simple concrete digit streams for executable prefix experiments.
These examples exercise the computable runner directly on raw digit streams,
avoiding any noncomputable `MobiusReal` wrapper.
-/
def zeroDigits : DigitStream := fun _ => .zero

def oneDigits : DigitStream := fun _ => .pos

def minusOneDigits : DigitStream := fun _ => .neg

def zeroVsZeroOut (fuel : ℕ) : List Digit :=
  (runSteps (lftStreamOfDigits zeroDigits) (lftStreamOfDigits zeroDigits) fuel halfAddInitState).1

def oneVsZeroOut (fuel : ℕ) : List Digit :=
  (runSteps (lftStreamOfDigits oneDigits) (lftStreamOfDigits zeroDigits) fuel halfAddInitState).1

def oneVsOneOut (fuel : ℕ) : List Digit :=
  (runSteps (lftStreamOfDigits oneDigits) (lftStreamOfDigits oneDigits) fuel halfAddInitState).1

def oneVsMinusOneOut (fuel : ℕ) : List Digit :=
  (runSteps (lftStreamOfDigits oneDigits) (lftStreamOfDigits minusOneDigits) fuel halfAddInitState).1

/-
Concrete two-digit prefix snapshots for the executable runner.
The previous examples only displayed a raw output list after fixed fuel;
these now also show the first two digits explicitly.
-/
#eval zeroVsZeroOut 12
#eval (zeroVsZeroOut 12).take 2

#eval oneVsZeroOut 12
#eval (oneVsZeroOut 12).take 2

#eval oneVsOneOut 12
#eval (oneVsOneOut 12).take 2

#eval oneVsMinusOneOut 12
#eval (oneVsMinusOneOut 12).take 2

end Mobius
end Computable
