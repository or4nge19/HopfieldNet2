import HopfieldNet.CReals.CRealCompareTactic
import HopfieldNet.CReals.CRealLtTactic

namespace Computable.CReal.Pre.Examples

open Computable

example : (Computable.CReal.Pre.toReal Computable.CReal.Pre.zero)
    < (Computable.CReal.Pre.toReal Computable.CReal.Pre.one) := by
  creal_compare

example : (Computable.CReal.Pre.toReal Computable.CReal.Pre.one)
    > (Computable.CReal.Pre.toReal Computable.CReal.Pre.zero) := by
  creal_compare (fuel := 400)

end Computable.CReal.Pre.Examples

namespace Computable.CReal.Examples

open Computable

def onePre : Computable.CReal.Pre where
  approx := fun _ ↦ 1
  is_regular := by intro n m _; simp

example : (⟦Computable.CReal.Pre.zero⟧ : Computable.CReal) < (⟦onePre⟧ : Computable.CReal) := by
  creal_lt

example :
    Computable.CReal.toReal (⟦Computable.CReal.Pre.zero⟧ : Computable.CReal) <
      Computable.CReal.toReal (⟦onePre⟧ : Computable.CReal) := by
  creal_compare

end Computable.CReal.Examples
