import HopfieldNet.CReals.SOTA
import HopfieldNet.CReals.Mobius
import HopfieldNet.CReals.Analytic
import HopfieldNet.CReals.CRealsFast

/-!
# CReals architecture facade

This file freezes the intended public split of the exact-real stack:

- `Computable.CReal`: extensional specification model.
- `Computable.Fast.FastReal`: executable dyadic/ball backend.
- `Computable.Mobius`: certified digit-stream execution layer.
- `Computable.CReal.Analytic`: symbolic / Taylor frontend.

The goal is to give downstream developments a small set of stable names for moving
between those layers without forcing them to discover the whole file graph first.
-/

namespace Computable
namespace CRealsArchitecture

set_option autoImplicit false

abbrev RealSpec : Type := Computable.CRealsSOTA.RealSpec

abbrev RealImpl (AQ : Type) [ApproxRationals AQ] : Type :=
  Computable.CRealsSOTA.RealImpl AQ

abbrev RealRep (AQ : Type) [ApproxRationals AQ] : Type :=
  Computable.CRealsSOTA.RealRep AQ

abbrev FastExecutable : Type := Computable.Fast.FastReal

abbrev MobiusDigits : Type := Computable.Mobius.DigitStream

abbrev MobiusState : Type := Computable.Mobius.VMState

abbrev AnalyticFrontend (V : Type) [Fintype V] [DecidableEq V] : Type :=
  Computable.CReal.Analytic.AnalyticReal V

abbrev AnalyticLimitAt (V : Type) [Fintype V] [DecidableEq V]
    (A : AnalyticFrontend V) (t : ℚ) : Type :=
  Computable.CReal.Analytic.HasConstructiveTaylorLimitAt A t

abbrev AnalyticLimit (V : Type) [Fintype V] [DecidableEq V]
    (A : AnalyticFrontend V) : Type :=
  Computable.CReal.Analytic.HasConstructiveTaylorLimit A

variable {AQ : Type} [ApproxRationals AQ]

def implToSpec : RealImpl AQ →+* RealSpec :=
  Computable.CRealsSOTA.toSpec (AQ := AQ)

noncomputable def implToReal : RealImpl AQ →+* ℝ :=
  Computable.CRealsSOTA.toRealRingHom (AQ := AQ)

def mobiusToSpec : MobiusDigits → RealSpec :=
  Computable.Mobius.toCReal

def mobiusToScaledSpec (k : ℕ) : MobiusDigits → RealSpec :=
  Computable.Mobius.toCRealScaled k

noncomputable def mobiusToReal : MobiusDigits → ℝ :=
  fun out => Computable.CReal.toReal (mobiusToSpec out)

noncomputable def analyticToSpecAt {V : Type} [Fintype V] [DecidableEq V]
    {A : AnalyticFrontend V} {t : ℚ} (hA : AnalyticLimitAt V A t) : RealSpec :=
  Computable.CReal.Analytic.toCRealAt hA

noncomputable def analyticToSpec {V : Type} [Fintype V] [DecidableEq V]
    {A : AnalyticFrontend V} (hA : AnalyticLimit V A) : RealSpec :=
  Computable.CReal.Analytic.toCReal hA

noncomputable def analyticToRealAt {V : Type} [Fintype V] [DecidableEq V]
    {A : AnalyticFrontend V} {t : ℚ} (hA : AnalyticLimitAt V A t) : ℝ :=
  Computable.CReal.Analytic.toRealAt hA

noncomputable def analyticToReal {V : Type} [Fintype V] [DecidableEq V]
    {A : AnalyticFrontend V} (hA : AnalyticLimit V A) : ℝ :=
  Computable.CReal.Analytic.toReal hA

@[simp] theorem implToSpec_apply (x : RealImpl AQ) :
    implToSpec (AQ := AQ) x = Computable.CRealAQ.toCReal (AQ := AQ) x := by
  rfl

@[simp] theorem mobiusToReal_eq_streamValue (out : MobiusDigits) :
    mobiusToReal out = (Computable.Mobius.MobiusReal.fromStream out).val := by
  simp [mobiusToReal, mobiusToSpec, Computable.Mobius.DigitStream.toReal_toCReal]

@[simp] theorem analyticToReal_eq_toRealAtOne
    {V : Type} [Fintype V] [DecidableEq V] {A : AnalyticFrontend V}
    (hA : AnalyticLimit V A) :
    analyticToReal hA = analyticToRealAt (V := V) (A := A) (t := (1 : ℚ)) hA := by
  rfl

end CRealsArchitecture
end Computable
