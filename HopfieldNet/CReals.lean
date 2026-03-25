import HopfieldNet.CReals.Architecture
import HopfieldNet.CReals.SOTA
import HopfieldNet.CReals.Mobius
import HopfieldNet.CReals.Analytic
import HopfieldNet.CReals.CRealsFast

/-!
# HopfieldNet exact reals

Public umbrella import for the exact-real stack:

- `Architecture` for stable layer boundaries and bridge names
- `SOTA` for the core `Computable.CReal` story
- `Mobius` for certified digit-stream execution
- `Analytic` for Taylor / symbolic fronts
- `CRealsFast` for executable dyadic-ball numerics
-/
