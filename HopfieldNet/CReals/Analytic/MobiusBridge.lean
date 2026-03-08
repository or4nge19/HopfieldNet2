import HopfieldNet.CReals.Analytic.CRealSemantics
import HopfieldNet.CReals.Mobius.CRealBridge

namespace Computable
namespace CReal
namespace Analytic

structure CertifiedMobiusBridge {V : Type} [Fintype V] [DecidableEq V]
    (A : AnalyticReal V) (hA : HasConstructiveTaylorLimit A) where
  out : Computable.Mobius.DigitStream
  agrees :
    Computable.Mobius.toCReal out = toCReal hA

end Analytic
end CReal
end Computable
