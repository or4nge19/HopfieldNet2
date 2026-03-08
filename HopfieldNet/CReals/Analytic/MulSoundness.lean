import HopfieldNet.CReals.Analytic.CRealSemantics

namespace Computable
namespace CReal
namespace Analytic

open AnalyticReal

section

variable {V₁ V₂ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]

@[simp] theorem mul_out_init_zero (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) :
    (AnalyticReal.mul ar₁ ar₂).init (AnalyticReal.mul ar₁ ar₂).out = 0 := by
  rfl

@[simp] theorem mul_taylorCoeff_zero (ar₁ : AnalyticReal V₁) (ar₂ : AnalyticReal V₂) :
    AnalyticReal.taylorCoeff (AnalyticReal.mul ar₁ ar₂) 0 = 0 := by
  simpa using AnalyticReal.taylorCoeff_zero (AnalyticReal.mul ar₁ ar₂)

end

end Analytic
end CReal
end Computable
