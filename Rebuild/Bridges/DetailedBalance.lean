import Rebuild.Models.BoltzmannMachine.DetailedBalance

open Rebuild.Models.BoltzmannMachine Rebuild.Core MeasureTheory ProbabilityTheory
open Rebuild.StatMech.FiniteGibbs Rebuild.Bridges
open scoped ENNReal NNReal

namespace Rebuild.Bridges

variable {Site : Type*} [Fintype Site] [DecidableEq Site]
    [MeasurableSpace (SignedState Site)] [MeasurableSingletonClass (SignedState Site)]

lemma detailed_balance (β : ℝ) (p : Parameters Site) (i : Site) :
  Kernel.IsReversible (signedSiteGibbsKernel β p i) (signedBoltzmannMachineGibbsMeasure β p) := by
  exact Rebuild.Models.BoltzmannMachine.signedSiteGibbsKernel_reversible β p i

end Rebuild.Bridges
