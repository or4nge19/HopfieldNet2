import Rebuild.Core.TwoState
import Rebuild.Models.BinarySpin.Pairwise
import Rebuild.Learning.Boltzmann.Gradient

/-!
# Rebuild Two-State to Boltzmann Learning Bridge

Bridge from canonical two-state model semantics to reusable Boltzmann-learning statistics.
-/

set_option autoImplicit false

namespace Rebuild.Bridges

open Rebuild.Core
open Rebuild.Models.BinarySpin.Pairwise
open Rebuild.Learning.Boltzmann

abbrev ParameterIndex (Site : Type*) := Site ⊕ (Site × Site)

section Statistics

variable {σ Site : Type*} [TwoState σ]

/-- One-site observable associated with a field parameter. -/
noncomputable def biasStatistic (encoding : TwoStateEncoding σ) (i : Site) :
  Statistic (State σ Site) :=
 fun τ => encoding.toReal (τ i)

/-- Pair observable associated with a coupling parameter. -/
noncomputable def couplingStatistic (encoding : TwoStateEncoding σ) (e : Site × Site) :
  Statistic (State σ Site) :=
 fun τ => encoding.toReal (τ e.1) * encoding.toReal (τ e.2)

/-- Sufficient statistics for two-state pairwise models: fields and pair couplings. -/
noncomputable def parameterStatisticFamily (encoding : TwoStateEncoding σ) :
  StatisticFamily (ParameterIndex Site) (State σ Site) where
 stat
 | Sum.inl i => biasStatistic encoding i
 | Sum.inr e => couplingStatistic encoding e

@[simp] lemma parameterStatisticFamily_field (encoding : TwoStateEncoding σ) (i : Site) :
  (parameterStatisticFamily (Site := Site) encoding).stat (Sum.inl i) =
   biasStatistic encoding i := rfl

@[simp] lemma parameterStatisticFamily_coupling (encoding : TwoStateEncoding σ) (e : Site × Site) :
  (parameterStatisticFamily (Site := Site) encoding).stat (Sum.inr e) =
   couplingStatistic encoding e := rfl

end Statistics

section FinitePairwise

variable {σ Site : Type*} [TwoState σ] [Fintype σ] [Fintype Site] [DecidableEq Site]
 [MeasurableSpace (State σ Site)] [MeasurableSingletonClass (State σ Site)]

/-- Positive-vs-model phase pair for a canonical finite pairwise two-state model. -/
noncomputable def pairwiseModelPhasePair (encoding : TwoStateEncoding σ)
  (data : MeasureTheory.Measure (State σ Site)) (β : ℝ) (p : Parameters Site) :
  PhasePair (State σ Site) :=
 modelPhasePair data β (finiteGibbsModel encoding p)

/-- Canonical expectation-gap learning rule on two-state pairwise parameters. -/
noncomputable def pairwiseCanonicalLearningRule (encoding : TwoStateEncoding σ) :
  LearningRule (ParameterIndex Site) (ParameterIndex Site → ℝ) (State σ Site) :=
 canonicalLearningRule (parameterStatisticFamily (Site := Site) encoding)

end FinitePairwise

section BoolSigned

variable {Site : Type*} [Fintype Site] [DecidableEq Site]
 [MeasurableSpace (SignedState Site)] [MeasurableSingletonClass (SignedState Site)]

noncomputable abbrev signedBiasStatistic (i : Site) : Statistic (SignedState Site) :=
 biasStatistic (Site := Site) TwoStateEncoding.boolSigned i

noncomputable abbrev signedCouplingStatistic (e : Site × Site) : Statistic (SignedState Site) :=
 couplingStatistic (Site := Site) TwoStateEncoding.boolSigned e

noncomputable abbrev signedParameterStatisticFamily :
  StatisticFamily (ParameterIndex Site) (SignedState Site) :=
 parameterStatisticFamily (Site := Site) TwoStateEncoding.boolSigned

noncomputable def signedPairwiseModelPhasePair (data : MeasureTheory.Measure (SignedState Site))
  (β : ℝ) (p : Parameters Site) : PhasePair (SignedState Site) :=
 pairwiseModelPhasePair (Site := Site) TwoStateEncoding.boolSigned data β p

noncomputable def signedPairwiseCanonicalLearningRule :
  LearningRule (ParameterIndex Site) (ParameterIndex Site → ℝ) (SignedState Site) :=
 pairwiseCanonicalLearningRule (Site := Site) TwoStateEncoding.boolSigned

end BoolSigned

end Rebuild.Bridges
