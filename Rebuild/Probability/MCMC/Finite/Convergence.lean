import Rebuild.Probability.MCMC.Finite.Core

/-!
# Rebuild Finite MCMC Convergence

Small rebuild-facing wrappers around the already audited finite-MCMC convergence facts.
This keeps convergence statements accessible from the rebuild namespace while deeper total-variation
and rate results are migrated later by strata.
-/

set_option autoImplicit false

namespace Rebuild.Probability.MCMC.Finite

theorem aperiodic_of_primitive {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]
    (P : TransitionMatrix State) (h_stoch : IsStochastic P) (h_prim : Matrix.IsPrimitive P) :
    Matrix.IsAperiodic P :=
  _root_.MCMC.Finite.aperiodic_of_properties P h_stoch h_prim

theorem exists_unique_stationary_of_irreducible
    {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]
    {P : TransitionMatrix State} (h_stoch : IsStochastic P) (h_irred : Matrix.IsIrreducible P) :
    ∃! (π : stdSimplex ℝ State), IsStationary P π :=
  exists_unique_stationary_distribution_of_irreducible h_stoch h_irred

lemma FiniteChain.has_unique_stationary_distribution
    {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]
    (chain : FiniteChain State) :
    ∃! (π : stdSimplex ℝ State), IsStationary chain.transition π :=
  exists_unique_stationary_distribution_of_irreducible chain.stochastic chain.irreducible

end Rebuild.Probability.MCMC.Finite
