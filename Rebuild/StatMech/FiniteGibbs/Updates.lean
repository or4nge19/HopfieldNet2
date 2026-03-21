import Rebuild.StatMech.FiniteGibbs.Core
import Rebuild.Core.Configuration
import Rebuild.Core.Dynamics

/-!
# Rebuild Finite Gibbs Updates

Generic single-site update semantics over configuration spaces.

This is intentionally small and model-independent:

- overwrite one site of a configuration,
- package the overwrite map as a local deterministic update,
- and expose a basic "changes only one site" lemma.

Model-specific stochastic Gibbs samplers should be built on top of this interface.
-/

set_option autoImplicit false

namespace Rebuild.StatMech.FiniteGibbs

open Rebuild.Core

variable {Site Spin : Type*} [DecidableEq Site]

/-- Overwrite a single site of a configuration. -/
def overwrite (σ : Configuration Site Spin) (i : Site) (value : Spin) : Configuration Site Spin :=
  Function.update σ i value

@[simp] lemma overwrite_self (σ : Configuration Site Spin) (i : Site) (value : Spin) :
    overwrite σ i value i = value := by
  simp [overwrite]

@[simp] lemma overwrite_of_ne (σ : Configuration Site Spin) {i j : Site} (value : Spin)
    (h : j ≠ i) :
    overwrite σ i value j = σ j := by
  simp [overwrite, h]

/-- The generic single-site overwrite operation as a local deterministic update. -/
def singleSiteOverwrite : LocalDeterministicUpdate Site Spin where
  update i σ := overwrite σ i (σ i)
  preserves_offsite := by
    intro i σ j hij
    simp [overwrite, hij]

/-- More useful parametrized overwrite map. -/
def singleSiteOverwriteWith (value : Site → Configuration Site Spin → Spin) :
    LocalDeterministicUpdate Site Spin where
  update i σ := overwrite σ i (value i σ)
  preserves_offsite := by
    intro i σ j hij
    simp [overwrite, hij]

lemma agreesOn_offsite_overwrite (σ : Configuration Site Spin) (i : Site) (value : Spin) :
    ∀ j, j ≠ i → overwrite σ i value j = σ j := by
  intro j hj
  simp [overwrite, hj]

end Rebuild.StatMech.FiniteGibbs
