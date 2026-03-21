/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import NeuralNetwork.NeuralNetwork.BoltzmannMachine
import HopfieldNet.CReals.CRealCCLOF

/-!
# Exact Hopfield Networks over `Computable.CReal` (via `TwoState.SymmetricBinary`)

This file instantiates the existing Hopfield theory in the `NeuralNetwork` framework
at `R = Computable.CReal`, using the canonical `TwoState.SymmetricBinary` architecture.

This aligns with Mathlib philosophy: reuse existing structures and theorems, and only add
new API where needed. In particular, we do **not** re-define:

- states
- updates
- energy / local field
- convergence theorems

Instead, we define the canonical abbreviations and re-export the relevant operations.

## Note on the diagonal (`w_{ii} = 0`)

The `TwoState.SymmetricBinary` parameters include a bundled diagonal-zero constraint, and
the concrete Hamiltonian proof (`HopfieldEnergy.hamiltonian_flip_relation`) relies on it
in the expected place (quadratic-form update lemma).

This file is intentionally lightweight; the executable evaluator lives in
`ExactHopfield/MonadicHopfield.lean` and `ExactHopfield/Eval.lean`.
-/

namespace ExactHopfield

open Computable
open NeuralNetwork TwoState HopfieldEnergy

/-! ## Canonical abbreviations (exact Hopfield over `CReal`) -/

abbrev R : Type := Computable.CReal

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

noncomputable section

abbrev NN : NeuralNetwork R U R :=
  TwoState.SymmetricBinary R U

abbrev SBParams : Type := Params (NN (U := U))

abbrev SBState : Type := (NN (U := U)).State

abbrev θ0 (p : SBParams (U := U)) (u : U) : R :=
  (p.θ u).get fin0

abbrev localField (p : SBParams (U := U)) (s : SBState (U := U)) (u : U) : R :=
  s.net p u

abbrev L (p : SBParams (U := U)) (s : SBState (U := U)) (u : U) : R :=
  localField p s u - θ0 p u

abbrev energy (p : SBParams (U := U)) (s : SBState (U := U)) : R :=
  HopfieldEnergy.hamiltonian (R := R) (U := U) p s

abbrev updPos (s : SBState (U := U)) (u : U) : SBState (U := U) :=
  TwoState.updPos (NN := NN (U := U)) s u

abbrev updNeg (s : SBState (U := U)) (u : U) : SBState (U := U) :=
  TwoState.updNeg (NN := NN (U := U)) s u

/-- Energy gap between forcing neuron `u` to `+1` and forcing it to `-1`. -/
abbrev energyDiff (p : SBParams (U := U)) (s : SBState (U := U)) (u : U) : R :=
  energy p (updPos s u) - energy p (updNeg s u)

/-- Symmetry of the weight matrix (bundled in `SBParams`). -/
lemma w_isSymm (p : SBParams (U := U)) : p.w.IsSymm :=
  p.hw'.1

/-- Zero diagonal constraint `w_{uu} = 0` (bundled in `SBParams`). -/
lemma w_diag_zero (p : SBParams (U := U)) (u : U) : p.w u u = 0 :=
  p.hw'.2 u

noncomputable def zeroTempDet (p : SBParams (U := U)) (s : SBState (U := U)) (u : U) : SBState (U := U) :=
  if θ0 p u ≤ localField p s u then updPos s u else updNeg s u

end

end ExactHopfield
