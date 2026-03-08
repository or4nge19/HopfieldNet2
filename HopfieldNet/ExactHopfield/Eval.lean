/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import HopfieldNet.CReals.CRealsFast

/-!
# Executable Evaluation of Exact Hopfield Networks

This file demonstrates that the Hopfield energy function can be **evaluated** to arbitrary
precision via the `Computable.Fast` dyadic ball arithmetic backend.

## Demo network

We use the classic 3-neuron XOR memory Hopfield network (2 stored patterns):
- Pattern 1: `[+1, +1, -1]`
- Pattern 2: `[-1, -1, +1]`

Weights are via the (unnormalized) Hebbian rule: `w_ij = ∑_μ ξ_μ_i · ξ_μ_j` (zero diagonal).

## What this demonstrates

1. **Exact energy evaluation**: `#eval` computes the energy with rigorous error bounds.
2. **Exact comparison**: `FastReal.compare` certifies which state has lower energy.
3. **No floating-point**: all computations are over dyadics — no IEEE-754 rounding.
-/

open Computable.Fast

namespace ExactHopfield.Eval

/-! ### Helpers for finite sums over `Fin n` (avoids Mathlib `Finset.sum` import) -/

/-- Sum a `Fin n → FastReal` function. -/
def finSum : {n : ℕ} → (Fin n → FastReal) → FastReal
  | 0,     _ => (0 : FastReal)
  | n + 1, f => finSum (n := n) (fun i => f i.castSucc) + f (Fin.last n)

/-- Double sum over `Fin n × Fin n`. -/
def finSum2 (n : ℕ) (f : Fin n → Fin n → FastReal) : FastReal :=
  finSum fun i => finSum fun j => f i j

/-! ### Energy and local field -/

/-- `FastReal` energy for a Hopfield network with `n` neurons. -/
def fastEnergy (n : ℕ) (w : Fin n → Fin n → FastReal) (θ : Fin n → FastReal)
    (s : Fin n → FastReal) : FastReal :=
  let halfNeg : FastReal := FastReal.neg (FastReal.ofDyadic ⟨1, -1⟩)
  let bilinear := finSum2 n fun i j => w i j * s i * s j
  let threshold := finSum fun i => θ i * s i
  halfNeg * bilinear + threshold

/-- `FastReal` local field at neuron `i`. -/
def fastLocalField (n : ℕ) (w : Fin n → Fin n → FastReal) (s : Fin n → FastReal)
    (i : Fin n) : FastReal :=
  finSum fun j => w i j * s j

/-! ### Demo: 3-neuron XOR-memory Hopfield network -/

private def mkFin3 (a b c : FastReal) : Fin 3 → FastReal
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

/-- Hebbian weight matrix for patterns `[+1,+1,-1]` and `[-1,-1,+1]`.
The off-diagonal entries are `ξ1_i*ξ1_j + ξ2_i*ξ2_j`, diagonal is 0. -/
private def demoW : Fin 3 → Fin 3 → FastReal := fun i j =>
  let p1 := mkFin3 1 1 (FastReal.neg 1)
  let p2 := mkFin3 (FastReal.neg 1) (FastReal.neg 1) 1
  if i == j then (0 : FastReal)
  else p1 i * p1 j + p2 i * p2 j

private def demoθ : Fin 3 → FastReal := fun _ => (0 : FastReal)

private def s_stored1 : Fin 3 → FastReal := mkFin3 1 1 (FastReal.neg 1)
private def s_stored2 : Fin 3 → FastReal := mkFin3 (FastReal.neg 1) (FastReal.neg 1) 1
private def s_spurious : Fin 3 → FastReal := mkFin3 1 (FastReal.neg 1) 1
private def s_allUp : Fin 3 → FastReal := mkFin3 1 1 1

/-! ### Evaluations -/

-- Energy of stored pattern 1 (should be most negative = lowest energy)
#eval fastEnergy 3 demoW demoθ s_stored1
-- Energy of stored pattern 2 (same energy as pattern 1 by symmetry)
#eval fastEnergy 3 demoW demoθ s_stored2
-- Energy of a spurious state (should be higher)
#eval fastEnergy 3 demoW demoθ s_spurious
-- Energy of all-up state (should be higher)
#eval fastEnergy 3 demoW demoθ s_allUp

-- Local field at each neuron for stored pattern 1
#eval fastLocalField 3 demoW s_stored1 ⟨0, by omega⟩
#eval fastLocalField 3 demoW s_stored1 ⟨1, by omega⟩
#eval fastLocalField 3 demoW s_stored1 ⟨2, by omega⟩

-- Certified comparison: is stored pattern's energy < spurious state's energy?
#eval FastReal.compare
  (fastEnergy 3 demoW demoθ s_stored1)
  (fastEnergy 3 demoW demoθ s_spurious) 40

-- Human-readable explanation with the separation certificate
#eval FastReal.compareExplain
  (fastEnergy 3 demoW demoθ s_stored1)
  (fastEnergy 3 demoW demoθ s_spurious) 40 8

end ExactHopfield.Eval
