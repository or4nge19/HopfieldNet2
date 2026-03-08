/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import HopfieldNet.ExactHopfield.ExactRealM

/-!
# Monadic Hopfield Network: Imperative-Style Exact Neural Computation

This file is the **headline demo** of the exact-real Hopfield architecture.

It implements a complete Hopfield network evaluator using the `ExactRealM` monad:
the user writes natural `if/then/else` update rules over exact reals, and the monad
handles precision management, comparison retries, and error bounding automatically.

## The key insight

In a discrete Hopfield network, the asynchronous update rule for neuron `i` is:

    if localField(i) ≥ θ(i) then s(i) := +1 else s(i) := -1

This is a **branch over reals**, which is undecidable in general (LPO). However:

1. For *concrete* networks (rational or dyadic weights/thresholds), the local field
   is a finite sum of dyadics, so the comparison is decidable at *some* precision.
2. The `ExactRealM` monad automatically finds that precision.

The result is: **verified exact neural computation with zero numerical error**,
where the precision management is invisible to the programmer.

## What this file demonstrates

- `hopfieldUpdate` : updates a single neuron monadically.
- `hopfieldStep` : updates all neurons in sequence.
- `hopfieldRun` : runs multiple update rounds until convergence.
- `#eval` demos showing the network correcting a corrupted pattern.

## Connection to the proof layer

The `ExactRealM` computations use the *same* mathematical operations (finite sums,
products, comparisons) as the `CReal`-level definitions in `Defs.lean`. The bridge
theorems in `Bridge.lean` ensure semantic agreement. Thus:

- Theorems proved about `ExactHopfield.energy` (e.g., energy descent) apply to
  the values computed by this evaluator.
- The evaluator is the *same* function, running on a different backend.
-/

open Computable.Fast ExactRealM

namespace MonadicHopfield

/-! ## Spin type at the fast level -/

inductive FastSpin | up | dn
  deriving DecidableEq, Repr, Inhabited

def FastSpin.toFR : FastSpin → FastReal
  | .up => (1 : FastReal)
  | .dn => FastReal.neg (1 : FastReal)

def FastSpin.flip : FastSpin → FastSpin
  | .up => .dn
  | .dn => .up

/-! ## Network types -/

structure HopfieldNet (n : ℕ) where
  w : Fin n → Fin n → FastReal
  θ : Fin n → FastReal

abbrev HState (n : ℕ) := Fin n → FastSpin

def stateToFR {n : ℕ} (s : HState n) : Fin n → FastReal :=
  fun i => (s i).toFR

/-! ## Helpers -/

def finSum : {n : ℕ} → (Fin n → FastReal) → FastReal
  | 0,     _ => (0 : FastReal)
  | n + 1, f => finSum (n := n) (fun i => f i.castSucc) + f (Fin.last n)

def finSum2 (n : ℕ) (f : Fin n → Fin n → FastReal) : FastReal :=
  finSum fun i => finSum fun j => f i j

/-! ## Core computations -/

/-- Compute the energy of a state. Always succeeds (no branching). -/
def energy {n : ℕ} (net : HopfieldNet n) (s : HState n) : FastReal :=
  let sv := stateToFR s
  let halfNeg := FastReal.neg (FastReal.ofDyadic ⟨1, -1⟩)
  let bilinear := finSum2 n fun i j => net.w i j * sv i * sv j
  let threshold := finSum fun i => net.θ i * sv i
  halfNeg * bilinear + threshold

/-- Compute the local field at neuron `i`. Always succeeds. -/
def localField {n : ℕ} (net : HopfieldNet n) (s : HState n) (i : Fin n) : FastReal :=
  finSum fun j => net.w i j * (stateToFR s j)

/-- **Monadic neuron update**: updates neuron `i` by comparing localField to threshold.

This is the core operation that requires the `ExactRealM` monad. The comparison
`localField(i) ≥ θ(i)` is performed via `branch`, which automatically manages
precision and retries. -/
def updateNeuron {n : ℕ} (net : HopfieldNet n) (s : HState n) (i : Fin n) :
    ExactRealM (HState n) :=
  let lf := localField net s i
  let th := net.θ i
  branch lf th
    (pure (Function.update s i .up))
    (pure (Function.update s i .dn))

/-- Update neurons at indices `0, 1, ..., n-1` (one sweep).
Uses an ascending loop from `start` to `n`. -/
def sweep {n : ℕ} (net : HopfieldNet n) (s : HState n) : ExactRealM (HState n) :=
  let rec go (start : ℕ) (s : HState n) : ExactRealM (HState n) :=
    if h : start < n then do
      let s' ← updateNeuron net s ⟨start, h⟩
      go (start + 1) s'
    else pure s
  termination_by n - start
  go 0 s

/-- Run multiple sweeps, returning the final state. -/
def multiSweep {n : ℕ} (net : HopfieldNet n) (s : HState n) (rounds : ℕ) :
    ExactRealM (HState n) :=
  match rounds with
  | 0 => pure s
  | k + 1 => do
    let s' ← sweep net s
    multiSweep net s' k

/-- Check if a state is stable (all neurons agree with their update). -/
def isStable {n : ℕ} (net : HopfieldNet n) (s : HState n) : ExactRealM Bool :=
  let rec go (start : ℕ) : ExactRealM Bool :=
    if h : start < n then do
      let s' ← updateNeuron net s ⟨start, h⟩
      if s' ⟨start, h⟩ == s ⟨start, h⟩ then go (start + 1)
      else pure false
    else pure true
  termination_by n - start
  go 0

/-- Run sweeps until stable or fuel exhaustion. Returns (finalState, numSweeps). -/
def runUntilStable {n : ℕ} (net : HopfieldNet n) (s : HState n) (maxRounds : ℕ := 20) :
    ExactRealM (HState n × ℕ) :=
  let rec go : ℕ → HState n → ℕ → ExactRealM (HState n × ℕ)
    | 0, s, k => pure (s, k)
    | fuel + 1, s, k => do
      let stable ← isStable net s
      if stable then pure (s, k)
      else do
        let s' ← sweep net s
        go fuel s' (k + 1)
  go maxRounds s 0

/-! ## Demo: 3-neuron XOR-memory Hopfield network -/

private def mkFin3 (a b c : FastReal) : Fin 3 → FastReal
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

private def mkSpin3 (a b c : FastSpin) : HState 3
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

/-- The demo network: Hebbian weights for `[+1,+1,-1]` and `[-1,-1,+1]`. -/
def demoNet : HopfieldNet 3 where
  w := fun i j =>
    if i == j then (0 : FastReal)
    else
      let p1 := mkFin3 1 1 (FastReal.neg 1)
      let p2 := mkFin3 (FastReal.neg 1) (FastReal.neg 1) 1
      p1 i * p1 j + p2 i * p2 j
  θ := fun _ => (0 : FastReal)

def showState (s : HState 3) : String :=
  let f : FastSpin → String | .up => "+1" | .dn => "-1"
  s!"[{f (s 0)}, {f (s 1)}, {f (s 2)}]"

instance : Repr (HState 3) where
  reprPrec s _ := .text (showState s)

/-! ## The headline demos -/

-- A stored pattern (should be stable)
private def s_stored : HState 3 := mkSpin3 .up .up .dn

-- A spurious state (should converge to an attractor)
private def s_spurious : HState 3 := mkSpin3 .up .dn .up

-- A corrupted pattern where localField(0) = 0 = θ(0) exactly
private def s_boundary : HState 3 := mkSpin3 .up .dn .dn

/-! ### Demo 1: Stored pattern is stable -/
#eval (isStable demoNet s_stored).run 40

/-! ### Demo 2: Spurious state converges to an attractor in 1 sweep -/
#eval (runUntilStable demoNet s_spurious).run 40 |>.map fun (s, k) => (showState s, k)

/-! ### Demo 3: Boundary case — monad correctly identifies undecidability

The corrupted pattern `[+1, -1, -1]` has `localField(0) = 0` and `θ(0) = 0`.
The comparison `0 ≥ 0` is genuinely on the boundary: ball arithmetic can never
separate two equal values, so `FastReal.compare 0 0` always returns `none`.

The monad **correctly refuses to decide** — this is the LPO in action!
In a classical setting, `0 ≥ 0` is true, but constructively/computably,
this comparison is undecidable. The `none` output is the right answer. -/
#eval (sweep demoNet s_boundary).run 200 |>.map showState

/-! ### Demo 4: Network with nonzero thresholds (all comparisons decidable)

Adding a small threshold `θ = 0.1` breaks the degeneracy and makes all
local field comparisons strictly decidable. -/
private def biasedNet : HopfieldNet 3 where
  w := demoNet.w
  θ := fun _ => FastReal.ofDyadic ⟨1, -4⟩  -- θ = 1/16 ≈ 0.0625

-- The corrupted pattern now converges (localField(0) = 0 > 0.0625 is false, so dn)
#eval (runUntilStable biasedNet s_boundary).run 40 |>.map fun (s, k) => (showState s, k)

-- And the stored pattern is still stable
#eval (isStable biasedNet s_stored).run 40

/-! ### Demo 5: Energy landscape -/
#eval energy demoNet s_stored
#eval energy demoNet s_spurious

-- Certified: stored has strictly lower energy than spurious
#eval FastReal.compareExplain
  (energy demoNet s_stored)
  (energy demoNet s_spurious) 40 6

end MonadicHopfield
