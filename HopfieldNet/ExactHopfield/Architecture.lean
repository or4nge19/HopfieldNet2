/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import HopfieldNet.ExactHopfield.Defs
import HopfieldNet.ExactHopfield.EnergyDescent
import HopfieldNet.ExactHopfield.Bridge
import HopfieldNet.ExactHopfield.ExactRealM

/-!
# Architecture: The Three-Layer Exact-Real Hopfield Stack

This file is the architectural facade for the Exact Hopfield project. It documents
how the three layers — specification, proof, and execution — address the fundamental
**ERA (Exact Real Arithmetic) Trilemma**:

> Choose two of: (1) definitional simplicity, (2) computational efficiency,
> (3) topological faithfulness.

Our answer: **all three**, via a principled three-layer split.

## Layer 1: Specification (`CReal.Pre` / Regular Cauchy Sequences)

- **Files**: `CRealPre2/*.lean`, `CRealRealEquiv.lean`, `CRealComplete.lean`
- **Trilemma axis**: maximizes **(1) definitional simplicity**.
- **Design**: reals are sequences `ℕ → ℚ` with modulus `|a_n - a_m| ≤ 2^{-n}`.
- **Strengths**: quotient-clean algebra, fully constructive completeness,
  direct bridge to `ℝ` via `toRealRingHom`.
- **Known cost**: multiplication requires explicit index shifting (`mulShift`),
  which causes term blowup in deep expressions.

The Hopfield energy `E(s) = -½ ∑ w_ij s_i s_j + ∑ θ_i s_i` is defined at this
layer (`ExactHopfield.energy`), and the built theorem path currently establishes
the one-step energy descent results. Broader convergence / fixed-point packaging
over `CReal` is still future work.

## Layer 2: Execution (`Computable.Fast` / Dyadic Ball Arithmetic)

- **Files**: `CRealsFast.lean`, `CRealsFastBackend.lean`
- **Trilemma axis**: maximizes **(2) computational efficiency**.
- **Design**: reals are streams `ℕ → Ball` where `Ball = (mid : Dyadic, rad : Dyadic)`.
  Arithmetic is demand-driven: `(x + y) n` evaluates `x` and `y` at precision `n+2`
  and sums the balls.
- **Strengths**: GMP-backed `Int` arithmetic, bit-shift rounding, sub-millisecond
  `#eval` for moderate-precision calculations.
- **Known cost**: soundness bridge to the spec layer (`ApproxRationals` instance)
  is the bottleneck for end-to-end verification.

The same Hopfield energy is evaluated here (`ExactHopfield.Eval.fastEnergy`) and
produces exact dyadic balls: `[-6.0 ± 0.0]` for stored patterns.

## Layer 3: Topological Execution Monad (`ExactRealM`)

- **Files**: `ExactRealM.lean`, `MonadicHopfield.lean`
- **Trilemma axis**: provides **(3) topological faithfulness**.
- **Design**: `ExactRealM α := ℕ → Option α`. Computations are parameterized by
  working precision; `none` means "comparison undecidable, retry at higher precision."
  The `run` function automatically scales precision (iRRAM-style).
- **Strengths**: the user writes `branch lf θ (pure .up) (pure .dn)` — standard
  imperative branching — and the monad manages precision invisibly.
- **Key property**: on the boundary (e.g., `localField = θ` exactly), the monad
  correctly returns `none`, matching the constructive fact that `x = y` is
  undecidable for computable reals. This is the **LPO** made computationally manifest.

The monadic update rule is prototyped here (`MonadicHopfield.updateNeuron`).
For separated comparisons, it behaves like the expected threshold update; on the
exact boundary it intentionally returns `none` rather than choosing a classical
tie-breaking branch. The concrete `#eval` examples show attractor behavior on
small networks, but a full backend-correctness theorem relating this evaluator
to `ExactHopfield.zeroTempDet` is still future work.

## The Faithfulness Bridge

The three layers are connected by two bridge theorems:

1. **Spec ↔ ℝ** (`Bridge.energy_toReal`):
   `toRealRingHom (energy p s) = classicalEnergy (toRealRingHom ∘ w) (toRealRingHom ∘ θ) …`
   — the `CReal` energy equals the `ℝ` energy under the denotation map.

2. **Fast ↔ Spec** (via `ApproxRationals` + `CRealsFastBackend`):
   the dyadic ball backend is a certified implementation of the spec.

Together, these layers supply the ingredients for end-to-end certification. At
present, the fully packaged theorem bridge is the spec ↔ `ℝ` one; the final
fast/spec correctness theorem for the `ExactHopfield` evaluator remains to be stated
and proved explicitly.

## Roadmap: future extensions

### Near-term (strengthen theorem surface and integration)

- package a more explicit theorem API around the already built energy-descent path,
  so downstream users can cite concise review-facing lemmas in addition to
  `energy_descent_detUpdate` and `energy_strict_of_L_apart`;
- state and prove the strongest end-to-end correctness theorem for the separate
  `FastHopfieldEnergy` route in `NeuralNetwork`, clarifying exactly how that fast
  path relates to the abstract Hopfield specification;
- extend the current bridge story from energy preservation to larger proof bundles
  that combine exact-real evaluation with convergence / stability statements.

### Medium-term (paper-ready)

- **Continuous Hopfield**: define the continuous relaxation with sigmoid activations
  (`CRealSigmoid.lean`) over `CReal`. Prove contractivity of the sigmoid map implies
  a unique fixed point (Banach fixed-point over `CReal`).
- **Convergence theorem over `CReal`**: instantiate `HopfieldNetwork CReal (Fin n)`
  using the CCLOF instance and inherit all convergence theorems from `HN/Core.lean`.
- **Certified evaluator**: build a tactic or reflection oracle that, given a concrete
  network, evaluates `energy` at the fast level and produces a kernel-checkable
  separation certificate.

### Long-term (follow-up papers)

- **Constructive Picard-Lindelöf**: continuous-time Hopfield dynamics via a
  computable ODE solver over `CReal`.
- **Signed-digit corecursive reals**: replace `CReal.Pre` with a coinductive
  stream of overlapping digits `{-1, 0, +1}`, eliminating the `mulShift` overhead.
  This addresses the performance axis at the spec level itself.
- **Verified FFT/binary-splitting**: asymptotically fast arithmetic for the
  transcendental functions (`exp`, `sin`, `π`).

## File map

```
ExactHopfield/
├── SpinCReal.lean        Layer 1: Spin ↪ CReal (computable)
├── Defs.lean             Layer 1: energy, localField over CReal (computable)
├── EnergyDescent.lean    Layer 1: built energy-descent theorem path
├── Bridge.lean           Bridge: CReal energy = ℝ energy
├── ExactRealM.lean       Layer 3: precision-retry monad (computable)
├── MonadicHopfield.lean  Layer 3: monadic Hopfield evaluator (computable)
├── Eval.lean             Layer 2: FastReal energy #eval demos (computable)
└── Architecture.lean     This file: facade + roadmap
```

## Current status note

The proof-facing `ExactHopfield` surface currently builds:

- `HopfieldNet.ExactHopfield.Bridge`
- `HopfieldNet.ExactHopfield.EnergyDescent`
- `HopfieldNet.ExactHopfield.ExactRealM`

The executable demo modules `MonadicHopfield` and `Eval` also build, but they are
kept separate from the default umbrella import until the full fast/spec correctness
story is packaged.

So the roadmap above should be read as *integration strengthening*, not as “the core proof path is still blocked by `sorry`s”.
-/

-- This file is documentation-only; no definitions.
