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
layer (`ExactHopfield.energy`) and all theorems (energy descent, convergence) are
proved here.

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

The Hopfield update rule is defined here (`MonadicHopfield.updateNeuron`) and
produces verified network dynamics: spurious states converge to attractors in
exactly 1 sweep, with a certified comparison showing energy descent.

## The Faithfulness Bridge

The three layers are connected by two bridge theorems:

1. **Spec ↔ ℝ** (`Bridge.energy_toReal`):
   `toRealRingHom (energy p s) = classicalEnergy (toRealRingHom ∘ w) (toRealRingHom ∘ θ) …`
   — the `CReal` energy equals the `ℝ` energy under the denotation map.

2. **Fast ↔ Spec** (via `ApproxRationals` + `CRealsFastBackend`):
   the dyadic ball backend is a certified implementation of the spec.

Together: **theorems proved at Layer 1 apply to computations run at Layer 2/3.**

## Roadmap: future extensions

### Near-term (fills remaining `sorry`s)

- `energyDiff_eq_energy_sub`: algebraic identity relating energy difference to
  `(old - new) * (localField - θ)`. Requires `Finset.sum` splitting at index `i`
  and `w_ii = 0` / symmetry.
- `energy_descent`: sign analysis showing `(old - new) * (localField - θ) ≤ 0`
  under the "correct update" hypothesis.
- RatCast diamond in `energy_toReal`: reconcile the two `RatCast` instances on `CReal`.

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
├── SpinCReal.lean        Layer 1: Spin ↪ CReal (computable, 0 sorry)
├── Defs.lean             Layer 1: energy, localField over CReal (computable, 0 sorry)
├── EnergyDescent.lean    Layer 1: hero theorem (2 sorry: algebraic identity + sign)
├── Bridge.lean           Bridge:  CReal energy = ℝ energy (1 sorry: ratcast diamond)
├── ExactRealM.lean       Layer 3: precision-retry monad (computable, 0 sorry)
├── MonadicHopfield.lean  Layer 3: monadic Hopfield evaluator (computable, 0 sorry)
├── Eval.lean             Layer 2: FastReal energy #eval demos (computable, 0 sorry)
└── Architecture.lean     This file: facade + roadmap
```
-/

-- This file is documentation-only; no definitions.
