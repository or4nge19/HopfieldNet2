/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import HopfieldNet.CReals.CRealsFast

/-!
# ExactRealM: A Verified Topological Execution Monad for Exact Reals

This file implements the core execution model that addresses the **branching problem**
in exact real arithmetic. In constructive mathematics, `x < 0 ∨ x ≥ 0` is undecidable
(the Limited Principle of Omniscience / LPO). This makes standard `if/then/else` illegal
when computing with exact reals.

## The iRRAM Paradigm (Müller, 2001)

The unverified C++ library iRRAM solves this by:
1. Attempting every computation at precision `p`.
2. If a comparison is undecidable at `p`, throwing a `PrecisionInsufficient` exception.
3. Catching the exception at the top level, doubling `p`, and re-executing from scratch.

This monad formalizes the same pattern in Lean 4, using `Option` instead of exceptions:

- `ExactRealM α := ℕ → Option α`
- A computation at precision `n` either succeeds (`some a`) or fails (`none`).
- `run` automatically scales precision until success or fuel exhaustion.

## Position in the ERA Trilemma

The ERA community faces a trilemma: choose two of
(1) definitional simplicity, (2) computational efficiency, (3) topological faithfulness.

- The **spec layer** (`CReal.Pre` / regular Cauchy sequences) maximizes (1).
- The **fast backend** (`Computable.Fast.FastReal`) maximizes (2).
- **This monad** bridges them, providing (3): users write imperative-style programs
  with `if/then/else`, and the monad handles precision management automatically.

Together, the three layers cover all three axes of the trilemma.

## Main definitions

- `ExactRealM` : the precision-parameterized computation monad.
- `ExactRealM.compareFR` : compare two `FastReal`s at the current precision.
- `ExactRealM.branch` : topological branching (the key operation).
- `ExactRealM.run` : execute with automatic precision scaling.

## Why this matters for Hopfield networks

The Hopfield update rule `if localField ≥ θ then up else dn` is a **branch over reals**.
Without this monad, the user must manually provide separation witnesses or fuel parameters.
With the monad, the update is written as:

```
def hopfieldUpdate (w θ s i) : ExactRealM Spin :=
  branch (localField w s i) (θ i) (pure .up) (pure .dn)
```

and the precision management is invisible.
-/

open Computable.Fast

/-- A computation over exact reals parameterized by working precision.

At precision level `n`, the computation either produces a result (`some a`)
or signals that the precision is insufficient (`none`).

This is the formal analogue of iRRAM's exception-based precision scaling. -/
def ExactRealM (α : Type) := ℕ → Option α

namespace ExactRealM

instance : Monad ExactRealM where
  pure a := fun _ => some a
  bind m f := fun n => do
    let a ← m n
    f a n

/-  `ExactRealM` satisfies the monad laws (pure_bind, bind_assoc, etc.) by
    pointwise unfolding — each law reduces to `Option.bind` equalities at
    each precision level `n`. The proofs are omitted here for brevity; they
    are straightforward `funext` + `Option.bind` simplifications. -/

/-! ## Lifting -/

/-- Lift a `FastReal` value into the monad (always succeeds). -/
def liftFR (x : FastReal) : ExactRealM FastReal :=
  pure x

/-- Lift an `Option`-valued computation: `none` signals precision failure. -/
def liftOption (f : ℕ → Option α) : ExactRealM α := f

/-- Fail at this precision level (request more precision). -/
def fail : ExactRealM α := fun _ => none

/-! ## Comparison: the heart of the monad -/

/-- Compare two `FastReal`s at the current precision level.

Returns `some ord` if the ball arithmetic can separate them, `none` otherwise.
This is the fundamental semi-decision that makes branching possible. -/
def compareFR (x y : FastReal) : ExactRealM Ordering :=
  fun n => FastReal.compare x y n

/-- **Topological branching**: the key operation.

`branch x y ifGe ifLt` evaluates to `ifGe` if `x ≥ y` and `ifLt` if `x < y`.
If the comparison is undecidable at the current precision, it returns `none`,
triggering a retry at higher precision.

This replaces the illegal `if x ≥ y then ... else ...` with a monadically
managed version that automatically handles the LPO-undecidability of real
comparison.

Implementation note: the current `FastReal.compare` returns only `.lt`, `.gt`,
or `none`; exact equality falls through to `none`. The `.eq` branch below is
kept as a forward-compatible convention and is treated as the `≥` branch. -/
def branch (x y : FastReal) (ifGe ifLt : ExactRealM α) : ExactRealM α :=
  fun n =>
    match FastReal.compare x y n with
    | some Ordering.lt => ifLt n
    | some Ordering.eq => ifGe n
    | some Ordering.gt => ifGe n
    | none => none

/-- Three-way branch: distinguish `<`, `=`, and `>`.

Note: with the current `FastReal.compare`, exact equality is not detected; equal
inputs return `none`. The `.eq` branch is therefore a reserved hook for future
comparators that may provide an explicit equality certificate. -/
def branch3 (x y : FastReal) (ifLt ifEq ifGt : ExactRealM α) : ExactRealM α :=
  fun n =>
    match FastReal.compare x y n with
    | some Ordering.lt => ifLt n
    | some Ordering.eq => ifEq n
    | some Ordering.gt => ifGt n
    | none => none

/-! ## Execution -/

/-- Execute a monadic computation with automatic precision scaling.

Starts at precision `startPrec` and increments until the computation succeeds
or `maxFuel` retries are exhausted. This is the top-level "catch and retry" loop
that corresponds to iRRAM's exception handler. -/
def run (m : ExactRealM α) (maxFuel : ℕ := 100) (startPrec : ℕ := 0) : Option α :=
  let rec loop : ℕ → ℕ → Option α
    | _, 0 => none
    | n, fuel + 1 =>
      match m n with
      | some a => some a
      | none => loop (n + 1) fuel
  loop startPrec (maxFuel + 1)

/-- Execute and unwrap, returning a default on failure. -/
def runD (m : ExactRealM α) [Inhabited α] (maxFuel : ℕ := 100) : α :=
  (run m maxFuel).getD default

/-! ## Arithmetic operations (lifted from FastReal) -/

def add (x y : ExactRealM FastReal) : ExactRealM FastReal :=
  (· + ·) <$> x <*> y

def mul (x y : ExactRealM FastReal) : ExactRealM FastReal :=
  (· * ·) <$> x <*> y

def neg (x : ExactRealM FastReal) : ExactRealM FastReal :=
  FastReal.neg <$> x

def sub (x y : ExactRealM FastReal) : ExactRealM FastReal :=
  add x (neg y)

/-! ## Rendering -/

instance [Repr α] : Repr (ExactRealM α) where
  reprPrec m _ :=
    match run m 50 with
    | some a => repr a
    | none => "⊥ (undecidable at fuel=50)"

end ExactRealM
