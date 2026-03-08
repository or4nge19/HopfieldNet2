import HopfieldNet.CReals.SignedDigit.Basic
import Mathlib.Lean.Thunk

/-!
# Executable (lazy) signed-digit streams

`SDStream := ℕ → Digit` is excellent as a **specification** type, but it is not suitable as an
executable stream representation: evaluating the `n`-th digit typically recomputes all earlier work.

This file provides a simple *lazy* stream representation for execution:

`LazySDStream` stores its head digit and a thunk for the tail.

We then provide a total projection `toSDStream : LazySDStream → SDStream` so the existing
specification/proof layer (notably `SignedDigit.toPre`) can be reused unchanged.

Note: `Thunk` is a suspended computation `Unit → α`. It is **pure** and supports sharing in the
usual functional-programming way (if you compute `t.get` once and reuse it, work is not repeated).
-/

namespace Computable
namespace CReal
namespace SignedDigit

/-- A lazy (executable) signed-digit stream. -/
structure LazySDStream where
  head : Digit
  tail : Thunk LazySDStream

namespace LazySDStream

/-- Force one step of the stream: return the head and the tail. -/
@[simp] def step (s : LazySDStream) : Digit × LazySDStream :=
  (s.head, s.tail.get)

/-- `cons` for lazy streams (non-suspending tail). -/
@[simp] def cons (d : Digit) (s : LazySDStream) : LazySDStream :=
  ⟨d, Thunk.pure s⟩

/-- The `n`-th digit (by iterated forcing). -/
def nth : LazySDStream → ℕ → Digit
  | s, 0     => s.head
  | s, n + 1 => nth (s.tail.get) n

@[simp] lemma nth_zero (s : LazySDStream) : nth s 0 = s.head := rfl
@[simp] lemma nth_succ (s : LazySDStream) (n : ℕ) : nth s (n + 1) = nth (s.tail.get) n := rfl

/-- Convert a lazy stream into the spec stream `ℕ → Digit`. -/
def toSDStream (s : LazySDStream) : SDStream :=
  fun n => nth s n

@[simp] lemma toSDStream_zero (s : LazySDStream) : toSDStream s 0 = s.head := rfl
@[simp] lemma toSDStream_succ (s : LazySDStream) (n : ℕ) :
    toSDStream s (n + 1) = toSDStream (s.tail.get) n := rfl

/-- Consume `n` digits, returning the list of digits and the remaining stream. -/
def take : ℕ → LazySDStream → List Digit × LazySDStream
  | 0,     s => ([], s)
  | n + 1, s =>
      let (d, t) := s.step
      let (ds, r) := take n t
      (d :: ds, r)

@[simp] lemma take_zero (s : LazySDStream) : take 0 s = ([], s) := rfl

/-- Denotation of a lazy stream as a `CReal.Pre` via the spec projection. -/
def toPre (s : LazySDStream) : Computable.CReal.Pre :=
  SignedDigit.toPre (toSDStream s)

/-- Denotation of a lazy stream as a quotient `CReal` via the spec projection. -/
def toCReal (s : LazySDStream) : Computable.CReal :=
  ⟦toPre s⟧

@[simp] theorem toPre_approx (s : LazySDStream) (n : ℕ) :
    (toPre s).approx n = (SignedDigit.toPre (toSDStream s)).approx n := rfl

end LazySDStream

end SignedDigit
end CReal
end Computable

