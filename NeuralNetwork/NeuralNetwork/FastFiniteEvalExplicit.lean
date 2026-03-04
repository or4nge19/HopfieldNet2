import HopfieldNet.CReals.CRealsFast
import Mathlib.Data.List.FinRange

/-!
# Executable finite evaluation with an explicit enumeration

Mathlib's `Finset.toList` / `Fintype.elems` can be non-executable (classical) in general.

To get a truly **computable** evaluator, we require the user to provide an explicit `List`
enumerating the finite type.

Correctness contract (important):
- `FiniteEnum.enum` should list **every** element exactly once (no duplicates, no omissions).
  This file does not (and cannot, in general) enforce that contract computationally.

This is the SOTA separation:

- `Fintype` is great for proofs.
- computation needs an *explicit enumeration*.
-/

namespace NeuralNetwork
namespace FastFiniteEvalExplicit

open Computable.Fast

class FiniteEnum (α : Type) : Type where
  enum : List α

namespace FiniteEnum

instance (n : Nat) : FiniteEnum (Fin n) where
  enum := List.finRange n

end FiniteEnum

/-!
## Soundness predicate for explicit enumerations

`FiniteEnum` is a compute-layer device: it carries only a list.

For *theorems* relating compute-layer objects to proof-layer `Fintype` semantics, we also
need a **Prop-only** contract stating that the list enumerates the type without duplicates.
-/

class FiniteEnumSound (α : Type) [FiniteEnum α] : Prop where
  /-- No duplicates in the enumeration list. -/
  nodup : (FiniteEnum.enum (α := α)).Nodup
  /-- Completeness: every element appears in the enumeration list. -/
  complete : ∀ a : α, a ∈ (FiniteEnum.enum (α := α))

namespace FiniteEnumSound

instance instFiniteEnumSoundFin (n : Nat) : FiniteEnumSound (Fin n) := by
  classical
  refine ⟨?_, ?_⟩
  · change (List.finRange n).Nodup
    exact List.nodup_finRange n
  · intro a
    change a ∈ List.finRange n
    exact List.mem_finRange a

end FiniteEnumSound

variable {ι : Type} [FiniteEnum ι]

def sum (f : ι → FastReal) : FastReal :=
  (FiniteEnum.enum (α := ι)).foldl (fun acc i => acc + f i) 0

def boltzmannWeight (β : FastReal) (E : FastReal) : FastReal :=
  FastReal.exp (-(β * E))

def partitionFunction (β : FastReal) (E : ι → FastReal) : FastReal :=
  sum (ι := ι) (fun i => boltzmannWeight β (E i))

def probability? (β : FastReal) (E : ι → FastReal) (i : ι) : ℕ → Option Ball :=
  let w : FastReal := boltzmannWeight β (E i)
  let Z : FastReal := partitionFunction (ι := ι) β E
  FastReal.div? w Z

end FastFiniteEvalExplicit
end NeuralNetwork
