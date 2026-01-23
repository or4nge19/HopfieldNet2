import Mathlib.CategoryTheory.MarkovCategory.Basic

/-!
## MarkovCategory integration (minimal, compile-safe)

This is a small “hook point” for later probabilistic semantics:
it packages the core MarkovCategory lemma (`discard_natural`) in a way that is
immediately useful when viewing a stochastic/dynamical *step* as a morphism.

The goal is to make it easy to later interpret neural dynamics / kernels as
morphisms in a concrete Markov category (e.g. kernels), without committing to a
specific model here.
-/

namespace MCNN

open CategoryTheory
open MonoidalCategory ComonObj

namespace MarkovSemantics

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CategoryTheory.MarkovCategory C]

/-- A single (possibly stochastic) “step” on state `X`, seen as a Markov morphism. -/
structure Step (X : C) where
  f : X ⟶ X

namespace Step

variable {X : C} (s : Step (C := C) X)

/-- In any Markov category, discarding after a step equals discarding directly. -/
@[simp] lemma discard_after : s.f ≫ ε[X] = ε[X] := by
  simp [CategoryTheory.MarkovCategory.discard_natural (C := C) (f := s.f) (X := X) (Y := X)]

end Step

end MarkovSemantics

end MCNN
