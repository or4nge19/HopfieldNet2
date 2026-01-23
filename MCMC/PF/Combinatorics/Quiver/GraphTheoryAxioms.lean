import MCMC.PF.Combinatorics.Quiver.Path
import Mathlib.Data.Nat.Find

/-!
Bridge module for NR's graph-theory axioms.

This file provides theorem versions of the first two axioms in
`AsyncDSLMath.Abstractions.GraphTheory` using the existing results in
`MCMC.PF.Combinatorics.Quiver.Path`.

Note: the third axiom as stated in the original file (strict `< Fintype.card V` for *all*
positive-length paths, including loops `a = b`) is not provable in general: a quiver can
have a Hamiltonian cycle of length `Fintype.card V`, and even the one-vertex quiver with a
loop gives an immediate counterexample.

We provide the strongest generally valid theorem we can prove from the current
MCMC development: the strict bound for the non-loop case `a ≠ b`.
-/

namespace AsyncDSLMath.Abstractions.GraphTheory

open Quiver

/-- **Simple Path Bound**

If a path has no repeated vertices, then its length is strictly less than the number of
vertices.

This is `Quiver.Path.length_lt_card_of_isStrictlySimple` from
`MCMC.PF.Combinatorics.Quiver.Path`.
-/
theorem quiver_simple_path_bound (V : Type*) [DecidableEq V] [Quiver V] [Fintype V]
    {a b : V} (p : Path a b)
    (h_simple : p.vertices.Nodup) :
    p.length < Fintype.card V := by
  simpa [Quiver.Path.IsStrictlySimple] using
    (Quiver.Path.length_lt_card_of_isStrictlySimple (p := p)
      (hp := (by simpa [Quiver.Path.IsStrictlySimple] using h_simple)))

/-- **Cycle Removal / Simple Subpath Extraction**

Every path admits a (strictly) simple path with the same endpoints and length bounded by the
original path length.

We choose a shortest-length path among all paths from `a` to `b` (which exists because `p`
itself is such a path), then use `Quiver.Path.isStrictlySimple_of_shortest`.
-/
theorem quiver_exists_simple_subpath (V : Type*) [DecidableEq V] [Quiver V]
    {a b : V} (p : Path a b) :
    ∃ (q : Path a b), q.vertices.Nodup ∧ q.length ≤ p.length := by
  classical
  let P : Nat → Prop := fun n => ∃ (q : Path a b), q.length = n
  have hP : ∃ n, P n := ⟨p.length, p, rfl⟩
  let n0 : Nat := Nat.find hP
  have hn0_spec : P n0 := Nat.find_spec hP
  rcases hn0_spec with ⟨q, hq_len⟩
  have hmin_all : ∀ r : Path a b, n0 ≤ r.length := by
    intro r
    have : P r.length := ⟨r, rfl⟩
    exact Nat.find_min' hP this
  have hmin_q : ∀ r : Path a b, q.length ≤ r.length := by
    intro r
    simpa [n0, hq_len] using hmin_all r
  have hq_simple_strict : Quiver.Path.IsStrictlySimple q :=
    Quiver.Path.isStrictlySimple_of_shortest (p := q) hmin_q
  have hq_nodup : q.vertices.Nodup := by
    simpa [Quiver.Path.IsStrictlySimple] using hq_simple_strict

  refine ⟨q, hq_nodup, ?_⟩
  exact hmin_q p

/-- A provable version of NR’s `quiver_shortest_path_bound` for the non-loop case.

If `a ≠ b`, any path from `a` to `b` has positive length, and we can extract a strictly
simple subpath and apply `quiver_simple_path_bound`.
-/
theorem quiver_shortest_path_bound_of_ne (V : Type*) [DecidableEq V] [Quiver V] [Fintype V]
    {a b : V} (hab : a ≠ b) (p : Path a b) :
    ∃ (q : Path a b), q.length > 0 ∧ q.length < Fintype.card V := by
  obtain ⟨q, hq_simple, hq_le⟩ := quiver_exists_simple_subpath V p
  have hq_bound : q.length < Fintype.card V := quiver_simple_path_bound V q hq_simple
  have hq_pos : q.length > 0 := by
    by_contra h0
    have hlen0 : q.length = 0 := Nat.eq_zero_of_not_pos h0
    have : a = b := Quiver.Path.eq_of_length_zero (p := q) hlen0
    exact hab this
  exact ⟨q, hq_pos, hq_bound⟩

end AsyncDSLMath.Abstractions.GraphTheory
