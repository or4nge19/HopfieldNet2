import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Combinatorics.Quiver.Path

namespace Quiver.Path

variable {V : Type*} [Quiver V] {R : Type*}

section Weight

variable [Monoid R]

@[simp]
def weight (w : ∀ {i j : V}, (i ⟶ j) → R) : ∀ {i j : V}, Path i j → R
  | _, _, Path.nil => 1
  | _, _, Path.cons p e => weight w p * w e
def weightFromVertices (w : V → V → R) : ∀ {i j : V}, Path i j → R :=
  weight (fun {i j} (_ : i ⟶ j) => w i j)

@[simp]
lemma weight_comp (w : ∀ {i j : V}, (i ⟶ j) → R) {a b c : V} (p : Path a b) (q : Path b c) :
    weight w (p.comp q) = weight w p * weight w q := by
  induction q with | nil => simp | cons q' e ih => simp [Path.comp_cons, ih, mul_assoc]

@[simp]
lemma weightFromVertices_comp (w : V → V → R) {a b c : V} (p : Path a b) (q : Path b c) :
    weightFromVertices w (p.comp q) = weightFromVertices w p * weightFromVertices w q := by
  simp [weightFromVertices, weight_comp]

end Weight

section PositiveWeight

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R]

lemma weight_pos {w : ∀ {i j : V}, (i ⟶ j) → R}
    (hw : ∀ {i j : V} (e : i ⟶ j), 0 < w e) {i j : V} (p : Path i j) :
    0 < weight w p := by
  induction p with
  | nil => simp [weight, zero_lt_one];
  | cons p e ih => simp [mul_pos ih (hw e)]

end PositiveWeight

section RealWeight

lemma weightFromVertices_pos {w : V → V → ℝ}
    (hw : ∀ i j : V, 0 < w i j) {i j : V} (p : Path i j) :
    0 < weightFromVertices w p := by
  apply weight_pos; intro i j _; exact hw i j

lemma weightFromVertices_nonneg {w : V → V → ℝ}
    (hw : ∀ i j : V, 0 ≤ w i j) {i j : V} (p : Path i j) :
    0 ≤ weightFromVertices w p := by
  induction p using Path.rec with
  | nil => simp [weightFromVertices, weight, zero_le_one]
  | cons p' e ih => simp only [weightFromVertices, weight]; exact mul_nonneg ih (hw _ _)

end RealWeight

section PathDecomposition

variable {V : Type*} [Quiver V]

/-- Every non-empty path can be decomposed as an initial path plus a final edge. -/
lemma path_decomposition_last_edge {a b : V} (p : Path a b) (h : p.length > 0) :
    ∃ (c : V) (p' : Path a c) (e : c ⟶ b), p = p'.cons e := by
  cases p with | nil => simp at h | cons p' e => exact ⟨_, p', e, rfl⟩

/-- Every non-empty path can be decomposed as a first edge plus a remaining path. -/
lemma path_decomposition_first_edge {a b : V} (p : Path a b) (h : p.length > 0) :
    ∃ (c : V) (e : a ⟶ c) (p' : Path c b), p = e.toPath.comp p' ∧ p.length = p'.length + 1 := by
  have h_len : p.length = (p.length - 1) + 1 := by omega
  obtain ⟨c, e, p', hp', rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p h_len
  use c, e, p'; exact ⟨rfl, by omega⟩

end PathDecomposition

section BoundaryEdges

variable {V : Type*} [Quiver V]

@[simp]
lemma cons_eq_comp_toPath {a b c : V} (p : Path a b) (e : b ⟶ c) :
    p.cons e = p.comp e.toPath := by
  rfl

/-- A path from a vertex not in `S` to a vertex in `S` must cross the boundary. -/
theorem exists_boundary_edge {a b : V} (p : Path a b) (S : Set V)
    (ha_not_in_S : a ∉ S) (hb_in_S : b ∈ S) :
    ∃ (u v : V) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      u ∉ S ∧ v ∈ S ∧ p = p₁.comp (e.toPath.comp p₂) := by
  induction' h_len : p.length with n ih generalizing a b S ha_not_in_S hb_in_S
  · -- Base case n = 0: Path must be nil, so a = b. Contradiction.
    have hab : a = b := eq_of_length_zero p h_len
    subst hab
    exact (ha_not_in_S hb_in_S).elim
  · -- Inductive step: Assume true for all paths of length < n+1.
    have h_pos : 0 < p.length := by rw[h_len]; simp
    obtain ⟨c, p', e, rfl⟩ := path_decomposition_last_edge p h_pos
    by_cases hc_in_S : c ∈ S
    · -- Case 1: The endpoint of `p'` is already in `S`.
      have p'_len : p'.length = n := by exact Nat.succ_inj.mp h_len
      obtain ⟨u, v, e_uv, p₁, p₂, hu_not_S, hv_S, hp'⟩ :=
        ih p' S ha_not_in_S hc_in_S p'_len
      refine ⟨u, v, e_uv, p₁, p₂.comp e.toPath, hu_not_S, hv_S, ?_⟩
      rw [cons_eq_comp_toPath, hp', Path.comp_assoc, Path.comp_assoc]
    · -- Case 2: The endpoint of `p'` is not in `S`.
      refine ⟨c, b, e, p', Path.nil, hc_in_S, hb_in_S, ?_⟩
      simp only [comp_nil]
      simp_all only [exists_and_left, length_cons, Nat.add_right_cancel_iff, lt_add_iff_pos_left, add_pos_iff,
        Nat.lt_one_iff, pos_of_gt, or_true]
      subst h_len
      rfl

/-- Alternative formulation: there exists an edge crossing the boundary. -/
theorem exists_crossing_edge {a b : V} (p : Path a b) (S : Set V)
    (ha_not_in_S : a ∉ S) (hb_in_S : b ∈ S) :
    ∃ (u v : V) (_ : u ⟶ v), u ∉ S ∧ v ∈ S := by
  obtain ⟨u, v, e, _, _, hu_not_S, hv_S, _⟩ := exists_boundary_edge p S ha_not_in_S hb_in_S
  exact ⟨u, v, e, hu_not_S, hv_S⟩

end BoundaryEdges

end Quiver.Path

namespace Quiver.Path

variable {V : Type*} [Quiver V]

/-- The end vertex of a path. A path `p : Path a b` has `p.end = b`. -/
def «end» {a : V} : ∀ {b : V}, Path a b → V
  | b, _ => b

/-- The set of vertices in a path. -/
def activeVertices {a : V} : ∀ {b : V}, Path a b → Set V
  | _, nil => {a}
  | _, cons p e => activeVertices p ∪ {«end» (cons p e)}

@[simp] lemma end_cons {a b c : V} (p : Path a b) (e : b ⟶ c) : «end» (p.cons e) = c := rfl
@[simp] lemma activeVertices_nil {a : V} : activeVertices (nil : Path a a) = {a} := rfl
@[simp] lemma activeVertices_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
  activeVertices (p.cons e) = activeVertices p ∪ {c} := by simp [activeVertices]; rfl

end Quiver.Path

namespace Prefunctor

open Quiver

variable {V W : Type*} [Quiver V] [Quiver W] (F : V ⥤q W)

@[simp]
lemma end_map {a b : V} (p : Path a b) : F.obj (p.end) = (F.mapPath p).end := by
  induction p with
  | nil => rfl
  | cons p' e ih => simp [ih]; rfl

end Prefunctor

open Quiver

namespace Quiver

/-- The quiver structure on a subtype is induced by the quiver structure on the original type.
    An arrow from `a : S` to `b : S` exists if an arrow from `a.val` to `b.val` exists. -/
def inducedQuiver {V : Type u} [Quiver.{v} V] (S : Set V) : Quiver.{v} S :=
  ⟨fun a b => a.val ⟶ b.val⟩

end Quiver

namespace Quiver.Subquiver

variable {V : Type u} [Quiver.{v} V] (S : Set V)

attribute [local instance] inducedQuiver

/-- The embedding of an induced subquiver on a set `S` into the original quiver. -/
@[simps]
def embedding : Prefunctor S V where
  obj := Subtype.val
  map := id

/-- The vertices in a path mapped by the embedding are all in the original set S. -/
@[simp]
lemma mapPath_embedding_vertices_in_set {i j : S} (p : Path i j) :
  ∀ v, v ∈ ((embedding S).mapPath p).activeVertices → v ∈ S := by
  induction p with
  | nil =>
    intro v hv
    simp only [Prefunctor.mapPath_nil, Path.activeVertices_nil, Set.mem_singleton_iff] at hv
    subst hv
    exact i.property
  | cons p' e ih =>
    intro v hv
    simp only [Prefunctor.mapPath_cons, Path.activeVertices_cons, Set.mem_union,
               Set.mem_singleton_iff] at hv
    cases hv with
    | inl h => exact ih v h
    | inr h => subst h; aesop

end Quiver.Subquiver
