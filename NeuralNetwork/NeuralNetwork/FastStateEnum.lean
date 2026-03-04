import NeuralNetwork.NeuralNetwork.FastFiniteEvalExplicit
import NeuralNetwork.NeuralNetwork.TwoState
import Mathlib.Data.List.Dedup

/-!
# Computable state enumeration for TwoState networks

For the **compute layer**, we avoid relying on `Fintype` enumeration (which can be classical).
Instead, we build explicit lists of configurations from an explicit site enumeration.

In this file we provide:
- an enumeration of Boolean assignments `U → Bool`, built by recursion over an explicit `List U`,
- an enumeration of states for `TwoState.SymmetricBinary ℚ U` by mapping `Bool` to `{ -1, 1 }`.
-/

namespace NeuralNetwork
namespace FastStateEnum

open TwoState
open NeuralNetwork.FastFiniteEvalExplicit

variable {U : Type} [DecidableEq U]

/-- Enumerate all Boolean assignments on a finite site list, by recursion. -/
def enumBoolFuns (sites : List U) : List (U → Bool) :=
  match sites with
  | [] => [fun _ => false]
  | u :: us =>
      let rest := enumBoolFuns us
      rest.flatMap (fun f => [Function.update f u false, Function.update f u true])

/-!
## Basic facts about `enumBoolFuns`

Key invariant: functions produced by `enumBoolFuns sites` are `false` outside `sites`.

If `sites` is complete (contains every `u : U`), this invariant becomes vacuous and
`enumBoolFuns sites` enumerates *all* `U → Bool`.
-/

def OutsideFalse (sites : List U) (f : U → Bool) : Prop :=
  ∀ u : U, u ∉ sites → f u = false

theorem outsideFalse_of_mem_enumBoolFuns :
    ∀ sites : List U, ∀ f : U → Bool, f ∈ enumBoolFuns (U := U) sites → OutsideFalse (U := U) sites f := by
  intro sites
  induction sites with
  | nil =>
      intro f hf
      simp [enumBoolFuns] at hf
      subst hf
      intro u _; rfl
  | cons u us ih =>
      intro f hf
      -- unfold membership in the flatMap
      simp [enumBoolFuns] at hf
      rcases hf with ⟨g, hg_rest, hf_mem⟩
      -- `f` is one of the two updates of `g`
      have hg_out : OutsideFalse (U := U) us g := ih g hg_rest
      -- prove the invariant for `u :: us`
      intro v hv
      have hv_ne : v ≠ u := by
        intro h; subst h
        exact hv (by simp)
      have hv_us : v ∉ us := by
        intro hmem
        exact hv (List.mem_cons_of_mem _ hmem)
      -- rewrite `f` as an update and use the IH for off-site coordinates
      have : f = Function.update g u false ∨ f = Function.update g u true := by
        simpa using hf_mem
      rcases this with rfl | rfl
      · simp [OutsideFalse, Function.update, hv_ne, hg_out v hv_us]
      · simp [OutsideFalse, Function.update, hv_ne, hg_out v hv_us]

theorem mem_enumBoolFuns_of_outsideFalse :
    ∀ sites : List U, ∀ f : U → Bool, OutsideFalse (U := U) sites f → f ∈ enumBoolFuns (U := U) sites := by
  intro sites
  induction sites with
  | nil =>
      intro f hf
      have hf' : f = (fun _ : U => false) := by
        funext u
        simpa using (hf u (by simp))
      subst hf'
      simp [enumBoolFuns]
  | cons u us ih =>
      intro f hf
      -- build a function in the recursive enumeration by forcing `u ↦ false`
      let g : U → Bool := Function.update f u false
      have hg_out : OutsideFalse (U := U) us g := by
        intro v hv
        by_cases hvu : v = u
        · subst hvu
          simp [g, Function.update]
        · have : v ∉ (u :: us) := by
            intro hmem
            cases (List.mem_cons.1 hmem) with
            | inl h => exact (hvu h)
            | inr h => exact hv h
          -- off-site: `g v = f v = false`
          simpa [g, Function.update, hvu] using (hf v this)
      have hg_mem : g ∈ enumBoolFuns (U := U) us := ih g hg_out
      -- now pick the appropriate branch depending on `f u`
      have hf_update : f = Function.update g u (f u) := by
        funext v
        by_cases hv : v = u
        · subst hv; simp [g, Function.update]
        · simp [g, Function.update, hv]
      -- show membership in the flatMap
      have : Function.update g u (f u) = Function.update g u false ∨
          Function.update g u (f u) = Function.update g u true := by
        cases hfu : f u <;> simp [hfu]
      -- reassemble
      have hflat :
          Function.update g u (f u) ∈
            (enumBoolFuns (U := U) us).flatMap
              (fun h => [Function.update h u false, Function.update h u true]) := by
        -- use `g ∈ rest`
        refine List.mem_flatMap.2 ?_
        refine ⟨g, hg_mem, ?_⟩
        rcases this with h | h <;> simpa [h]
      have : f ∈
          (enumBoolFuns (U := U) us).flatMap
            (fun h => [Function.update h u false, Function.update h u true]) := by
        -- avoid `simp` recursion on function updates
        -- `hf_update : f = Function.update g u (f u)`
        -- rewrite the goal and use `hflat`
        rw [hf_update]
        exact hflat
      simpa [enumBoolFuns] using this
/-!
## Note on duplicate-freeness

`FiniteEnum` is a compute-layer interface, so it intentionally carries only a list.

For some downstream correctness theorems it is useful to know that explicit enumerations are
duplicate-free (`List.Nodup`). A clean `Nodup` theorem for `enumBoolFuns` (under `sites.Nodup`)
can be added later; the compute-layer algorithms in this project do not currently rely on it.
-/
/-!
## SymmetricBinary ℚ states

We construct the `State` record (including the `pact` proof) from a `Bool` assignment.
-/

variable [Fintype U] [Nonempty U]

abbrev NNQ : NeuralNetwork ℚ U ℚ := TwoState.SymmetricBinary ℚ U

def actOfBool (b : Bool) : ℚ := if b then (1 : ℚ) else (-1 : ℚ)

def stateOfBoolFun (f : U → Bool) : (NNQ (U := U)).State :=
{ act := fun u => actOfBool (f u)
  hp := by
    intro u
    -- `pact a := a = 1 ∨ a = -1` for SymmetricBinary
    by_cases h : f u
    · simp [NNQ, TwoState.SymmetricBinary, actOfBool, h]
    · simp [NNQ, TwoState.SymmetricBinary, actOfBool, h] }

theorem actOfBool_injective : Function.Injective actOfBool := by
  intro b₁ b₂ h
  cases b₁ <;> cases b₂
  · rfl
  · -- false vs true
    have hne : (-1 : ℚ) ≠ (1 : ℚ) := by decide
    exact False.elim (hne (by simpa [actOfBool] using h))
  · -- true vs false
    have hne : (1 : ℚ) ≠ (-1 : ℚ) := by decide
    exact False.elim (hne (by simpa [actOfBool] using h))
  · rfl

theorem stateOfBoolFun_injective : Function.Injective (stateOfBoolFun (U := U)) := by
  intro f g hfg
  funext u
  have hact : actOfBool (f u) = actOfBool (g u) :=
    congrArg (fun s : (NNQ (U := U)).State => s.act u) hfg
  exact actOfBool_injective hact

instance instFiniteEnumStateSymmetricBinaryQ [FiniteEnum U] :
    FiniteEnum (NNQ (U := U)).State where
  enum :=
    -- Defensive: if the provided site enumeration has duplicates, remove them.
    -- (This does not fix omissions; it just avoids exponential blowup from repeated sites.)
    let sites := (FiniteEnum.enum (α := U)).dedup
    (enumBoolFuns (U := U) sites).map stateOfBoolFun

end FastStateEnum
end NeuralNetwork
