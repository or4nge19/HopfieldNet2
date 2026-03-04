import HopfieldNet.CReals.CRealCompare
import Lean.Elab.Tactic

namespace Computable
namespace CReal
namespace Tactic

open Lean Meta Elab Tactic

/-!
## `creal_compare`: proof-by-computation for strict inequalities in `ℝ`

`creal_compare` is a **semi-decision** tactic for goals of the form

- `Computable.CReal.Pre.toReal x < Computable.CReal.Pre.toReal y`
- `Computable.CReal.Pre.toReal x > Computable.CReal.Pre.toReal y`
- `Computable.CReal.toReal a < Computable.CReal.toReal b`
- `Computable.CReal.toReal a > Computable.CReal.toReal b`

It works by searching for an index `i` such that the rational approximants at level `i+1`
are *provably separated* by a margin `2^{-(i+1)}`; this reduces the goal to a decidable
inequality over `ℚ`, discharged by the kernel-safe `decide` tactic.

Intended use:
- **Best** on closed terms where the relevant `approx` functions compute.
- It may fail (returning an error) when the terms are not computationally reducible, or when
  the reals are too close to separate within the given search budget.

Fuel:
- `creal_compare` (default fuel = 200)
- `creal_compare 500`
- `creal_compare (fuel := 500)`
-/

private def appLast2? (e : Expr) (n : Name) : Option (Expr × Expr) :=
  if e.getAppFn.isConstOf n then
    let args := e.getAppArgs
    if h : 2 ≤ args.size then
      some (args[args.size - 2], args[args.size - 1])
    else
      none
  else
    none

private def isPreToReal (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Computable.CReal.Pre.toReal 1 then
    some (e.getArg! 0)
  else none

private def isCRealToReal (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Computable.CReal.toReal 1 then
    some (e.getArg! 0)
  else none

private def trySolveWithIndex (lem : Name) (x y : Expr) (i : Nat) : TacticM Bool := do
  let saved ← saveState
  try
    let g ← getMainGoal
    let pr :=
      mkAppN (mkConst lem) #[x, y, mkNatLit i]
    let gs ← g.apply pr
    setGoals gs
    evalTactic (← `(tactic| decide))
    pure true
  catch _ =>
    restoreState saved
    pure false

private def solveLt (x y : Expr) (fuel : Nat) : TacticM Unit := do
  -- Try increasing indices until `decide` can certify the rational separation subgoal.
  for i in List.range (fuel + 1) do
    if (← trySolveWithIndex ``Computable.CReal.Pre.toReal_lt_of_sep x y i) then
      return
  throwError "creal_compare: unable to decide `<` within fuel={fuel}. Try `creal_compare (fuel := N)` with a larger N."

private def solveGt (x y : Expr) (fuel : Nat) : TacticM Unit := do
  for i in List.range (fuel + 1) do
    if (← trySolveWithIndex ``Computable.CReal.Pre.toReal_gt_of_sep x y i) then
      return
  throwError "creal_compare: unable to decide `>` within fuel={fuel}. Try `creal_compare (fuel := N)` with a larger N."

declare_syntax_cat creal_compare_cfg
syntax num : creal_compare_cfg
syntax "(" &"fuel" " := " num ")" : creal_compare_cfg

syntax (name := creal_compare) "creal_compare" (ppSpace creal_compare_cfg)? : tactic

private def parseFuel (stx : Syntax) : Nat :=
  match stx with
  | `(tactic| creal_compare) => 200
  | `(tactic| creal_compare $n:num) => n.getNat
  | `(tactic| creal_compare (fuel := $n:num)) => n.getNat
  | _ => 200

@[tactic creal_compare] def evalCRealCompare : Tactic := fun _stx => do
  let fuel : Nat := parseFuel _stx
  let goal ← getMainGoal
  let tgt ← goal.getType
  -- match on `<` / `>`
  if let some (lhs, rhs) := appLast2? tgt ``LT.lt then
    match (isPreToReal lhs, isPreToReal rhs, isCRealToReal lhs, isCRealToReal rhs) with
    | (some x, some y, _, _) =>
        solveLt x y fuel
    | (_, _, some _x, some _y) =>
        -- Reduce to the pre-level goal when possible.
        evalTactic (← `(tactic| simp [Computable.CReal.toReal_mk] ))
        if (← getGoals).isEmpty then pure () else
          let goal ← getMainGoal
          let tgt ← goal.getType
          if let some (lhs', rhs') := appLast2? tgt ``LT.lt then
            match (isPreToReal lhs', isPreToReal rhs') with
            | (some x, some y) => solveLt x y fuel
            | _ =>
                throwError "creal_compare: after simplification, goal is `<` but not on `CReal.Pre.toReal`"
          else
            throwError "creal_compare: after simplification, unsupported goal shape"
    | (_, _, _, _) =>
        throwError "creal_compare: goal is `<` but not on `CReal.Pre.toReal` or `CReal.toReal`"
  else if let some (lhs, rhs) := appLast2? tgt ``GT.gt then
    match (isPreToReal lhs, isPreToReal rhs, isCRealToReal lhs, isCRealToReal rhs) with
    | (some x, some y, _, _) =>
        solveGt x y fuel
    | (_, _, some _x, some _y) =>
        evalTactic (← `(tactic| simp [Computable.CReal.toReal_mk] ))
        if (← getGoals).isEmpty then pure () else
          let goal ← getMainGoal
          let tgt ← goal.getType
          if let some (lhs', rhs') := appLast2? tgt ``GT.gt then
            match (isPreToReal lhs', isPreToReal rhs') with
            | (some x, some y) => solveGt x y fuel
            | _ =>
                throwError "creal_compare: after simplification, goal is `>` but not on `CReal.Pre.toReal`"
          else
            throwError "creal_compare: after simplification, unsupported goal shape"
    | (_, _, _, _) =>
        throwError "creal_compare: goal is `>` but not on `CReal.Pre.toReal` or `CReal.toReal`"
  else
    throwError "creal_compare: unsupported goal shape (expected `<` or `>`)"

end Tactic
end CReal
end Computable

