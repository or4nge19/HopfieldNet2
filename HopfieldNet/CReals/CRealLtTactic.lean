import HopfieldNet.CReals.CRealCompare
import Lean.Elab.Tactic

namespace Computable
namespace CReal
namespace Tactic

open Lean Meta Elab Tactic

/-!
## `creal_lt`: proof-by-computation for strict inequalities in `CReal`

`creal_lt` is a semi-decision tactic for goals of the form `a < b` or `a > b` where
`a b : Computable.CReal` are presented as quotient constructors `⟦x⟧`.

It searches for a rational separation index `i` on the chosen representatives and then
discharges the resulting `ℚ` inequality via the kernel-safe `decide` tactic.

Fuel:
- `creal_lt` (default fuel = 200)
- `creal_lt 500`
- `creal_lt (fuel := 500)`
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

private def trySolveSepLt (a b : Expr) (i : Nat) : TacticM Bool := do
  let saved ← saveState
  try
    let g ← getMainGoal
    let pr := mkAppN (mkConst ``Computable.CReal.Pre.lt_mk_of_sep) #[a, b, mkNatLit i]
    let gs ← g.apply pr
    setGoals gs
    evalTactic (← `(tactic| decide))
    pure true
  catch _ =>
    restoreState saved
    pure false

private def trySolveSepGt (a b : Expr) (i : Nat) : TacticM Bool := do
  let saved ← saveState
  try
    let g ← getMainGoal
    let pr := mkAppN (mkConst ``Computable.CReal.Pre.gt_mk_of_sep) #[a, b, mkNatLit i]
    let gs ← g.apply pr
    setGoals gs
    evalTactic (← `(tactic| decide))
    pure true
  catch _ =>
    restoreState saved
    pure false

private def solveLtCore (a b : Expr) (fuel : Nat) : TacticM Unit := do
  for i in List.range (fuel + 1) do
    if (← trySolveSepLt a b i) then return
  throwError "creal_lt: unable to decide `<` within fuel={fuel}. Try `creal_lt (fuel := N)` with a larger N."

private def solveGtCore (a b : Expr) (fuel : Nat) : TacticM Unit := do
  for i in List.range (fuel + 1) do
    if (← trySolveSepGt a b i) then return
  throwError "creal_lt: unable to decide `>` within fuel={fuel}. Try `creal_lt (fuel := N)` with a larger N."

private def isQuotMkLast? (e : Expr) : Option Expr :=
  let fn := e.getAppFn
  if fn.isConstOf ``Quotient.mk then
    let args := e.getAppArgs
    if h : 0 < args.size then
      some (args[args.size - 1])
    else none
  else none

declare_syntax_cat creal_lt_cfg
syntax num : creal_lt_cfg
syntax "(" &"fuel" " := " num ")" : creal_lt_cfg

syntax (name := creal_lt) "creal_lt" (ppSpace creal_lt_cfg)? : tactic

private def parseFuel (stx : Syntax) : Nat :=
  match stx with
  | `(tactic| creal_lt) => 200
  | `(tactic| creal_lt $n:num) => n.getNat
  | `(tactic| creal_lt (fuel := $n:num)) => n.getNat
  | _ => 200

@[tactic creal_lt] def evalCRealLt : Tactic := fun _stx => do
  let fuel : Nat := parseFuel _stx
  let g ← getMainGoal
  let tgt ← g.getType
  if let some (lhs, rhs) := appLast2? tgt ``LT.lt then
    let lhs ← withTransparency TransparencyMode.reducible (whnf lhs)
    let rhs ← withTransparency TransparencyMode.reducible (whnf rhs)
    match (isQuotMkLast? lhs, isQuotMkLast? rhs) with
    | (some a, some b) =>
        solveLtCore a b fuel
    | _ =>
        throwError "creal_lt: could not expose `CReal` representatives as `⟦a⟧` and `⟦b⟧`"
  else if let some (lhs, rhs) := appLast2? tgt ``GT.gt then
    let lhs ← withTransparency TransparencyMode.reducible (whnf lhs)
    let rhs ← withTransparency TransparencyMode.reducible (whnf rhs)
    match (isQuotMkLast? lhs, isQuotMkLast? rhs) with
    | (some a, some b) =>
        solveGtCore a b fuel
    | _ =>
        throwError "creal_lt: could not expose `CReal` representatives as `⟦a⟧` and `⟦b⟧`"
  else
    throwError "creal_lt: unsupported goal shape (expected `<` or `>` on `CReal`)"

end Tactic
end CReal
end Computable

