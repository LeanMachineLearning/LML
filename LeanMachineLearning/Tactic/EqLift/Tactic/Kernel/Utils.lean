/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.Tactic.EqLift.ForMathlib.MeasurableEquiv
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# Kernel lifting utilities

This file provides helper functions for lifting and unlifting kernel expressions, including type
extraction and equivalence construction.

## Main declarations

* `getTypesFromKernel`: extracts carrier types and universe levels from kernel expressions.
* `constructMeasurableEquiv`: recursively builds measurable equivalences.
* `getOriginalType`: retrieves the original type from a lifted type.
-/

public meta section

open Lean Meta ProbabilityTheory Elab Term

/-- Extract `(X, Y, u, v)` from an expression of type `Kernel X Y`. -/
def getTypesFromKernel (κ : Expr) : MetaM (Expr × Expr × Level × Level) := do
  let κType ← inferType κ
  match κType.getAppFn with
  | Expr.const ``Kernel univs =>
    let args := κType.getAppArgs
    if args.size < 2 then
      throwError "Kernel type with insufficient arguments: {κType}."
    let X := args[0]!
    let Y := args[1]!
    let xLevel := univs[0]!
    let yLevel := univs[1]!
    return (X, Y, xLevel, yLevel)
  | _ => throwError "Expected a kernel type, got: {κType}."

/-- Build a measurable equivalence for `e` into universe `maxLvl` (recursive on products). -/
partial def constructMeasurableEquiv (e : Expr) (eLevel maxLvl : Level) : MetaM Expr := do
  let ewhnf ← whnf e
  match ewhnf.getAppFn with
  | Expr.const ``PUnit _ | Expr.const ``Unit _ =>
    mkAppOptM' (Expr.const `MeasurableEquiv.punit [maxLvl, eLevel]) #[]
  | Expr.const ``Prod univs =>
    let args := ewhnf.getAppArgs
    let X := args[0]!
    let Y := args[1]!
    let xLevel := univs[0]!
    let yLevel := univs[1]!
    let ex ← constructMeasurableEquiv X xLevel maxLvl
    let ey ← constructMeasurableEquiv Y yLevel maxLvl
    let res ← mkAppOptM' (Expr.const ``MeasurableEquiv.prodCongr [maxLvl, xLevel, maxLvl, yLevel])
      #[none, none, none, none, none, none, none, none, ex, ey]
    return res
  | _ => mkAppOptM' (Expr.const ``MeasurableEquiv.ulift [eLevel, maxLvl]) #[e, none]

/-- Get departure and target types from a `MeasurableEquiv` expression. -/
def getTypesFromMeasurableEquiv (e : Expr) : MetaM (Expr × Expr) := do
  let equivT ← (whnf (← inferType e))
  match equivT.getAppFn with
  | Expr.const ``MeasurableEquiv _ =>
    let args := equivT.getAppArgs
    return (args[0]!, args[1]!)
  | _ => throwError "Expected a MeasurableEquiv, got: {e}."

/-- Get the original type from a lifted type. -/
partial def getOriginalType (t : Expr) : MetaM (Expr × Level) := do
  let twhnf ← whnf t
  match twhnf.getAppFn with
  | Expr.const ``PUnit _ | Expr.const ``Unit _ =>
    return (mkConst ``Unit [], 0)
  | Expr.const ``ULift univs =>
    return (twhnf.getAppArgs[0]!, univs[1]!)
  | Expr.const ``Prod _ =>
    let args := twhnf.getAppArgs
    let (X, xLvl) ← getOriginalType args[0]!
    let (Y, yLvl) ← getOriginalType args[1]!
    return (← mkAppM ``Prod #[X, Y], .max xLvl yLvl)
  | _ =>
    return (t, ← getDecLevel (← inferType t))

end
