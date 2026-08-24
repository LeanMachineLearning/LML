/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public meta import Lean.Elab.Tactic.Location

/-!
# Tactic location support

This module provides utilities for applying tactics to multiple goals and hypotheses
specified by location patterns, following the standard Lean syntax (like in `rw` or `simp`).

## Main declarations

* `applyLocTactic`: applies a tactic to goals and hypotheses at specified locations.
-/

public meta section

open Lean Elab Tactic Meta

/-- Replace an equality in a goal or hypothesis with a transformed expression, using a provided
transformation function. -/
def replaceEquality (goal : MVarId) (fvarId : Option FVarId)
    (transform : Expr → MetaM (Expr × Expr)) : TacticM MVarId := do
  goal.withContext do
    let expr ← match fvarId with
        | some fid => do
          let decl ← fid.getDecl
          pure decl.type
        | none => goal.getType
    let (lift_expr, eq_proof) ← transform expr
    match fvarId with
    | some fid => do
      let mvarId ← getMainGoal
      let h_proof ← mkEqMP eq_proof (mkFVar fid)
      let userName := (← fid.getDecl).userName
      let mvarId ← mvarId.assert userName lift_expr h_proof
      let mvarId ← mvarId.tryClear fid
      let (_, mvarId) ← mvarId.intro1P
      pure mvarId
    | none => do
      let mvarId ← getMainGoal
      mvarId.replaceTargetEq lift_expr eq_proof

/-- Apply a given transformation to all goals and/or hypotheses specified by a `Location`. -/
def applyLocTactic (loc : Location) (transform : Expr → MetaM (Expr × Expr)) :
    TacticM Unit := do
  match loc with
  | Location.targets hyps target =>
    for hyp in hyps do
      let hFVarId ← getFVarId hyp
      let newGoal ← replaceEquality (← getMainGoal) (some hFVarId) transform
      replaceMainGoal [newGoal]
    if target then
      let newGoal ← replaceEquality (← getMainGoal) none transform
      replaceMainGoal [newGoal]
  | Location.wildcard =>
    let goal ← getMainGoal
    goal.withContext do
      let lctx ← getLCtx
      let mut currentGoal := goal
      for decl in lctx do
        if decl.isImplementationDetail then continue
        try
          currentGoal ← replaceEquality currentGoal (some decl.fvarId) transform
          replaceMainGoal [currentGoal]
        catch _ => continue
      try
        currentGoal ← replaceEquality currentGoal none transform
        replaceMainGoal [currentGoal]
      catch _ => pure ()
