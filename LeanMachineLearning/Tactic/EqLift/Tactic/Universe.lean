/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Lean.Meta.DecLevel
public import Lean.Meta.Transform
public import Lean.Util.Recognizers
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Universe level utilities

This file provides utilities for working with universe levels in metaprograms.
It includes conversion functions between levels and syntax, and universe level collection.

## Main declarations

* `collectExprUniverses`: recursively collects universe levels from expressions.
* `getUniverseFromEq`: extracts the universe level from the left-hand side of an equality
expression.
-/

public meta section

open Lean Meta ProbabilityTheory

/-- Recursively traverses an expression and collects all universe levels. -/
def collectExprUniverses.aux (e : Expr) : List Level :=
  match e with
  | Expr.const _ univs => univs
  | Expr.sort u => [u]
  | Expr.app f a => aux f ++ aux a
  | Expr.lam _ t b _ => aux t ++ aux b
  | Expr.forallE _ t b _ => aux t ++ aux b
  | Expr.letE _ t v b _ => aux t ++ aux v ++ aux b
  | Expr.mdata _ b => aux b
  | Expr.proj _ _ b => aux b
  | Expr.bvar _ | Expr.fvar _ | Expr.mvar _ | Expr.lit _ => []

/-- Recursively traverse an expression and collect universe levels found.
Returns a list of all unique universe levels encountered. -/
def collectExprUniverses (e : Expr) : MetaM (List Level) := do
  let e ← instantiateMVars e
  let e ← zetaReduce e
  return (collectExprUniverses.aux e).eraseDups

/-- Compute the maximum universe level from a list of levels. -/
def computeMaxLevel (levels : List Level) : MetaM Level :=
  match levels with
    | [] => throwError "Expected at least one universe level, got an empty list."
    | head :: tail => pure (tail.foldl Level.max head)

/-- Extract the universe level from the left side of an equality expression. -/
def getLevelFromEq (eq : Expr) : MetaM Level := do
  let eq ← whnf (← zetaReduce (← instantiateMVars eq))
  let eq := eq.consumeMData
  let some (_, lhs, _) := eq.eq? | throwError "Expected an equality, got: {eq}."
  getDecLevel (← inferType lhs)
