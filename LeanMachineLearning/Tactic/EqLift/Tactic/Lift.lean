/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

import Lean.Elab.Tactic.Location
public import LeanMachineLearning.Tactic.EqLift.Tactic.Utils
public import LeanMachineLearning.Tactic.EqLift.Tactic.Universe
public import LeanMachineLearning.Tactic.EqLift.Tactic.Location

/-!
# Lift tactic

This file defines the `lift_eq` tactic, which lifts an equality to a common universe level. It
propagates the lifting through the structure of the equality. The tactic is implemented in a way
that it can be easily extended to support new types of expressions by registering new lifting
functions.
-/

public meta section

open Lean Elab Tactic Meta Parser.Tactic

private initialize liftImplRef : IO.Ref (Array liftMetadata) ← IO.mkRef #[]

/-- Registers a new lifting function for expressions. The function should take an expression, a
universe level (most likely the common universe level where the equality is being lifted), and a
list of proofs, and return a new expression and an updated list of proofs. -/
def registerLiftExpr (f : liftMetadata) : IO Unit := do liftImplRef.modify (·.push f)

private initialize liftFinisherRef : IO.Ref (Array (finisherMetadata)) ← IO.mkRef #[]

/-- Registers a new finisher function for constructing the final proof of equality after lifting
inner expressions. The function should take the original left-hand side and right-hand side, the
transformed left-hand side and right-hand side, the common universe level, and return a proof of
equality. -/
def registerLiftFinisher (f : finisherMetadata) : IO Unit := do
  liftFinisherRef.modify (·.push f)

/-- Lifts an expression to a common universe level using the registered lifting functions. -/
def liftExpr := fun a b c ↦ transformExpr a b c liftImplRef

/-- Gets the maximum universe level from an equality expression by collecting all universe levels
from the left-hand side and right-hand side of the equality. -/
def getMaxLvl (eq : Expr) : MetaM Level := do
  let univs ← collectExprUniverses eq
  computeMaxLevel univs

/-- Lifts an equality expression to a common universe level using the registered lifting functions
and finisher functions. -/
def liftEquality := transformEquality getMaxLvl liftImplRef liftFinisherRef

/-- Same as `liftEquality`, but allows specifying a universe level that will be taken into account
when computing the maximum universe level. -/
def liftEqualityWithLevel (Lvl : Level) (eq : Expr) : MetaM (Expr × Expr) := do
  let getMaxLvl := fun e ↦ do
    let univs ← collectExprUniverses e
    computeMaxLevel <| Lvl :: univs
  transformEquality getMaxLvl liftImplRef liftFinisherRef eq

/-- Transforms an equality expression by lifting both sides to a common universe level.

The tactic supports location specifiers like `rw` or `simp`:
* `lift_eq` — applies to the goal
* `lift_eq at h` — applies to hypothesis `h`
* `lift_eq at h₁ h₂` — applies to multiple hypotheses
* `lift_eq at h ⊢` — applies to hypothesis `h` and the goal
* `lift_eq at *` — applies to all hypotheses and the goal
-/
syntax (name := EqLift) "lift_eq" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| lift_eq $[$loc]?) =>
    expandOptLocation (mkOptionalNode loc) |> applyLocTactic <| liftEquality

end
