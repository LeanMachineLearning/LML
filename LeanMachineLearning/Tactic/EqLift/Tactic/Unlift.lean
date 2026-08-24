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
# Unlift tactic

This file defines the `unlift_eq` tactic, which performs the inverse operation of `lift_eq`. It
takes an equality that has been lifted to a common universe level and attempts to unlift it back to
its original form. The tactic is designed to work with various types of expressions, and can be
extended by registering new unlift functions.
-/

public meta section

open Lean Elab Tactic Meta Parser.Tactic

private initialize unliftImplRef : IO.Ref (Array liftMetadata) ← IO.mkRef #[]

/-- Registers a new unlifting function for expressions. The function should take an expression, a
universe level (most likely the common universe level where the equality is being lifted), and a
list of proofs, and return a new expression and an updated list of proofs. -/
def registerUnliftExpr (f : liftMetadata) : IO Unit := do unliftImplRef.modify (·.push f)

private initialize unliftFinisherRef : IO.Ref (Array finisherMetadata) ← IO.mkRef #[]

/-- Registers a new finisher function for constructing the final proof of equality after unlifting
inner expressions. The function should take the original left-hand side and right-hand side, the
transformed left-hand side and right-hand side, the common universe level, and return a proof of
equality. -/
def registerUnliftFinisher (f : finisherMetadata) : IO Unit := do
  unliftFinisherRef.modify (·.push f)

/-- Unlifts an expression that has been lifted to a common universe level using the registered
unlifting functions. -/
def unliftExpr := fun a b c ↦ transformExpr a b c unliftImplRef

/-- Unlifts an equality expression that has been lifted to a common universe level using the
registered unlifting functions and finisher functions. -/
def unliftEquality := transformEquality getLevelFromEq unliftImplRef unliftFinisherRef

/-- Performs the inverse operation of `lift_eq`, transforming an equality that has been lifted to a
common universe level back to its original form.

The tactic supports location specifiers like `rw` or `simp`:
* `unlift_eq` — applies to the goal
* `unlift_eq at h` — applies to hypothesis `h`
* `unlift_eq at h₁ h₂` — applies to multiple hypotheses
* `unlift_eq at h ⊢` — applies to hypothesis `h` and the goal
* `unlift_eq at *` — applies to all hypotheses and the goal
-/
syntax (name := EqUnlift) "unlift_eq" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| unlift_eq $[$loc]?) =>
    expandOptLocation (mkOptionalNode loc) |> applyLocTactic <| unliftEquality

end
