/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# Kernel transformation utilities
-/

public meta section

open Lean Meta ProbabilityTheory

/-- Unfold kernel operations in an expression. -/
def unfoldKernelOp (e : Expr) : MetaM Expr := do
  let names := (.empty |> NameSet.insert <| ``Kernel.prod) |> NameSet.insert <| ``Kernel.compProd
  transform e (post := fun e => do
    let e' ← deltaExpand e names.contains
    let e' ← Core.betaReduce e'
    return .done e')

/-- Returns the application `constName` `xs` with `n_impls` last arguments as implicit. -/
def Lean.Meta.mkAppMInst (constName : Name) (xs : Array Expr) (n_impls : Nat) : MetaM Expr := do
  let e ← mkAppM constName xs
  let nones : Array (Option Expr) := Array.replicate n_impls none
  mkAppOptM' e nones

/-- Similar to `mkAppMInst`, but takes an `Expr` instead of a constant name. -/
def Lean.Meta.mkAppMInst' (f : Expr) (xs : Array Expr) (n_insts : Nat) : MetaM Expr := do
  let e ← mkAppM' f xs
  let nones : Array (Option Expr) := Array.replicate n_insts none
  mkAppOptM' e nones
