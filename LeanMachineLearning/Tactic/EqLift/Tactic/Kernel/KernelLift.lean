/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.Tactic.EqLift.Kernel.Lift
public import LeanMachineLearning.Tactic.EqLift.Tactic.Lift
public import LeanMachineLearning.Tactic.EqLift.Tactic.Kernel.Utils

/-!
# Implementation of the `lift_eq` tactic for kernels.

This file contains functions that propagate the lifting of kernel expressions through several
operators and primitives, and constructs the necessary proofs for the `lift_eq` tactic.
-/

public meta section

open Lean Meta Parser.Tactic ProbabilityTheory ProbabilityTheory.Kernel

/-- Lifts a composition of kernels by lifting the inner kernels. -/
def liftComposition (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.comp do
    throwError "Expected a composition of kernels, but got {e}."
  let args := e.getAppArgs
  let η := args[args.size - 2]!
  let κ := args[args.size - 1]!
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel η
  let (Z, _, tLvl, _) ← getTypesFromKernel κ
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let ez ← constructMeasurableEquiv Z tLvl maxLvl
  let comp_lift_proof ← mkAppM ``comp_lift #[ex, ey, ez, η, κ]
  let (η', proofs_η) ← liftExpr η maxLvl proofs
  let (κ', proofs_κ) ← liftExpr κ maxLvl proofs_η
  return (← mkAppM ``Kernel.comp #[η', κ'], comp_lift_proof :: proofs_κ)

initialize registerLiftExpr liftComposition

/-- Lifts a parallel composition of kernels by lifting the inner kernels. -/
def liftParallelComp (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.parallelComp do
    throwError "Expected a parallel composition of kernels, but got {e}."
  let args := e.getAppArgs
  let κ := args[args.size - 2]!
  let η := args[args.size - 1]!
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
  let (Z, T, zLvl, tLvl) ← getTypesFromKernel η
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let ez ← constructMeasurableEquiv Z zLvl maxLvl
  let et ← constructMeasurableEquiv T tLvl maxLvl
  let parallelComp_lift_proof ← mkAppM ``parallelComp_lift #[ex, ey, ez, et, κ, η]
  let (κ', proofs_κ) ← liftExpr κ maxLvl proofs
  let (η', proofs_η) ← liftExpr η maxLvl proofs_κ
  return (← mkAppM ``Kernel.parallelComp #[κ', η'], parallelComp_lift_proof :: proofs_η)

initialize registerLiftExpr liftParallelComp

/-- Lifts a product of kernels by lifting the inner kernels. -/
def liftProd (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.prod do
    throwError "Expected a product of kernels, but got {e}."
  let args := e.getAppArgs
  let κ := args[args.size - 2]!
  let η := args[args.size - 1]!
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
  let (_, Z, _, zLvl) ← getTypesFromKernel η
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let ez ← constructMeasurableEquiv Z zLvl maxLvl
  let prod_lift_proof ← mkAppM ``prod_lift #[ex, ey, ez, κ, η]
  let (κ', proofs_κ) ← liftExpr κ maxLvl proofs
  let (η', proofs_η) ← liftExpr η maxLvl proofs_κ
  return (← mkAppM ``Kernel.prod #[κ', η'], prod_lift_proof :: proofs_η)

initialize registerLiftExpr liftProd

/-- Lifts a composition-product of kernels by lifting the inner kernels. -/
def liftCompProd (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.compProd do
    throwError "Expected a composition of product of kernels, but got {e}."
  let args := e.getAppArgs
  let κ := args[args.size - 2]!
  let η := args[args.size - 1]!
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
  let (_, Z, _, zLvl) ← getTypesFromKernel η
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let ez ← constructMeasurableEquiv Z zLvl maxLvl
  let compProd_lift_proof ← mkAppM ``compProd_lift #[ex, ey, ez, κ, η]
  let (κ', proofs_κ) ← liftExpr κ maxLvl proofs
  let (η', proofs_η) ← liftExpr η maxLvl proofs_κ
  return (← mkAppM ``Kernel.compProd #[κ', η'], compProd_lift_proof :: proofs_η)

initialize registerLiftExpr liftCompProd

/-- Lifts a composition of kernels by lifting the carrier type. -/
def liftId (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.id do
    throwError "Expected the identity kernel, but got {e}."
  let (X, _, xLvl, _) ← getTypesFromKernel e
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let (X', _) ← getTypesFromMeasurableEquiv ex
  let id_lift_proof ← mkAppM ``id_lift #[ex]
  let mX' ← synthInstance (mkApp (mkConst ``MeasurableSpace [maxLvl]) X')
  return (← mkAppOptM ``Kernel.id #[X', mX'], id_lift_proof :: proofs)

initialize registerLiftExpr liftId

/-- Lifts a discard kernel by lifting the carrier type. -/
def liftDiscard (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.discard do
    throwError "Expected the discard kernel, but got {e}."
  let (X, _, xLvl, punitLvl) ← getTypesFromKernel e
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let (X', _) ← getTypesFromMeasurableEquiv ex
  let discard_const := mkConst ``discard_lift [xLvl, maxLvl, punitLvl]
  let discard_lift_proof ← mkAppM' discard_const #[ex]
  let discard_const := mkConst ``Kernel.discard [maxLvl, maxLvl]
  return (← mkAppOptM' discard_const #[X', none], discard_lift_proof :: proofs)

initialize registerLiftExpr liftDiscard

/-- Lifts a copy kernel by lifting the carrier type. -/
def liftCopy (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.copy do
    throwError "Expected the copy kernel, but got {e}."
  let (X, _, xLvl, _) ← getTypesFromKernel e
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let (X', _) ← getTypesFromMeasurableEquiv ex
  let copy_lift_proof ← mkAppM ``copy_lift #[ex]
  return (← mkAppOptM ``Kernel.copy #[X', none], copy_lift_proof :: proofs)

initialize registerLiftExpr liftCopy

/-- Lifts a swap kernel by lifting the carrier types. -/
def liftSwap (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.swap do
    throwError "Expected the swap kernel, but got {e}."
  let args := e.getAppArgs
  let X := args[0]!
  let Y := args[1]!
  let xLvl := (← getDecLevel X)
  let yLvl := (← getDecLevel Y)
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let (X', _) ← getTypesFromMeasurableEquiv ex
  let (Y', _) ← getTypesFromMeasurableEquiv ey
  let swap_lift_proof ← mkAppM ``swap_lift #[ex, ey]
  return (← mkAppOptM ``Kernel.swap #[X', Y', none, none], swap_lift_proof :: proofs)

initialize registerLiftExpr liftSwap

/-- Lifts a kernel using `Kernel.lift`. -/
def liftKernel (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel e
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let expr ← mkAppOptM ``Kernel.lift
    #[none, none, none, none, none, none, none, none, ex, ey, e]
  return (expr, proofs)

initialize registerLiftExpr liftKernel

/-- Constructs the finisher proof that concludes the lifting after rewriting the equalities. -/
def finisherKernelLift (lhs rhs _ _ : Expr) (maxLvl : Level) : MetaM Expr := do
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel lhs
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  mkAppM ``lift_congr #[ex, ey, lhs, rhs]

initialize registerLiftFinisher finisherKernelLift

end
