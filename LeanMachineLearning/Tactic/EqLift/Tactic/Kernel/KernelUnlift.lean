/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.Tactic.EqLift.Kernel.Lift
public import LeanMachineLearning.Tactic.EqLift.Tactic.Unlift
public import LeanMachineLearning.Tactic.EqLift.Tactic.Kernel.Utils

/-!
# Implementation of the `unlift_eq` tactic for kernels.

This file contains functions that propagate the unlifting of lifted kernel expressions through
several operators and primitives, and constructs the necessary proofs for the `unlift_eq` tactic.
-/

public meta section

open Lean Meta Parser.Tactic ProbabilityTheory ProbabilityTheory.Kernel

/-- Unlifts a composition of kernels by unlifting the inner kernels. -/
def unliftComposition (e : Expr) (eLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.comp do
    throwError "Expected a composition of kernels, but got {e}."
  let args := e.getAppArgs
  let η' := args[args.size - 2]!
  let κ' := args[args.size - 1]!
  let (η, proofs_η) ← unliftExpr η' eLvl proofs
  let (κ, proofs_κ) ← unliftExpr κ' eLvl proofs_η
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel η
  let (Z, _, tLvl, _) ← getTypesFromKernel κ
  let ex ← constructMeasurableEquiv X xLvl eLvl
  let ey ← constructMeasurableEquiv Y yLvl eLvl
  let ez ← constructMeasurableEquiv Z tLvl eLvl
  let comp_unlift_proof ← mkAppM ``comp_lift #[ex, ey, ez, η, κ]
  return (← mkAppM ``Kernel.comp #[η, κ], comp_unlift_proof :: proofs_κ)

initialize registerUnliftExpr unliftComposition

/-- Unlifts a parallel composition of kernels by unlifting the inner kernels. -/
def unliftParallelComp (e : Expr) (eLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.parallelComp do
    throwError "Expected a parallel composition of kernels, but got {e}."
  let args := e.getAppArgs
  let κ' := args[args.size - 2]!
  let η' := args[args.size - 1]!
  let (κ, proofs_κ) ← unliftExpr κ' eLvl proofs
  let (η, proofs_η) ← unliftExpr η' eLvl proofs_κ
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
  let (Z, T, zLvl, tLvl) ← getTypesFromKernel η
  let ex ← constructMeasurableEquiv X xLvl eLvl
  let ey ← constructMeasurableEquiv Y yLvl eLvl
  let ez ← constructMeasurableEquiv Z zLvl eLvl
  let et ← constructMeasurableEquiv T tLvl eLvl
  let parallelComp_unlift_proof ← mkAppM ``parallelComp_lift #[ex, ey, ez, et, κ, η]
  return (← mkAppM ``Kernel.parallelComp #[κ, η], parallelComp_unlift_proof :: proofs_η)

initialize registerUnliftExpr unliftParallelComp

/-- Unlifts a product of kernels by unlifting the inner kernels. -/
def unliftProd (e : Expr) (eLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.prod do
    throwError "Expected a product of kernels, but got {e}."
  let args := e.getAppArgs
  let κ' := args[args.size - 2]!
  let η' := args[args.size - 1]!
  let (κ, proofs_κ) ← unliftExpr κ' eLvl proofs
  let (η, proofs_η) ← unliftExpr η' eLvl proofs_κ
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
  let (_, Z, _, zLvl) ← getTypesFromKernel η
  let ex ← constructMeasurableEquiv X xLvl eLvl
  let ey ← constructMeasurableEquiv Y yLvl eLvl
  let ez ← constructMeasurableEquiv Z zLvl eLvl
  let prod_unlift_proof ← mkAppM ``prod_lift #[ex, ey, ez, κ, η]
  return (← mkAppM ``Kernel.prod #[κ, η], prod_unlift_proof :: proofs_η)

initialize registerUnliftExpr unliftProd

/-- Unlifts a composition-product of kernels by unlifting the inner kernels. -/
def unliftCompProd (e : Expr) (eLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.compProd do
    throwError "Expected a composition of product of kernels, but got {e}."
  let args := e.getAppArgs
  let κ' := args[args.size - 2]!
  let η' := args[args.size - 1]!
  let (κ, proofs_κ) ← unliftExpr κ' eLvl proofs
  let (η, proofs_η) ← unliftExpr η' eLvl proofs_κ
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
  let (_, Z, _, zLvl) ← getTypesFromKernel η
  let ex ← constructMeasurableEquiv X xLvl eLvl
  let ey ← constructMeasurableEquiv Y yLvl eLvl
  let ez ← constructMeasurableEquiv Z zLvl eLvl
  let compProd_unlift_proof ← mkAppM ``compProd_lift #[ex, ey, ez, κ, η]
  return (← mkAppM ``compProd #[κ, η], compProd_unlift_proof :: proofs_η)

initialize registerUnliftExpr unliftCompProd

/-- Unlifts the identity kernel by unlifting the carrier type. -/
def unliftId (e : Expr) (eLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.id do
    throwError "Expected the identity kernel, but got {e}."
  let (X', _, _, _) ← getTypesFromKernel e
  let (X, xLvl) ← getOriginalType X'
  if X == X' then
    return (e, proofs)
  else
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let id_unlift_proof ← mkAppM ``id_lift #[ex]
    let mX ← synthInstance (mkApp (mkConst ``MeasurableSpace [xLvl]) X)
    return (← mkAppOptM ``Kernel.id #[X, mX], id_unlift_proof :: proofs)

initialize registerUnliftExpr unliftId

/-- Unlifts the discard kernel by unlifting the carrier type. -/
def unliftDiscard (e : Expr) (eLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.discard do
    throwError "Expected the discard kernel, but got {e}."
  let (X', _, _, _) ← getTypesFromKernel e
  let (X, xLvl) ← getOriginalType X'
  if X == X' then
    return (e, proofs)
  else
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let discard_const := mkConst ``discard_lift [xLvl, eLvl, Level.zero]
    let discard_unlift_proof ← mkAppM' discard_const #[ex]
    let discard_const := mkConst ``Kernel.discard [xLvl, 0]
    return (← mkAppOptM' discard_const #[X, none], discard_unlift_proof :: proofs)

initialize registerUnliftExpr unliftDiscard

/-- Unlifts the copy kernel by unlifting the carrier type. -/
def unliftCopy (e : Expr) (eLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.copy do
    throwError "Expected the copy kernel, but got {e}."
  let (X', _, _, _) ← getTypesFromKernel e
  let (X, xLvl) ← getOriginalType X'
  if X == X' then
    return (e, proofs)
  else
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let copy_unlift_proof ← mkAppM ``copy_lift #[ex]
    return (← mkAppOptM ``Kernel.copy #[X, none], copy_unlift_proof :: proofs)

initialize registerUnliftExpr unliftCopy

/-- Unlifts the swap kernel by unlifting the carrier types. -/
def unliftSwap (e : Expr) (eLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.swap do
    throwError "Expected the swap kernel, but got {e}."
  let args := e.getAppArgs
  let X' := args[0]!
  let Y' := args[1]!
  let (X, xLvl) ← getOriginalType X'
  let (Y, yLvl) ← getOriginalType Y'
  if X == X' && Y == Y' then
    return (e, proofs)
  else
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let ey ← constructMeasurableEquiv Y yLvl eLvl
    let swap_unlift_proof ← mkAppM ``swap_lift #[ex, ey]
    return (← mkAppOptM ``Kernel.swap #[X, Y, none, none], swap_unlift_proof :: proofs)

initialize registerUnliftExpr unliftSwap

/-- Unlifts a lifted kernel by returning the inner kernel. -/
def unliftKernel (e : Expr) (_ : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.lift do
    throwError "Expected a lifted kernel, but got {e}."
  let args := e.getAppArgs
  let κ := args[args.size - 1]!
  return (κ, proofs)

initialize registerUnliftExpr unliftKernel

/-- Constructs the finisher proof that concludes the unlifting after rewriting the equalities. -/
def finisherKernelUnlift (_ _ lhs rhs : Expr) (maxLvl : Level) : MetaM Expr := do
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel lhs
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let lift_congr_expr ← mkAppM ``lift_congr #[ex, ey, lhs, rhs]
  mkAppM ``Iff.symm #[lift_congr_expr]

initialize registerUnliftFinisher finisherKernelUnlift

end
