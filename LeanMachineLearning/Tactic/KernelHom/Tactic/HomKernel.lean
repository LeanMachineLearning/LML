/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.Tactic.KernelHom.Tactic.KernelHom
public import LeanMachineLearning.Tactic.EqLift.Tactic.Kernel.KernelUnlift

/-!
# `hom_kernel` tactic

This file implements the `hom_kernel` tactic, the inverse of `kernel_hom`.
It transforms equalities written in the monoidal category back into
equivalent equalities of kernels.

## Main declarations

* `transformHomToKernel`: recursive translation from categorical morphism expressions to
  kernel expressions.
* `applyHomKernel`: core implementation on goals and hypotheses.
* `hom_kernel`: user-facing tactic (with location support).
-/

public meta section

open Lean Elab Tactic Meta CategoryTheory Parser.Tactic ProbabilityTheory MonoidalCategory
open ProbabilityTheory.Kernel

/-- Get the original type and its universe from a `SFinKer.of` expression. -/
partial def getTypeFromSFinKer (e : Expr) : MetaM Expr := do
  match e.getAppFn with
  | Expr.const ``tensorUnit [eLvl, _] =>
    return mkConst ``PUnit [eLvl.succ]
  | Expr.const ``SFinKer.of _ =>
    let args := e.getAppArgs
    return args[0]!
  | Expr.const ``MonoidalCategory.tensorObj _ =>
    let args := e.getAppArgs
    let SY := args[args.size - 1]!
    let SX := args[args.size - 2]!
    let Y ← getTypeFromSFinKer SY
    let X ← getTypeFromSFinKer SX
    mkAppOptM ``Prod #[X, Y]
  | _ => throwError "Expected a SFinKer.of expression, got: {e}."

/-- Deconstruct a left or right whisker. -/
def deconstructWhiskersHomArgs (e : Expr) (eLvl : Level) (left : Bool) :
    MetaM (Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr) := do
  let args := e.getAppArgs
  let SZ := if left then args[args.size - 4]! else args[args.size - 1]!
  let SY := if left then args[args.size - 2]! else args[args.size - 3]!
  let SX := if left then args[args.size - 3]! else args[args.size - 4]!
  let κ := if left then args[args.size - 1]! else args[args.size - 2]!
  let Z ← getTypeFromSFinKer SZ
  let Y ← getTypeFromSFinKer SY
  let X ← getTypeFromSFinKer SX
  let mXUnit ← synthInstance (mkApp (mkConst ``MeasurableSpace [eLvl]) Z)
  let kernel_id ← mkAppOptM ``Kernel.id #[Z, mXUnit]
  return (κ, kernel_id, SX, SY, SZ, X, Y, Z)

/-- Deconstruct a braiding morphism. -/
def deconstructBraiding (e : Expr) : MetaM (Expr × Expr) := do
  let args := e.getAppArgs
  let SY := args[args.size - 1]!
  let SX := args[args.size - 2]!
  let Y ← getTypeFromSFinKer SY
  let X ← getTypeFromSFinKer SX
  let swap_hom_proof ← mkAppM ``braiding_hom #[SX, SY, ← idME X, ← idME Y]
  return (← mkAppOptM ``Kernel.swap #[X, Y, none, none], swap_hom_proof)

/-- Given an equality between a categorical morphism (left) and a "morphized" kernel (right), get
the kernel on the right side of the equality. -/
def getKernelRHSEqProofType (e : Expr) : MetaM Expr := do
  let some (_, _, hom_expr) := (← inferType e).eq? | throwError "Expected an equality, got: {e}."
  match hom_expr.getAppFn with
  | Expr.const ``Kernel.hom _ =>
    let args := hom_expr.getAppArgs
    return args[args.size - 2]!
  | _ => throwError "Expected a hom expression, got: {hom_expr}."

/-- Deconstruct a left or right unitor [inverse] morphism. -/
def deconstructUnitors (e : Expr) (eLvl : Level) (left hom : Bool) :
    MetaM (Expr × Expr) := do
  let args := e.getAppArgs
  let SX := args[args.size - 1]!
  let X ← getTypeFromSFinKer SX
  let ex ← idME X
  let (X₀, x₀Lvl) ← getOriginalType X
  let ex₀ ← constructMeasurableEquiv X₀ x₀Lvl eLvl
  let const_args := [eLvl, x₀Lvl, eLvl, Level.zero]
  let const_name :=
    if left then
      if hom then ``leftUnitor_hom
      else ``leftUnitor_inv
    else
      if hom then ``rightUnitor_hom
      else ``rightUnitor_inv
  let const := mkConst const_name const_args
  let unitor_proof_eq ← mkAppM' const #[SX, ex, ex₀]
  return (← getKernelRHSEqProofType unitor_proof_eq, unitor_proof_eq)

/-- Deconstruct an associator [inverse] morphism. -/
def deconstructAssociator (e : Expr) (eLvl : Level) (hom : Bool) : MetaM (Expr × Expr) := do
  let args := e.getAppArgs
  let SZ := args[args.size - 1]!
  let SY := args[args.size - 2]!
  let SX := args[args.size - 3]!
  let Z ← getTypeFromSFinKer SZ
  let Y ← getTypeFromSFinKer SY
  let X ← getTypeFromSFinKer SX
  let (Z₀, z₀Lvl) ← getOriginalType Z
  let (Y₀, y₀Lvl) ← getOriginalType Y
  let (X₀, x₀Lvl) ← getOriginalType X
  let ez₀ ← constructMeasurableEquiv Z₀ z₀Lvl eLvl
  let ey₀ ← constructMeasurableEquiv Y₀ y₀Lvl eLvl
  let ex₀ ← constructMeasurableEquiv X₀ x₀Lvl eLvl
  let associator_const := mkConst
    (if hom then ``Kernel.associator_hom else ``Kernel.associator_inv)
    [eLvl, eLvl, eLvl, x₀Lvl, y₀Lvl, z₀Lvl, eLvl]
  let associator_proof_eq ← mkAppM' associator_const
    #[SX, SY, SZ, ← idME X, ← idME Y, ← idME Z, ex₀, ey₀, ez₀]
  return (← getKernelRHSEqProofType associator_proof_eq, associator_proof_eq)

/-- Recursive transformation from morphism expression in `SFinKer` to kernel expression. -/
partial def transformHomToKernel (e : Expr) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  match e.getAppFn with
  | Expr.const ``tensorHom _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let ST := args[args.size - 3]!
    let SZ := args[args.size - 4]!
    let SY := args[args.size - 5]!
    let SX := args[args.size - 6]!
    let (κ', proofs_κ) ← transformHomToKernel κ proofs
    let (η', proofs_η) ← transformHomToKernel η proofs_κ
    let (X, Y, _, _) ← getTypesFromKernel κ'
    let (Z, T, _, _) ← getTypesFromKernel η'
    let parallelComp_hom_proof ← mkAppMInst ``parallelComp_hom
        #[SX, SY, SZ, ST, ← idME X, ← idME Y, ← idME Z, ← idME T, κ', η'] 2
    return (← mkAppM ``Kernel.parallelComp #[κ', η'], parallelComp_hom_proof :: proofs_η)
  | Expr.const ``CategoryStruct.comp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let SY := args[args.size - 3]!
    let SX := args[args.size - 4]!
    let SZ := args[args.size - 5]!
    let (κ', proofs_κ) ← transformHomToKernel κ proofs
    let (η', proofs_η) ← transformHomToKernel η proofs_κ
    let (X, Y, _, _) ← getTypesFromKernel η'
    let (Z, _, _, _) ← getTypesFromKernel κ'
    let comp_hom_proof ← mkAppMInst ``comp_hom
        #[SX, SY, SZ, ← idME X, ← idME Y, ← idME Z, η', κ'] 2
    return (← mkAppM ``Kernel.comp #[η', κ'], comp_hom_proof :: proofs_η)
  | Expr.const ``CategoryStruct.id [xLvl, _] =>
    let args := e.getAppArgs
    let SX := args[args.size - 1]!
    let X ← getTypeFromSFinKer SX
    let mX' ← synthInstance (mkApp (mkConst ``MeasurableSpace [xLvl]) X)
    let id ← mkAppOptM ``Kernel.id #[X, mX']
    let id_hom_proof ← mkAppM ``id_hom #[SX, ← idME X]
    return (id, id_hom_proof :: proofs)
  | Expr.const ``ComonObj.counit [xLvl, _] =>
    let args := e.getAppArgs
    let SX := args[args.size - 2]!
    let X ← getTypeFromSFinKer SX
    let discard_kernel_const := mkConst ``Kernel.discard [xLvl, xLvl]
    let discard_const := mkConst ``counit [xLvl, xLvl, xLvl]
    let discard_hom_proof ← mkAppM' discard_const #[SX, ← idME X]
    return (← mkAppOptM' discard_kernel_const #[X, none], discard_hom_proof :: proofs)
  | Expr.const ``ComonObj.comul [xLvl, _] =>
    let args := e.getAppArgs
    let SX := args[args.size - 2]!
    let X ← getTypeFromSFinKer SX
    let copy_kernel_const := mkConst ``Kernel.copy [xLvl]
    let copy_hom_proof ← mkAppM ``comul #[SX, ← idME X]
    return (← mkAppOptM' copy_kernel_const #[X, none], copy_hom_proof :: proofs)
  | Expr.const ``Kernel.hom _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    return (κ, proofs)
  | Expr.const ``MonoidalCategory.whiskerLeft [eLvl, _] =>
    let (κ, kernel_id, SX, SY, SZ, X, Y, Z) ← deconstructWhiskersHomArgs e eLvl true
    let (κ', proofs_κ) ← transformHomToKernel κ proofs
    let whisker_left_hom_proof ← mkAppMInst ``Kernel.whiskerLeft
      #[SX, SY, SZ, ← idME X, ← idME Y, ← idME Z, κ'] 1
    return (← mkAppM ``Kernel.parallelComp #[kernel_id, κ'], whisker_left_hom_proof :: proofs_κ)
  | Expr.const ``MonoidalCategory.whiskerRight [eLvl, _] =>
    let (κ, kernel_id, SX, SY, SZ, X, Y, Z) ← deconstructWhiskersHomArgs e eLvl false
    let (κ', proofs_κ) ← transformHomToKernel κ proofs
    let whisker_right_hom_proof ← mkAppMInst ``Kernel.whiskerRight
      #[SX, SY, SZ, ← idME X, ← idME Y, ← idME Z, κ'] 1
    return (← mkAppM ``Kernel.parallelComp #[κ', kernel_id], whisker_right_hom_proof :: proofs_κ)
  | Expr.const ``Iso.hom _ =>
    let args := e.getAppArgs
    let iso := args[args.size - 1]!
    match iso.getAppFn with
    | Expr.const ``BraidedCategory.braiding _ =>
      let (braiding_expr, swap_hom_proof) ← deconstructBraiding iso
      return (braiding_expr, swap_hom_proof :: proofs)
    | Expr.const ``leftUnitor [eLvl, _] =>
      let (left_unitor_expr, left_unitor_hom_proof) ← deconstructUnitors iso eLvl true true
      return (left_unitor_expr, left_unitor_hom_proof :: proofs)
    | Expr.const ``rightUnitor [eLvl, _] =>
      let (right_unitor_expr, right_unitor_hom_proof) ← deconstructUnitors iso eLvl false true
      return (right_unitor_expr, right_unitor_hom_proof :: proofs)
    | Expr.const ``MonoidalCategory.associator [eLvl, _] =>
      let (associator_expr, associator_hom_proof) ← deconstructAssociator iso eLvl true
      return (associator_expr, associator_hom_proof :: proofs)
    | _ => throwError "Unexpected isomorphism {iso}."
  | Expr.const ``Iso.inv _ =>
    let args := e.getAppArgs
    let iso := args[args.size - 1]!
    match iso.getAppFn with
    | Expr.const ``BraidedCategory.braiding _ =>
      let (braiding_expr, swap_hom_proof) ← deconstructBraiding iso
      return (braiding_expr, swap_hom_proof :: proofs)
    | Expr.const ``leftUnitor [eLvl, _] =>
      let (left_unitor_expr, left_unitor_inv_hom_proof) ← deconstructUnitors iso eLvl true false
      return (left_unitor_expr, left_unitor_inv_hom_proof :: proofs)
    | Expr.const ``rightUnitor [eLvl, _] =>
      let (right_unitor_expr, right_unitor_inv_hom_proof) ← deconstructUnitors iso eLvl false false
      return (right_unitor_expr, right_unitor_inv_hom_proof :: proofs)
    | Expr.const ``MonoidalCategory.associator [eLvl, _] =>
      let (associator_expr, associator_inv_hom_proof) ← deconstructAssociator iso eLvl false
      return (associator_expr, associator_inv_hom_proof :: proofs)
    | _ => throwError "Unexpected isomorphism {iso}."
  | _ => throwError "Expected a hom expression, got: {e}."

/-- Get the universe level from the left side of an equality expression. -/
def getUniverseFromEq (eq : Expr) : MetaM Level := do
  let eq ← instantiateMVars eq
  let eq ← zetaReduce eq
  let eq ← whnf eq
  let eq := eq.consumeMData
  let some (_, lhs, _) := eq.eq? | throwError "Expected an equality, got: {eq}."
  let l ← getLevel (← inferType lhs)
  match l with
  | Level.succ l' => return l'
  | _ => throwError "Expected a universe level ≥ 1, got: {l}"

/-- Transform a `SFinKer` equality into an equivalent equality of kernels, along with a proof of
equivalence. -/
def KernelEquality (eq : Expr) : MetaM (Expr × Expr) := do
  let eq ← whnfR <| ← instantiateMVars eq
  let some (_, lhs_hom, rhs_hom) := eq.eq? | throwError "Expected an equality, got: {eq}."
  let (lhs, proofs) ← transformHomToKernel lhs_hom []
  let (rhs, proofs) ← transformHomToKernel rhs_hom proofs
  let kernel_expr ← mkEq lhs rhs
  let (unlifted_expr, unlifted_proof) ← unliftEquality kernel_expr
  let kernel_eq_proof_type ← mkEq kernel_expr eq
  let kernel_eq_proof ← mkAppM ``Eq.symm #[← mkKernelHomEqProof kernel_eq_proof_type lhs rhs proofs]
  return (unlifted_expr, ← mkEqTrans kernel_eq_proof unlifted_proof)

/-- The `hom_kernel` tactic is the inverse of `kernel_hom`: it transforms an
equality written in the monoidal category back to an equivalent equality of
s-finite kernels.

The tactic supports location specifiers like `rw` or `simp`:
- `hom_kernel` — applies to the goal
- `hom_kernel at h` — applies to hypothesis `h`
- `hom_kernel at h₁ h₂` — applies to multiple hypotheses
- `hom_kernel at h ⊢` — applies to hypothesis `h` and the goal
- `hom_kernel at *` — applies to all hypotheses and the goal

It is useful to switch back to kernel equations once categorical rewrites are done. -/
syntax (name := homKernel) "hom_kernel" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| hom_kernel $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| KernelEquality
