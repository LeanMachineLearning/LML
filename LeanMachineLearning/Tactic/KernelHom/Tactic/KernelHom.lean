/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.Tactic.KernelHom.Kernel.MonoidalComp
public import LeanMachineLearning.Tactic.KernelHom.Tactic.Utils
public import Lean.Elab.Tactic.Location
public import LeanMachineLearning.Tactic.EqLift.Tactic.Kernel.KernelLift

/-!
# `kernel_hom` tactic

This file implements the `kernel_hom` tactic, which transforms equalities of
kernels into equivalent equalities in the monoidal category.

## Main declarations

* `transformKernelToHom`: recursive translation from kernel expressions to
  categorical morphism expressions.
* `mkKernelHomEqProof`: construction of the equivalence proof used by the
  tactic.
* `applyKernelHom`: core implementation of `kernel_hom` on goals and hypotheses.
* `kernel_hom`: user-facing tactic (with location support).
-/

public meta section

open Lean Elab Tactic Meta CategoryTheory Parser.Tactic ProbabilityTheory MonoidalCategory
open ProbabilityTheory.Kernel

/-- Recursively decompose a product type into `SFinKer` objects with monoidal tensor structure. -/
partial def decomposeProductToSFinker (X : Expr) (xLvl : Level) : MetaM Expr := do
  match X.getAppFn with
  | Expr.const ``Prod _ =>
    let args := X.getAppArgs
    let t1 ← decomposeProductToSFinker args[0]! xLvl
    let t2 ← decomposeProductToSFinker args[1]! xLvl
    mkAppM ``tensorObj #[t1, t2]
  | _ =>
    mkAppOptM ``SFinKer.of #[X, none]

/-- Compute the `SFinKer` object corresponding to a measurable space. -/
def computeSFinkerOf (X : Expr) (xLvl : Level) : MetaM Expr := do
  match X with
  | Expr.const ``PUnit _ | Expr.const ``Unit _ =>
    let tensorunit := mkConst ``tensorUnit [xLvl, xLvl.succ]
    let sfinker := mkConst ``SFinKer [xLvl]
    mkAppOptM' tensorunit #[sfinker, none, none]
  | _ =>
    decomposeProductToSFinker X xLvl

/-- Compute a measurable equivalence between a type and itself by recursively decomposing
products. -/
partial def idME (X : Expr) : MetaM Expr := do
  match X.getAppFn with
  | Expr.const ``Prod _ =>
    let args := X.getAppArgs
    let id1 ← idME args[0]!
    let id2 ← idME args[1]!
    mkAppM ``MeasurableEquiv.prodCongr #[id1, id2]
  | Expr.const ``PUnit [xLvl] | Expr.const ``Unit [xLvl] =>
    let xLvl ← match xLvl with
      | Level.succ l => pure l
      | _ => throwError "Expected a successor level for PUnit/Unit, got: {xLvl}."
    let punitME := mkConst ``MeasurableEquiv.punit [xLvl, xLvl]
    mkAppM' punitME #[]
  | _ =>
    mkAppOptM ``MeasurableEquiv.refl #[X, none]

/-- Check if a kernel expression corresponds to a left or right whisker. -/
def checkWhiskers (κ : Expr) (offset : Nat) : MetaM Bool := do
  let κ := κ.consumeMData
  let args := κ.getAppArgs
  let idKernel := args[args.size - offset]!
  if !idKernel.isAppOf ``Kernel.id then
    return false
  else return true

/-- Check if a kernel expression corresponds to a left whisker. -/
def checkWhiskerLeft (κ : Expr) : MetaM Bool := checkWhiskers κ 2

/-- Check if a kernel expression corresponds to a right whisker. -/
def checkWhiskerRight (κ : Expr) : MetaM Bool := checkWhiskers κ 1

/-- Construct the relevant data for converting a kernel expression to its whisker morphism
representation. -/
def constructWhiskersArgs (e X Y : Expr) (left : Bool) :
    MetaM (Expr × Expr × Expr × Expr × Expr × Expr × Expr) := do
  let (Z, zLvl, X, xLvl) ← match X.getAppFn with
    | Expr.const ``Prod univs =>
      let args := X.getAppArgs
      pure (args[left.toNat]!, univs[left.toNat]!, args[1 - left.toNat]!, univs[1 - left.toNat]!)
    | _ =>
      if left then throwError "Expected left whisker with source Z × X, got: {X}."
      else throwError "Expected right whisker with source X × Z, got: {X}."
  let (Y, yLvl) ← match Y.getAppFn with
    | Expr.const ``Prod univs =>
      let args := Y.getAppArgs
      pure (args[1 - left.toNat]!, univs[1 - left.toNat]!)
    | _ =>
      if left then throwError "Expected left whisker with target Z × Y, got: {Y}."
      else throwError "Expected right whisker with target Y × Z, got: {Y}."
  let κ ← match e.getAppFn with
    | Expr.const ``Kernel.parallelComp _ =>
      let args := e.getAppArgs
      pure args[args.size - (left.toNat + 1)]!
    | _ =>
      if left then throwError "Expected left whisker with parallelComp, got: {e}."
      else throwError "Expected right whisker with parallelComp, got: {e}."
  let SZ ← computeSFinkerOf Z zLvl
  let SX ← computeSFinkerOf X xLvl
  let SY ← computeSFinkerOf Y yLvl
  return (SZ, Z, SX, X, SY, Y, κ)

/-- Check if a kernel expression corresponds to a left or right unitor. -/
def checkUnitors (κ : Expr) (offset : Nat) (prod : Name) : MetaM Bool := do
  let κ := κ.consumeMData
  if !κ.isAppOf ``Kernel.map then
    return false
  let args := κ.getAppArgs
  let fn := args[args.size - 1]!
  let idKernel := args[args.size - 2]!
  if !fn.isAppOf prod then
    return false
  if !idKernel.isAppOf ``Kernel.id then
    return false
  let (src, _, _) ← getTypesFromKernel κ
  match src.getAppFn with
  | Expr.const ``Prod _ =>
    let args := src.getAppArgs
    if args.size < 2 then
      return false
    let punit? := args[offset]!
    match punit?.getAppFn with
    | Expr.const ``PUnit _ | Expr.const ``Unit _ => return true
    | _ => return false
  | _ => return false

/-- Check if a kernel expression corresponds to a left unitor. -/
def checkLeftUnitor (κ : Expr) : MetaM Bool := checkUnitors κ 0 ``Prod.snd

/-- Check if a kernel expression corresponds to a right unitor. -/
def checkRightUnitor (κ : Expr) : MetaM Bool := checkUnitors κ 1 ``Prod.fst

/-- Construct the left or right unitor morphism. -/
def constructUnitors (X ex₀ : Expr) (xLvl y₀Lvl punitLvl : Level) (offset : Nat) :
    MetaM (Expr × Expr) := do
  let left ← if offset == 0 then pure true
    else if offset == 1 then pure false
    else throwError "Invalid offset for unitors."
  let SX ← computeSFinkerOf X xLvl
  let unitor ← if left then mkAppM ``leftUnitor #[SX]
    else mkAppM ``rightUnitor #[SX]
  let unitor_hom_const :=
    if left then mkConst ``leftUnitor_hom [xLvl, y₀Lvl, xLvl, punitLvl]
    else mkConst ``rightUnitor_hom [xLvl, y₀Lvl, xLvl, punitLvl]
  let unitor_hom_proof ←
    if left then mkAppM' unitor_hom_const #[SX, ← idME X, ex₀]
    else mkAppM' unitor_hom_const #[SX, ← idME X, ex₀]
  return (← mkAppM ``Iso.hom #[unitor], unitor_hom_proof)

/-- Check if a kernel expression corresponds to an associator morphism or its inverse. -/
def checkAssociator (κ : Expr) (hom : Bool) : MetaM Bool := do
  let κ := κ.consumeMData
  if !κ.isAppOf ``Kernel.deterministic then
    return false
  let args := κ.getAppArgs
  let fn := args[args.size - 2]!
  if !fn.isAppOf ``DFunLike.coe then
    return false
  let fn := fn.getAppArgs[fn.getAppApps.size - 1]!
  if hom then
    if !fn.isAppOf ``MeasurableEquiv.prodAssoc then
      return false
  else
    if !fn.isAppOf ``MeasurableEquiv.symm then
      return false
    let innerFn := fn.getAppArgs[fn.getAppArgs.size - 1]!
    if !innerFn.isAppOf ``MeasurableEquiv.prodAssoc then
      return false
  return true

/-- Check if a kernel expression corresponds to an associator morphism. -/
def checkAssociatorHom (κ : Expr) : MetaM Bool := checkAssociator κ true

/-- Check if a kernel expression corresponds to an inverse associator morphism. -/
def checkAssociatorInv (κ : Expr) : MetaM Bool := checkAssociator κ false

/-- Get the types and universe levels from a expression of the form `X × Y × Z`. -/
def getTypesFromThreeProds (prod : Expr) :
    MetaM (Expr × Expr × Expr × Level × Level × Level) := do
  match prod.getAppFn with
  | Expr.const ``Prod univs =>
    let X := prod.getAppArgs[0]!
    match prod.getAppArgs[1]!.getAppFn with
    | Expr.const ``Prod univs_right =>
      let Y := prod.getAppArgs[1]!.getAppArgs[0]!
      let Z := prod.getAppArgs[1]!.getAppArgs[1]!
      return (X, Y, Z, univs[0]!, univs_right[0]!, univs_right[1]!)
    | _ => throwError "Expected a product of two types, got: {prod.getAppArgs[1]!}."
  | _ => throwError "Expected a product of three types, got: {prod}."

/-- Get the measurable equivalences from a product of three measurable equivalences. -/
def getMEFromThreeProds (me_prod : Expr) :
    MetaM (Expr × Expr × Expr) := do
  match me_prod.getAppFn with
  | Expr.const ``MeasurableEquiv.prodCongr _ =>
    let args := me_prod.getAppArgs
    let ex := args[args.size - 2]!
    let right := args[args.size - 1]!
    match right.getAppFn with
    | Expr.const ``MeasurableEquiv.prodCongr _ =>
      let rightArgs := right.getAppArgs
      let ey := rightArgs[rightArgs.size - 2]!
      let ez := rightArgs[rightArgs.size - 1]!
      return (ex, ey, ez)
    | _ => throwError "Expected a product of two measurable equivalences, got: {right}."
  | _ => throwError "Expected a product of three measurable equivalences, got: {me_prod}."

/-- Construct the associator morphism or its inverse. -/
def constructAssociator (left right ex₀ ey₀ ez₀ : Expr) (hom : Bool) :
    MetaM (Expr × Expr) := do
  let (X, Y, Z, xLvl, yLvl, zLvl) ← if hom then getTypesFromThreeProds right
    else getTypesFromThreeProds left
  let SX ← computeSFinkerOf X xLvl
  let SY ← computeSFinkerOf Y yLvl
  let SZ ← computeSFinkerOf Z zLvl
  let associator ← mkAppM ``MonoidalCategory.associator #[SX, SY, SZ]
  let associator_hom_proof ←
    if hom then mkAppM ``associator_hom #[SX, SY, SZ, ← idME X, ← idME Y, ← idME Z, ex₀, ey₀, ez₀]
    else mkAppM ``associator_inv #[SX, SY, SZ, ← idME X, ← idME Y, ← idME Z, ex₀, ey₀, ez₀]
  return (← mkAppM (if hom then ``Iso.hom else ``Iso.inv) #[associator], associator_hom_proof)

/-- Construct the associator morphism. -/
def constructAssociatorHom (left right ex₀ ey₀ ez₀ : Expr) :=
  constructAssociator left right ex₀ ey₀ ez₀ true

/-- Construct the inverse associator morphism. -/
def constructAssociatorInv (left right ex₀ ey₀ ez₀ : Expr) :=
  constructAssociator left right ex₀ ey₀ ez₀ false

/-- Recursive transformation from kernel expressions to morphism expressions in the `SFinKer`
category. -/
partial def transformKernelToHom (e : Expr) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  match e.getAppFn with
  | Expr.const ``Kernel.comp _ =>
    let args := e.getAppArgs
    let η := args[args.size - 2]!
    let κ := args[args.size - 1]!
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel η
    let (Z, _, tLvl, _) ← getTypesFromKernel κ
    let SX ← computeSFinkerOf X xLvl
    let SY ← computeSFinkerOf Y yLvl
    let SZ ← computeSFinkerOf Z tLvl
    let comp_hom_proof ← mkAppMInst ``comp_hom #[SX, SY, SZ, ← idME X, ← idME Y, ← idME Z, η, κ] 2
    let (κ', proofs_κ) ← transformKernelToHom κ proofs
    let (η', proofs_η) ← transformKernelToHom η proofs_κ
    return (← mkAppM ``CategoryStruct.comp #[κ', η'], comp_hom_proof :: proofs_η)
  | Expr.const ``Kernel.parallelComp _ =>
    if ← checkWhiskerLeft e then
      let (X, Y, _, _) ← getTypesFromKernel e
      let (SZ, Z, SX, X, SY, Y, κ) ← constructWhiskersArgs e X Y false
      let (κ', proofs_κ) ← transformKernelToHom κ proofs
      let whisker_left_hom_proof ← mkAppMInst ``Kernel.whiskerLeft
          #[SX, SY, SZ, ← idME X, ← idME Y, ← idME Z, κ] 1
      let whiskerleft ← mkAppM ``MonoidalCategory.whiskerLeft #[SZ, κ']
      return (whiskerleft, whisker_left_hom_proof :: proofs_κ)
    else if ← checkWhiskerRight e then
      let (X, Y, _, _) ← getTypesFromKernel e
      let (SZ, Z, SX, X, SY, Y, κ) ← constructWhiskersArgs e X Y true
      let (κ', proofs_κ) ← transformKernelToHom κ proofs
      let whiskerright ← mkAppM ``MonoidalCategory.whiskerRight #[κ', SZ]
      let whiskerright_hom_proof ← mkAppMInst ``Kernel.whiskerRight
        #[SX, SY, SZ, ← idME X, ← idME Y, ← idME Z, κ] 1
      return (whiskerright, whiskerright_hom_proof :: proofs_κ)
    else
      let args := e.getAppArgs
      let κ := args[args.size - 2]!
      let η := args[args.size - 1]!
      let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
      let (Z, T, zLvl, tLvl) ← getTypesFromKernel η
      let SX ← computeSFinkerOf X xLvl
      let SY ← computeSFinkerOf Y yLvl
      let SZ ← computeSFinkerOf Z zLvl
      let ST ← computeSFinkerOf T tLvl
      let parallelComp_hom_proof ← mkAppMInst ``parallelComp_hom
        #[SX, SY, SZ, ST, ← idME X, ← idME Y, ← idME Z, ← idME T, κ, η] 2
      let (κ', proofs_κ) ← transformKernelToHom κ proofs
      let (η', proofs_η) ← transformKernelToHom η proofs_κ
      return (← mkAppM ``tensorHom #[κ', η'], parallelComp_hom_proof :: proofs_η)
  | Expr.const ``Kernel.id [xLvl] =>
    let X := e.getAppArgs[0]!
    let SX ← computeSFinkerOf X xLvl
    let id_hom_proof ← mkAppM ``id_hom #[SX, ← idME X]
    return (← mkAppM ``CategoryStruct.id #[SX], id_hom_proof :: proofs)
  | Expr.const ``Kernel.discard [xLvl, punitLvl] =>
    let X := e.getAppArgs[0]!
    let SX ← computeSFinkerOf X xLvl
    let discard_const := mkConst ``counit [xLvl, xLvl, punitLvl]
    let discard_hom_proof ← mkAppM' discard_const #[SX, ← idME X]
    return (← mkAppOptM ``ComonObj.counit #[none, none, none, SX, none],
      discard_hom_proof :: proofs)
  | Expr.const ``Kernel.copy [xLvl] =>
    let X := e.getAppArgs[0]!
    let SX ← computeSFinkerOf X xLvl
    let copy_hom_proof ← mkAppM ``comul #[SX, ← idME X]
    return (← mkAppOptM ``ComonObj.comul #[none, none, none, SX, none], copy_hom_proof :: proofs)
  | Expr.const ``Kernel.swap [xLvl, yLvl] =>
    let X := e.getAppArgs[0]!
    let Y := e.getAppArgs[1]!
    let SX ← computeSFinkerOf X xLvl
    let SY ← computeSFinkerOf Y yLvl
    let swap_hom_proof ← mkAppM ``braiding_hom #[SX, SY, ← idME X, ← idME Y]
    let braiding ← mkAppM ``Iso.hom #[← mkAppM ``BraidedCategory.braiding #[SX, SY]]
    return (braiding, swap_hom_proof :: proofs)
  | Expr.const ``Kernel.lift [_, y₀Lvl, _] =>
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel e
    let args := e.getAppArgs
    let κ := args[args.size - 1]!
    if ← checkLeftUnitor κ then
      let punitLvl ← match args[0]!.getAppFn with
        | Expr.const ``Prod [punitLvl, _] => pure punitLvl
        | _ => throwError "Expected a product with PUnit as the first component, got {args[0]!}."
      let ey₀ := args[args.size - 2]!
      let (leftUnitorExpr, left_unitor_hom_proof) ← constructUnitors Y ey₀ yLvl y₀Lvl punitLvl 0
      return (leftUnitorExpr, left_unitor_hom_proof :: proofs)
    else if ← checkRightUnitor κ then
      let punitLvl ← match args[0]!.getAppFn with
        | Expr.const ``Prod [_, punitLvl] => pure punitLvl
        | _ => throwError "Expected a product with PUnit as the first component, got {args[0]!}."
      let ey₀ := args[args.size - 2]!
      let (rightUnitorExpr, right_unitor_hom_proof) ← constructUnitors Y ey₀ yLvl y₀Lvl punitLvl 1
      return (rightUnitorExpr, right_unitor_hom_proof :: proofs)
    else if ← checkAssociatorHom κ then
      let (ex₀, ey₀, ez₀) ← getMEFromThreeProds args[args.size - 2]!
      let (associatorExpr, associator_hom_proof) ← constructAssociatorHom X Y ex₀ ey₀ ez₀
      return (associatorExpr, associator_hom_proof :: proofs)
    else if ← checkAssociatorInv κ then
      let (ex₀, ey₀, ez₀) ← getMEFromThreeProds args[args.size - 3]!
      let (associatorInvExpr, associator_inv_hom_proof) ← constructAssociatorInv X Y ex₀ ey₀ ez₀
      return (associatorInvExpr, associator_inv_hom_proof :: proofs)
    else
      let SX ← computeSFinkerOf X xLvl
      let SY ← computeSFinkerOf Y yLvl
      let homExpr ← mkAppOptM ``ProbabilityTheory.Kernel.hom
        #[X, Y, none, none, SX, SY, (← idME X), (← idME Y), e, none]
      pure (homExpr, proofs)
  | _ =>
    throwError "Expected a lifted kernel expression, got: {e}."

/-- Construct the proof of equivalence between the original equality and the transformed one. -/
def mkKernelHomEqProof (eqProofType lhs rhs : Expr) (proofs : List Expr) : MetaM Expr := do
  let mvar ← mkFreshExprSyntheticOpaqueMVar eqProofType
  let mvarId := mvar.mvarId!
  let propext := mkConst ``propext
  match ← mvarId.apply propext with
  | [mvarId] =>
    let proofs := proofs.reverse
    let mut mvarId := mvarId
    for proof in proofs do
      mvarId ← mvarId.nthRewrite 1 proof
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel lhs
    let SX ← computeSFinkerOf X xLvl
    let SY ← computeSFinkerOf Y yLvl
    let e ← mkAppMInst ``hom_congr #[SX, SY, ← idME X, ← idME Y, lhs, rhs] 2
    unless ← isDefEq (← mvarId.getType) (← inferType e) do
      throwError "Type mismatch: expected {← mvarId.getType}, got {← inferType e}."
    mvarId.assign e
    instantiateMVars mvar
  | _ =>
    throwError "Failed to apply propext while building kernel_hom equivalence proof for
      {eqProofType}."

/-- Transform a kernel equality into an equivalent equality in `SFinKer`, along with a proof of
equivalence. -/
def HomEquality (eq : Expr) : MetaM (Expr × Expr) := do
  let eq ← unfoldKernelOp eq
  let (lifted_expr, lifted_proof) ← liftEquality eq
  let some (_, lhs, rhs) := lifted_expr.eq? | throwError "Expected an equality, got: {lifted_expr}."
  let (lhs_hom, proofs) ← transformKernelToHom lhs []
  let (rhs_hom, proofs) ← transformKernelToHom rhs proofs
  let hom_expr ← mkEq lhs_hom rhs_hom
  let hom_eq_proof_type ← mkEq lifted_expr hom_expr
  let hom_eq_proof ← mkKernelHomEqProof hom_eq_proof_type lhs rhs proofs
  return (hom_expr, ← mkEqTrans lifted_proof hom_eq_proof)

/-- The `kernel_hom` tactic transforms a kernel equality to an equivalent equality in
the category of measurable spaces and s-finite kernels.

The tactic supports location specifiers like `rw` or `simp`:
* `kernel_hom` — applies to the goal
* `kernel_hom at h` — applies to hypothesis `h`
* `kernel_hom at h₁ h₂` — applies to multiple hypotheses
* `kernel_hom at h ⊢` — applies to hypothesis `h` and the goal
* `kernel_hom at *` — applies to all hypotheses and the goal

Example:
```lean
example {W X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace W] (κ : Kernel X Y) (η : Kernel Y Z) (ξ : Kernel Z W)
    [IsFiniteKernel ξ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    ξ ∘ₖ (η ∘ₖ κ) = ξ ∘ₖ η ∘ₖ κ := by
  kernel_hom
  exact Category.assoc _ _ _
``` -/
syntax (name := kernelHom) "kernel_hom" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| kernel_hom $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| HomEquality
