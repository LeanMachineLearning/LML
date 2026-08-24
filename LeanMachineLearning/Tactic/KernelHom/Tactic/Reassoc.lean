/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Tactic.CategoryTheory.Reassoc
public import LeanMachineLearning.Tactic.KernelHom.Tactic.HomKernel

/-!
# `kernel_reassoc`

This file extends `Mathlib.Tactic.CategoryTheory.Reassoc` with a kernel-specific variant for
equalities of s-finite kernels. It mirrors the structure of `Mathlib.Tactic.CategoryTheory.
Reassoc`, but targets the kernel language developed in `KernelHom` rather than categorical
morphisms.
-/

public meta section

open Lean Meta Elab Tactic ProbabilityTheory Mathlib.Tactic Reassoc

/-- Same as `HomEquality`, but allows specifying a universe level that will be taken into account
when computing the maximum universe level. -/
def HomEqualityToLvl (eq : Expr) (Lvl : Level) : MetaM (Expr × Expr) := do
  let eq ← unfoldKernelOp eq
  let (lifted_expr, lifted_proof) ← liftEqualityWithLevel Lvl eq
  let some (_, lhs, rhs) := lifted_expr.eq? | throwError "Expected an equality, got: {lifted_expr}."
  let (lhs_hom, proofs) ← transformKernelToHom lhs []
  let (rhs_hom, proofs) ← transformKernelToHom rhs proofs
  let hom_expr ← mkEq lhs_hom rhs_hom
  let hom_eq_proof_type ← mkEq lifted_expr hom_expr
  let hom_eq_proof ← mkKernelHomEqProof hom_eq_proof_type lhs rhs proofs
  return (hom_expr, ← mkEqTrans lifted_proof hom_eq_proof)

/-- Replace all level metavariables appearing in an expression with named level parameters. -/
def freshenLevelParam (e : Expr) : MetaM Expr := do
  let mvarIds := (Lean.collectLevelMVars {} e).result
  for mvarId in mvarIds do
    Lean.assignLevelMVar mvarId (Level.param mvarId.name)
  instantiateMVars e

/-- Core handler for `@[kernel_reassoc]`.

Given an equality between s-finite kernels, this constructs the corresponding reassociated
equality in `SFinKer` category, under the extra `Z` measurable space and instance binders needed to
state the result. The returned array contains the fresh level metavariables that still need to be
added to the declaration's universe levels.
-/
def kernelReassocHandler (h_eq : Expr) : MetaM (Expr × Array LMVarId) := do
  let eq_type ← inferType h_eq
  let some (_, lhs, _) := eq_type.eq? |
    throwError "Expected an equality, but got {eq_type}"
  let (_, Y, _, _) ← getTypesFromKernel lhs
  let u ← mkFreshLevelMVar
  let proof : Expr ←
    withLocalDecl `Z .implicit (mkSort (mkLevelSucc u)) fun Z => do
      let mspaceType ← mkAppM ``MeasurableSpace #[Z]
      withLocalDecl `inst .instImplicit mspaceType fun _inst => do
        let kernelType ← mkAppMInst ``Kernel #[Y, Z] 2
        withLocalDeclD `ξ kernelType fun ξ => do
          let sfiniteType ← mkAppM ``IsSFiniteKernel #[ξ]
          withLocalDecl `inst_1 BinderInfo.instImplicit sfiniteType fun _inst_1 => do
            let (_, hom_proof) ← HomEqualityToLvl eq_type u
            let hom_proof ← mkAppM ``Eq.mp #[hom_proof, h_eq]
            let (hom_proof_reassoc, _) ← reassocExprHom hom_proof
            let univs ← collectExprUniverses eq_type
            let maxLvl ← computeMaxLevel <| u :: univs
            let (ξ_lift, _) ← liftKernel ξ maxLvl []
            let (ξ_hom, _) ← transformKernelToHom ξ_lift []
            let reassoc_body ← mkAppM' hom_proof_reassoc #[ξ_hom]
            let (_, kernel_reassoc_proof) ← KernelEquality <| ← inferType reassoc_body
            let kernel_reassoc_proof ← mkAppM ``Eq.mp #[kernel_reassoc_proof, reassoc_body]
            mkLambdaFVars #[Z, _inst, ξ, _inst_1] kernel_reassoc_proof
  let proof ← freshenLevelParam proof
  return (proof, #[u.mvarId!])

/-- Same as `@[reassoc]`, but for equalities of s-finite kernels. -/
syntax (name := kernelReassoc) "kernel_reassoc" optAttrArg : attr

/-- Registry of kernel reassociation handlers.

The default handler translates equalities of s-finite kernels, and additional handlers can be
registered to extend the attribute to other kernel-shaped equalities.
-/
private initialize kernelreassocImplRef : IO.Ref (Array (Expr → MetaM (Expr × Array LMVarId))) ←
  IO.mkRef #[kernelReassocHandler]

/-- IO ref for reassociation handlers `kernel_reassoc` attribute, so that it can be extended
with additional handlers. Handlers take a proof of the equation. -/
def registerKernelReassocExpr (f : Expr → MetaM (Expr × Array LMVarId)) : IO Unit := do
  kernelreassocImplRef.modify (·.push f)

/-- Reassociates the kernels in the type of `pf` using the registered handlers,
using `kernelReassocHandler` as the default.

Returns the proof of the lemma along with a list of fresh level metavariables. -/
def kernelreassocExpr (pf : Expr) : MetaM (Expr × Array LMVarId) := do
  forallTelescopeReducing (← inferType pf) fun xs _ => do
    let pf := mkAppN pf xs
    let handlers ← kernelreassocImplRef.get
    let (pf, levels) ← handlers.firstM (fun h => h pf) <|> do
      throwError "`kernel_reassoc` can only be used on terms about equality of s-finite kernels."
    return (← mkLambdaFVars xs pf, levels)

private def kernelReassocImpl (src : Name) (ref : Syntax) (kind : AttributeKind) : AttrM Name :=
  match ref with
  | `(attr| kernel_reassoc $optAttr) => MetaM.run' do
    unless kind == AttributeKind.global do
      throwAttrMustBeGlobal `reassoc kind
    let tgt := src.appendAfter "_assoc"
    addRelatedDecl src tgt ref optAttr fun value levels => do
      Term.TermElabM.run' <| Term.withSynthesize do
        let (pf, newLevelMVars) ← kernelreassocExpr value
        let newNames := newLevelMVars.map (·.name)
        for mvarId in newLevelMVars do
          Lean.assignLevelMVar mvarId (Level.param mvarId.name)
        let pf ← instantiateMVars pf
        pure (pf, levels ++ newNames.toList)
    return tgt
  | _ => throwUnsupportedSyntax

initialize
  registerGeneratingAttr `kernelReassoc ((#[·]) <$> kernelReassocImpl · · ·)
  registerBuiltinAttribute {
    name := `kernelReassoc
    descr := ""
    applicationTime := .afterCompilation
    add := (discard <| kernelReassocImpl · · ·)
  }
