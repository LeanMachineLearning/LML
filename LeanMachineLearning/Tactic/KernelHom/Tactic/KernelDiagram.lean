/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Lean.Elab.Tactic.Location
public import LeanMachineLearning.Tactic.KernelHom.Tactic.HomKernel
public import Mathlib.Tactic.Widget.StringDiagram

/-!
# Kernel Diagram Widget

This file provides meta infrastructure for displaying string diagrams for s-finite kernels in the
infoview. To enable the kernel diagram widget, you need to import this file and inserting
`with_panel_widgets [KernelDiagram]` at the beginning of the proof. Alternatively, you can also
write
```lean
show_panel_widgets [local KernelDiagram]
```
to enable the string diagram widget in the current section.

We also have the `#kernel_diagram` command. For example,
```lean
#string_diagram ProbabilityTheory.Kernel.deterministic_comp_copy
```

This is an adaptation of the string diagram widget where kernels are transformed into morphisms of
the `SFinKer` monoidal category using the `kernel_hom` tactic.
-/

public meta section

open Lean Meta Elab Command ProofWidgets Mathlib.Tactic.Widget

open Mathlib.Tactic BicategoryLike Penrose Server

open MeasureTheory ProbabilityTheory CategoryTheory

open CategoryTheory

open scoped MonoidalCategory ComonObj

namespace Mathlib.Tactic.Widget.StringDiagram

/-- The kernelized penrose variable associated with a node. -/
def Node.toPenroseVar_kernel (n : Node) : MetaM PenroseVar := do
  let expr ←
    try
      match n.e.getAppFn with
      | Expr.const ``SFinKer.of _ => do
        let res ← getTypeFromSFinKer n.e
        pure res
      | _ => do
        let (expr, _) ← transformHomToKernel n.e []
        pure expr
    catch _ =>
      pure n.e
  return ⟨"E", [n.vPos, n.hPosSrc, n.hPosTar], expr⟩

open scoped Jsx in
/-- Construct a kernelized string diagram from a Penrose `sub`stance program and
expressions `embeds` to display as labels in the diagram. -/
def mkKernelDiagram (nodes : List (List Node)) (strands : List (List Strand)) :
    DiagramBuilderM PUnit := do
  /- Add 2-morphisms. -/
  for x in nodes.flatten do
    match x with
    | .atom _ => do addPenroseVar "Atom" (← x.toPenroseVar_kernel)
    | .id _ => do StringDiagram.addPenroseVar "Id" (← x.toPenroseVar_kernel)
  /- Add constraints. -/
  for l in nodes do
    for (x₁, x₂) in l.consecutivePairs do
      DiagramBuilderM.addInstruction
        s!"Left({← x₁.toPenroseVar_kernel}, {← x₂.toPenroseVar_kernel})"
  /- Add constraints. -/
  for (l₁, l₂) in nodes.consecutivePairs do
    if let some x₁ := l₁.head? then
      if let some x₂ := l₂.head? then
        DiagramBuilderM.addInstruction
          s!"Above({← x₁.toPenroseVar_kernel}, {← x₂.toPenroseVar_kernel})"
  /- Add 1-morphisms as strings. -/
  for l in strands do
    for s in l do
      StringDiagram.addConstructor "Mor1" s.toPenroseVar
        "MakeString" [← s.startPoint.toPenroseVar_kernel, ← s.endPoint.toPenroseVar_kernel]

end Mathlib.Tactic.Widget.StringDiagram

namespace KernelDiagram

open scoped Jsx in
/-- Given a kernel expression, return a string diagram. Otherwise `none`. -/
def KernelM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  try
    let (e, _) ← transformKernelToHom e []
    let k ← StringDiagram.mkKind e
    let x : Option (List (List StringDiagram.Node) × List (List StringDiagram.Strand))
    ← (match k with
      | .monoidal => do
        let some ctx ← BicategoryLike.mkContext? (ρ := Monoidal.Context) e | return none
        CoherenceM.run (ctx := ctx) do
          let e' := (← BicategoryLike.eval k.name (← MkMor₂.ofExpr e)).expr
          return some (← e'.nodes, ← e'.strands)
      | .bicategory => do
        let some ctx ← BicategoryLike.mkContext? (ρ := Bicategory.Context) e | return none
        CoherenceM.run (ctx := ctx) do
          let e' := (← BicategoryLike.eval k.name (← MkMor₂.ofExpr e)).expr
          return some (← e'.nodes, ← e'.strands)
      | .none => return none)
    match x with
    | none => return none
    | some (nodes, strands) => do
      DiagramBuilderM.run do
        StringDiagram.mkKernelDiagram nodes strands
        trace[string_diagram] "Penrose substance: \n{(← get).sub}"
        match ← DiagramBuilderM.buildDiagram StringDiagram.dsl StringDiagram.sty with
        | some html => return html
        | none => return <span>No non-structural morphisms found.</span>
  catch _ => return none

open scoped Jsx in
/-- Help function for displaying two string diagrams in an equality. -/
def mkEqHtml (lhs rhs : Html) : Html :=
  <div className="flex">
    <div className="w-50">
      <details «open»={true}>
        <summary className="mv2 pointer">Kernel diagram for LHS</summary> {lhs}
      </details>
    </div>
    <div className="w-50">
      <details «open»={true}>
        <summary className="mv2 pointer">Kernel diagram for RHS</summary> {rhs}
      </details>
    </div>
  </div>

/-- Given an equality between kernels, return a string diagram of the LHS and RHS.
Otherwise `none`. -/
def kernelEqM? (e : Expr) : MetaM (Option Html) := do
  try
    let e ← unfoldKernelOp <| ← instantiateMVars e
    let (lifted_e, _) ← liftEquality e
    let some (_, lhs, rhs) := lifted_e.eq? | return none
    let some lhs ← KernelM? lhs | return none
    let some rhs ← KernelM? rhs | return none
    return some <| mkEqHtml lhs rhs
  catch _ => return none

/-- Reduce a forall expression and try to display a kernel diagram
if it is an equality of kernels. -/
def kernelEqMReduce? (e : Expr) : MetaM (Option Html) := do
  forallTelescopeReducing (← whnfR <| ← inferType e) fun _ expr => do
    kernelEqM? expr

open scoped Jsx in
/-- The RPC method for displaying kernel diagrams. -/
@[server_rpc_method]
def rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let html : Option Html ← (do
      if props.goals.isEmpty then
        return none
      let some g := props.goals[0]? | unreachable!
      g.ctx.val.runMetaM {} do
        g.mvarId.withContext do
          let type ← g.mvarId.getType
          kernelEqM? type)
    match html with
    | none => return <span>No Kernel Diagram.</span>
    | some inner => return inner

end KernelDiagram

/-- Display the kernel diagrams if the goal is an equality of s-finite kernels. -/
@[widget_module]
def KernelDiagram : Component PanelWidgetProps :=
  mk_rpc_widget% KernelDiagram.rpc

/--
Display the kernel diagram for a given term.

Example usage:
```
/- Kernel diagram for an equality theorem. -/
#kernel_diagram ProbabilityTheory.Kernel.deterministic_comp_copy
```
-/
syntax (name := kernelDiagram) "#kernel_diagram " term : command

@[command_elab kernelDiagram, inherit_doc kernelDiagram]
def elabKernelDiagramCmd : CommandElab := fun
  | stx@`(#kernel_diagram $t:term) => do
    let html ← runTermElabM fun _ => do
      let e ← try mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverloadWithInfo t)
        catch _ => Term.levelMVarToParam (← instantiateMVars (← Term.elabTerm t none))
      match ← KernelDiagram.kernelEqMReduce? e with
      | some html => return html
      | none => throwError "could not find an equality of kernels: {e}."
    liftCoreM <| Widget.savePanelWidgetInfo
      (hash HtmlDisplay.javascript)
      (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
      stx
  | stx => throwError "Unexpected syntax {stx}."
