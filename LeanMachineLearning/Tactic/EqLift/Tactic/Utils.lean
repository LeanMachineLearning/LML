/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public meta import Lean.Meta.Tactic.Replace
public meta import Lean.Meta.Tactic.Rewrite

/-!

# Lift and Unlift utilities

This file provides utility functions for lifting and unlifting equalities.

-/

public meta section

open Lean Elab Tactic Meta Parser.Tactic

/-- A type alias for lifting/unlifting functions. -/
abbrev liftMetadata := Expr → Level → List Expr → MetaM (Expr × List Expr)

/-- A type alias for finisher functions that construct the final proof of equality after lifting/
unlifting inner expressions. -/
abbrev finisherMetadata := Expr → Expr → Expr → Expr → Level → MetaM Expr

/-- Transforms an expression using the registered lifting/unlifting functions given in `impl_ref`. Returns the first successful transformation along with the updated list of proofs. -/
def transformExpr (e : Expr) (maxLvl : Level) (proofs : List Expr)
    (impl_ref : IO.Ref (Array (liftMetadata))) : MetaM (Expr × List Expr) := do
  let handlers ← impl_ref.get
  let (lift_expr, proofs) ← handlers.firstM (fun h => h e maxLvl proofs) <|> do
    throwError "No transform handler found for {e}."
  return (lift_expr, proofs)

/-- Rewrites the type of `mvarId` at the `n`-th occurrence using `heq`.-/
def Lean.MVarId.nthRewrite (mvarId : MVarId) (n : Nat) (heq : Expr) : MetaM MVarId := do
  let r ← mvarId.rewrite (← mvarId.getType) heq (config := { occs := .pos [n] })
  mvarId.replaceTargetEq r.eNew r.eqProof

/-- Constructs a proof of equality between the original and transformed expressions using the provided proofs and finisher functions. -/
def constructProof (eqProofType lhs rhs lhs_t rhs_t : Expr) (maxLvl : Level) (proofs : List Expr)
    (finisher_ref : IO.Ref (Array finisherMetadata)) : MetaM Expr := do
  let mvar ← mkFreshExprSyntheticOpaqueMVar eqProofType
  let mvarId := mvar.mvarId!
  let propext := mkConst ``propext
  match ← mvarId.apply propext with
  | [mvarId] =>
    let proofs := proofs.reverse
    let mut mvarId := mvarId
    for proof in proofs do
      mvarId ← mvarId.nthRewrite 1 proof
    let handlers ← finisher_ref.get
    let e ← handlers.firstM (fun h => do
      let finisher ← h lhs rhs lhs_t rhs_t maxLvl
      unless ← isDefEq (← mvarId.getType) (← inferType finisher) do
        throwError "Type mismatch: expected {← mvarId.getType}, got {← inferType finisher}."
      mvarId.assign finisher
      instantiateMVars mvar
    ) <|> do
      throwError m!"No finisher found for {eqProofType}."
    return e
  | _ =>
    throwError "Failed to apply propext while building kernel_lift equivalence proof for
      {eqProofType}."

/-- Lifts or unlifts an equality expression by transforming both sides using the registered lifting/
unlifting functions. Returns the transformed equality and a proof of equality between the original
and transformed expressions. -/
def transformEquality (getLvl : Expr → MetaM Level) (lift_ref : IO.Ref (Array liftMetadata))
    (finisher_ref : IO.Ref (Array finisherMetadata)) (eq : Expr) : MetaM (Expr × Expr) := do
  let e ← whnfR <| ← zetaReduce <| ← instantiateMVars eq
  let e := e.consumeMData
  let lvl ← getLvl eq
  let some (_, lhs, rhs) := e.eq? | throwError "Expected an equality, got: {e}."
  let (lhs_transformed, proofs) ← transformExpr lhs lvl [] lift_ref
  let (rhs_transformed, proofs) ← transformExpr rhs lvl proofs lift_ref
  let eq_transformed ← mkEq lhs_transformed rhs_transformed
  let eq_proof_type ← mkEq eq eq_transformed
  let proof ← constructProof
    eq_proof_type
    lhs rhs
    lhs_transformed rhs_transformed
    lvl
    proofs
    finisher_ref
  return (eq_transformed, proof)

end
