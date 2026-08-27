/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Batteries.Tactic.Lint.Basic
public meta import Lean.Meta.ForEachExpr

/-!
# The `extraData` linter

`LMLExtra` is a companion library of `LeanMachineLearning` with a lighter review process.
It may use everything in `LeanMachineLearning`. In the other direction, `LeanMachineLearning`
may use the *theorems* of `LMLExtra`, but must not depend on any *data* defined there:
definitions, instances, structures, inductive types, `Prop`-valued predicates...

The `extraData` environment linter enforces this. A declaration `d` outside `LMLExtra` is
flagged if a non-proof constant declared in an `LMLExtra` module occurs
* in the type of `d`, or
* if `d` is not itself a proof, in the value of `d` outside of proof subterms.

Proofs are never constrained: a proof may use any `LMLExtra` theorem, including theorems whose
statements mention `LMLExtra` definitions.

Together with the module system this gives the intended discipline: `LeanMachineLearning` files
import `LMLExtra` files *privately* (`import`, never `public import` nor `import all`; see
`scripts/check_extra_imports.sh`), so that Lean already rejects `LMLExtra` constants in public
signatures and exposed bodies, and this linter covers what the module system allows through
(non-exposed definition bodies, instances found by typeclass resolution).
-/

open Lean Meta Batteries.Tactic.Lint

namespace LeanMachineLearning.Linter

/-- The root module name of the `LMLExtra` library. -/
meta def extraRoot : Name := `LMLExtra

/-- The module in which `c` was declared (the main module for a declaration of the current
file). -/
meta def moduleOf (c : Name) : CoreM Name := do
  let env ← getEnv
  return match env.getModuleIdxFor? c with
    | some idx => env.header.moduleNames[idx]!
    | none => env.mainModule

/-- Is `c` declared in `LMLExtra` and not a proof, i.e. is its type not a proposition?
Definitions, instances, structures and their projections, inductive types and their constructors,
and `Prop`-valued predicates all qualify. Theorems do not. -/
meta def isExtraData (c : Name) : MetaM Bool := do
  unless (← moduleOf c).getRoot == extraRoot do return false
  let some ci := (← getEnv).find? c | return false
  return !(← isProp ci.type)

/-- Add to `acc` the constants occurring in `e` outside of proof subterms. -/
meta def collectDataConsts (acc : IO.Ref NameSet) (e : Expr) : MetaM Unit :=
  forEachExpr' e fun t => do
    match t with
    | .const n _ => acc.modify (·.insert n); return false
    | .app .. | .lam .. | .letE .. | .proj .. | .mdata .. =>
      -- Do not descend into proofs: what a proof mentions is irrelevant.
      return !(← try isProof t catch _ => pure false)
    | _ => return true

/-- The constants that the declaration `d` depends on as data: those occurring in its type, and,
if `d` is not itself a proof, those occurring in its value outside of proof subterms. -/
meta def dataConsts (d : Name) : MetaM NameSet := do
  let ci ← getConstInfo d
  let acc ← IO.mkRef ({} : NameSet)
  collectDataConsts acc ci.type
  unless ← isProp ci.type do
    if let some v := ci.value? then collectDataConsts acc v
  acc.get

/-- Declarations outside `LMLExtra` must not depend on data defined in `LMLExtra`.
See the module docstring of `LeanMachineLearning.Tactic.Linter.ExtraData`. -/
@[env_linter] public meta def extraData : Linter where
  noErrorsFound := "No declaration depends on `LMLExtra` data."
  errorsFound := "DECLARATIONS DEPEND ON `LMLExtra` DATA. \
    Only theorems of `LMLExtra` may be used, and only inside proofs:"
  test d := do
    -- `LMLExtra` may of course use its own definitions.
    if (← moduleOf d).getRoot == extraRoot then return none
    let bad ← (← dataConsts d).toList.filterM isExtraData
    if bad.isEmpty then return none
    return m!"depends on `LMLExtra` data: {bad.map MessageData.ofConstName}"

end LeanMachineLearning.Linter
