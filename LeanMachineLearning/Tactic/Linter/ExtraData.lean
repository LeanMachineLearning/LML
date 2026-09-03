/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Batteries.Tactic.Lint.Basic
public meta import Lean.Compiler.ImplementedByAttr
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
* if `d` is not itself a proof, in the value of `d` outside of proof subterms (the body of an
  `opaque` counts as its value, and so does the target of an `@[implemented_by]` attribute: both
  are what the compiled code of `d` runs).

The linter is applied to every constant of the environment, including private and automatically
generated ones (structure field defaults, `match` auxiliaries, `_unsafe_rec` of `partial` defs,
`where` auxiliaries...): a violation is reported on the constant that mentions the `LMLExtra`
data, so it cannot be laundered through an unlinted helper.

Proofs are never constrained: a proof may use any `LMLExtra` theorem, including theorems whose
statements mention `LMLExtra` definitions.

`scripts/check_extra_data.lean` runs the same check in CI, ignoring `@[nolint extraData]`: an
attribute can be added by a metaprogram (of `LMLExtra`, since a plain `import` already runs the
macros and elaborators of the imported module) without appearing in the source, and there is no
legitimate exception to the rule anyway.

Together with the module system this gives the intended discipline: `LeanMachineLearning` files
import `LMLExtra` files *privately* (`import`, never `public import` nor `import all`; see
`scripts/check_extra_imports.sh`), so that Lean already rejects `LMLExtra` constants in public
signatures and exposed bodies, and this linter covers what the module system allows through
(non-exposed definition bodies, instances found by typeclass resolution).
-/

open Lean Meta Batteries.Tactic.Lint

namespace LeanMachineLearning.Linter

/-- The root module name of the `LMLExtra` library. -/
public meta def extraRoot : Name := `LMLExtra

/-- The module in which `c` was declared (the main module for a declaration of the current
file). -/
public meta def moduleOf (c : Name) : CoreM Name := do
  let env ← getEnv
  return match env.getModuleIdxFor? c with
    | some idx => env.header.moduleNames[idx]!
    | none => env.mainModule

/-- Is `c` declared in `LMLExtra` and not a proof, i.e. is its type not a proposition?
Definitions, instances, structures and their projections, inductive types and their constructors,
and `Prop`-valued predicates all qualify. Theorems do not. -/
public meta def isExtraData (c : Name) : MetaM Bool := do
  unless (← moduleOf c).getRoot == extraRoot do return false
  let some ci := (← getEnv).find? c | return false
  return !(← isProp ci.type)

/-- Add to `acc` the constants occurring in `e` outside of proof subterms. -/
public meta def collectDataConsts (acc : IO.Ref NameSet) (e : Expr) : MetaM Unit :=
  forEachExpr' e fun t => do
    match t with
    | .const n _ => acc.modify (·.insert n); return false
    | .app .. | .lam .. | .letE .. | .proj .. | .mdata .. =>
      -- Do not descend into proofs: what a proof mentions is irrelevant.
      return !(← try isProof t catch _ => pure false)
    | _ => return true

/-- The constants that the declaration `d` depends on as data: those occurring in its type, and,
if `d` is not itself a proof, those occurring in its value outside of proof subterms, as well as
the target of an `@[implemented_by]` attribute on `d`. -/
public meta def dataConsts (d : Name) : MetaM NameSet := do
  let ci ← getConstInfo d
  let acc ← IO.mkRef ({} : NameSet)
  collectDataConsts acc ci.type
  unless ← isProp ci.type do
    -- The body of an `opaque` is not unfoldable, but it is what its compiled code runs.
    if let some v := ci.value? (allowOpaque := true) then collectDataConsts acc v
    -- `@[implemented_by impl] def d` replaces the compiled code of `d` by that of `impl`.
    if let some impl := Compiler.implementedByAttr.getParam? (← getEnv) d then
      acc.modify (·.insert impl)
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
