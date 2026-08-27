/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanMachineLearning.Tactic.Linter.ExtraData

/-!
# `check_extra_data`: no `LeanMachineLearning` declaration depends on `LMLExtra` data

Standalone driver, for CI, of the check performed by the `extraData` environment linter
(see `LeanMachineLearning/Tactic/Linter/ExtraData.lean`).

Unlike `lake lint`, it does not honor `@[nolint extraData]`: there is no legitimate exception to
this rule (move the definition to `LeanMachineLearning` instead), and an attribute can be added by
a metaprogram without appearing in the source.

Usage: `lake env lean --run scripts/check_extra_data.lean [Module ...]`, default
`LeanMachineLearning`. The given modules are imported and every constant declared in a module with
the same root as one of them is checked. Exits with code 1 if a violation is found.
-/

open Lean Meta LeanMachineLearning.Linter

/-- The constants declared in a module whose root is in `roots` that depend on `LMLExtra` data,
with the data they depend on. -/
def findViolations (roots : List Name) : MetaM (Array (Name × List Name)) := do
  let mut bad := #[]
  for (c, _) in (← getEnv).constants.map₁ do
    let root := (← moduleOf c).getRoot
    if root == extraRoot || !roots.contains root then continue
    let deps ← (← dataConsts c).toList.filterM isExtraData
    unless deps.isEmpty do bad := bad.push (c, deps)
  return bad.qsort (·.1.toString < ·.1.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let modules := if args.isEmpty then [`LeanMachineLearning] else args.map String.toName
  let roots := modules.map Name.getRoot
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map ({ module := · })).toArray {} (trustLevel := 1024)
    (loadExts := true)
  let ctx : Core.Context := { fileName := "<check_extra_data>", fileMap := default }
  let (bad, _) ← (findViolations roots).run'.toIO ctx { env }
  if bad.isEmpty then
    IO.println s!"OK: no declaration of {roots} depends on LMLExtra data."
    return 0
  IO.eprintln s!"error: {bad.size} declaration(s) depend on LMLExtra data \
    (definitions, instances, predicates...). Only theorems of LMLExtra may be used, in proofs."
  for (c, deps) in bad do
    IO.eprintln s!"  {c}: {deps}"
  return 1
