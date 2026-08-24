/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.Tactic.KernelHom.Kernel.Hom

/-!
# Delaborators for simplified kernel presentations

This file implements delaborators that provide simplified pretty-printing kernel-related
categorical operations that are generated using the `kernel_hom` tactic.

To use these delaborators, simply open the `KernelHom` namespace.
-/

public meta section

open Lean Meta Elab Command PrettyPrinter Delaborator
open Lean.PrettyPrinter.Delaborator.SubExpr

namespace KernelHom

/-- Removes the `ULift` wrapper for readability. -/
@[scoped app_delab ULift]
meta def delabULift : Delab := do
  let x ← withNaryArg 0 delab
  `($x)

/-- Only display the carrier space of `SFinKer.of` for readability. -/
@[scoped app_delab SFinKer.of]
meta def delabSFinKerOf : Delab := do
  let x ← withNaryArg 0 delab
  `($x)

/-- Only display the underlying kernel of `Kernel.hom` for readability. -/
@[scoped app_delab ProbabilityTheory.Kernel.hom]
meta def delabKernelHom : Delab := do
  let x ← withNaryArg 8 delab
  `($x)

/-- Only display the underlying kernel of `Kernel.lift` for readability. -/
@[scoped app_delab ProbabilityTheory.Kernel.lift]
meta def delabKernelLift : Delab := do
  let x ← withNaryArg 10 delab
  `($x)

end KernelHom
