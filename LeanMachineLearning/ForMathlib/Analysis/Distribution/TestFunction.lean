/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Test functions as compactly supported continuous maps

Every member of a `TestFunctionClass` is continuous and has compact support.  This file packages
those two existing facts in the standard `CompactlySupportedContinuousMapClass` interface.
-/

@[expose] public section

namespace TestFunctionClass

variable {B E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : TopologicalSpace.Opens E} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ∞} [TestFunctionClass B Ω F n]

/-- A test-function class is, in particular, a class of compactly supported continuous maps. -/
instance instCompactlySupportedContinuousMapClass :
    CompactlySupportedContinuousMapClass B E F :=
  CompactlySupportedContinuousMapClass.mk map_hasCompactSupport

end TestFunctionClass
