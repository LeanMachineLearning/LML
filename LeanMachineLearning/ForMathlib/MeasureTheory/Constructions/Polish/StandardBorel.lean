/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Properties of standard Borel spaces
-/

@[expose] public section

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

instance [StandardBorelSpace Ω] : MeasurableEq Ω := by
  letI := upgradeStandardBorel Ω
  infer_instance
