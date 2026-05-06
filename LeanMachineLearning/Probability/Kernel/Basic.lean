/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Basic

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Two deterministic kernels are equal if and only if their underlying functions are equal. -/
@[simp]
lemma deterministic_inj [MeasurableSpace.SeparatesPoints β]
    {f g : α → β} {hf : Measurable f} {hg : Measurable g} :
    Kernel.deterministic f hf = Kernel.deterministic g hg ↔ f = g := by
  simp [Kernel.ext_iff, Kernel.deterministic_apply, dirac_eq_dirac_iff, funext_iff]

end ProbabilityTheory.Kernel
