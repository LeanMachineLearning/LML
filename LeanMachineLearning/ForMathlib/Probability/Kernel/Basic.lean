/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.Dirac
public import Mathlib.Probability.Kernel.Basic

/-! # Basic lemmas about kernels
-/

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

/-- Every Markov kernel with a subsingleton codomain is a constant kernel at a Dirac mass. -/
lemma eq_const_dirac_of_subsingleton [Subsingleton β] (κ : Kernel α β) [IsMarkovKernel κ] (y : β) :
    κ = Kernel.const α (Measure.dirac y) := by
  ext a : 1
  rw [Kernel.const_apply]
  exact (κ a).eq_dirac_of_subsingleton y

end ProbabilityTheory.Kernel
