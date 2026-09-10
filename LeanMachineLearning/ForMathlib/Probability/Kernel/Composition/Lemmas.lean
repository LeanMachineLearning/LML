/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.Lemmas

/-! # Lemmas about composition of kernel
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

lemma compProd_prodMkLeft_apply (ξ : Kernel α β) [IsSFiniteKernel ξ]
    (κ : Kernel β γ) [IsSFiniteKernel κ] (a : α) :
    (ξ ⊗ₖ Kernel.prodMkLeft α κ) a = ξ a ⊗ₘ κ := by
  ext s hs
  rw [Kernel.compProd_apply hs, Measure.compProd_apply hs]
  simp [Kernel.prodMkLeft_apply]

end ProbabilityTheory.Kernel
