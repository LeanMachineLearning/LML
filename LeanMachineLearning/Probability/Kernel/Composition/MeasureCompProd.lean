/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section

open ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ η : Kernel α β}

section AbsolutelyContinuous

lemma AbsolutelyContinuous.compProd_left_apply {γ : Type*} {mγ : MeasurableSpace γ}
    [IsSFiniteKernel η] {a : α} (hac : κ a ≪ η a) (ξ : Kernel (α × β) γ) :
    (κ ⊗ₖ ξ) a ≪ (η ⊗ₖ ξ) a := by
  by_cases hκ : IsSFiniteKernel κ
  · by_cases hξ : IsSFiniteKernel ξ
    · simp_rw [Kernel.compProd_apply_eq_compProd_sectR, hac.compProd_left _]
    · simp [Kernel.compProd_of_not_isSFiniteKernel_right _ _ hξ]
  · simp [Kernel.compProd_of_not_isSFiniteKernel_left _ _ hκ]

end AbsolutelyContinuous

end MeasureTheory.Measure
