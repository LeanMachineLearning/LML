/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! # Lemmas about measure composition-product
-/

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

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

/-- Recording a measurable function of a draw: mapping a kernel to the graph of `f` is the
composition-product of that kernel with the deterministic kernel given by `f`. This is how an
algorithm announces a variable that it then uses deterministically. -/
lemma map_graph (κ : Kernel α β) [IsSFiniteKernel κ] {f : β → γ} (hf : Measurable f) :
    κ.map (fun b ↦ (b, f b))
      = κ ⊗ₖ Kernel.deterministic (fun p : α × β ↦ f p.2) (by fun_prop) := by
  ext a : 1
  have h_sectR : (Kernel.deterministic (fun p : α × β ↦ f p.2) (by fun_prop)).sectR a
      = Kernel.deterministic f hf := by
    ext b : 1
    rw [Kernel.sectR_apply, Kernel.deterministic_apply, Kernel.deterministic_apply]
  rw [Kernel.map_apply _ (by fun_prop), Kernel.compProd_apply_eq_compProd_sectR, h_sectR,
    MeasureTheory.Measure.compProd_deterministic]

end ProbabilityTheory.Kernel
