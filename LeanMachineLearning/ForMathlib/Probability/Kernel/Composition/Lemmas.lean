/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.Lemmas

/-! # Lemmas about compositions of kernels and measures

## Main statements

* `Kernel.compProd_prodMkLeft_apply`: `(ξ ⊗ₖ κ.prodMkLeft α) a = ξ a ⊗ₘ κ`.
* `Measure.map_compProd_comap`: transporting `μ ⊗ₘ η.comap f` along `f` in the first coordinate
  gives `μ.map f ⊗ₘ η`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

lemma compProd_prodMkLeft_apply (ξ : Kernel α β) [IsSFiniteKernel ξ]
    (κ : Kernel β γ) [IsSFiniteKernel κ] (a : α) :
    (ξ ⊗ₖ Kernel.prodMkLeft α κ) a = ξ a ⊗ₘ κ := by
  ext s hs
  rw [Kernel.compProd_apply hs, Measure.compProd_apply hs]
  simp [Kernel.prodMkLeft_apply]

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

/-- Transporting `μ ⊗ₘ η.comap f` along `f` in the first coordinate gives `μ.map f ⊗ₘ η`. -/
lemma map_compProd_comap (μ : Measure α) [SFinite μ]
    (η : Kernel β γ) [IsSFiniteKernel η] {f : α → β} (hf : Measurable f) :
    (μ ⊗ₘ η.comap f hf).map (fun p : α × γ ↦ (f p.1, p.2)) = μ.map f ⊗ₘ η := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.compProd_apply (hs.preimage (by fun_prop)),
    Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

end MeasureTheory.Measure
