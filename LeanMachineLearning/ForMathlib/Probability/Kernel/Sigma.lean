/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Sigma
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Kernels on a sigma type

`Kernel.sigma κ` is the kernel on `Σ a, β a` which is `κ a` on the fiber `β a`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α γ : Type*} {β : α → Type*} [∀ a, MeasurableSpace (β a)] {mγ : MeasurableSpace γ}

/-- The kernel on `Σ a, β a` which is `κ a` on the fiber `β a`. -/
def sigma (κ : (a : α) → Kernel (β a) γ) : Kernel (Σ a, β a) γ where
  toFun x := κ x.1 x.2
  measurable' := measurable_sigma_of_measurable_comp_mk fun a ↦ (κ a).measurable

@[simp]
lemma sigma_apply (κ : (a : α) → Kernel (β a) γ) (x : Σ a, β a) : sigma κ x = κ x.1 x.2 := rfl

lemma sigma_apply_mk (κ : (a : α) → Kernel (β a) γ) (a : α) (b : β a) :
    sigma κ ⟨a, b⟩ = κ a b := rfl

lemma comap_sigma_mk (κ : (a : α) → Kernel (β a) γ) (a : α) :
    (sigma κ).comap (Sigma.mk a) (measurable_sigma_mk a) = κ a := by
  ext b : 1
  rw [comap_apply, sigma_apply_mk]

instance (κ : (a : α) → Kernel (β a) γ) [∀ a, IsMarkovKernel (κ a)] : IsMarkovKernel (sigma κ) :=
  ⟨fun x ↦ (IsMarkovKernel.isProbabilityMeasure (κ := κ x.1) x.2)⟩

end ProbabilityTheory.Kernel
