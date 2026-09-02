/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Basic

/-!
# Measurable space of kernels

-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {𝓧 𝓨 𝓩 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩}

instance instMeasurableSpaceKernel : MeasurableSpace (Kernel 𝓧 𝓨) :=
  MeasurableSpace.comap (fun κ ↦ (κ : 𝓧 → Measure 𝓨)) inferInstance

lemma measurable_kernel_iff (f : 𝓧 → Kernel 𝓨 𝓩) : Measurable f ↔ ∀ y, Measurable (f · y) := by
  unfold instMeasurableSpaceKernel
  rw [measurable_comap_iff, measurable_pi_iff]
  simp

@[fun_prop]
lemma Kernel.measurable_const : Measurable (@Kernel.const 𝓧 𝓨 m𝓧 m𝓨) := by
  rw [measurable_kernel_iff]
  simp only [const_apply]
  fun_prop

end ProbabilityTheory
