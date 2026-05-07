/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MapComap

@[expose] public section

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

@[simp]
lemma prodMkLeft_inj [h_nonempty : Nonempty γ]
    (κ ν : Kernel α β) :
    κ.prodMkLeft γ = ν.prodMkLeft γ ↔ κ = ν := by
  simp only [Kernel.ext_iff, Kernel.prodMkLeft_apply, Prod.forall]
  exact ⟨fun h b ↦ h h_nonempty.some b, fun h _ b ↦ h b⟩

@[simp]
lemma prodMkRight_inj [h_nonempty : Nonempty γ]
    (κ ν : Kernel α β) :
    κ.prodMkRight γ = ν.prodMkRight γ ↔ κ = ν := by
  simp only [Kernel.ext_iff, Kernel.prodMkRight_apply, Prod.forall]
  exact ⟨fun h a ↦ h a h_nonempty.some, fun h a _ ↦ h a⟩

@[simp]
lemma prodMkLeft_deterministic {f : α → β} (hf : Measurable f) :
    (Kernel.deterministic f hf).prodMkLeft γ =
      Kernel.deterministic (fun p ↦ f p.2) (by fun_prop) := by
  ext
  simp [Kernel.deterministic_apply]

@[simp]
lemma prodMkRight_deterministic {f : α → β} (hf : Measurable f) :
    (Kernel.deterministic f hf).prodMkRight γ =
      Kernel.deterministic (fun p ↦ f p.1) (by fun_prop) := by
  ext
  simp [Kernel.deterministic_apply]

end ProbabilityTheory.Kernel
