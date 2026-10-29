/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Lemmas about almost everywhere measurable functions

## Main statements

* `ae_eq_of_map_prodMk_eq`: if the joint laws of `(X, Y)` and `(X, f ∘ X)` are equal, then
  `Y = f ∘ X` almost everywhere.
-/

@[expose] public section

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

lemma ae_eq_of_map_prodMk_eq {β Ω : Type*} {_ : MeasurableSpace β} {_ : MeasurableSpace Ω}
    [MeasurableEq Ω] {X : α → β} {Y : α → Ω} {f : β → Ω} (hf : Measurable f) (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (h : μ.map (fun ω ↦ (X ω, Y ω)) = μ.map (fun ω ↦ (X ω, f (X ω)))) :
    Y =ᵐ[μ] f ∘ X := by
  have hp : ∀ᵐ p ∂μ.map (fun ω ↦ (X ω, f (X ω))), p.2 = f p.1 :=
    (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2 (by simp)
  exact ae_of_ae_map (by fun_prop) (h ▸ hp)

end MeasureTheory
