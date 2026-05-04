/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Basic

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

section OuterMeasureClass

variable {α F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α]
  {μ : F} {s : Set α}

lemma measure_null_iff_eq_empty_of_measure_singleton_ne_zero (h : ∀ a, μ {a} ≠ 0) :
    μ s = 0 ↔ s = ∅ := by
  refine ⟨fun hs ↦ ?_, fun he ↦ by simp [he]⟩
  apply Set.eq_empty_of_forall_notMem
  exact fun a ha ↦ h a (measure_mono_null (Set.singleton_subset_iff.mpr ha) hs)

end OuterMeasureClass

end MeasureTheory
