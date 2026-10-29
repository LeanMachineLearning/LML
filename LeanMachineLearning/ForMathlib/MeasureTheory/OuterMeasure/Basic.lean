/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Basic

/-!
# Null sets of a measure charging every singleton
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

section OuterMeasureClass

variable {α F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α]
  {μ : F} {s : Set α}

/-- For a measure that charges every singleton, the only null set is the empty set. -/
lemma measure_null_iff_eq_empty_of_measure_singleton_ne_zero (h : ∀ a, μ {a} ≠ 0) :
    μ s = 0 ↔ s = ∅ := by
  refine ⟨fun hs ↦ ?_, fun he ↦ by simp [he]⟩
  apply Set.eq_empty_of_forall_notMem
  exact fun a ha ↦ h a (measure_mono_null (Set.singleton_subset_iff.mpr ha) hs)

end OuterMeasureClass

end MeasureTheory
