/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Dirac measures on a subsingleton

On a subsingleton, every probability measure is a Dirac mass.
-/

@[expose] public section

namespace MeasureTheory.Measure

/-- On a subsingleton, every probability measure is a Dirac mass. -/
lemma eq_dirac_of_subsingleton {α : Type*} {mα : MeasurableSpace α}
    [Subsingleton α] (μ : Measure α) [IsProbabilityMeasure μ] (x : α) :
    μ = Measure.dirac x := by
  ext s hs
  rcases Set.eq_empty_or_nonempty s with rfl | ⟨y, hy⟩
  · simp
  · rw [Set.eq_univ_of_forall (s := s) fun z ↦ by rwa [Subsingleton.elim z y]]
    simp

end MeasureTheory.Measure
