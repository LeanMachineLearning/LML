/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Process.HittingTime

/-!
# Hitting times
-/

@[expose] public section

namespace MeasureTheory

variable {Ω β ι : Type*} [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
  {u : ι → Ω → β} {s : Set β} {n i : ι} {ω : Ω}

lemma hittingAfter_eq_coe_iff :
    hittingAfter u s n ω = i ↔ n ≤ i ∧ u i ω ∈ s ∧ ∀ j ∈ Set.Ico n i, u j ω ∉ s := by
  constructor
  · intro h
    have h_le := le_hittingAfter (u := u) (s := s) (n := n) ω
    have h_mem := hittingAfter_mem_set_of_ne_top (u := u) (s := s) (n := n) (ω := ω) (by simp [h])
    rw [h] at h_le h_mem
    exact ⟨mod_cast h_le, h_mem,
      fun j hj ↦ notMem_of_lt_hittingAfter (h ▸ mod_cast hj.2) hj.1⟩
  · rintro ⟨hni, his, h⟩
    refine le_antisymm (hittingAfter_le_of_mem hni his) (not_lt.1 fun hlt ↦ ?_)
    obtain ⟨j, hj, hjs⟩ := hittingAfter_lt_iff.1 hlt
    exact h j hj hjs

end MeasureTheory
