/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Normed.Group.Basic

@[expose] public section

open ENNReal Filter

open scoped Topology

lemma ENNReal.tendsto_zero_le {α : Type*} {f g : α → ℝ≥0∞} {ι : Filter α}
    (hg : Tendsto g ι (𝓝 0)) (h : f ≤ g) : Tendsto f ι (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ ↦ 0) tendsto_const_nhds hg ?_ h
  intro
  simp
