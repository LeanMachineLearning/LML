/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Probability.Kernel.Composition.ParallelComp

/-!
# Kernel utilities

This file provides helper lemmas for working with kernels.

## Main declarations

* `comap_parallelComp_comap`: the comap of a parallel composition is the parallel composition of
  the comaps.
* `map_parallelComp_map`: the map of a parallel composition is the parallel composition of the maps.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory

variable {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace ι]

namespace ProbabilityTheory.Kernel

lemma comap_parallelComp_comap {α₂ γ₂ : Type*} [MeasurableSpace α₂] [MeasurableSpace γ₂]
    (κ : Kernel α β) (η : Kernel γ ι) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    {f : α₂ → α} {g : γ₂ → γ} (hf : Measurable f) (hg : Measurable g) :
    κ.comap f hf ∥ₖ η.comap g hg = (κ ∥ₖ η).comap (fun a ↦ (f a.1, g a.2)) (by fun_prop) := by
  ext : 1
  rw [Kernel.parallelComp_apply, Kernel.comap_apply, Kernel.comap_apply, Kernel.comap_apply,
    Kernel.parallelComp_apply]

lemma map_parallelComp_map {β₂ ι₂ : Type*} [MeasurableSpace β₂] [MeasurableSpace ι₂]
    (κ : Kernel α β) (η : Kernel γ ι) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    {f : β → β₂} {g : ι → ι₂} (hf : Measurable f) (hg : Measurable g) :
    κ.map f ∥ₖ η.map g = (κ ∥ₖ η).map (fun a ↦ (f a.1, g a.2)) := by
  ext a s hs
  rw [Kernel.parallelComp_apply', Kernel.lintegral_map, Kernel.map_apply',
    Kernel.parallelComp_apply']
  · congr with x
    rw [Kernel.map_apply' _ (by fun_prop) _ (by measurability)]
    congr
  all_goals try fun_prop
  all_goals try measurability
  exact measurable_measure_prodMk_left hs

end ProbabilityTheory.Kernel
