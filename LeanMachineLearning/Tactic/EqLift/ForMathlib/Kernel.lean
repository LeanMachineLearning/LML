/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Probability.Kernel.Deterministic

/-!
# Kernel utilities

This file provides helper lemmas for working with kernels.

## Main declarations

* `comap_parallelComp_comap`: the comap of a parallel composition is the parallel composition of
  the comaps.
* `map_parallelComp_map`: the map of a parallel composition is the parallel composition of the maps.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory ENNReal Set

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

instance (κ : Kernel α β) [IsDeterministic κ] : IsSFiniteKernel κ := by
  by_contra
  have : ∀ C < ∞, ∃ a, C < (κ a) univ := by
    by_contra! h
    have : IsFiniteKernel κ := ⟨h⟩
    have : IsSFiniteKernel κ := inferInstance
    contradiction
  obtain ⟨a, ha⟩ := this 0 (by simp)
  have h := DFunLike.congr_fun κ.parallelComp_self_comp_copy a
  simp_all only [not_false_eq_true, parallelComp_of_not_isSFiniteKernel_left, zero_comp, zero_apply]
  replace h := DFunLike.congr_fun h Set.univ
  rw [comp_apply'] at h
  · simp_rw [copy_apply, Measure.dirac_apply' _ MeasurableSet.univ, indicator_univ] at h
    simp only [Measure.coe_zero, Pi.zero_apply, Pi.one_apply, MeasureTheory.lintegral_const,
      one_mul] at h
    exact ha.ne h
  exact MeasurableSet.univ

end ProbabilityTheory.Kernel
