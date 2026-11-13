/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.SubFinite

/-!
# Lemmas about the Lebesgue decomposition

## Main statements

* `Measure.sub_apply_eq_rnDeriv_add_singularPart`: for finite measures,
  `(μ - ν) s = ν.withDensity (μ.rnDeriv ν - 1) s + μ.singularPart ν s`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

lemma sub_apply_eq_rnDeriv_add_singularPart [IsFiniteMeasure μ] [IsFiniteMeasure ν] (s : Set α) :
    (μ - ν) s = ν.withDensity (fun a ↦ μ.rnDeriv ν a - 1) s + μ.singularPart ν s := by
  have hμ : μ = ν.withDensity (fun a ↦ μ.rnDeriv ν a) + μ.singularPart ν := by
    rw [rnDeriv_add_singularPart]
  have hν : ν = ν.withDensity 1 := by rw [withDensity_one]
  conv_lhs => rw [hν, hμ, add_comm _ (μ.singularPart ν)]
  rw [← add_sub_of_mutuallySingular]
  swap
  · simp only [withDensity_one]
    exact mutuallySingular_singularPart μ ν
  simp only [FunLike.coe_add, Pi.add_apply]
  have : IsFiniteMeasure (ν.withDensity 1) := by simp only [withDensity_one]; infer_instance
  rw [add_comm, ← withDensity_sub (by fun_prop) (by fun_prop)]
  congr

end MeasureTheory.Measure
