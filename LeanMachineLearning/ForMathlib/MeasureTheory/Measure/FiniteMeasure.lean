/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.SubFinite

/-!
# Order structure on finite measures

We equip `FiniteMeasure α` with the partial order and the truncated subtraction of the underlying
measures, which makes it a canonically ordered additive monoid with ordered subtraction.

## Main statements

* `FiniteMeasure.ext_iff_coe`, `FiniteMeasure.le_iff_coe`: equality and order of finite measures
  are those of the underlying measures.
* `FiniteMeasure.toMeasure_sub`: the subtraction of finite measures is that of the underlying
  measures.
-/

@[expose] public section

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

lemma FiniteMeasure.ext_iff_coe {μ ν : FiniteMeasure α} :
    μ = ν ↔ (μ : Measure α) = ν := Subtype.ext_iff

instance FiniteMeasure.instPartialOrder : PartialOrder (FiniteMeasure α) :=
  PartialOrder.lift _ FiniteMeasure.toMeasure_injective

lemma FiniteMeasure.le_iff_coe {μ ν : FiniteMeasure α} :
    μ ≤ ν ↔ (μ : Measure α) ≤ (ν : Measure α) := Iff.rfl

noncomputable
instance FiniteMeasure.instSub : Sub (FiniteMeasure α) :=
  ⟨fun μ ν ↦ ⟨μ.toMeasure - ν.toMeasure, inferInstance⟩⟩

lemma FiniteMeasure.sub_def (μ ν : FiniteMeasure α) :
    μ - ν = ⟨μ.toMeasure - ν.toMeasure, inferInstance⟩ :=
  rfl

@[simp, norm_cast]
lemma FiniteMeasure.toMeasure_sub (μ ν : FiniteMeasure α) : ↑(μ - ν) = (↑μ - ↑ν : Measure α) :=
  rfl

instance FiniteMeasure.instCanonicallyOrderedAdd : CanonicallyOrderedAdd (FiniteMeasure α) where
  le_add_self μ ν := fun s ↦ by simp
  exists_add_of_le {μ ν} hμν := by
    refine ⟨ν - μ, ?_⟩
    rw [FiniteMeasure.ext_iff_coe]
    simp only [FiniteMeasure.toMeasure_add, FiniteMeasure.toMeasure_sub]
    rw [add_comm, Measure.sub_add_cancel_of_le hμν]
  le_self_add μ ν := by
    simp only [FiniteMeasure.le_iff_coe, FiniteMeasure.toMeasure_add]
    exact Measure.le_add_right le_rfl

instance FiniteMeasure.instOrderedSub : OrderedSub (FiniteMeasure α) where
  tsub_le_iff_right μ ν ξ := by
    simp only [FiniteMeasure.le_iff_coe, FiniteMeasure.toMeasure_sub, FiniteMeasure.toMeasure_add]
    exact Measure.sub_le_iff_le_add

end MeasureTheory
