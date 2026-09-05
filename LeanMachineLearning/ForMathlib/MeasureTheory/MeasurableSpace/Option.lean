/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# The measurable space structure on `Option α`

`Option α` is the disjoint union of `α` and the singleton `{none}`: a set of `Option α` is
measurable if and only if its preimage under `Option.some` is measurable. Equivalently, a function
out of `Option α` is measurable if and only if its restriction to `α` is.
-/

@[expose] public section

/-- The measurable space structure on `Option α`, in which a set is measurable if and only if its
preimage under `Option.some` is measurable. This makes `Option α` the disjoint union of `α` and the
measurable atom `{none}`. -/
instance Option.instMeasurableSpace {α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Option α) where
  MeasurableSet' s := MeasurableSet (Option.some ⁻¹' s)
  measurableSet_empty := by simp
  measurableSet_compl s hs := by
    rw [Set.preimage_compl]
    exact hs.compl
  measurableSet_iUnion f hf := by
    rw [Set.preimage_iUnion]
    exact MeasurableSet.iUnion hf

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma measurableSet_option_iff {s : Set (Option α)} :
    MeasurableSet s ↔ MeasurableSet (Option.some ⁻¹' s) := Iff.rfl

/-- A function out of `Option α` is measurable if and only if its restriction along `Option.some`
is measurable: no condition is imposed at `none`. -/
lemma measurable_option_iff {f : Option α → β} : Measurable f ↔ Measurable (f ∘ Option.some) :=
  Iff.rfl

@[fun_prop]
lemma measurable_some : Measurable (Option.some : α → Option α) := fun _ hs ↦ hs

lemma measurableEmbedding_some : MeasurableEmbedding (Option.some : α → Option α) where
  injective := Option.some_injective α
  measurable := measurable_some
  measurableSet_image' s hs := by
    rw [measurableSet_option_iff, Set.preimage_image_eq _ (Option.some_injective α)]
    exact hs

@[simp]
lemma measurableSet_singleton_none : MeasurableSet ({none} : Set (Option α)) := by
  rw [measurableSet_option_iff, Set.preimage_singleton_eq_empty.2 (by simp)]
  exact MeasurableSet.empty
