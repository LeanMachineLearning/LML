/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Measurability of functions on a sigma type

A function on `Σ a, β a` is measurable as soon as each of its restrictions `f ∘ Sigma.mk a` is.
-/

@[expose] public section

open MeasurableSpace

variable {α γ : Type*} {β : α → Type*} [∀ a, MeasurableSpace (β a)] [MeasurableSpace γ]

@[fun_prop]
lemma measurable_sigma_mk (a : α) : Measurable (Sigma.mk a : β a → Σ a, β a) :=
  fun _ hs ↦ measurableSet_iInf.1 hs a

/-- A function on a sigma type is measurable if all its restrictions to the fibers are. -/
lemma measurable_sigma_of_measurable_comp_mk {f : (Σ a, β a) → γ}
    (h : ∀ a, Measurable (f ∘ Sigma.mk a)) : Measurable f :=
  fun _ hs ↦ measurableSet_iInf.2 fun a ↦ (h a) hs

/-- A set in a sigma type is measurable iff its trace on every fiber is. -/
lemma measurableSet_sigma_iff {s : Set (Σ a, β a)} :
    MeasurableSet s ↔ ∀ a, MeasurableSet (Sigma.mk a ⁻¹' s) :=
  measurableSet_iInf

lemma measurable_sigma_iff {f : (Σ a, β a) → γ} :
    Measurable f ↔ ∀ a, Measurable (f ∘ Sigma.mk a) :=
  ⟨fun hf a ↦ hf.comp (measurable_sigma_mk a), measurable_sigma_of_measurable_comp_mk⟩

/-- The first projection of a sigma type is measurable (it is constant on every fiber). -/
lemma measurable_sigma_fst [MeasurableSpace α] : Measurable (Sigma.fst : (Σ a, β a) → α) :=
  measurable_sigma_of_measurable_comp_mk fun _ ↦ measurable_const

/-- `x ↦ ⟨n x, f (n x) x⟩` is measurable when the index `n x` ranges over a countable type with
measurable singletons and each `f i` is measurable. -/
lemma Measurable.sigmaMk [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {n : γ → α} (hn : Measurable n) {f : (a : α) → γ → β a} (hf : ∀ a, Measurable (f a)) :
    Measurable fun x ↦ (⟨n x, f (n x) x⟩ : Σ a, β a) := by
  intro s hs
  have : (fun x ↦ (⟨n x, f (n x) x⟩ : Σ a, β a)) ⁻¹' s =
      ⋃ a, n ⁻¹' {a} ∩ f a ⁻¹' (Sigma.mk a ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨n x, rfl, h⟩
    · rintro ⟨a, rfl, h⟩
      exact h
  rw [this]
  exact MeasurableSet.iUnion fun a ↦
    (hn (measurableSet_singleton a)).inter (hf a (measurableSet_sigma_iff.1 hs a))

/-- `Sigma.mk a` is a measurable embedding. -/
lemma measurableEmbedding_sigma_mk (a : α) :
    MeasurableEmbedding (Sigma.mk a : β a → Σ a, β a) where
  injective := sigma_mk_injective
  measurable := measurable_sigma_mk a
  measurableSet_image' s hs := by
    rw [measurableSet_sigma_iff]
    intro b
    by_cases hab : a = b
    · subst hab
      rwa [sigma_mk_preimage_image_eq_self]
    · rw [sigma_mk_preimage_image' hab]
      exact MeasurableSet.empty
