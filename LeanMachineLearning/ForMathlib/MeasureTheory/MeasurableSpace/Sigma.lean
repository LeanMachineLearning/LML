/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map

/-!
# Measurability of functions on a sigma type

We develop the API of the σ-algebra `Sigma.instMeasurableSpace` on `Σ a, β a`, the finest one
making all the injections `Sigma.mk a` measurable.

## Main statements

* `measurableSet_sigma_iff`: a set is measurable iff all its traces on the fibers are.
* `measurable_sigma_iff`: a function on `Σ a, β a` is measurable iff all its restrictions
  `f ∘ Sigma.mk a` are.
* `measurableEmbedding_sigmaMk`: `Sigma.mk a` is a measurable embedding.
* `Measurable.sigmaMk`: `x ↦ ⟨n x, f (n x) x⟩` is measurable when the index ranges over a countable
  type.

We also record measurability facts about the first projection of `Σ n : ℕ, X n`.
-/

@[expose] public section

open MeasurableSpace MeasureTheory

variable {α γ : Type*} {β : α → Type*} [∀ a, MeasurableSpace (β a)] [MeasurableSpace γ]

/-- A set in a sigma type is measurable iff its trace on every fiber is. -/
lemma measurableSet_sigma_iff {s : Set (Σ a, β a)} :
    MeasurableSet s ↔ ∀ a, MeasurableSet (Sigma.mk a ⁻¹' s) :=
  measurableSet_iInf

/-- The injection `Sigma.mk a` of a fiber into a sigma type is measurable. -/
@[fun_prop]
lemma measurable_sigmaMk (a : α) : Measurable (Sigma.mk a : β a → Σ a, β a) :=
  fun _ hs ↦ measurableSet_sigma_iff.1 hs a

/-- A function on a sigma type is measurable if all its restrictions to the fibers are. -/
lemma measurable_sigma {f : (Σ a, β a) → γ} (h : ∀ a, Measurable (f ∘ Sigma.mk a)) :
    Measurable f :=
  fun _ hs ↦ measurableSet_sigma_iff.2 fun a ↦ (h a) hs

/-- A function on a sigma type is measurable iff all its restrictions to the fibers are. -/
lemma measurable_sigma_iff {f : (Σ a, β a) → γ} :
    Measurable f ↔ ∀ a, Measurable (f ∘ Sigma.mk a) :=
  ⟨fun hf a ↦ hf.comp (measurable_sigmaMk a), measurable_sigma⟩

/-- The first projection of a sigma type is measurable (it is constant on every fiber). -/
lemma measurable_sigma_fst [MeasurableSpace α] : Measurable (Sigma.fst : (Σ a, β a) → α) :=
  measurable_sigma fun _ ↦ measurable_const

/-- `x ↦ ⟨n x, f (n x) x⟩` is measurable when the index `n x` ranges over a countable type with
measurable singletons and each `f i` is measurable. -/
@[fun_prop]
lemma Measurable.sigmaMk [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {n : γ → α} (hn : Measurable n) {f : (a : α) → γ → β a} (hf : ∀ a, Measurable (f a)) :
    Measurable fun x ↦ (⟨n x, f (n x) x⟩ : Σ a, β a) :=
  (measurable_from_prod_countable_left (f := fun p : γ × α ↦ (⟨p.2, f p.2 p.1⟩ : Σ a, β a))
    fun a ↦ (measurable_sigmaMk a).comp (hf a)).comp (measurable_id.prodMk hn)

/-- `Sigma.mk a` is a measurable embedding. -/
lemma measurableEmbedding_sigmaMk (a : α) :
    MeasurableEmbedding (Sigma.mk a : β a → Σ a, β a) where
  injective := sigma_mk_injective
  measurable := measurable_sigmaMk a
  measurableSet_image' s hs := by
    rw [measurableSet_sigma_iff]
    intro b
    by_cases hab : a = b
    · subst hab
      rwa [sigma_mk_preimage_image_eq_self]
    · rw [sigma_mk_preimage_image' hab]
      exact MeasurableSet.empty

section Nat

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] {M : ℕ}

/-- The set of elements of `Σ n : ℕ, X n` with first component at most `M` is measurable. -/
lemma measurableSet_sigma_fst_le (M : ℕ) : MeasurableSet {x : Σ n, X n | x.1 ≤ M} :=
  measurable_sigma_fst (MeasurableSet.of_discrete (s := Set.Iic M))

/-- The set of elements of `Σ n : ℕ, X n` with first component less than `M` is measurable. -/
lemma measurableSet_sigma_fst_lt (M : ℕ) : MeasurableSet {x : Σ n, X n | x.1 < M} :=
  measurable_sigma_fst (MeasurableSet.of_discrete (s := Set.Iio M))

/-- The image of a measure on `X (M + 1)` by `Sigma.mk (M + 1)` gives measure zero to the elements
of `Σ n : ℕ, X n` with first component at most `M`. -/
lemma MeasureTheory.Measure.map_sigmaMk_succ_apply_fst_le (μ : Measure (X (M + 1))) :
    (μ.map (Sigma.mk (M + 1))) {x : Σ n, X n | x.1 ≤ M} = 0 := by
  rw [Measure.map_apply (measurable_sigmaMk (M + 1)) (measurableSet_sigma_fst_le M)]
  have : Sigma.mk (M + 1) ⁻¹' {x : Σ n, X n | x.1 ≤ M} = ∅ := by
    ext x
    simp
  rw [this, measure_empty]

end Nat
