/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Measurability of sums with a variable number of terms

## Main statements

* `measurable_sum_range`, `measurable_sum_Icc`: `a ↦ ∑ i ∈ range (g a), f i a` and
  `a ↦ ∑ i ∈ Icc 1 (g a), f i a` are measurable when `g : α → ℕ` and all the `f i` are.
-/

@[expose] public section

open Finset

variable {α M : Type*} {mα : MeasurableSpace α} [AddCommMonoid M] [MeasurableSpace M]
  [MeasurableAdd₂ M]

/-- `a ↦ ∑ i ∈ range (g a), f i a` is measurable when `g : α → ℕ` and all the `f i` are. -/
lemma measurable_sum_range {f : ℕ → α → M} {g : α → ℕ} (hf : ∀ i, Measurable (f i))
    (hg : Measurable g) :
    Measurable (fun a ↦ ∑ i ∈ range (g a), f i a) :=
  (measurable_from_prod_countable_left (f := fun p : α × ℕ ↦ ∑ i ∈ range p.2, f i p.1)
    fun n ↦ Finset.measurable_sum (range n) fun i _ ↦ hf i).comp (measurable_id.prodMk hg)

/-- `a ↦ ∑ i ∈ Icc 1 (g a), f i a` is measurable when `g : α → ℕ` and all the `f i` are. -/
lemma measurable_sum_Icc {f : ℕ → α → M} {g : α → ℕ} (hf : ∀ i, Measurable (f i))
    (hg : Measurable g) :
    Measurable (fun a ↦ ∑ i ∈ Icc 1 (g a), f i a) :=
  (measurable_from_prod_countable_left (f := fun p : α × ℕ ↦ ∑ i ∈ Icc 1 p.2, f i p.1)
    fun n ↦ Finset.measurable_sum (Icc 1 n) fun i _ ↦ hf i).comp (measurable_id.prodMk hg)
