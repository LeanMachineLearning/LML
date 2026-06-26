/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability lemmas
-/

@[expose] public section

open Finset

namespace MeasureTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ : Measure α}

lemma measurable_comp_comap (f : α → β) {g : β → γ} (hg : Measurable g) :
    Measurable[mβ.comap f] (g ∘ f) := by
  rw [measurable_iff_comap_le, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hg.comap_le

@[fun_prop]
lemma Measurable.coe_nat_enat {f : α → ℕ} (hf : Measurable f) :
    Measurable (fun a ↦ (f a : ℕ∞)) := Measurable.comp (by fun_prop) hf

@[fun_prop]
lemma Measurable.toNat {f : α → ℕ∞} (hf : Measurable f) : Measurable (fun a ↦ (f a).toNat) :=
  Measurable.comp (by fun_prop) hf

lemma measurable_sum_range_of_le {f : ℕ → α → ℝ} {g : α → ℕ} {n : ℕ}
    (hg_le : ∀ a, g a ≤ n) (hf : ∀ i, Measurable (f i)) (hg : Measurable g) :
    Measurable (fun a ↦ ∑ i ∈ range (g a), f i a) := by
  have h_eq : (fun a ↦ ∑ i ∈ range (g a), f i a)
      = fun a ↦ ∑ i ∈ range (n + 1), if g a = i then ∑ j ∈ range i, f j a else 0 := by
    ext ω
    rw [sum_ite_eq_of_mem]
    grind
  rw [h_eq]
  refine measurable_sum _ fun n hn ↦ ?_
  refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
  exact (measurableSet_singleton _).preimage (by fun_prop)

lemma measurable_sum_Icc_of_le {f : ℕ → α → ℝ} {g : α → ℕ} {n : ℕ}
    (hg_le : ∀ a, g a ≤ n) (hf : ∀ i, Measurable (f i)) (hg : Measurable g) :
    Measurable (fun a ↦ ∑ i ∈ Icc 1 (g a), f i a) := by
  have h_eq : (fun a ↦ ∑ i ∈ Icc 1 (g a), f i a)
      = fun a ↦ ∑ i ∈ range (n + 1), if g a = i then ∑ j ∈ Icc 1 i, f j a else 0 := by
    ext ω
    rw [sum_ite_eq_of_mem]
    grind
  rw [h_eq]
  refine measurable_sum _ fun n hn ↦ ?_
  refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
  exact (measurableSet_singleton _).preimage (by fun_prop)

end MeasureTheory
