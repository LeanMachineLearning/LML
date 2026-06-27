/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.Lattice
public import Mathlib.CategoryTheory.Countable
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Order.CompletePartialOrder

/-! # Argmax and argmin functions on finite sets

We prove in particular that those functions are measurable.

-/

@[expose] public section

open Finset

variable {ι α : Type*} [LinearOrder α] [Fintype ι] [Nonempty ι] (f : ι → α)

namespace Function

/-- The maximum value of a tuple. -/
@[to_dual /-- The minimum value of a tuple. -/]
abbrev max : α := univ.sup' univ_nonempty f

@[to_dual min_le]
lemma le_max (x : ι) : f x ≤ max f := le_sup' _ (by simp)

end Function

section Argmax

@[to_dual exists_argmin]
lemma exists_argmax : ∃ i, f i = f.max := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (by simp : Finset.univ.Nonempty) f
  exact ⟨i, hi.symm⟩

/-- The index of the maximum value of a tuple. -/
@[to_dual argmin /-- The index of the minimum value of a tuple. -/]
noncomputable def argmax := (exists_argmax f).choose

@[to_dual argmin_spec]
lemma argmax_spec : f (argmax f) = f.max := (exists_argmax f).choose_spec

@[to_dual isMinOn_argmin]
lemma isMaxOn_argmax (x : ι) : f x ≤ f (argmax f) := by
  rw [argmax_spec f]
  exact f.le_max x

variable [MeasurableSpace α]

@[to_dual (attr := fun_prop)]
lemma measurable_max [MeasurableSup₂ α] : Measurable (fun (t : ι → α) => t.max) := by
  suffices (fun f : ι → α ↦ f.max) = (univ.sup' univ_nonempty fun i f => f i) by
    rw [this]
    exact measurable_sup' univ_nonempty (fun i _ => measurable_pi_apply i)
  ext
  simp [Function.max]

@[to_dual (attr := fun_prop) measurable_argmin]
lemma measurable_argmax [MeasurableSpace ι] [MeasurableEq α] [MeasurableSup₂ α] :
    Measurable fun f : ι → α ↦ argmax f := by
  refine measurable_to_countable' fun i ↦ ?_
  simp only [Set.preimage, Set.mem_singleton_iff]
  let Maximizers (f : ι → α) : Set ι := {i | f i = f.max}
  suffices {f : ι → α | argmax f = i} = ⋃ (S)
      (hS : ∀ x, Maximizers x = S → argmax x = i), {f | Maximizers f = S} by
    rw [this]
    refine MeasurableSet.iUnion fun S ↦ (.iUnion fun hS ↦ ?_)
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, exists_eq_right']
  constructor
  · intro hf x hx
    rw [← hf]
    exact Classical.choose.congr_simp hx (exists_argmax x)
  · intro h
    exact h f rfl

end Argmax

lemma neg_max_eq_min_neg [AddGroup α] [AddLeftMono α] [AddRightMono α] : -f.max = (-f).min := by
  refine le_antisymm ?_ ?_
  · simp; grind
  · simp only [inf'_le_iff, mem_univ, Pi.neg_apply, neg_le_neg_iff, sup'_le_iff, forall_const,
      true_and]
    exact ⟨argmax f, isMaxOn_argmax f⟩
