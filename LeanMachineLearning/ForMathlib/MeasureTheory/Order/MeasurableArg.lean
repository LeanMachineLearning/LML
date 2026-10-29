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

/-! # Maximum, minimum, argmax and argmin of a function on a finite type

For `f : ι → α` with `ι` a nonempty finite type and `α` a linear order, we define the maximum
`Function.max f` and the minimum `Function.min f` of `f`, as well as an index `argmax f` (resp.
`argmin f`) at which `f` attains its maximum (resp. minimum).

## Main definitions

* `Function.max f`, `Function.min f`: the maximum and minimum values of `f`.
* `argmax f`, `argmin f`: an index at which `f` attains its maximum, resp. minimum.

## Main statements

* `isMaxOn_argmax`, `isMinOn_argmin`: `f` attains its maximum at `argmax f` and its minimum at
  `argmin f`.
* `measurable_max`, `measurable_min`, `measurable_argmax`, `measurable_argmin`: the maximum,
  minimum, argmax and argmin are measurable functions of `f`.
-/

@[expose] public section

open Finset

variable {ι α : Type*} [LinearOrder α] [Fintype ι] [Nonempty ι] (f : ι → α)

namespace Function

/-- The maximum value of a tuple. -/
@[to_dual /-- The minimum value of a tuple. -/]
abbrev max : α := univ.sup' univ_nonempty f

/-- Every value of `f` is at most its maximum. -/
@[to_dual min_le /-- The minimum of `f` is at most every value of `f`. -/]
lemma le_max (x : ι) : f x ≤ max f := le_sup' _ (by simp)

end Function

section Argmax

@[to_dual]
lemma exists_argmax : ∃ i, f i = f.max := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (by simp : Finset.univ.Nonempty) f
  exact ⟨i, hi.symm⟩

/-- The index of the maximum value of a tuple. -/
@[to_dual /-- The index of the minimum value of a tuple. -/]
noncomputable def argmax := (exists_argmax f).choose

@[to_dual]
lemma argmax_spec : f (argmax f) = f.max := (exists_argmax f).choose_spec

/-- `f` attains its maximum at `argmax f`. -/
lemma isMaxOn_argmax : IsMaxOn f Set.univ (argmax f) :=
  isMaxOn_univ_iff.2 fun x ↦ argmax_spec f ▸ f.le_max x

/-- `f` attains its minimum at `argmin f`. -/
lemma isMinOn_argmin : IsMinOn f Set.univ (argmin f) :=
  isMinOn_univ_iff.2 fun x ↦ argmin_spec f ▸ f.min_le x

variable [MeasurableSpace α]

/-- The maximum of a tuple is a measurable function of the tuple. -/
@[to_dual (attr := fun_prop) /-- The minimum of a tuple is a measurable function of the tuple. -/]
lemma measurable_max [MeasurableSup₂ α] : Measurable (fun (t : ι → α) => t.max) := by
  suffices (fun f : ι → α ↦ f.max) = (univ.sup' univ_nonempty fun i f => f i) by
    rw [this]
    exact measurable_sup' univ_nonempty (fun i _ => measurable_pi_apply i)
  ext
  simp [Function.max]

/-- The argmax of a tuple is a measurable function of the tuple. -/
@[to_dual (attr := fun_prop) /-- The argmin of a tuple is a measurable function of the tuple. -/]
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
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, exists_eq_right']
  constructor
  · intro hf x hx
    rw [← hf]
    exact Classical.choose.congr_simp (funext fun j ↦ propext (Set.ext_iff.mp hx j))
      (exists_argmax x)
  · intro h
    exact h f rfl

end Argmax

lemma neg_max_eq_min_neg [AddGroup α] [AddLeftMono α] [AddRightMono α] : -f.max = (-f).min := by
  refine le_antisymm ?_ ?_
  · simp; grind
  · simp only [inf'_le_iff, mem_univ, Pi.neg_apply, neg_le_neg_iff, sup'_le_iff, forall_const,
      true_and]
    exact ⟨argmax f, isMaxOn_univ_iff.1 (isMaxOn_argmax f)⟩
