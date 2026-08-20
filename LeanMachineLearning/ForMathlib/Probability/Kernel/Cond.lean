/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib

/-! # Definition of conditional Markov kernels
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {κ : Kernel α β} {A : α → Set β}

/-- If the graph `{p | p.2 ∈ A p.1}` of the set-valued map `A` is measurable, then
`x ↦ κ x (s ∩ A x)` is measurable for every measurable set `s`. -/
lemma measurable_apply_inter [IsSFiniteKernel κ]
    (hA : MeasurableSet {p : α × β | p.2 ∈ A p.1}) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun x ↦ κ x (s ∩ A x) := by
  have h (x : α) : s ∩ A x = Prod.mk x ⁻¹' (Prod.snd ⁻¹' s ∩ {p : α × β | p.2 ∈ A p.1}) := rfl
  simp_rw [h]
  exact measurable_kernel_prodMk_left <| (measurable_snd hs).inter hA

variable (κ) [IsSFiniteKernel κ]

/-- The kernel `x ↦ (κ x)[|A x]`, obtained by conditioning `κ x` on the set `A x`. -/
noncomputable def cond (hA : MeasurableSet {p : α × β | p.2 ∈ A p.1}) : Kernel α β where
  toFun x := (κ x)[|A x]
  measurable' := by
    rw [Measure.measurable_measure]
    intro t ht
    simp only [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul]
    refine Measurable.mul (.inv ?_) ?_
    · simpa using measurable_apply_inter hA MeasurableSet.univ
    · simp_rw [fun b ↦ (κ b).restrict_apply (s := A b) ht]
      exact measurable_apply_inter hA ht

variable {hA : MeasurableSet {p : α × β | p.2 ∈ A p.1}}

@[simp]
lemma cond_apply (x : α) : cond κ hA x = (κ x)[|A x] := rfl

/-- `cond κ hA` is always a finite kernel, bounded by `1`: each `(κ x)[|A x]` is either the zero
measure (when `κ x (A x)` is `0` or `∞`) or a probability measure. -/
instance : IsFiniteKernel (cond κ hA) :=
  ⟨1, ENNReal.one_lt_top, fun x ↦ by rw [cond_apply]; exact prob_le_one⟩

/-- `cond κ hA` is a Markov kernel as soon as every `A x` has positive and finite measure
under `κ x`. -/
lemma isMarkovKernel_cond_of_finite (h₀ : ∀ x, κ x (A x) ≠ 0) (htop : ∀ x, κ x (A x) ≠ ⊤) :
    IsMarkovKernel (cond κ hA) :=
  ⟨fun x ↦ cond_isProbabilityMeasure_of_finite (h₀ x) (htop x)⟩

lemma isMarkovKernel_cond [IsFiniteKernel κ] (h₀ : ∀ x, κ x (A x) ≠ 0) :
    IsMarkovKernel (cond κ hA) :=
  isMarkovKernel_cond_of_finite κ h₀ fun x ↦ measure_ne_top (κ x) (A x)

end ProbabilityTheory.Kernel
