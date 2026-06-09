/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Tactic.Recall

/-! # Tutorial source file for Markov kernels
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

-- ANCHOR: Types
variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
-- ANCHOR_END: Types

variable {P : Measure 𝓧} [IsProbabilityMeasure P]
  {κ : Kernel 𝓧 𝓨} [IsMarkovKernel κ]

-- ANCHOR: Kernel
example (κ : Kernel 𝓧 𝓨) (x : 𝓧) : Measure 𝓨 := κ x

example (κ : Kernel 𝓧 𝓨) : Measurable κ := κ.measurable

example (f : 𝓧 → Measure 𝓨) (hf : Measurable f) : Kernel 𝓧 𝓨 := ⟨f, hf⟩
-- ANCHOR_END: Kernel

-- ANCHOR: Measurability
example (f : 𝓧 → Measure 𝓨) :
    Measurable f ↔ ∀ B : Set 𝓨, MeasurableSet B → Measurable (fun x : 𝓧 ↦ f x B) :=
  ⟨fun hf _ hB ↦ (Measure.measurable_coe hB).comp hf,
    Measure.measurable_of_measurable_coe f⟩
-- ANCHOR_END: Measurability

-- ANCHOR: ExtFun
example (κ η : Kernel 𝓧 𝓨) :
    κ = η ↔ ∀ x f, Measurable f → ∫⁻ y, f y ∂(κ x) = ∫⁻ y, f y ∂(η x) :=
  Kernel.ext_fun_iff
-- ANCHOR_END: ExtFun


-- ANCHOR: Markov
example (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] (x : 𝓧) :
    κ x Set.univ = 1 := by simp

example (κ : Kernel 𝓧 𝓨) [IsFiniteKernel κ] :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ a, κ a Set.univ ≤ C :=
  IsFiniteKernel.exists_univ_le

example (κ : Kernel 𝓧 𝓨) [IsFiniteKernel κ] (x : 𝓧) :
    IsFiniteMeasure (κ x) := inferInstance
-- ANCHOR_END: Markov
