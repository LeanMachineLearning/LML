/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.ConditionalProbability

/-! # Lemmas about conditional probability
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Conditioning a product measure on an event of the first coordinate amounts to conditioning
the first measure. -/
lemma cond_prod_univ {μ : Measure α} [SFinite μ] {ν : Measure β} [IsProbabilityMeasure ν]
    (s : Set α) :
    (μ.prod ν)[|s ×ˢ Set.univ] = (μ[|s]).prod ν := by
  simp only [cond, Measure.prod_prod, measure_univ, mul_one, Measure.prod_smul_left,
    ← Measure.prod_restrict, Measure.restrict_univ]

end ProbabilityTheory
