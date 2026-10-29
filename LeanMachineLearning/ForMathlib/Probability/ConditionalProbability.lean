/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.ConditionalProbability

/-! # Lemmas about conditional probability

## Main statements

* `MeasureTheory.Measure.sum_meas_smul_cond_fiber`: the **law of total probability** for a random
  variable taking countably many values.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {Ω α : Type*} {mΩ : MeasurableSpace Ω} [Countable α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α]

/-- The **law of total probability** for a random variable taking countably many values: a finite
measure `μ` is the sum of its conditional measures `μ[|X ⁻¹' {x}]` on the fibers of `X`, weighted
by the measures of the fibers. See `ProbabilityTheory.sum_meas_smul_cond_fiber` for the version
with a finite sum. -/
lemma sum_meas_smul_cond_fiber {X : Ω → α} (hX : Measurable X) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
    Measure.sum (fun x ↦ μ (X ⁻¹' {x}) • μ[|X ⁻¹' {x}]) = μ := by
  ext s hs
  simp_rw [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, mul_comm (μ _),
    cond_mul_eq_inter (hX (.singleton _))]
  rw [← measure_iUnion (fun i j hij ↦ ((Set.disjoint_singleton.2 hij).preimage X).mono
      Set.inter_subset_left Set.inter_subset_left) fun i ↦ (hX (.singleton i)).inter hs,
    ← Set.iUnion_inter, ← Set.preimage_iUnion, Set.iUnion_singleton_eq_range, Set.range_id',
    Set.preimage_univ, Set.univ_inter]

end MeasureTheory.Measure

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

lemma lintegral_cond {μ : Measure α} (s : Set α) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ[|s] = (μ s)⁻¹ * ∫⁻ x in s, f x ∂μ := by
  simp [cond, lintegral_smul_measure]

/-- Conditioning a product measure on an event of the first coordinate amounts to conditioning
the first measure. -/
lemma cond_prod_univ {μ : Measure α} [SFinite μ] {ν : Measure β} [IsZeroOrProbabilityMeasure ν]
    (s : Set α) :
    (μ.prod ν)[|s ×ˢ Set.univ] = (μ[|s]).prod ν := by
  rcases eq_zero_or_isProbabilityMeasure ν with rfl | _
  · simp
  simp only [cond, Measure.prod_prod, measure_univ, mul_one, Measure.prod_smul_left,
    ← Measure.prod_restrict, Measure.restrict_univ]

end ProbabilityTheory
