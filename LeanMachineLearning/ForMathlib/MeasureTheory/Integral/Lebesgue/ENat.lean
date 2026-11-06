/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import LeanMachineLearning.ForMathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Lebesgue integral of an `ℕ∞`-valued function

The expectation of a random variable `f` with values in `ℕ∞`, such as a random time, is the sum of
its tail probabilities: `∫⁻ f ∂μ = ∑ n, μ {n < f}` (the discrete layer cake formula).

## Main statements

* `MeasureTheory.lintegral_toENNReal_eq_tsum_measure_lt`: `∫⁻ f ∂μ = ∑' n, μ {n < f}`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → ℕ∞}

/-- **Tail-sum formula** (discrete layer cake formula): the integral of a function with values in
`ℕ∞` is the sum of the measures of the sets where it exceeds each natural number. -/
lemma lintegral_toENNReal_eq_tsum_measure_lt (hf : AEMeasurable f μ) :
    ∫⁻ ω, (f ω : ℝ≥0∞) ∂μ = ∑' n : ℕ, μ {ω | (n : ℕ∞) < f ω} := by
  have h_meas (n : ℕ) : NullMeasurableSet {ω | (n : ℕ∞) < f ω} μ :=
    hf.nullMeasurableSet_preimage (s := Set.Ioi (n : ℕ∞)) .of_discrete
  -- Pointwise, `f ω` is the number of natural numbers below it.
  have h_card (k : ℕ∞) : (k : ℝ≥0∞) = ∑' n : ℕ, {n : ℕ | (n : ℕ∞) < k}.indicator 1 n := by
    induction k using ENat.recTopCoe with
    | top => simp
    | coe k =>
      exact ((tsum_indicator_natCast_lt_eq_sum_range (ENat.natCast_ne_top k) 1).trans
        (by simp)).symm
  calc ∫⁻ ω, (f ω : ℝ≥0∞) ∂μ
  _ = ∫⁻ ω, ∑' n : ℕ, {ω | (n : ℕ∞) < f ω}.indicator 1 ω ∂μ :=
    lintegral_congr fun ω ↦ by simp [h_card (f ω), Set.indicator_apply]
  _ = ∑' n : ℕ, μ {ω | (n : ℕ∞) < f ω} := by
    rw [lintegral_tsum (f := fun (n : ℕ) ↦ {ω | (n : ℕ∞) < f ω}.indicator 1)
      fun n ↦ aemeasurable_one.indicator₀ (h_meas n)]
    exact tsum_congr fun n ↦ lintegral_indicator_one₀ (h_meas n)

end MeasureTheory
