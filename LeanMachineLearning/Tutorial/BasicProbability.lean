/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Basic

/-! # Tutorial source file for basic probability
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

section
-- ANCHOR: One
variable {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
-- ANCHOR_END: One
end

section
-- ANCHOR: Two
variable {P : Measure ℝ} [IsProbabilityMeasure P]
-- ANCHOR_END: Two
end

section
-- ANCHOR: Three
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
-- ANCHOR_END: Three
end

section
-- ANCHOR: Four
example (P : Measure ℝ) (s : Set ℝ) : ℝ≥0∞ := P s
-- ANCHOR_END: Four
end

section
-- ANCHOR: Five
variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} (hX : Measurable X)
-- ANCHOR_END: Five
end

section
-- ANCHOR: Six
variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω]
-- ANCHOR_END: Six
end


section
-- ANCHOR: Gaussian
example (μ : ℝ) (v : ℝ≥0) : Measure ℝ := gaussianReal μ v
-- ANCHOR_END: Gaussian
end

section
-- ANCHOR: Indep
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → ℝ} {Y : Ω → ℕ} (hX : Measurable X) (hY : Measurable Y)
  (hXY : IndepFun X Y P)
-- ANCHOR_END: Indep
end
