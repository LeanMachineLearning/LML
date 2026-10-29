/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Integral

/-!
# Jensen's inequality for the norm to a power

## Main statements

* `norm_integral_rpow_le_integral_norm_rpow`: for a probability measure `μ` and `1 ≤ p < ∞`,
  `‖∫ x, f x ∂μ‖ ^ p ≤ ∫ x, ‖f x‖ ^ p ∂μ`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

/-- **Jensen's inequality** for the convex function `x ↦ ‖x‖ ^ p`, `1 ≤ p`. -/
lemma norm_integral_rpow_le_integral_norm_rpow
    {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → E} {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp_top : p ≠ ∞) (hf : MemLp f p μ) :
    ‖∫ x, f x ∂μ‖ ^ p.toReal ≤ ∫ x, ‖f x‖ ^ p.toReal ∂μ := by
  have hp0 : p ≠ 0 := by positivity
  have hp1' : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp1
  calc ‖∫ x, f x ∂μ‖ ^ p.toReal
  _ ≤ (∫ x, ‖f x‖ ∂μ) ^ p.toReal := by
    gcongr
    exact norm_integral_le_integral_norm _
  _ ≤ ∫ x, ‖f x‖ ^ p.toReal ∂μ :=
    ConvexOn.map_integral_le (convexOn_rpow hp1')
      (Real.continuous_rpow_const (by positivity)).continuousOn isClosed_Ici
      (ae_of_all _ fun x ↦ norm_nonneg _) (hf.integrable hp1).norm
      ((integrable_norm_rpow_iff hf.aestronglyMeasurable hp0 hp_top).mpr hf)
