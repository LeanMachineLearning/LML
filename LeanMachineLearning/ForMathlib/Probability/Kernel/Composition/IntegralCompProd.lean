/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

import Mathlib.Analysis.Convex.Integral

/-
# Lp functions with respect to a composition of kernels and measures
-/

@[expose] public section

open ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

protected lemma Measure.memLp_comp_iff
    {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [NormedAddCommGroup E]
    {κ : Kernel α β} {μ : Measure α} {f : β → E} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f (κ ∘ₘ μ)) :
    MemLp f p (κ ∘ₘ μ)
      ↔ (∀ᵐ x ∂μ, MemLp f p (κ x)) ∧ Integrable (fun x ↦ ∫ y, ‖f y‖ ^ p.toReal ∂κ x) μ := by
    rw [← integrable_norm_rpow_iff (by fun_prop) hp0 hp_top, Measure.integrable_comp_iff]
    swap; · exact (hf.norm.aemeasurable.pow_const p.toReal).aestronglyMeasurable
    -- todo extract
    unfold AEStronglyMeasurable at hf
    obtain ⟨g, hg, hfg⟩ := hf
    obtain hfg' := Measure.ae_ae_of_ae_comp hfg
    have hf' : ∀ᵐ ω ∂μ, AEStronglyMeasurable f (κ ω) := by
      filter_upwards [hfg'] with ω hω using ⟨g, hg, hω⟩
    --
    congr! 1
    · suffices ∀ᵐ x ∂μ, Integrable (fun x ↦ ‖f x‖ ^ p.toReal) (κ x) ↔ MemLp f p (κ x) by
        refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
          <;> filter_upwards [h, this] with x hx h_iff
        · rwa [h_iff] at hx
        · rwa [← h_iff] at hx
      filter_upwards [hf'] with ω hω
      rw [integrable_norm_rpow_iff hω hp0 hp_top]
    · congr! 4 with y
      simp only [Real.norm_eq_abs, abs_eq_self]
      positivity

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
      ((integrable_norm_rpow_iff hf.1 hp0 hp_top).mpr hf)

end MeasureTheory
