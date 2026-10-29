/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Lp functions with respect to a composition of kernels and measures
-/

@[expose] public section

open ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

lemma AEStronglyMeasurable.ae_of_comp {α β E : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} [TopologicalSpace E] {κ : Kernel α β} {μ : Measure α} {f : β → E}
    (hf : AEStronglyMeasurable f (κ ∘ₘ μ)) :
    ∀ᵐ x ∂μ, AEStronglyMeasurable f (κ x) := by
  obtain ⟨g, hg, hfg⟩ := hf
  filter_upwards [Measure.ae_ae_of_ae_comp hfg] with x hx using ⟨g, hg, hx⟩

protected lemma Measure.memLp_comp_iff
    {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [NormedAddCommGroup E]
    {κ : Kernel α β} {μ : Measure α} {f : β → E} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f (κ ∘ₘ μ)) :
    MemLp f p (κ ∘ₘ μ)
      ↔ (∀ᵐ x ∂μ, MemLp f p (κ x)) ∧ Integrable (fun x ↦ ∫ y, ‖f y‖ ^ p.toReal ∂κ x) μ := by
  rw [← integrable_norm_rpow_iff (by fun_prop) hp0 hp_top, Measure.integrable_comp_iff]
  swap; · exact (hf.norm.aemeasurable.pow_const p.toReal).aestronglyMeasurable
  congr! 1
  · suffices ∀ᵐ x ∂μ, Integrable (fun x ↦ ‖f x‖ ^ p.toReal) (κ x) ↔ MemLp f p (κ x) by
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
        <;> filter_upwards [h, this] with x hx h_iff
      · rwa [h_iff] at hx
      · rwa [← h_iff] at hx
    filter_upwards [hf.ae_of_comp] with ω hω
    rw [integrable_norm_rpow_iff hω hp0 hp_top]
  · congr! 4 with y
    simp only [Real.norm_eq_abs, abs_eq_self]
    positivity

end MeasureTheory
