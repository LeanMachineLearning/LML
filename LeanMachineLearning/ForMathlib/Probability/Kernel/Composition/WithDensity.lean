/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber
-/
module

public import Mathlib.Probability.Kernel.Composition.WithDensity

/-!
# Composition-product with a kernel with density

## Main statements

* `Measure.compProd_eq_compProd_withDensity_comp_snd`: if `κ` is a.e. equal to `η` with density
  `f` (a function of the second coordinate only), then `μ ⊗ₘ κ` is `μ ⊗ₘ η` with density
  `fun ab ↦ f ab.2`.
-/

@[expose] public section

open ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}

lemma compProd_eq_compProd_withDensity_comp_snd [SFinite μ] {κ η : Kernel α β} [IsSFiniteKernel κ]
    [IsSFiniteKernel η] {f : β → ℝ≥0∞} (hf : Measurable f)
    (h : κ =ᵐ[μ] η.withDensity (fun _ b ↦ f b)) :
    μ ⊗ₘ κ = (μ ⊗ₘ η).withDensity (fun ab ↦ f ab.2) := by
  /- A proof based on `compProd_congr` requires `IsSFiniteKernel (η.withDensity fun _ b ↦ f b)`. -/
  refine ext_of_lintegral _ fun g hg ↦ ?_
  calc ∫⁻ ab, g ab ∂(μ ⊗ₘ κ)
      = ∫⁻ a, ∫⁻ b, g (a, b) ∂κ a ∂μ :=
        lintegral_compProd hg
    _ = ∫⁻ a, ∫⁻ b, g (a, b) ∂((η a).withDensity f) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [h] with a ha
        rw [ha, Kernel.withDensity_apply _ (by fun_prop)]
    _ = ∫⁻ a, ∫⁻ b, f b * g (a, b) ∂η a ∂μ := by
        congr with a
        exact lintegral_withDensity_eq_lintegral_mul _ hf (by fun_prop)
    _ = ∫⁻ ab, f ab.2 * g ab ∂(μ ⊗ₘ η) :=
        (lintegral_compProd ((hf.comp measurable_snd).mul hg)).symm
    _ = ∫⁻ ab, g ab ∂((μ ⊗ₘ η).withDensity (fun ab ↦ f ab.2)) :=
        (lintegral_withDensity_eq_lintegral_mul _ (hf.comp measurable_snd) hg).symm

end MeasureTheory.Measure
