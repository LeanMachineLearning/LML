/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber
-/
module

public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Composition.MeasureComp

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
variable {μ : Measure α}

namespace MeasureTheory

lemma map_withDensity_comp {g : α → γ} {f : γ → ℝ≥0∞} (hg : Measurable g) (hf : Measurable f) :
    (μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f := by
  ext s hs
  rw [Measure.map_apply hg hs, withDensity_apply _ (hg hs), withDensity_apply _ hs,
    setLIntegral_map hs hf hg]
  rfl

lemma map_equiv_withDensity {e : α ≃ᵐ β} {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  simp_rw [← map_withDensity_comp e.measurable (hf.comp e.symm.measurable),
    Function.comp_assoc, MeasurableEquiv.symm_comp_self]
  rfl

lemma map_swap_withDensity_comp_snd {μ : Measure (α × β)} {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (fun ab ↦ f ab.2)).map Prod.swap =
      (μ.map Prod.swap).withDensity (fun ba ↦ f ba.1) := by
  rw [← map_withDensity_comp measurable_swap (by fun_prop)]
  rfl

end MeasureTheory

namespace MeasureTheory.Measure

lemma compProd_withDensity_left [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ] {f : α → ℝ≥0∞}
    (hf : Measurable f) : (μ.withDensity f) ⊗ₘ κ = (μ ⊗ₘ κ).withDensity (fun ab ↦ f ab.1) := by
  refine ext_of_lintegral _ fun g hg ↦ ?_
  calc ∫⁻ ab, g ab ∂((μ.withDensity f) ⊗ₘ κ)
      = ∫⁻ a, ∫⁻ b, g (a, b) ∂κ a ∂(μ.withDensity f) :=
        lintegral_compProd hg
    _ = ∫⁻ a, f a * ∫⁻ b, g (a, b) ∂κ a ∂μ :=
        lintegral_withDensity_eq_lintegral_mul _ hf hg.lintegral_kernel_prod_right'
    _ = ∫⁻ a, ∫⁻ b, f a * g (a, b) ∂κ a ∂μ :=
        lintegral_congr fun a ↦ (lintegral_const_mul _ (by fun_prop)).symm
    _ = ∫⁻ ab, (fun ab ↦ f ab.1) ab * g ab ∂(μ ⊗ₘ κ) :=
        (lintegral_compProd ((hf.comp measurable_fst).mul hg)).symm
    _ = ∫⁻ ab, g ab ∂((μ ⊗ₘ κ).withDensity (fun ab ↦ f ab.1)) :=
        (lintegral_withDensity_eq_lintegral_mul _ (hf.comp measurable_fst) hg).symm

lemma compProd_withDensity_withDensity [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ]
    {f : α → ℝ≥0∞} {g : α → β → ℝ≥0∞} (hf : Measurable f) (hg : Measurable (Function.uncurry g))
    [IsSFiniteKernel (κ.withDensity g)] :
    (μ.withDensity f) ⊗ₘ (κ.withDensity g) =
      (μ ⊗ₘ κ).withDensity (fun ac ↦ f ac.1 * g ac.1 ac.2) := by
  rw [compProd_withDensity hg, compProd_withDensity_left hf]
  exact (withDensity_mul _ (hf.comp measurable_fst) hg).symm

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

namespace ProbabilityTheory.Kernel

lemma comp_withDensity_eq_withDensity_comp {κ : Kernel α β} [IsSFiniteKernel κ] {f : β → ℝ≥0∞}
    (hf : Measurable f) : (κ.withDensity (fun _ b ↦ f b)) ∘ₘ μ = (κ ∘ₘ μ).withDensity f := by
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  calc ∫⁻ b, g b ∂((κ.withDensity (fun _ b ↦ f b)) ∘ₘ μ)
      = ∫⁻ a, ∫⁻ b, g b ∂(κ.withDensity (fun _ b ↦ f b)) a ∂μ :=
        Measure.lintegral_bind (measurable _).aemeasurable hg.aemeasurable
    _ = ∫⁻ a, ∫⁻ b, f b * g b ∂κ a ∂μ := by
        congr with a
        exact lintegral_withDensity _ (by fun_prop) _ hg
    _ = ∫⁻ b, f b * g b ∂(κ ∘ₘ μ) :=
        (Measure.lintegral_bind (measurable _).aemeasurable (hf.mul hg).aemeasurable).symm
    _ = ∫⁻ b, g b ∂((κ ∘ₘ μ).withDensity f) :=
        (lintegral_withDensity_eq_lintegral_mul _ hf hg).symm

lemma compProd_withDensity_left {κ : Kernel α β} {η : Kernel (α × β) γ} {f : α → β → ℝ≥0∞}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel (κ.withDensity f)]
    (hf : Measurable (Function.uncurry f)) :
    (κ.withDensity f) ⊗ₖ η = (κ ⊗ₖ η).withDensity (fun a bc ↦ f a bc.1) := by
  ext a : 1
  calc ((κ.withDensity f) ⊗ₖ η) a
      = (κ a).withDensity (f a) ⊗ₘ η.sectR a := by
        rw [compProd_apply_eq_compProd_sectR, Kernel.withDensity_apply _ hf]
    _ = ((κ a) ⊗ₘ (η.sectR a)).withDensity (fun bc ↦ f a bc.1) :=
        Measure.compProd_withDensity_left (by fun_prop)
    _ = ((κ ⊗ₖ η).withDensity (fun a bc ↦ f a bc.1)) a := by
        rw [← compProd_apply_eq_compProd_sectR, Kernel.withDensity_apply _ (by fun_prop)]

lemma withDensity_rnDeriv_eq' {κ η : Kernel α β} [MeasurableSpace.CountableOrCountablyGenerated α β]
    [IsFiniteKernel κ] [IsFiniteKernel η] (h : ∀ a, κ a ≪ η a) :
    η.withDensity (κ.rnDeriv η) = κ :=
  Kernel.ext fun a ↦ withDensity_rnDeriv_eq (h a)

end ProbabilityTheory.Kernel
