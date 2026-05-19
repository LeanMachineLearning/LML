/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
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
  simp only [Measure.map_apply hg hs, withDensity_apply _ (hg hs), withDensity_apply _ hs,
    setLIntegral_map hs hf hg, Function.comp]

lemma map_withDensity_equiv {e : α ≃ᵐ β} {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) :=
  calc (μ.withDensity f).map e
      = (μ.withDensity ((f ∘ e.symm) ∘ e)).map e := by
        congr
        funext x
        simp
    _ = (μ.map e).withDensity (f ∘ e.symm) :=
        map_withDensity_comp e.measurable (hf.comp e.symm.measurable)

lemma map_swap_withDensity_fst {μ : Measure (α × β)} {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (f ∘ Prod.snd)).map Prod.swap = (μ.map Prod.swap).withDensity (f ∘ Prod.fst) :=
  calc (μ.withDensity (f ∘ Prod.snd)).map Prod.swap
  _ = (μ.withDensity ((f ∘ Prod.fst) ∘ Prod.swap)).map Prod.swap :=
    rfl
  _ = (μ.map Prod.swap).withDensity (f ∘ Prod.fst) :=
    map_withDensity_comp measurable_swap (hf.comp measurable_fst)

end MeasureTheory

namespace MeasureTheory.Measure

lemma compProd_withDensity_left [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ] {f : α → ℝ≥0∞}
    (hf : Measurable f) : (μ.withDensity f) ⊗ₘ κ = (μ ⊗ₘ κ).withDensity (f ∘ Prod.fst) := by
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  calc ∫⁻ p, g p ∂((μ.withDensity f) ⊗ₘ κ)
      = ∫⁻ a, ∫⁻ b, g (a, b) ∂κ a ∂(μ.withDensity f) :=
        Measure.lintegral_compProd hg
    _ = ∫⁻ a, f a * ∫⁻ b, g (a, b) ∂κ a ∂μ :=
        lintegral_withDensity_eq_lintegral_mul _ hf hg.lintegral_kernel_prod_right'
    _ = ∫⁻ a, ∫⁻ b, f a * g (a, b) ∂κ a ∂μ := by
        refine lintegral_congr fun a ↦ ?_
        rw [← lintegral_const_mul _ (by fun_prop)]
    _ = ∫⁻ p, (f ∘ Prod.fst) p * g p ∂(μ ⊗ₘ κ) :=
        (Measure.lintegral_compProd ((hf.comp measurable_fst).mul hg)).symm
    _ = ∫⁻ p, g p ∂((μ ⊗ₘ κ).withDensity (f ∘ Prod.fst)) :=
        (lintegral_withDensity_eq_lintegral_mul _ (hf.comp measurable_fst) hg).symm

lemma compProd_withDensity_withDensity [SFinite μ] {κ : Kernel α γ} [IsSFiniteKernel κ]
    {f : α → ℝ≥0∞} {g : α → γ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable (Function.uncurry g))
    [IsSFiniteKernel (κ.withDensity g)] :
    (μ.withDensity f) ⊗ₘ (κ.withDensity g) = (μ ⊗ₘ κ).withDensity (fun (a, c) => f a * g a c) := by
  rw [Measure.compProd_withDensity hg, compProd_withDensity_left hf]
  exact (withDensity_mul _ (hf.comp measurable_fst) hg).symm

lemma compProd_eq_compProd_withDensity [SFinite μ] {κ η : Kernel α β} [IsSFiniteKernel κ]
    [IsSFiniteKernel η] {f : β → ℝ≥0∞} (hf : Measurable f)
    (h : κ =ᵐ[μ] η.withDensity (fun _ b ↦ f b)) : μ ⊗ₘ κ = (μ ⊗ₘ η).withDensity (f ∘ Prod.snd) := by
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  calc ∫⁻ p, g p ∂(μ ⊗ₘ κ)
      = ∫⁻ a, ∫⁻ b, g (a, b) ∂κ a ∂μ :=
        Measure.lintegral_compProd hg
    _ = ∫⁻ a, ∫⁻ b, g (a, b) ∂(η.withDensity (fun _ b ↦ f b)) a ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [h] with a ha; rw [ha]
    _ = ∫⁻ a, ∫⁻ b, g (a, b) ∂((η a).withDensity f) ∂μ := by
        refine lintegral_congr fun a ↦ ?_
        rw [Kernel.withDensity_apply _ (by fun_prop)]
    _ = ∫⁻ a, ∫⁻ b, f b * g (a, b) ∂η a ∂μ := by
        refine lintegral_congr fun a ↦ ?_
        exact lintegral_withDensity_eq_lintegral_mul _ hf (by fun_prop)
    _ = ∫⁻ p, (f ∘ Prod.snd) p * g p ∂(μ ⊗ₘ η) :=
        (Measure.lintegral_compProd ((hf.comp measurable_snd).mul hg)).symm
    _ = ∫⁻ p, g p ∂((μ ⊗ₘ η).withDensity (f ∘ Prod.snd)) :=
        (lintegral_withDensity_eq_lintegral_mul _ (hf.comp measurable_snd) hg).symm

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

lemma comp_withDensity_const {κ : Kernel α γ} [IsSFiniteKernel κ] {f : γ → ℝ≥0∞}
    (hf : Measurable f) : (κ.withDensity (fun _ c ↦ f c)) ∘ₘ μ = (κ ∘ₘ μ).withDensity f := by
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  calc ∫⁻ x, g x ∂((κ.withDensity (fun _ c ↦ f c)) ∘ₘ μ)
      = ∫⁻ a, ∫⁻ x, g x ∂(κ.withDensity (fun _ c ↦ f c)) a ∂μ :=
        Measure.lintegral_bind (Kernel.measurable _).aemeasurable hg.aemeasurable
    _ = ∫⁻ a, ∫⁻ x, g x ∂((κ a).withDensity f) ∂μ := by
        refine lintegral_congr fun a ↦ ?_
        rw [Kernel.withDensity_apply _ (by fun_prop)]
    _ = ∫⁻ a, ∫⁻ x, f x * g x ∂κ a ∂μ := by
        refine lintegral_congr fun a ↦ ?_
        exact lintegral_withDensity_eq_lintegral_mul _ hf hg
    _ = ∫⁻ x, f x * g x ∂(κ ∘ₘ μ) :=
        (Measure.lintegral_bind (Kernel.measurable _).aemeasurable (hf.mul hg).aemeasurable).symm
    _ = ∫⁻ x, g x ∂((κ ∘ₘ μ).withDensity f) :=
        (lintegral_withDensity_eq_lintegral_mul _ hf hg).symm

lemma compProd_withDensity_left {κ : Kernel α β} {η : Kernel (α × β) γ} {f : α → β → ℝ≥0∞}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel (κ.withDensity f)]
    (hf : Measurable (Function.uncurry f)) :
    (κ.withDensity f) ⊗ₖ η = (κ ⊗ₖ η).withDensity (fun a (b, _) ↦ f a b) := by
  have hg : Measurable (Function.uncurry (fun a (bc : β × γ) => f a bc.1)) :=
    hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  ext x : 1
  haveI : SFinite ((κ x).withDensity (f x)) := by
    rw [← Kernel.withDensity_apply _ hf]; infer_instance
  simp only [Kernel.compProd_apply_eq_compProd_sectR, Kernel.withDensity_apply _ hf,
    Kernel.withDensity_apply _ hg]
  exact Measure.compProd_withDensity_left hf.of_uncurry_left

lemma withDensity_rnDeriv_eq' {κ η : Kernel α β} [MeasurableSpace.CountableOrCountablyGenerated α β]
    [IsFiniteKernel κ] [IsFiniteKernel η] (h : ∀ a, κ a ≪ η a) :
    η.withDensity (κ.rnDeriv η) = κ := by
  ext a : 1
  exact Kernel.withDensity_rnDeriv_eq (h a)

end ProbabilityTheory.Kernel
