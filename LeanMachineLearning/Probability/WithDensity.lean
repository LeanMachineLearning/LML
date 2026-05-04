/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Interactions of `withDensity` with `compProd`, `map`, and `swap`

Lemmas for pushing `Measure.withDensity` and `Kernel.withDensity` through
`compProd`, `MeasurableEquiv.map`, `Prod.swap`, and composition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {μ : Measure α}

namespace Measure

/-- Composing `withDensity` on the measure side of a `compProd`:
`(μ.withDensity f) ⊗ₘ κ = (μ ⊗ₘ κ).withDensity (f ∘ Prod.fst)`. -/
lemma withDensity_compProd_left [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ]
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f) ⊗ₘ κ = (μ ⊗ₘ κ).withDensity (f ∘ Prod.fst) := by
  ext s hs
  rw [Measure.compProd_apply hs, withDensity_apply _ hs,
    lintegral_withDensity_eq_lintegral_mul₀ hf.aemeasurable
      (Kernel.measurable_kernel_prodMk_left hs).aemeasurable,
    ← lintegral_indicator hs,
    Measure.lintegral_compProd ((hf.comp measurable_fst).indicator hs)]
  congr 1
  ext a
  simp_rw [Pi.mul_apply]
  have : (fun b ↦ s.indicator (f ∘ Prod.fst) (a, b)) =
      fun b ↦ (Prod.mk a ⁻¹' s).indicator (fun _ ↦ f a) b := by
    ext b; simp only [Function.comp, Set.indicator, Set.mem_preimage]; rfl
  rw [this, lintegral_indicator_const (hs.preimage (by fun_prop))]

/-- Pushing a `withDensity` through a `MeasurableEquiv`:
`(μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm)`. -/
lemma withDensity_map_equiv
    {e : α ≃ᵐ β} {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, Measure.restrict_map e.measurable hs,
    lintegral_map (hf.comp e.symm.measurable) e.measurable]
  simp_rw [Function.comp_apply, e.symm_apply_apply]

/-- Mapping a `withDensity` through a `MeasurableEquiv` from the snd component. -/
lemma map_swap_withDensity_fst
    {μ : Measure (α × β)} [SFinite μ]
    {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (f ∘ Prod.snd)).map Prod.swap
      = (μ.map Prod.swap).withDensity (f ∘ Prod.fst) := by
  ext s hs
  rw [Measure.map_apply measurable_swap hs, withDensity_apply _ (measurable_swap hs),
    withDensity_apply _ hs, Measure.restrict_map measurable_swap hs]
  exact (lintegral_map (hf.comp measurable_fst) measurable_swap).symm

/-- `(μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f`. -/
lemma map_withDensity_comp
    {g : α → γ} {f : γ → ℝ≥0∞}
    (hg : Measurable g) (hf : Measurable f) :
    (μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f := by
  ext s hs
  simp only [Measure.map_apply hg hs, withDensity_apply _ (hg hs), withDensity_apply _ hs,
    setLIntegral_map hs hf hg, Function.comp]

/-- `(f · μ) ⊗ₘ (g · κ) = ((a, c) ↦ f a * g a c) · (μ ⊗ₘ κ)`. -/
lemma withDensity_compProd_withDensity [SFinite μ]
    {κ : Kernel α γ} [IsSFiniteKernel κ]
    {f : α → ℝ≥0∞} {g : α → γ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable (Function.uncurry g))
    [IsSFiniteKernel (κ.withDensity g)] :
    (μ.withDensity f) ⊗ₘ (κ.withDensity g) =
      (μ ⊗ₘ κ).withDensity (fun (a, c) => f a * g a c) := by
  rw [Measure.compProd_withDensity hg, withDensity_compProd_left hf]
  exact (withDensity_mul _ (hf.comp measurable_fst) hg).symm

/-- If `κ =ᵐ[μ] η.withDensity (fun _ => f)`, then `μ ⊗ₘ κ = (μ ⊗ₘ η).withDensity (f ∘ Prod.snd)`.
    Unlike `compProd_congr` + `compProd_withDensity`, does not need
    `IsSFiniteKernel (η.withDensity (fun _ => f))`. -/
lemma compProd_eq_compProd_withDensity [SFinite μ]
    {κ η : Kernel α β} [IsSFiniteKernel κ] [IsSFiniteKernel η]
    {f : β → ℝ≥0∞} (hf : Measurable f)
    (h : κ =ᵐ[μ] η.withDensity (fun _ b ↦ f b)) :
    μ ⊗ₘ κ = (μ ⊗ₘ η).withDensity (f ∘ Prod.snd) := by
  have hf_uncurry : Measurable (Function.uncurry (fun (_ : α) => f)) :=
    hf.comp measurable_snd
  ext s hs
  have lhs : (μ ⊗ₘ κ) s = ∫⁻ a, (κ a) (Prod.mk a ⁻¹' s) ∂μ :=
    Measure.compProd_apply hs
  have rhs : ((μ ⊗ₘ η).withDensity (f ∘ Prod.snd)) s =
      ∫⁻ a, ∫⁻ b in Prod.mk a ⁻¹' s, f b ∂(η a) ∂μ := by
    rw [withDensity_apply _ hs, ← lintegral_indicator hs,
      Measure.lintegral_compProd ((hf.comp measurable_snd).indicator hs)]
    congr 1; ext a
    have : (fun b => s.indicator (f ∘ Prod.snd) (a, b)) = (Prod.mk a ⁻¹' s).indicator f := by
      ext b; simp only [Set.indicator, Set.mem_preimage]; rfl
    rw [this, lintegral_indicator (hs.preimage measurable_prodMk_left)]
  rw [lhs, rhs]
  apply lintegral_congr_ae
  filter_upwards [h] with a ha
  rw [ha, Kernel.withDensity_apply _ hf_uncurry, withDensity_apply _ (hs.preimage (by fun_prop))]

end Measure

namespace ProbabilityTheory.Kernel

/-- `(κ.withDensity (fun _ => f)) ∘ₘ μ = (κ ∘ₘ μ).withDensity f`. -/
lemma comp_withDensity_const
    {κ : Kernel α γ} [IsSFiniteKernel κ]
    {f : γ → ℝ≥0∞} (hf : Measurable f) :
    (κ.withDensity (fun _ c ↦ f c)) ∘ₘ μ = (κ ∘ₘ μ).withDensity f := by
  have hf_uncurry : Measurable (Function.uncurry (fun (_ : α) => f)) :=
    hf.comp measurable_snd
  ext s hs
  have lhs : ((κ.withDensity (fun _ => f)) ∘ₘ μ) s = ∫⁻ a, ∫⁻ x in s, f x ∂(κ a) ∂μ := by
    rw [Measure.bind_apply hs (Kernel.measurable _).aemeasurable]
    congr 1; ext a
    rw [Kernel.withDensity_apply _ hf_uncurry, withDensity_apply _ hs]
  have rhs : ((κ ∘ₘ μ).withDensity f) s = ∫⁻ a, ∫⁻ x in s, f x ∂(κ a) ∂μ := by
    rw [withDensity_apply _ hs, ← lintegral_indicator hs f,
      Measure.lintegral_bind (Kernel.measurable _).aemeasurable ((hf.indicator hs).aemeasurable)]
    congr 1; ext a; rw [lintegral_indicator hs f]
  rw [lhs, rhs]

/-- Composing `Kernel.withDensity` on the left kernel of `Kernel.compProd`:
`(κ.withDensity f) ⊗ₖ η = (κ ⊗ₖ η).withDensity (fun a (b, _) => f a b)`. -/
lemma withDensity_compProd_left
    {κ : Kernel α β} {η : Kernel (α × β) γ} {f : α → β → ℝ≥0∞}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel (κ.withDensity f)]
    (hf : Measurable (Function.uncurry f)) :
    (κ.withDensity f) ⊗ₖ η =
      (κ ⊗ₖ η).withDensity (fun a (b, _) ↦ f a b) := by
  have hg : Measurable (Function.uncurry (fun a (bc : β × γ) => f a bc.1)) :=
    hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  ext x : 1
  haveI : SFinite ((κ x).withDensity (f x)) := by
    rw [← Kernel.withDensity_apply _ hf]; infer_instance
  simp only [Kernel.compProd_apply_eq_compProd_sectR, Kernel.withDensity_apply _ hf,
    Kernel.withDensity_apply _ hg]
  exact Measure.withDensity_compProd_left hf.of_uncurry_left

/-- If `κ a ≪ η a` for all `a`, then `η.withDensity (κ.rnDeriv η) = κ`. -/
lemma withDensity_rnDeriv_eq' {κ η : Kernel α β}
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : ∀ a, κ a ≪ η a) :
    η.withDensity (κ.rnDeriv η) = κ := by
  ext a : 1
  exact Kernel.withDensity_rnDeriv_eq (h a)

end ProbabilityTheory.Kernel
