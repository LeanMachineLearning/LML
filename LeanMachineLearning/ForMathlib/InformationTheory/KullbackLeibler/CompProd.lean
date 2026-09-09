/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! # Lemmas about the Kullback-Leibler divergence of the images of two measures by a measurable map
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Transporting `μ ⊗ₘ η.comap f` along `f` in the first coordinate gives `μ.map f ⊗ₘ η`. -/
lemma _root_.MeasureTheory.Measure.map_compProd_comap (μ : Measure α) [SFinite μ]
    (η : Kernel β γ) [IsSFiniteKernel η] {f : α → β} (hf : Measurable f) :
    (μ ⊗ₘ η.comap f hf).map (fun p : α × γ ↦ (f p.1, p.2)) = μ.map f ⊗ₘ η := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.compProd_apply (hs.preimage (by fun_prop)),
    Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

omit [IsFiniteMeasure ν] in
lemma _root_.MeasureTheory.Measure.map_withDensity_comp
    {f : β → ℝ≥0∞} (hf : Measurable f) {g : α → β} (hg : Measurable g) :
    (ν.withDensity (f ∘ g)).map g = (ν.map g).withDensity f := by
  ext s hs
  rw [Measure.map_apply hg hs, withDensity_apply _ (hg hs), withDensity_apply _ hs,
    ← lintegral_indicator hs, ← lintegral_indicator (hg hs), lintegral_map (hf.indicator hs) hg]
  rfl

lemma klDiv_withDensity_comp_map {f : β → ℝ≥0∞} (hf : Measurable f) {g : α → β} (hg : Measurable g)
    [IsFiniteMeasure (ν.withDensity (f ∘ g))] :
    klDiv ((ν.withDensity (f ∘ g)).map g) (ν.map g) = klDiv (ν.withDensity (f ∘ g)) ν := by
  have hac : ν.withDensity (f ∘ g) ≪ ν := withDensity_absolutelyContinuous ν (f ∘ g)
  have h_rnDeriv : ((ν.withDensity (f ∘ g)).map g).rnDeriv (ν.map g) =ᵐ[ν.map g] f := by
    rw [Measure.map_withDensity_comp hf hg]
    exact Measure.rnDeriv_withDensity _ hf
  have hmeas : Measurable fun x : β ↦
      ENNReal.ofReal (klFun (((ν.withDensity (f ∘ g)).map g).rnDeriv (ν.map g) x).toReal) :=
    (measurable_klFun.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal).ennreal_ofReal
  rw [klDiv_eq_lintegral_klFun_of_ac (hac.map hg), klDiv_eq_lintegral_klFun_of_ac hac,
    lintegral_map hmeas hg]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity ν (hf.comp hg),
    ae_of_ae_map hg.aemeasurable h_rnDeriv] with x hx1 hx2
  rw [hx1, hx2]
  rfl

/-- If `μ` has density `f ∘ g` with respect to `ν`, then the divergence of the images by `g` is
the divergence of `μ` and `ν`: `g` is a sufficient statistic. -/
lemma klDiv_map_of_eq_withDensity_comp {f : β → ℝ≥0∞} (hf : Measurable f) {g : α → β}
    (hg : Measurable g) (hμ : μ = ν.withDensity (f ∘ g)) :
    klDiv (μ.map g) (ν.map g) = klDiv μ ν := by
  rw [hμ]
  have : IsFiniteMeasure (ν.withDensity (f ∘ g)) := by rw [← hμ]; infer_instance
  exact klDiv_withDensity_comp_map hf hg

/-- The conditional divergence of two kernels which depend on the conditioning variable only
through a statistic `f` is the conditional divergence given `f`. -/
lemma klDiv_compProd_comap (μ : Measure α) [IsFiniteMeasure μ] (κ η : Kernel β γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] {f : α → β} (hf : Measurable f) :
    klDiv (μ ⊗ₘ κ.comap f hf) (μ ⊗ₘ η.comap f hf) = klDiv (μ.map f ⊗ₘ κ) (μ.map f ⊗ₘ η) := by
  have hg : Measurable fun p : α × γ ↦ (f p.1, p.2) := by fun_prop
  by_cases hac : μ.map f ⊗ₘ κ ≪ μ.map f ⊗ₘ η
  swap
  · rw [klDiv_of_not_ac hac, klDiv_of_not_ac]
    refine fun h ↦ hac ?_
    have := h.map hg
    rwa [Measure.map_compProd_comap, Measure.map_compProd_comap] at this
  let D := (μ.map f ⊗ₘ κ).rnDeriv (μ.map f ⊗ₘ η)
  have hD : Measurable D := Measure.measurable_rnDeriv _ _
  have hDκ : μ.map f ⊗ₘ κ = (μ.map f ⊗ₘ η).withDensity D :=
    (Measure.withDensity_rnDeriv_eq _ _ hac).symm
  -- for every measurable `t`, the sections of the density integrate to `κ (f a) t`, `μ`-a.e.
  have h_sect {t : Set γ} (ht : MeasurableSet t) :
      ∀ᵐ a ∂μ, ∫⁻ c in t, D (f a, c) ∂(η (f a)) = κ (f a) t := by
    refine ae_of_ae_map (p := fun b ↦ ∫⁻ c in t, D (b, c) ∂(η b) = κ b t) hf.aemeasurable ?_
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      (Measurable.setLIntegral_kernel_prod_right (f := fun b c ↦ D (b, c)) hD ht)
      (Kernel.measurable_coe κ ht) fun u hu _ ↦ ?_
    have h1 := congrArg (fun ρ : Measure (β × γ) ↦ ρ (u ×ˢ t)) hDκ
    rw [Measure.compProd_apply_prod hu ht, withDensity_apply _ (hu.prod ht),
      Measure.setLIntegral_compProd hD hu ht] at h1
    exact h1.symm
  have h_rect s t (hs : MeasurableSet s) (ht : MeasurableSet t) :
      (μ ⊗ₘ κ.comap f hf) (s ×ˢ t) =
        ((μ ⊗ₘ η.comap f hf).withDensity (D ∘ fun p ↦ (f p.1, p.2))) (s ×ˢ t) := by
    rw [Measure.compProd_apply_prod hs ht, withDensity_apply _ (hs.prod ht),
      Measure.setLIntegral_compProd (hD.comp hg) hs ht]
    refine setLIntegral_congr_fun_ae hs ?_
    filter_upwards [h_sect ht] with a ha _
    simp only [Kernel.comap_apply, Function.comp_apply]
    exact ha.symm
  have key : μ ⊗ₘ κ.comap f hf =
      (μ ⊗ₘ η.comap f hf).withDensity (D ∘ fun p ↦ (f p.1, p.2)) := by
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨s, hs, t, ht, rfl⟩
      exact h_rect s t hs ht
    · simpa using h_rect Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
  rw [← Measure.map_compProd_comap μ κ hf, ← Measure.map_compProd_comap μ η hf,
    klDiv_map_of_eq_withDensity_comp hD hg key]

end InformationTheory
