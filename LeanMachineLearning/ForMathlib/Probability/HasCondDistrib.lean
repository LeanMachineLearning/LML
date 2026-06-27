/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Independence.CondDistrib
public import Mathlib.Probability.HasCondDistrib

/-!
# A predicate for having a specified conditional distribution
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {α β γ Ω Ω' : Type*}
  {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {mΩ : MeasurableSpace Ω}
  {mΩ' : MeasurableSpace Ω'}
  {μ : Measure α} {X : α → β} {Y : α → Ω} {κ : Kernel β Ω}

lemma hasCondDistrib_fst_prod {Y : α → Ω} {X : α → β} {κ : Kernel β Ω}
    {μ : Measure α} {ν : Measure γ} [IsProbabilityMeasure ν]
    (h : HasCondDistrib Y X κ μ) :
    HasCondDistrib (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) κ (μ.prod ν) where
  aemeasurable := by fun_prop
  map_eq := by
    have h_rhs : Measure.map (fun ω ↦ X ω.1) (μ.prod ν) ⊗ₘ κ = (μ.map X) ⊗ₘ κ := by
      conv_rhs => rw [← Measure.fst_prod (μ := μ) (ν := ν), Measure.fst]
      rw [AEMeasurable.map_map_of_aemeasurable _ (by fun_prop)]
      · rfl
      · have := h.aemeasurable_fst
        simpa
    rw [h_rhs, ← h.map_eq]
    conv_rhs => rw [← Measure.fst_prod (μ := μ) (ν := ν), Measure.fst]
    rw [AEMeasurable.map_map_of_aemeasurable _ (by fun_prop)]
    · rfl
    · have := h.aemeasurable
      simpa

lemma HasCondDistrib.prod_right [IsFiniteMeasure μ] [IsFiniteKernel κ] (h : HasCondDistrib Y X κ μ)
    {f : β → γ} (hf : Measurable f) :
    HasCondDistrib Y (fun a ↦ (X a, f (X a))) (κ.prodMkRight _) μ := by
  refine ⟨by fun_prop, ?_⟩
  have h_eq := h.map_eq
  calc μ.map (fun x ↦ ((X x, f (X x)), Y x))
  _ = (μ.map (fun ω ↦ (X ω, Y ω))).map (fun p ↦ ((p.1, f p.1), p.2)) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    congr
  _ = (μ.map X ⊗ₘ κ).map (fun p ↦ ((p.1, f p.1), p.2)) := by rw [h_eq]
  _ = (μ.map X).map (fun a ↦ (a, f a)) ⊗ₘ κ.prodMkRight γ := by
    rw [Measure.compProd_eq_comp_prod, Measure.compProd_eq_comp_prod,
      ← Measure.deterministic_comp_eq_map (f := fun a ↦ (a, f a)),
      ← Measure.deterministic_comp_eq_map, Measure.comp_assoc, Measure.comp_assoc]
    swap; · fun_prop
    swap; · fun_prop
    congr 1
    ext b : 1
    rw [Kernel.comp_apply, Kernel.comp_apply, Kernel.prod_apply, Kernel.deterministic_apply,
      Kernel.id_apply, Measure.dirac_bind (Kernel.measurable _), Kernel.prod_apply,
      Measure.deterministic_comp_eq_map, Kernel.prodMkRight_apply, Kernel.id_apply]
    change Measure.map (Prod.map (fun x ↦ (x, f x)) id) ((Measure.dirac b).prod (κ b)) =
      (Measure.dirac (b, f b)).prod (κ b)
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), Measure.map_id,
      Measure.map_dirac' (by fun_prop)]
  _ = μ.map (fun a ↦ (X a, f (X a))) ⊗ₘ κ.prodMkRight γ := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    congr

lemma hasCondDistrib_prod_right_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] (X : α → β) (Y : α → Ω)
    {f : β → γ} (hf : Measurable f) :
    HasCondDistrib Y (fun a ↦ (X a, f (X a))) (κ.prodMkRight _) μ ↔ HasCondDistrib Y X κ μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.prod_right hf⟩
  have hX : AEMeasurable X μ := by
    have := h.aemeasurable_snd
    have h_eq : X = (fun p ↦ p.1) ∘ (fun a ↦ (X a, f (X a))) := by ext; simp
    rw [h_eq]
    exact Measurable.comp_aemeasurable (by fun_prop) (by fun_prop)
  refine ⟨by fun_prop, ?_⟩
  have h_eq := h.map_eq
  calc μ.map (fun x ↦ (X x, Y x))
  _ = (μ.map (fun ω ↦ ((X ω, f (X ω)), Y ω))).map (fun p ↦ (p.1.1, p.2)) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    congr
  _ = (μ.map (fun a ↦ (X a, f (X a))) ⊗ₘ κ.prodMkRight γ).map (fun p ↦ (p.1.1, p.2)) := by rw [h_eq]
  _ = ((μ.map X).map (fun a ↦ (a, f a)) ⊗ₘ κ.prodMkRight γ).map (fun p ↦ (p.1.1, p.2)) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    congr
  _ = μ.map X ⊗ₘ κ := by
    simp_rw [Measure.compProd_eq_comp_prod,
      ← Measure.deterministic_comp_eq_map (f := fun a ↦ (a, f a)) (by fun_prop),
      ← Measure.deterministic_comp_eq_map (f := fun p : (β × γ) × Ω ↦ (p.1.1, p.2)) (by fun_prop),
      Measure.comp_assoc]
    congr 1
    ext b : 1
    rw [Kernel.comp_apply, Kernel.comp_apply, Kernel.prod_apply, Kernel.id_apply,
      Kernel.deterministic_apply, Measure.dirac_bind (Kernel.measurable _),
      Kernel.prod_apply, Measure.deterministic_comp_eq_map, Kernel.prodMkRight_apply,
      Kernel.id_apply]
    change Measure.map (Prod.map (fun x ↦ x.1) id) ((Measure.dirac (b, f b)).prod (κ b)) = _
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), Measure.map_id,
      Measure.map_dirac' (by fun_prop)]

lemma HasCondDistrib.indepFun_of_const [IsProbabilityMeasure μ] {Q : Measure Ω} [SFinite Q]
    (h : HasCondDistrib Y X (Kernel.const β Q) μ) :
    IndepFun X Y μ := by
  rw [indepFun_iff_map_prod_eq_prod_map_map h.aemeasurable_fst h.aemeasurable_snd, h.map_eq,
    h.hasLaw_of_const.map_eq, Measure.compProd_const]

lemma HasCondDistrib.const_map_of_const [IsProbabilityMeasure μ] {Q : Measure Ω} [SFinite Q]
    (h : HasCondDistrib Y X (Kernel.const β Q) μ) :
    HasCondDistrib X Y (Kernel.const Ω (μ.map X)) μ where
  aemeasurable := by fun_prop
  map_eq := by
    calc μ.map (fun ω ↦ (Y ω, X ω))
    _ = (μ.map (fun ω ↦ (X ω, Y ω))).map Prod.swap := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
      rfl
    _ = (μ.map X ⊗ₘ Kernel.const β Q).map Prod.swap := by rw [h.map_eq]
    _ = μ.map Y ⊗ₘ Kernel.const Ω (μ.map X) := by simp [h.hasLaw_of_const.map_eq, Measure.prod_swap]

lemma HasLaw.prod_of_hasCondDistrib {P : Measure β}
    (h1 : HasLaw X P μ) (h2 : HasCondDistrib Y X κ μ) :
    HasLaw (fun ω ↦ (X ω, Y ω)) (P ⊗ₘ κ) μ :=
  ⟨by fun_prop, by rw [h2.map_eq, h1.map_eq]⟩

lemma HasCondDistrib.prod {Z : α → Ω'} {η : Kernel (β × Ω) Ω'}
    (h1 : HasCondDistrib Y X κ μ) (h2 : HasCondDistrib Z (fun ω ↦ (X ω, Y ω)) η μ) :
    HasCondDistrib (fun ω ↦ (Y ω, Z ω)) X (κ ⊗ₖ η) μ := by
  refine ⟨by fun_prop, ?_⟩
  rw [← Measure.compProd_assoc', ← h1.map_eq, ← h2.map_eq,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

lemma ae_eq_of_hasCondDistrib_deterministic [MeasurableEq Ω] [SFinite μ] {f : β → Ω}
    (hf : Measurable f) (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (h : HasCondDistrib Y X (Kernel.deterministic f hf) μ) :
    Y =ᵐ[μ] f ∘ X := by
  refine ae_eq_of_map_prodMk_eq hf hX hY ?_
  rw [h.map_eq, Measure.compProd_deterministic,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

variable [StandardBorelSpace Ω] [Nonempty Ω] [StandardBorelSpace Ω'] [Nonempty Ω']

lemma HasCondDistrib.condDistrib_eq [IsFiniteMeasure μ] [IsFiniteKernel κ]
    (h : HasCondDistrib Y X κ μ) :
    condDistrib Y X μ =ᵐ[μ.map X] κ := by
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop), h.map_eq]

lemma hasCondDistrib_of_condDistrib_eq [IsFiniteMeasure μ] [IsFiniteKernel κ]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (h : condDistrib Y X μ =ᵐ[μ.map X] κ) :
    HasCondDistrib Y X κ μ where
  aemeasurable := by fun_prop
  map_eq := by rw [← compProd_map_condDistrib hY, Measure.compProd_congr h]

lemma HasCondDistrib.hasCondDistrib_sectR [IsFiniteMeasure μ] [StandardBorelSpace β] [Nonempty β]
    {W : α → Ω'} {Z : α → γ} {f : Ω' → β} {g : Ω' → Ω}
    {η : Kernel (γ × β) Ω} [IsFiniteKernel η] (hf : Measurable f)
    (hg : Measurable g) (hW : AEMeasurable W μ)
    (hcd : HasCondDistrib (g ∘ W) (fun a ↦ (Z a, (f ∘ W) a)) η μ) :
    ∀ᵐ z ∂(μ.map Z), HasCondDistrib g f (η.sectR z) (condDistrib W Z μ z) := by
  suffices ∀ᵐ z ∂μ.map Z, condDistrib g f (condDistrib W Z μ z) =ᵐ[(condDistrib W Z μ z).map f]
      (η.sectR z) by
    filter_upwards [this] with z hz
    exact hasCondDistrib_of_condDistrib_eq (by fun_prop) (by fun_prop) hz
  have h_eq : condDistrib (g ∘ W) (fun a ↦ (Z a, (f ∘ W) a)) μ
      =ᵐ[μ.map Z ⊗ₘ (condDistrib W Z μ).map f] η := by
    rw [← Measure.compProd_congr (condDistrib_comp Z hW hf),
        compProd_map_condDistrib (hf.comp_aemeasurable hW)]
    exact hcd.condDistrib_eq
  filter_upwards [
    condDistrib_condDistrib_ae_eq_sectR_condDistrib hf hg hW hcd.aemeasurable_fst.fst,
    Measure.ae_ae_of_ae_compProd h_eq] with z hc ha
  rw [Kernel.map_apply _ hf] at ha
  filter_upwards [hc, ha] with b hcb hab using hcb.trans hab

end ProbabilityTheory
