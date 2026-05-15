/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.Probability.Independence.CondDistrib
public import Mathlib.Probability.HasLaw

/-!
# A predicate for having a specified conditional distribution
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {α β γ Ω Ω' : Type*}
  {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] [Nonempty Ω]
  {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] [Nonempty Ω']
  {μ : Measure α} {X : α → β} {Y : α → Ω} {κ : Kernel β Ω}

/-- Predicate stating that the conditional distribution of `Y` given `X` under the measure `μ`
is equal to the kernel `κ`. -/
structure HasCondDistrib (Y : α → Ω) (X : α → β) (κ : Kernel β Ω)
  (μ : Measure α) [IsFiniteMeasure μ] : Prop where
  aemeasurable_fst : AEMeasurable Y μ := by fun_prop
  aemeasurable_snd : AEMeasurable X μ := by fun_prop
  condDistrib_eq : condDistrib Y X μ =ᵐ[μ.map X] κ

attribute [fun_prop] HasCondDistrib.aemeasurable_fst HasCondDistrib.aemeasurable_snd

lemma hasCondDistrib_fst_prod {Y : α → Ω} {X : α → β}
    {κ : Kernel β Ω}
    {μ : Measure α} [IsFiniteMeasure μ] {ν : Measure γ} [IsProbabilityMeasure ν]
    (h : HasCondDistrib Y X κ μ) :
    HasCondDistrib (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) κ (μ.prod ν) where
  aemeasurable_fst := by have := h.aemeasurable_fst; fun_prop
  aemeasurable_snd := by have := h.aemeasurable_snd; fun_prop
  condDistrib_eq := by
    have : ((μ.prod ν).map (fun ω ↦ X ω.1)) = μ.map X := by
      conv_rhs => rw [← Measure.fst_prod (μ := μ) (ν := ν), Measure.fst]
      rw [AEMeasurable.map_map_of_aemeasurable _ (by fun_prop)]
      · rfl
      · have := h.aemeasurable_snd
        simpa
    rw [this]
    exact (condDistrib_fst_prod X h.aemeasurable_fst ν).trans h.condDistrib_eq

lemma HasCondDistrib.comp [IsFiniteMeasure μ]
    (h : HasCondDistrib Y X κ μ) {f : Ω → Ω'} (hf : Measurable f) :
    HasCondDistrib (fun ω ↦ f (Y ω)) X (κ.map f) μ where
  aemeasurable_fst := by have := h.aemeasurable_fst; fun_prop
  aemeasurable_snd := by have := h.aemeasurable_snd; fun_prop
  condDistrib_eq := by
    have h_comp := condDistrib_comp X (Y := Y) (f := f) (mβ := mβ) h.aemeasurable_fst hf
    refine h_comp.trans ?_
    have h' := h.condDistrib_eq
    filter_upwards [h'] with ω hω
    rw [Kernel.map_apply _ hf, hω, Kernel.map_apply _ hf]

lemma HasCondDistrib.fst {Y : α → Ω × Ω'} {κ : Kernel β (Ω × Ω')} [IsFiniteMeasure μ]
    (h : HasCondDistrib Y X κ μ) :
    HasCondDistrib (fun ω ↦ (Y ω).1) X κ.fst μ := by
  rw [Kernel.fst_eq]
  exact HasCondDistrib.comp h measurable_fst

lemma HasCondDistrib.snd {Y : α → Ω × Ω'} {κ : Kernel β (Ω × Ω')} [IsFiniteMeasure μ]
    (h : HasCondDistrib Y X κ μ) :
    HasCondDistrib (fun ω ↦ (Y ω).2) X κ.snd μ := by
  rw [Kernel.snd_eq]
  exact HasCondDistrib.comp h measurable_snd

-- TODO: Rename to `HasCondDistrib.comp_right`?
lemma HasCondDistrib.comp_right' [IsFiniteMeasure μ] [IsFiniteKernel κ] {f : γ → β}
    (hf : Measurable f) {Z : α → γ} (h : HasCondDistrib Y Z (κ.comap f hf) μ) :
    HasCondDistrib Y (f ∘ Z) κ μ := by
  have hY : AEMeasurable Y μ := h.aemeasurable_fst
  have hZ : AEMeasurable Z μ := h.aemeasurable_snd
  have hfZ : AEMeasurable (f ∘ Z) μ := hf.comp_aemeasurable hZ
  refine ⟨hY, hfZ, ?_⟩
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ hY]
  calc μ.map (fun a ↦ ((f ∘ Z) a, Y a))
  _ = (μ.map (fun a ↦ (Z a, Y a))).map (Prod.map f id) := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (hZ.prodMk hY)]
      rfl
  _ = (μ.map Z ⊗ₘ κ.comap f hf).map (Prod.map f id) := by
      rw [(condDistrib_ae_eq_iff_measure_eq_compProd Z hY _).mp h.condDistrib_eq]
  _ = (μ.map Z).map f ⊗ₘ κ := by
      ext s hs
      rw [Measure.map_apply (by fun_prop) hs, Measure.compProd_apply (by measurability),
          Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
      rfl
  _ = μ.map (f ∘ Z) ⊗ₘ κ := by
      rw [AEMeasurable.map_map_of_aemeasurable hf.aemeasurable hZ]

lemma HasCondDistrib.comp_right [IsFiniteMeasure μ] [IsFiniteKernel κ] (h : HasCondDistrib Y X κ μ)
    (f : β ≃ᵐ γ) :
    HasCondDistrib Y (f ∘ X) (κ.comap f.symm (by fun_prop) : Kernel γ Ω) μ := by
  apply HasCondDistrib.comp_right' f.measurable
  simpa [← Kernel.comap_comp_right]

lemma HasCondDistrib.prod_right [IsFiniteMeasure μ] [IsFiniteKernel κ] (h : HasCondDistrib Y X κ μ)
    {f : β → γ} (hf : Measurable f) :
    HasCondDistrib Y (fun a ↦ (X a, f (X a))) (κ.prodMkRight _) μ := by
  have hY := h.aemeasurable_fst
  have hX := h.aemeasurable_snd
  refine ⟨h.aemeasurable_fst, by fun_prop, ?_⟩
  have h_eq := h.condDistrib_eq
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop) _] at h_eq ⊢
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
  have hY := h.aemeasurable_fst
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  have h_eq := h.condDistrib_eq
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop) _] at h_eq ⊢
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

lemma HasCondDistrib.hasLaw_of_const [IsProbabilityMeasure μ] {Q : Measure Ω} [SFinite Q]
    (h : HasCondDistrib Y X (Kernel.const β Q) μ) : HasLaw Y Q μ := by
  obtain ⟨hY, hX, h⟩ := h
  refine ⟨hY, ?_⟩
  have h_snd : (μ.map (fun ω => (X ω, Y ω))).snd = Q := by
    have h_map : μ.map (fun ω => (X ω, Y ω)) = (μ.map X) ⊗ₘ (Kernel.const _ Q) :=
      have h_map : μ.map (fun ω => (X ω, Y ω)) = (μ.map X) ⊗ₘ (condDistrib Y X μ) :=
      (compProd_map_condDistrib hY).symm
      h_map.trans (Measure.compProd_congr h)
    rw [h_map, MeasureTheory.Measure.snd_compProd]
    simp [MeasureTheory.Measure.map_apply_of_aemeasurable hX]
  rwa [Measure.snd_map_prodMk₀ hX] at h_snd

lemma HasCondDistrib.indepFun_of_const [IsProbabilityMeasure μ] {Q : Measure Ω} [SFinite Q]
    (h : HasCondDistrib Y X (Kernel.const β Q) μ) : IndepFun X Y μ := by
  rw [indepFun_iff_condDistrib_eq_const h.aemeasurable_snd h.aemeasurable_fst,
    h.hasLaw_of_const.map_eq]
  exact h.condDistrib_eq

lemma HasCondDistrib.const_map_of_const [IsProbabilityMeasure μ] {Q : Measure Ω} [SFinite Q]
    (h : HasCondDistrib Y X (Kernel.const β Q) μ) [StandardBorelSpace β] [Nonempty β] :
    HasCondDistrib X Y (Kernel.const Ω (μ.map X)) μ where
  aemeasurable_fst := h.aemeasurable_snd
  aemeasurable_snd := h.aemeasurable_fst
  condDistrib_eq :=
    condDistrib_of_indepFun h.indepFun_of_const.symm h.aemeasurable_fst h.aemeasurable_snd

lemma HasLaw.prod_of_hasCondDistrib {P : Measure β} [IsFiniteMeasure μ] [IsSFiniteKernel κ]
    (h1 : HasLaw X P μ) (h2 : HasCondDistrib Y X κ μ) :
    HasLaw (fun ω ↦ (X ω, Y ω)) (P ⊗ₘ κ) μ := by
  have hX := h1.aemeasurable
  have hY := h2.aemeasurable_fst
  refine ⟨by fun_prop, ?_⟩
  rw [← compProd_map_condDistrib (by fun_prop), h1.map_eq]
  refine Measure.compProd_congr ?_
  rw [← h1.map_eq]
  exact h2.condDistrib_eq

lemma HasCondDistrib.of_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ] {Z : α → Ω'}
    {η : Kernel (β × Ω) Ω'} [IsMarkovKernel η]
    (h : HasCondDistrib (fun a ↦ (Y a, Z a)) X (κ ⊗ₖ η) μ) :
    HasCondDistrib Z (fun a ↦ (X a, Y a)) η μ := by
  have hZ : AEMeasurable Z μ := h.aemeasurable_fst.snd
  have hX : AEMeasurable X μ := h.aemeasurable_snd
  have hY : AEMeasurable Y μ := h.aemeasurable_fst.fst
  refine ⟨hZ, (hX.prodMk hY), ?_⟩
  have hc := h.condDistrib_eq
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)] at hc ⊢
  calc μ.map (fun a ↦ ((X a, Y a), Z a))
  _ = (μ.map X ⊗ₘ (κ ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm := by
      rw [← hc, AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
      rfl
  _ = μ.map X ⊗ₘ κ ⊗ₘ η :=
      Measure.compProd_assoc
  _ = μ.map (fun a ↦ (X a, Y a)) ⊗ₘ η := by
      rw [← (condDistrib_ae_eq_iff_measure_eq_compProd X hY κ).1]
      simpa using h.fst.condDistrib_eq

lemma HasCondDistrib.prod [IsFiniteMeasure μ] [IsFiniteKernel κ]
    {Z : α → Ω'} {η : Kernel (β × Ω) Ω'} [IsFiniteKernel η]
    (h1 : HasCondDistrib Y X κ μ) (h2 : HasCondDistrib Z (fun ω ↦ (X ω, Y ω)) η μ) :
    HasCondDistrib (fun ω ↦ (Y ω, Z ω)) X (κ ⊗ₖ η) μ := by
  have hX := h1.aemeasurable_snd
  have hY := h1.aemeasurable_fst
  have hZ := h2.aemeasurable_fst
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  have h_condDistrib_Y := h1.condDistrib_eq
  have h_condDistrib_Z := h2.condDistrib_eq
  have h_prod := condDistrib_prod_left hY hZ hX
  have h_prod' : 𝓛[fun ω ↦ (Y ω, Z ω) | X; μ] =ᵐ[μ.map X] (κ ⊗ₖ 𝓛[Z | fun ω ↦ (X ω, Y ω); μ]) := by
    filter_upwards [h_condDistrib_Y, h_prod] with ω hω₁ hω₂
    rw [hω₂]
    ext s hs
    rw [Kernel.compProd_apply hs, Kernel.compProd_apply hs]
    simp [hω₁]
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)]
    at h_condDistrib_Z h_condDistrib_Y ⊢
  rw [← Measure.compProd_assoc', ← h_condDistrib_Y, ← h_condDistrib_Z,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

lemma HasCondDistrib.ae_hasCondDistrib_sectR [IsFiniteMeasure μ] [StandardBorelSpace β] [Nonempty β]
    {W : α → Ω'} {Z : α → γ} {f : Ω' → β} {g : Ω' → Ω} {η : Kernel (γ × β) Ω} [IsFiniteKernel η]
    (hf : Measurable f) (hg : Measurable g) (hW : AEMeasurable W μ)
    (hcd : HasCondDistrib (g ∘ W) (fun a ↦ (Z a, f (W a))) η μ) :
    ∀ᵐ z ∂(μ.map Z), HasCondDistrib g f (η.sectR z) (condDistrib W Z μ z) := by
  have h_eq : (condDistrib (g ∘ W) (fun a ↦ (Z a, f (W a))) μ)
      =ᵐ[μ.map Z ⊗ₘ (condDistrib W Z μ).map f] η := by
    rw [← Measure.compProd_congr (condDistrib_comp Z hW hf),
        compProd_map_condDistrib (X := Z) (hf.comp_aemeasurable hW)]
    exact hcd.condDistrib_eq
  filter_upwards [
    ae_condDistrib_condDistrib_ae_eq_sectR_condDistrib hf hg hW hcd.aemeasurable_snd.fst,
    Measure.ae_ae_of_ae_compProd h_eq] with z ht hn
  refine ⟨hg.aemeasurable, hf.aemeasurable, ?_⟩
  apply ht.trans
  rw [← Kernel.map_apply _ hf]
  exact hn.mono (fun _ hb ↦ hb)

end ProbabilityTheory
