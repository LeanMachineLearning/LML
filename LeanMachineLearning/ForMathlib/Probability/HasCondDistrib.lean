/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Embedding
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

lemma IndepFun.hasCondDistrib_const [IsFiniteMeasure μ] {Q : Measure Ω} [SFinite Q]
    (h : IndepFun X Y μ) (hX : AEMeasurable X μ) (hY : HasLaw Y Q μ) :
    HasCondDistrib Y X (Kernel.const β Q) μ where
  aemeasurable := hX.prodMk hY.aemeasurable
  map_eq := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX hY.aemeasurable).1 h, hY.map_eq,
      Measure.compProd_const]

lemma hasCondDistrib_self [SFinite μ] (hX : AEMeasurable X μ) :
    HasCondDistrib X X (@Kernel.id β mβ) μ where
  aemeasurable := hX.prodMk hX
  map_eq := by
    rw [Measure.compProd_id, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]
    rfl

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

/-- `HasCondDistrib` only depends on the almost everywhere equivalence classes of the two random
variables. -/
lemma HasCondDistrib.congr {X' : α → β} {Y' : α → Ω} (h : HasCondDistrib Y X κ μ)
    (hX : X' =ᵐ[μ] X) (hY : Y' =ᵐ[μ] Y) :
    HasCondDistrib Y' X' κ μ := by
  have h_pair : (fun a ↦ (X' a, Y' a)) =ᵐ[μ] fun a ↦ (X a, Y a) := by
    filter_upwards [hX, hY] with a h1 h2
    rw [h1, h2]
  exact ⟨h.aemeasurable.congr h_pair.symm, by rw [Measure.map_congr h_pair,
    Measure.map_congr hX, h.map_eq]⟩

lemma HasCondDistrib.hasLaw_comp [SFinite μ] [IsSFiniteKernel κ] (h : HasCondDistrib Y X κ μ) :
    HasLaw Y (κ ∘ₘ (μ.map X)) μ := by
  refine ⟨by fun_prop, ?_⟩
  rw [← Measure.snd_compProd, ← h.map_eq, Measure.snd,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

lemma HasCondDistrib.prod {Z : α → Ω'} {η : Kernel (β × Ω) Ω'}
    (h1 : HasCondDistrib Y X κ μ) (h2 : HasCondDistrib Z (fun ω ↦ (X ω, Y ω)) η μ) :
    HasCondDistrib (fun ω ↦ (Y ω, Z ω)) X (κ ⊗ₖ η) μ := by
  refine ⟨by fun_prop, ?_⟩
  rw [← Measure.compProd_assoc', ← h1.map_eq, ← h2.map_eq,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

/-- A random variable that is almost surely a measurable function of `X` has the corresponding
deterministic conditional distribution given `X`. -/
lemma hasCondDistrib_deterministic [SFinite μ] {f : β → Ω} (hf : Measurable f)
    (hX : AEMeasurable X μ) (hY : Y =ᵐ[μ] f ∘ X) :
    HasCondDistrib Y X (Kernel.deterministic f hf) μ := by
  have h : HasCondDistrib (f ∘ X) X (Kernel.deterministic f hf) μ := by
    refine ⟨hX.prodMk (hf.comp_aemeasurable hX), ?_⟩
    rw [Measure.compProd_deterministic, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]
    rfl
  exact HasCondDistrib.congr h .rfl hY

lemma ae_eq_of_hasCondDistrib_deterministic [MeasurableEq Ω] [SFinite μ] {f : β → Ω}
    (hf : Measurable f) (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (h : HasCondDistrib Y X (Kernel.deterministic f hf) μ) :
    Y =ᵐ[μ] f ∘ X := by
  refine ae_eq_of_map_prodMk_eq hf hX hY ?_
  rw [h.map_eq, Measure.compProd_deterministic,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

section Const

section CompRight

variable [SFinite μ]

/-- Converse of `HasCondDistrib.comp_right` for a measurable embedding. -/
lemma HasCondDistrib.of_measurableEmbedding_comp_right {f : β → γ} (hf : MeasurableEmbedding f)
    {κ : Kernel γ Ω} [IsSFiniteKernel κ] (h : HasCondDistrib Y (f ∘ X) κ μ) :
    HasCondDistrib Y X (κ.comap f hf.measurable) μ := by
  have hX : AEMeasurable X μ := hf.aemeasurable_comp_iff.mp h.aemeasurable_fst
  have hY : AEMeasurable Y μ := h.aemeasurable_snd
  have hfm : Measurable (Prod.map f (id : Ω → Ω)) := hf.measurable.prodMap measurable_id
  refine ⟨hX.prodMk hY, (hf.prodMap MeasurableEmbedding.id).map_injective ?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable hfm.aemeasurable (by fun_prop)]
  calc μ.map (Prod.map f id ∘ fun ω ↦ (X ω, Y ω))
  _ = μ.map (f ∘ X) ⊗ₘ κ := h.map_eq
  _ = (μ.map X).map f ⊗ₘ κ := by
    rw [AEMeasurable.map_map_of_aemeasurable hf.measurable.aemeasurable hX]
  _ = (μ.map X ⊗ₘ κ.comap f hf.measurable).map (Prod.map f id) := by
    symm
    ext s hs
    rw [Measure.map_apply hfm hs, Measure.compProd_apply (hs.preimage hfm),
      Measure.compProd_apply hs,
      lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf.measurable]
    rfl

/-- `HasCondDistrib.comp_right` is an equivalence for measurable embeddings. -/
lemma hasCondDistrib_measurableEmbedding_comp_right_iff {f : β → γ} (hf : MeasurableEmbedding f)
    {κ : Kernel γ Ω} [IsSFiniteKernel κ] :
    HasCondDistrib Y (f ∘ X) κ μ ↔ HasCondDistrib Y X (κ.comap f hf.measurable) μ :=
  ⟨fun h ↦ h.of_measurableEmbedding_comp_right hf, fun h ↦ h.comp_right⟩

/-- `HasCondDistrib.comp_right` is an equivalence for measurable equivalences. -/
lemma hasCondDistrib_measurableEquiv_comp_right_iff (e : β ≃ᵐ γ) {κ : Kernel γ Ω}
    [IsSFiniteKernel κ] :
    HasCondDistrib Y (e ∘ X) κ μ ↔ HasCondDistrib Y X (κ.comap e e.measurable) μ :=
  hasCondDistrib_measurableEmbedding_comp_right_iff e.measurableEmbedding

end CompRight

section UniqueComponent

variable {δ : Type*} {mδ : MeasurableSpace δ} [Unique δ] [SFinite μ]

/-- Conditioning on a pair whose first component takes values in a type with a unique element
is the same as conditioning on the second component. -/
lemma hasCondDistrib_prodMk_left_unique_iff {U : α → δ} {η : Kernel (δ × β) Ω}
    [IsSFiniteKernel η] :
    HasCondDistrib Y (fun ω ↦ (U ω, X ω)) η μ ↔ HasCondDistrib Y X (η.sectR default) μ := by
  have hU : U = fun _ ↦ default := funext fun _ ↦ Unique.eq_default _
  subst hU
  exact hasCondDistrib_measurableEmbedding_comp_right_iff (measurableEmbedding_prodMk_left default)

/-- Conditioning on a pair whose second component takes values in a type with a unique element
is the same as conditioning on the first component. -/
lemma hasCondDistrib_prodMk_right_unique_iff {U : α → δ} {η : Kernel (β × δ) Ω}
    [IsSFiniteKernel η] :
    HasCondDistrib Y (fun ω ↦ (X ω, U ω)) η μ ↔ HasCondDistrib Y X (η.sectL default) μ := by
  have hU : U = fun _ ↦ default := funext fun _ ↦ Unique.eq_default _
  subst hU
  exact hasCondDistrib_measurableEmbedding_comp_right_iff
    (measurableEmbedding_prod_mk_right default)

end UniqueComponent


lemma _root_.MeasureTheory.Measure.dirac_compProd {κ : Kernel β Ω} [IsSFiniteKernel κ] (b : β) :
    Measure.dirac b ⊗ₘ κ = (κ b).map (Prod.mk b) := by
  ext s hs
  rw [Measure.compProd_apply hs, lintegral_dirac' _ (Kernel.measurable_kernel_prodMk_left hs),
    Measure.map_apply measurable_prodMk_left hs]

/-- Conditioning on a constant is the same as having law `κ b`. -/
lemma hasCondDistrib_const_iff [IsProbabilityMeasure μ] [IsSFiniteKernel κ] {b : β} :
    HasCondDistrib Y (fun _ ↦ b) κ μ ↔ HasLaw Y (κ b) μ := by
  refine ⟨fun h ↦ ⟨h.aemeasurable_snd, ?_⟩, fun h ↦ ⟨aemeasurable_const.prodMk h.aemeasurable, ?_⟩⟩
  · rw [← Measure.snd_map_prodMk₀ (X := fun _ ↦ b) (Y := Y) aemeasurable_const, h.map_eq,
      Measure.map_const, measure_univ, one_smul, Measure.dirac_compProd, Measure.snd,
      Measure.map_map measurable_snd measurable_prodMk_left]
    exact Measure.map_id
  · rw [Measure.map_const, measure_univ, one_smul, Measure.dirac_compProd, ← h.map_eq,
      AEMeasurable.map_map_of_aemeasurable measurable_prodMk_left.aemeasurable h.aemeasurable]
    rfl

alias ⟨HasCondDistrib.hasLaw_of_const', HasLaw.hasCondDistrib_const⟩ := hasCondDistrib_const_iff

end Const

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
