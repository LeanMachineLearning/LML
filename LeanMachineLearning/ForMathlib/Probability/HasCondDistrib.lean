/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Embedding
public import LeanMachineLearning.ForMathlib.Probability.HasLaw
public import LeanMachineLearning.ForMathlib.Probability.Kernel.CondDistrib
public import LeanMachineLearning.ForMathlib.Probability.Kernel.Basic
public import LeanMachineLearning.ForMathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.HasCondDistrib

/-!
# Lemmas about `HasCondDistrib`

`HasCondDistrib Y X κ μ` states that the conditional distribution of `Y` given `X` under `μ` is
the kernel `κ`. This file complements the API of Mathlib's `Mathlib.Probability.HasCondDistrib`.

## Main statements

* `HasCondDistrib.compProd`: chain rule, building the conditional distribution of a pair.
* `hasCondDistrib_measurableEmbedding_comp_right_iff`: conditioning on `f ∘ X` for a measurable
  embedding `f` is the same as conditioning on `X`.
* `HasCondDistrib.hasLaw_cond`, `HasCondDistrib.indepFun_cond`: if the conditional distribution
  of `Y` given `X` is constant on a set `s`, then `Y` has that law under `μ` conditioned on
  `X ∈ s`, and is independent of `X` under that conditioned measure.
* `HasCondDistrib.condDistrib_ae_eq`, `hasCondDistrib_of_condDistrib_ae_eq`: relation with
  `condDistrib`.
* `HasCondDistrib.condExp_comp_ae_eq`: the conditional expectation of `g ∘ Y` given `X` is the
  integral of `g` against the conditional distribution.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {α β γ Ω Ω' : Type*}
  {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {mΩ : MeasurableSpace Ω}
  {mΩ' : MeasurableSpace Ω'}
  {μ : Measure α} {X : α → β} {Y : α → Ω} {κ : Kernel β Ω}

/-- If `Y` has conditional distribution `κ` given `X` under `μ` and `f` has law `μ` under `P`,
then `Y ∘ f` has conditional distribution `κ` given `X ∘ f` under `P`. -/
lemma HasCondDistrib.comp_hasLaw {P : Measure Ω'} {f : Ω' → α} (h : HasCondDistrib Y X κ μ)
    (hf : HasLaw f μ P) :
    HasCondDistrib (Y ∘ f) (X ∘ f) κ P := by
  refine ⟨(h.comp hf).aemeasurable, ?_⟩
  rw [← AEMeasurable.map_map_of_aemeasurable (hf.map_eq ▸ h.aemeasurable_fst) hf.aemeasurable,
    hf.map_eq]
  exact (h.comp hf).map_eq

lemma hasCondDistrib_fst_prod {ν : Measure γ} [IsProbabilityMeasure ν]
    (h : HasCondDistrib Y X κ μ) :
    HasCondDistrib (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) κ (μ.prod ν) :=
  h.comp_hasLaw (hasLaw_fst_prod μ ν)

lemma HasCondDistrib.prod_right [SFinite μ] [IsSFiniteKernel κ] (h : HasCondDistrib Y X κ μ)
    {f : β → γ} (hf : Measurable f) :
    HasCondDistrib Y (fun a ↦ (X a, f (X a))) (κ.prodMkRight _) μ :=
  -- `(κ.prodMkRight γ).comap (fun b ↦ (b, f b))` is definitionally equal to `κ`
  HasCondDistrib.comp_right (hf := measurable_id.prodMk hf) (Z := X) h

lemma hasCondDistrib_prod_right_iff [SFinite μ] [IsSFiniteKernel κ] (X : α → β) (Y : α → Ω)
    {f : β → γ} (hf : Measurable f) :
    HasCondDistrib Y (fun a ↦ (X a, f (X a))) (κ.prodMkRight _) μ ↔ HasCondDistrib Y X κ μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.prod_right hf⟩
  have hX : AEMeasurable X μ := measurable_fst.comp_aemeasurable h.aemeasurable_fst
  refine ⟨hX.prodMk h.aemeasurable_snd, ?_⟩
  have h_fst : μ.map X = (μ.map (fun a ↦ (X a, f (X a)))).fst := by
    rw [Measure.fst, AEMeasurable.map_map_of_aemeasurable (by fun_prop) h.aemeasurable_fst]
    rfl
  rw [h_fst, ← Measure.map_prodMap_fst_compProd_prodMkRight, ← h.map_eq,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) h.aemeasurable]
  rfl

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
    HasCondDistrib X Y (Kernel.const Ω (μ.map X)) μ :=
  h.indepFun_of_const.symm.hasCondDistrib_const h.aemeasurable_snd (hasLaw_map h.aemeasurable_fst)

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

/-- Chain rule for conditional distributions: if `κ` is the conditional distribution of `Y`
given `X` and `η` is the conditional distribution of `Z` given `(X, Y)`, then `κ ⊗ₖ η` is the
conditional distribution of `(Y, Z)` given `X`. See `HasCondDistrib.of_compProd` for a converse. -/
lemma HasCondDistrib.compProd {Z : α → Ω'} {η : Kernel (β × Ω) Ω'}
    (h1 : HasCondDistrib Y X κ μ) (h2 : HasCondDistrib Z (fun ω ↦ (X ω, Y ω)) η μ) :
    HasCondDistrib (fun ω ↦ (Y ω, Z ω)) X (κ ⊗ₖ η) μ := by
  refine ⟨by fun_prop, ?_⟩
  rw [← Measure.compProd_assoc', ← h1.map_eq, ← h2.map_eq,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

lemma hasCondDistrib_comp_self [SFinite μ] {f : β → Ω} (hf : Measurable f)
    (hX : AEMeasurable X μ) :
    HasCondDistrib (f ∘ X) X (Kernel.deterministic f hf) μ := by
  refine ⟨hX.prodMk (hf.comp_aemeasurable hX), ?_⟩
  rw [Measure.compProd_deterministic, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]
  rfl

/-- If the conditional distribution of `Y` given `X` is deterministic, given by a function `f`, then
`Y` is almost surely equal to `f ∘ X`. -/
lemma HasCondDistrib.ae_eq_of_deterministic [MeasurableEq Ω] [SFinite μ] {f : β → Ω}
    {hf : Measurable f} (h : HasCondDistrib Y X (Kernel.deterministic f hf) μ) :
    Y =ᵐ[μ] f ∘ X := by
  refine ae_eq_of_map_prodMk_eq hf h.aemeasurable_fst h.aemeasurable_snd ?_
  rw [h.map_eq, Measure.compProd_deterministic,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

lemma hasCondDistrib_deterministic_iff [MeasurableEq Ω] [SFinite μ] {f : β → Ω}
    (hf : Measurable f) (hX : AEMeasurable X μ) :
    HasCondDistrib Y X (Kernel.deterministic f hf) μ ↔ Y =ᵐ[μ] f ∘ X :=
  ⟨fun h ↦ h.ae_eq_of_deterministic, fun h ↦ (hasCondDistrib_comp_self hf hX).congr .rfl h⟩

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

section Const

/-- Conditioning on a constant is the same as having law `κ b`. -/
lemma hasCondDistrib_const_iff [IsProbabilityMeasure μ] [IsSFiniteKernel κ] {b : β} :
    HasCondDistrib Y (fun _ ↦ b) κ μ ↔ HasLaw Y (κ b) μ := by
  refine ⟨fun h ↦ ⟨h.aemeasurable_snd, ?_⟩, fun h ↦ ⟨aemeasurable_const.prodMk h.aemeasurable, ?_⟩⟩
  · rw [← Measure.snd_map_prodMk₀ (X := fun _ ↦ b) (Y := Y) aemeasurable_const
      h.aemeasurable_snd, h.map_eq,
      Measure.map_const, measure_univ, one_smul, Measure.dirac_compProd, Measure.snd,
      Measure.map_map measurable_snd measurable_prodMk_left]
    exact Measure.map_id
  · rw [Measure.map_const, measure_univ, one_smul, Measure.dirac_compProd, ← h.map_eq,
      AEMeasurable.map_map_of_aemeasurable measurable_prodMk_left.aemeasurable h.aemeasurable]
    rfl

alias ⟨HasCondDistrib.hasLaw_of_const', HasLaw.hasCondDistrib_const⟩ := hasCondDistrib_const_iff

end Const

/-- A random variable with values in `Unit` admits any Markov kernel as conditional
distribution. -/
lemma hasCondDistrib_unit [SFinite μ] (hX : AEMeasurable X μ) (U : α → Unit)
    (η : Kernel β Unit) [IsMarkovKernel η] :
    HasCondDistrib U X η μ := by
  have hU : U = fun _ ↦ () := funext fun _ ↦ rfl
  subst hU
  refine HasLaw.mk (hX.prodMk aemeasurable_const) ?_
  rw [η.eq_const_dirac_of_subsingleton (), Measure.compProd_const, Measure.prod_dirac,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]
  rfl

section Cond

variable [IsSFiniteKernel κ]

/-- If the conditional distribution of `Y` given `X` is a kernel `κ` which is constant equal to `η`
on a measurable set `s`, then `μ (X ⁻¹' s ∩ Y ⁻¹' u) = μ (X ⁻¹' s) * η u` for all measurable `u`. -/
lemma HasCondDistrib.measure_inter_preimage_eq_mul_of_eqOn_const [SFinite μ]
    (h : HasCondDistrib Y X κ μ) {s : Set β} (hs : MeasurableSet s) {η : Measure Ω}
    (hκ : Set.EqOn κ (fun _ ↦ η) s) {u : Set Ω} (hu : MeasurableSet u) :
    μ (X ⁻¹' s ∩ Y ⁻¹' u) = μ (X ⁻¹' s) * η u := by
  have h_eq : X ⁻¹' s ∩ Y ⁻¹' u = (fun ω ↦ (X ω, Y ω)) ⁻¹' (s ×ˢ u) := by
    ext ω
    simp
  rw [h_eq, ← Measure.map_apply_of_aemeasurable h.aemeasurable (hs.prod hu), h.map_eq,
    Measure.compProd_apply_prod hs hu,
    setLIntegral_congr_fun hs (g := fun _ ↦ η u) (fun x hx ↦ by rw [hκ hx]),
    setLIntegral_const, Measure.map_apply_of_aemeasurable h.aemeasurable_fst hs, mul_comm]

variable [IsFiniteMeasure μ]

/-- If the conditional distribution of `Y` given `X` is a kernel `κ` which is constant equal to `η`
on a measurable set `s`, then the law of `Y` under `μ` conditioned on `X ∈ s` is `η`. -/
lemma HasCondDistrib.hasLaw_cond (h : HasCondDistrib Y X κ μ)
    {s : Set β} (hs : MeasurableSet s) {η : Measure Ω} (hκ : Set.EqOn κ (fun _ ↦ η) s)
    (hμs : μ (X ⁻¹' s) ≠ 0) :
    HasLaw Y η μ[|X ⁻¹' s] where
  aemeasurable := h.aemeasurable_snd.mono_ac cond_absolutelyContinuous
  map_eq := by
    ext u hu
    rw [Measure.map_apply_of_aemeasurable (h.aemeasurable_snd.mono_ac cond_absolutelyContinuous) hu,
      cond, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply₀ (h.aemeasurable_snd.restrict.nullMeasurableSet_preimage hu),
      Set.inter_comm, h.measure_inter_preimage_eq_mul_of_eqOn_const hs hκ hu, ← mul_assoc,
      ENNReal.inv_mul_cancel hμs (measure_ne_top _ _), one_mul]

/-- If the conditional distribution of `Y` given `X` is a kernel `κ` which is constant on a
measurable set `s`, then `X` and `Y` are independent under `μ` conditioned on `X ∈ s`. -/
lemma HasCondDistrib.indepFun_cond (h : HasCondDistrib Y X κ μ) (hX : Measurable X)
    {s : Set β} (hs : MeasurableSet s) {η : Measure Ω} (hκ : Set.EqOn κ (fun _ ↦ η) s) :
    X ⟂ᵢ[μ[|X ⁻¹' s]] Y := by
  by_cases hμs : μ (X ⁻¹' s) = 0
  · rw [cond_eq_zero.2 (Or.inr hμs)]
    simp [indepFun_iff_measure_inter_preimage_eq_mul]
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro t u ht hu
  have h1 : X ⁻¹' s ∩ (X ⁻¹' t ∩ Y ⁻¹' u) = X ⁻¹' (s ∩ t) ∩ Y ⁻¹' u := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [cond_apply (hs.preimage hX), cond_apply (hs.preimage hX), cond_apply (hs.preimage hX), h1,
    ← Set.preimage_inter,
    h.measure_inter_preimage_eq_mul_of_eqOn_const (hs.inter ht) (hκ.mono Set.inter_subset_left)
      hu,
    h.measure_inter_preimage_eq_mul_of_eqOn_const hs hκ hu,
    ← mul_assoc (μ (X ⁻¹' s))⁻¹ (μ (X ⁻¹' s)) (η u),
    ENNReal.inv_mul_cancel hμs (measure_ne_top _ _), one_mul, mul_assoc]

end Cond

variable [StandardBorelSpace Ω] [Nonempty Ω] [StandardBorelSpace Ω'] [Nonempty Ω']

lemma HasCondDistrib.condDistrib_ae_eq [IsFiniteMeasure μ] [IsFiniteKernel κ]
    (h : HasCondDistrib Y X κ μ) :
    condDistrib Y X μ =ᵐ[μ.map X] κ := by
  rw [condDistrib_ae_eq_iff_measure_eq_compProd h.aemeasurable_fst h.aemeasurable_snd, h.map_eq]

lemma hasCondDistrib_of_condDistrib_ae_eq [IsFiniteMeasure μ] [IsSFiniteKernel κ]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (h : condDistrib Y X μ =ᵐ[μ.map X] κ) :
    HasCondDistrib Y X κ μ where
  aemeasurable := by fun_prop
  map_eq := by rw [← compProd_map_condDistrib hX hY, Measure.compProd_congr h]

lemma HasCondDistrib.hasCondDistrib_sectR [IsFiniteMeasure μ] [StandardBorelSpace β] [Nonempty β]
    {W : α → Ω'} {Z : α → γ} {f : Ω' → β} {g : Ω' → Ω}
    {η : Kernel (γ × β) Ω} [IsFiniteKernel η] (hf : Measurable f)
    (hg : Measurable g) (hW : AEMeasurable W μ)
    (hcd : HasCondDistrib (g ∘ W) (fun a ↦ (Z a, (f ∘ W) a)) η μ) :
    ∀ᵐ z ∂(μ.map Z), HasCondDistrib g f (η.sectR z) (condDistrib W Z μ z) := by
  suffices ∀ᵐ z ∂μ.map Z, condDistrib g f (condDistrib W Z μ z) =ᵐ[(condDistrib W Z μ z).map f]
      (η.sectR z) by
    filter_upwards [this] with z hz
    exact hasCondDistrib_of_condDistrib_ae_eq (by fun_prop) (by fun_prop) hz
  have h_eq : condDistrib (g ∘ W) (fun a ↦ (Z a, (f ∘ W) a)) μ
      =ᵐ[μ.map Z ⊗ₘ (condDistrib W Z μ).map f] η := by
    rw [← Measure.compProd_congr (condDistrib_comp hcd.aemeasurable_fst.fst hW hf),
        compProd_map_condDistrib hcd.aemeasurable_fst.fst (hf.comp_aemeasurable hW)]
    exact hcd.condDistrib_ae_eq
  filter_upwards [
    condDistrib_condDistrib_ae_eq_sectR_condDistrib hf hg hW hcd.aemeasurable_fst.fst,
    Measure.ae_ae_of_ae_compProd h_eq] with z hc ha
  rw [Kernel.map_apply _ hf] at ha
  filter_upwards [hc, ha] with b hcb hab using hcb.trans hab

/-- If `Y` has conditional distribution `κ` given `X`, then the conditional expectation of `g ∘ Y`
given `X` is `∫ y, g y ∂(κ (X ·))`. -/
lemma HasCondDistrib.condExp_comp_ae_eq [IsFiniteMeasure μ] [IsFiniteKernel κ]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (h : HasCondDistrib Y X κ μ) (hX : Measurable X) {g : Ω → F} (hg : StronglyMeasurable g)
    (hint : Integrable (fun a ↦ g (Y a)) μ) :
    μ[fun a ↦ g (Y a) | mβ.comap X] =ᵐ[μ] fun a ↦ ∫ y, g y ∂(κ (X a)) := by
  refine (condExp_ae_eq_integral_condDistrib hX h.aemeasurable_snd hg hint).trans ?_
  filter_upwards [ae_of_ae_map hX.aemeasurable h.condDistrib_ae_eq] with a ha
  rw [ha]

end ProbabilityTheory
