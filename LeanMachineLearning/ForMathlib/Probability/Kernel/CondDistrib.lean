/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.AEMeasurable
public import LeanMachineLearning.ForMathlib.Probability.ConditionalProbability
public import LeanMachineLearning.ForMathlib.Probability.Kernel.RadonNikodym
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Lemmas about conditional distributions

This file contains lemmas about `condDistrib`: its behavior with respect to products and
compositions of the random variables, and its expression as a conditioned measure when
conditioning on a random variable with countably many values.

## Main statements

* `condDistrib_prod_left`: chain rule for `condDistrib`.
* `ae_eq_of_condDistrib_eq_deterministic`: if the conditional distribution of `Y` given `X` is
  a.e. the deterministic kernel of `f`, then `Y = f ∘ X` almost surely.
* `condDistrib_ae_eq_cond`: for `X` with countably many values, `condDistrib Y X μ` is given by
  the laws of `Y` under the conditioned measures `μ[|X ⁻¹' {b}]`.
* `condDistrib_prod_of_forall_condDistrib_cond`: for `Z` with countably many values, the
  conditional distribution of `Y` given `(X, Z)` can be computed from the conditional
  distributions of `Y` given `X` under the conditioned measures `μ[|Z ⁻¹' {b}]`.

## Notation

* `𝓛[Y | X; μ]`: the conditional distribution `condDistrib Y X μ`, scoped in `ProbabilityTheory`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

variable {α β γ δ Ω Ω' : Type*}
  {mα : MeasurableSpace α} {μ : Measure α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {mδ : MeasurableSpace δ}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [mΩ' : MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
  {X : α → β} {Y : α → Ω} {Z : α → Ω'} {T : α → γ}

namespace ProbabilityTheory

/-- Law of `Y` conditioned on `X`. -/
scoped notation "𝓛[" Y " | " X "; " μ "]" => condDistrib Y X μ

section CondDistrib

variable [IsFiniteMeasure μ]

lemma map_swap_compProd_map_condDistrib (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    (μ.map X ⊗ₘ condDistrib Y X μ).map Prod.swap = μ.map (fun a ↦ (Y a, X a)) := by
  rw [compProd_map_condDistrib hX hY,
    AEMeasurable.map_map_of_aemeasurable measurable_swap.aemeasurable (hX.prodMk hY)]
  rfl

lemma condDistrib_prod_left [StandardBorelSpace β] [Nonempty β]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (hT : AEMeasurable T μ) :
    condDistrib (fun ω ↦ (X ω, Y ω)) T μ
      =ᵐ[μ.map T] condDistrib X T μ ⊗ₖ condDistrib Y (fun ω ↦ (T ω, X ω)) μ := by
  refine condDistrib_ae_eq_of_measure_eq_compProd hT (by fun_prop) ?_
  rw [← Measure.compProd_assoc', compProd_map_condDistrib hT hX,
    compProd_map_condDistrib (hT.prodMk hX) hY,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

lemma condDistrib_condDistrib_ae_eq_sectR_condDistrib [StandardBorelSpace β] [Nonempty β]
    {f : Ω' → β} {g : Ω' → Ω} (hf : Measurable f) (hg : Measurable g) (hZ : AEMeasurable Z μ)
    (hT : AEMeasurable T μ) :
    ∀ᵐ t ∂(μ.map T),
      condDistrib g f (condDistrib Z T μ t) =ᵐ[(condDistrib Z T μ t).map f]
        (condDistrib (g ∘ Z) (fun a ↦ (T a, (f ∘ Z) a)) μ).sectR t := by
  filter_upwards [
    condDistrib_prod_left (hf.comp_aemeasurable hZ) (hg.comp_aemeasurable hZ) hT,
    condDistrib_comp hT hZ (hf.prodMk hg), condDistrib_comp hT hZ hf] with t h_prod h_pair h_fst
  rw [condDistrib_ae_eq_iff_measure_eq_compProd hf.aemeasurable hg.aemeasurable]
  calc (condDistrib Z T μ t).map (fun ω' ↦ (f ω', g ω'))
  _ = condDistrib (fun a ↦ ((f ∘ Z) a, (g ∘ Z) a)) T μ t := by
      rw [← Kernel.map_apply _ (hf.prodMk hg)]
      exact h_pair.symm
  _ = (condDistrib Z T μ t).map f
        ⊗ₘ (condDistrib (g ∘ Z) (fun a ↦ (T a, (f ∘ Z) a)) μ).sectR t := by
      rw [h_prod, Kernel.compProd_apply_eq_compProd_sectR, h_fst, Kernel.map_apply _ hf]

lemma condDistrib_prod_self_left [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace γ]
    [Nonempty γ]
    (hX : AEMeasurable X μ) (hT : AEMeasurable T μ) :
    condDistrib (fun ω ↦ (X ω, T ω)) T μ =ᵐ[μ.map T] condDistrib X T μ ×ₖ Kernel.id := by
  have h_prod := condDistrib_prod_left hX hT hT (μ := μ)
  have h_fst := condDistrib_comp_self (μ := μ) (X := fun ω ↦ (T ω, X ω)) (f := Prod.fst)
    (hT.prodMk hX) measurable_fst
  rw [(compProd_map_condDistrib hT hX).symm] at h_fst
  have h_fst' := (Measure.ae_compProd_iff (Kernel.measurableSet_eq _ _)).mp h_fst
  filter_upwards [h_prod, h_fst'] with z hz1 hz2
  rw [hz1]
  simp only [Kernel.deterministic_apply, Function.comp_def] at hz2
  ext t ht
  rw [Kernel.compProd_apply ht]
  calc ∫⁻ y, condDistrib T (fun ω ↦ (T ω, X ω)) μ (z, y) (Prod.mk y ⁻¹' t) ∂condDistrib X T μ z
  _ = ∫⁻ y, (Measure.dirac z) (Prod.mk y ⁻¹' t) ∂condDistrib X T μ z :=
    lintegral_congr_ae (hz2.mono fun y hy ↦ by simp only [hy])
  _ = ∫⁻ y, (Prod.mk y ⁻¹' t).indicator 1 z ∂condDistrib X T μ z :=
    lintegral_congr fun y ↦ Measure.dirac_apply' _ (ht.preimage (by fun_prop))
  _ = (condDistrib X T μ z) ((fun y ↦ (y, z)) ⁻¹' t) := by
    rw [← lintegral_indicator_one (ht.preimage (by fun_prop : Measurable fun y ↦ (y, z)))]
    exact lintegral_congr fun _ ↦ rfl
  _ = ((condDistrib X T μ ×ₖ Kernel.id) z) t := by
    rw [Kernel.prod_apply, Kernel.id_apply, Measure.prod_apply_symm ht, lintegral_dirac]

lemma fst_condDistrib_prod [StandardBorelSpace β] [Nonempty β]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (hT : AEMeasurable T μ) :
    (condDistrib (fun ω ↦ (X ω, Y ω)) T μ).fst =ᵐ[μ.map T] condDistrib X T μ := by
  filter_upwards [condDistrib_prod_left hX hY hT] with c hc
  rw [Kernel.fst_apply, hc, ← Kernel.fst_apply, Kernel.fst_compProd]

lemma ae_eq_of_condDistrib_eq_deterministic {f : β → Ω} (hf : Measurable f) (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (h : condDistrib Y X μ =ᵐ[μ.map X] Kernel.deterministic f hf) :
    Y =ᵐ[μ] f ∘ X := by
  have hfX := condDistrib_comp_self hX hf
  rw [condDistrib_ae_eq_iff_measure_eq_compProd hX (by fun_prop)] at h hfX
  exact ae_eq_of_map_prodMk_eq hf hX hY (hfX ▸ h)

end CondDistrib

section Cond

lemma condDistrib_ae_eq_cond [Countable β] [MeasurableSingletonClass β]
    [IsFiniteMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) :
    condDistrib Y X μ =ᵐ[μ.map X] fun b ↦ (μ[|X ⁻¹' {b}]).map Y := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro b hb
  ext s hs
  rw [condDistrib_apply_of_ne_zero hX hY,
    Measure.map_apply hX (measurableSet_singleton _), Measure.map_apply hY hs,
    Measure.map_apply (hX.prodMk hY) ((measurableSet_singleton _).prod hs),
    cond_apply (hX (measurableSet_singleton _))]
  · congr
  · exact hb

omit [Nonempty Ω'] in
/-- Let `Z` be a random variable with countably many values. If for every value `b` of `Z` with
positive probability, the conditional distribution of `Y` given `X` under `μ[|Z ⁻¹' {b}]` is
`κ (·, b)`, then the conditional distribution of `Y` given `(X, Z)` under `μ` is `κ`. -/
lemma condDistrib_prod_of_forall_condDistrib_cond [Countable Ω'] [IsFiniteMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (κ : Kernel (β × Ω') Ω) [IsFiniteKernel κ]
    (h_cond : ∀ b, μ (Z ⁻¹' {b}) ≠ 0 → condDistrib Y X μ[|Z ⁻¹' {b}] =ᵐ[μ[|Z ⁻¹' {b}].map X]
      (κ.comap (fun ω ↦ (ω, b)) (by fun_prop) : Kernel β Ω)) :
    condDistrib Y (fun ω ↦ (X ω, Z ω)) μ =ᵐ[μ.map (fun ω ↦ (X ω, Z ω))] κ := by
  refine condDistrib_ae_eq_of_measure_eq_compProd (by fun_prop) (by fun_prop) ?_
  ext s hs
  -- It suffices to prove the equality of the two measures on the sets where `Z` is constant,
  -- since those sets form a countable partition.
  suffices ∀ b, (Measure.map (fun x ↦ ((X x, Z x), Y x)) μ) (s ∩ {p | p.1.2 = b}) =
      (Measure.map (fun ω ↦ (X ω, Z ω)) μ ⊗ₘ κ) (s ∩ {p | p.1.2 = b}) by
    have hs_iUnion : s = ⋃ b, s ∩ {p | p.1.2 = b} := by
      ext p
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      grind
    have h_disj : Pairwise (Function.onFun Disjoint fun b ↦ s ∩ {p | p.1.2 = b}) := by
      intro i j hij
      simp only [Set.disjoint_iff_inter_eq_empty]
      ext
      grind
    have h_meas (b : Ω') : MeasurableSet (s ∩ {p | p.1.2 = b}) :=
      hs.inter ((measurableSet_singleton _).preimage (by fun_prop))
    rw [hs_iUnion, measure_iUnion h_disj h_meas, measure_iUnion h_disj h_meas]
    congr with b
    exact this b
  intro b
  by_cases hb : μ (Z ⁻¹' {b}) = 0
  -- If `Z = b` has probability zero, both measures vanish on `{p | p.1.2 = b}`.
  · have h_left : (Measure.map (fun x ↦ ((X x, Z x), Y x)) μ) (s ∩ {p | p.1.2 = b}) = 0 := by
      suffices (Measure.map (fun x ↦ ((X x, Z x), Y x)) μ) {p | p.1.2 = b} = 0 from
        measure_mono_null Set.inter_subset_right this
      rw [Measure.map_apply (by fun_prop)]
      · simpa
      · exact (measurableSet_singleton _).preimage (by fun_prop)
    have h_right : (Measure.map (fun ω ↦ (X ω, Z ω)) μ ⊗ₘ κ) (s ∩ {p | p.1.2 = b}) = 0 := by
      suffices (Measure.map (fun ω ↦ (X ω, Z ω)) μ ⊗ₘ κ) {p | p.1.2 = b} = 0 from
        measure_mono_null Set.inter_subset_right this
      rw [Measure.compProd_apply, lintegral_map]
      rotate_left
      · exact Kernel.measurable_kernel_prodMk_left
          ((measurableSet_singleton _).preimage (by fun_prop))
      · fun_prop
      · exact (measurableSet_singleton _).preimage (by fun_prop)
      simp only [Set.preimage_ofPred_eq]
      classical
      have h_le : ∫⁻ a, (κ (X a, Z a)) {a_1 | Z a = b} ∂μ ≤
          ∫⁻ a, {a' | Z a' = b}.indicator (fun _ ↦ κ.bound) a ∂μ := by
        gcongr with a
        by_cases hZ : Z a = b
        · simp only [hZ, Set.ofPred_true, Set.mem_ofPred_eq, Set.indicator_of_mem]
          exact κ.measure_le_bound _ _
        · simp [hZ]
      refine le_antisymm (h_le.trans ?_) zero_le
      rw [lintegral_indicator]
      swap; · exact (measurableSet_singleton _).preimage (by fun_prop)
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
        nonpos_iff_eq_zero, mul_eq_zero]
      exact .inr hb
    rw [h_left, h_right]
  -- Otherwise, we use the hypothesis on `μ[|Z ⁻¹' {b}]` and unfold the definition of `cond`.
  specialize h_cond b hb
  rw [condDistrib_ae_eq_iff_measure_eq_compProd (by fun_prop) (by fun_prop)] at h_cond
  rw [Measure.ext_iff] at h_cond
  have hs' : MeasurableSet {p : β × Ω | ((p.1, b), p.2) ∈ s} := hs.preimage (by fun_prop)
  have h1 := h_cond {p | ((p.1, b), p.2) ∈ s} hs'
  have h_indicator : Measurable ({ω' | Z ω' = b}.indicator (fun x ↦ 1)) :=
    Measurable.indicator (by fun_prop) ((measurableSet_singleton _).preimage (by fun_prop))
  rw [Measure.map_apply] at h1 ⊢
  rotate_left
  · fun_prop
  · exact hs.inter ((measurableSet_singleton _).preimage (by fun_prop))
  · fun_prop
  · exact hs'
  rw [cond_apply] at h1
  swap; · exact (measurableSet_singleton _).preimage (by fun_prop)
  have h1' : μ (Z ⁻¹' {b} ∩ (fun x ↦ (X x, Y x)) ⁻¹' {p | ((p.1, b), p.2) ∈ s}) =
      (μ (Z ⁻¹' {b})) *
        (Measure.map X μ[|Z ⁻¹' {b}] ⊗ₘ κ.comap (fun ω ↦ (ω, b)) (by fun_prop))
        {p | ((p.1, b), p.2) ∈ s} := by
    rw [← h1, ← mul_assoc, ENNReal.mul_inv_cancel hb (by simp), one_mul]
  convert h1'
  · ext x
    simp only [Set.preimage_inter, Set.preimage_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_ofPred_eq]
    grind
  · rw [Measure.compProd_apply, Measure.compProd_apply, lintegral_map, lintegral_map]
    rotate_left
    · exact Kernel.measurable_kernel_prodMk_left hs'
    · fun_prop
    · apply Kernel.measurable_kernel_prodMk_left
      exact hs.inter ((measurableSet_singleton _).preimage (by fun_prop))
    · fun_prop
    · exact hs'
    · exact hs.inter ((measurableSet_singleton _).preimage (by fun_prop))
    rw [lintegral_cond, ← mul_assoc, ENNReal.mul_inv_cancel hb (by simp), one_mul]
    simp only [Set.preimage_inter, Set.preimage_ofPred_eq, Kernel.coe_comap, Function.comp_apply]
    classical
    have h_eq : (fun a ↦ κ (X a, Z a) (Prod.mk (X a, Z a) ⁻¹' s ∩ {a_1 | Z a = b})) =
        {a | Z a = b}.indicator
          (fun a ↦ κ (X a, b) (Prod.mk (X a, b) ⁻¹' s ∩ {a_1 | Z a = b})) := by
      ext a
      by_cases hZ : Z a = b <;> simp [hZ]
    simp_rw [h_eq]
    rw [lintegral_indicator]
    swap; · exact (measurableSet_singleton _).preimage (by fun_prop)
    refine setLIntegral_congr_fun ((measurableSet_singleton _).preimage (by fun_prop)) fun a ha ↦ ?_
    congr 1 with ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, and_iff_left_iff_imp]
    grind

end Cond

end ProbabilityTheory
