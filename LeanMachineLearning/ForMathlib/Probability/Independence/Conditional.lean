/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Independence.Kernel.IndepFun
public import LeanMachineLearning.ForMathlib.Probability.Kernel.CondDistrib
public import LeanMachineLearning.ForMathlib.Probability.Kernel.Composition.MeasureCompProd
public import LeanMachineLearning.ForMathlib.Probability.Kernel.RadonNikodym
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Conditional

import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Lemmas about conditional independence

This file contains lemmas about conditional independence of random variables and about the
relation between (conditional) independence and conditional distributions.

## Main statements

* `CondIndepFun.of_measurable`: if `Y` and `Z` are conditionally independent, then so are any
  `Y'` measurable with respect to `σ(Y)` and any `Z'` measurable with respect to `σ(Z)`.
* `indepFun_iff_condDistrib_ae_eq_const`: `X` and `Y` are independent iff the conditional
  distribution of `Y` given `X` is a.e. constant.
* `condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkRight`: `Y` is conditionally independent of
  `X` given `Z` if the conditional distribution of `Y` given `(Z, X)` depends only on `Z`.
* `cond_of_condIndepFun`: if `Y` and `X` are conditionally independent given `Z`, then the law of
  `Y` conditioned on `Z = ω` and `X = b` is its law conditioned on `Z = ω`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

section OfMeasurable

variable {α β γ δ γ' δ' : Type*}
  {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {mδ : MeasurableSpace δ} {mγ' : MeasurableSpace γ'} {mδ' : MeasurableSpace δ'}
  {μ : Measure α}
  {X : α → β} {hX : Measurable X} {Y : α → γ} {Z : α → δ} {Y' : α → γ'} {Z' : α → δ'}

lemma CondIndepFun.of_prod_right {ε : Type*} {mε : MeasurableSpace ε}
    [StandardBorelSpace α] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → γ} {Z : α → δ} {T : α → ε} (hZ : Measurable Z)
    (h : X ⟂ᵢ[Z, hZ; μ] (fun ω ↦ (Y ω, T ω))) :
    X ⟂ᵢ[Z, hZ; μ] Y :=
  Kernel.IndepFun.of_prod_right h

lemma CondIndepFun.of_prod_left {ε : Type*} {mε : MeasurableSpace ε}
    [StandardBorelSpace α] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → γ} {Z : α → δ} {T : α → ε} (hZ : Measurable Z)
    (h : (fun ω ↦ (X ω, T ω)) ⟂ᵢ[Z, hZ; μ] Y) :
    X ⟂ᵢ[Z, hZ; μ] Y :=
  Kernel.IndepFun.of_prod_left h

variable [StandardBorelSpace α] [IsFiniteMeasure μ]

lemma CondIndepFun.of_measurable_left
    (h_indep : Y ⟂ᵢ[X, hX; μ] Z) (hY_meas : Measurable[mγ.comap Y] Y') :
    Y' ⟂ᵢ[X, hX; μ] Z := by
  rw [condIndepFun_iff_condIndep] at h_indep ⊢
  exact condIndep_of_condIndep_of_le_left h_indep hY_meas.comap_le

lemma CondIndepFun.of_measurable_right
    (h_indep : Y ⟂ᵢ[X, hX; μ] Z) (hZ_meas : Measurable[mδ.comap Z] Z') :
    Y ⟂ᵢ[X, hX; μ] Z' := by
  rw [condIndepFun_iff_condIndep] at h_indep ⊢
  exact condIndep_of_condIndep_of_le_right h_indep hZ_meas.comap_le

lemma CondIndepFun.of_measurable (h_indep : Y ⟂ᵢ[X, hX; μ] Z)
    (hY_meas : Measurable[mγ.comap Y] Y') (hZ_meas : Measurable[mδ.comap Z] Z') :
    Y' ⟂ᵢ[X, hX; μ] Z' :=
  (h_indep.of_measurable_left (hX := hX) hY_meas).of_measurable_right (hX := hX) hZ_meas

end OfMeasurable

section CondDistrib

variable {α β γ δ Ω Ω' : Type*}
  {mα : MeasurableSpace α} {μ : Measure α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {mδ : MeasurableSpace δ}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [mΩ' : MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
  {X : α → β} {Y : α → Ω} {Z : α → Ω'} {T : α → γ}

section IsFiniteMeasure

variable [IsFiniteMeasure μ]

/-- If `X` is conditionally independent of `Y` given `Z`, then it is conditionally independent of
`(Y, Z)` given `Z`. -/
lemma CondIndepFun.prod_right [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace γ] [Nonempty γ] [StandardBorelSpace δ] [Nonempty δ]
    {X : α → β} {Y : α → γ} {Z : α → δ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h : X ⟂ᵢ[Z, hZ; μ] Y) :
    X ⟂ᵢ[Z, hZ; μ] (fun ω ↦ (Y ω, Z ω)) := by
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY hX hZ,
    condDistrib_ae_eq_iff_measure_eq_compProd (by fun_prop) (by fun_prop)] at h
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight (by fun_prop) hX hZ,
    condDistrib_ae_eq_iff_measure_eq_compProd (by fun_prop) (by fun_prop)]
  -- Key: condDistrib (Y, Z) Z μ z = (condDistrib Y Z μ z).map (y ↦ (y, z))
  have h_cond : condDistrib (fun ω ↦ (Y ω, Z ω)) Z μ =ᵐ[μ.map Z]
      fun z ↦ (condDistrib Y Z μ z).map (fun y ↦ (y, z)) := by
    suffices condDistrib (fun ω ↦ (Y ω, Z ω)) Z μ =ᵐ[μ.map Z]
        (condDistrib Y Z μ) ×ₖ Kernel.id by
      refine this.trans (ae_of_all _ fun x ↦ ?_)
      simp only
      rw [Kernel.prod_apply, Kernel.id_apply]
      ext s hs
      rw [Measure.map_apply (by fun_prop) hs, Measure.prod_apply_symm hs, lintegral_dirac]
    exact condDistrib_prod_self_left hY.aemeasurable hZ.aemeasurable
  -- Main calculation
  calc μ.map (fun x ↦ ((Z x, X x), (Y x, Z x)))
  _ = (μ.map (fun x ↦ ((Z x, X x), Y x))).map (fun p ↦ (p.1, (p.2, p.1.1))) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
  _ = (μ.map (fun ω ↦ (Z ω, X ω)) ⊗ₘ (condDistrib Y Z μ).prodMkRight β).map
        (fun p ↦ (p.1, (p.2, p.1.1))) := by rw [h]
  _ = μ.map (fun ω ↦ (Z ω, X ω)) ⊗ₘ (condDistrib (fun ω ↦ (Y ω, Z ω)) Z μ).prodMkRight β := by
    ext s hs
    rw [Measure.map_apply (by fun_prop) hs,
      Measure.compProd_apply (hs.preimage (by fun_prop)), Measure.compProd_apply hs]
    have h_cond' : ∀ᵐ p ∂(μ.map (fun ω ↦ (Z ω, X ω))),
        condDistrib (fun ω ↦ (Y ω, Z ω)) Z μ p.1 =
          (condDistrib Y Z μ p.1).map (fun y ↦ (y, p.1)) := by
      have h_fst : (μ.map (fun ω ↦ (Z ω, X ω))).map Prod.fst = μ.map Z := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
      rw [← h_fst] at h_cond
      exact mem_ae_of_mem_ae_map (by fun_prop) h_cond
    refine lintegral_congr_ae (h_cond'.mono fun ⟨z, x⟩ hzx ↦ ?_)
    simp only [Kernel.prodMkRight_apply, hzx,
      Measure.map_apply (by fun_prop : Measurable fun y ↦ (y, z))
        (hs.preimage (by fun_prop : Measurable (Prod.mk (z, x))))]
    congr 1

lemma condDistrib_ae_eq_of_indepFun (h : IndepFun X Y μ) (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) :
    condDistrib Y X μ =ᵐ[μ.map X] Kernel.const β (μ.map Y) := by
  refine condDistrib_ae_eq_of_measure_eq_compProd hX hY ?_
  simp only [Measure.compProd_const]
  exact (indepFun_iff_map_prod_eq_prod_map_map hX hY).mp h

lemma indepFun_iff_condDistrib_ae_eq_const (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    IndepFun X Y μ ↔ condDistrib Y X μ =ᵐ[μ.map X] Kernel.const β (μ.map Y) := by
  refine ⟨fun h ↦ condDistrib_ae_eq_of_indepFun h hX hY, fun h ↦ ?_⟩
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY, ← compProd_map_condDistrib hX hY,
    Measure.compProd_congr h]
  simp

omit [StandardBorelSpace Ω'] [Nonempty Ω'] in
lemma condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkRight
    [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) {η : Kernel Ω' Ω}
    [IsMarkovKernel η]
    (h : condDistrib Y (fun ω ↦ (Z ω, X ω)) μ =ᵐ[μ.map (fun ω ↦ (Z ω, X ω))] η.prodMkRight _) :
    Y ⟂ᵢ[Z, hZ; μ] X := by
  have hη_eq : condDistrib Y Z μ =ᵐ[μ.map Z] η := by
    rw [condDistrib_ae_eq_iff_measure_eq_compProd (by fun_prop) (by fun_prop)] at h ⊢
    have h_fst : μ.map Z = (μ.map (fun ω ↦ (Z ω, X ω))).fst := by
      rw [Measure.fst_map_prodMk hZ hX]
    rw [h_fst, ← Measure.map_prodMap_fst_compProd_prodMkRight, ← h,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  symm
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY hX hZ]
  refine h.trans ?_
  rw [Kernel.prodMkRight_ae_eq_iff, Measure.fst_map_prodMk (by fun_prop) (by fun_prop)]
  exact hη_eq.symm

omit [StandardBorelSpace Ω'] [Nonempty Ω'] in
lemma condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) {η : Kernel Ω' Ω}
    [IsMarkovKernel η]
    (h : condDistrib Y (fun ω ↦ (X ω, Z ω)) μ =ᵐ[μ.map (fun ω ↦ (X ω, Z ω))] η.prodMkLeft _) :
    Y ⟂ᵢ[Z, hZ; μ] X := by
  refine condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkRight hX hY hZ ?_ (η := η)
  rw [← Kernel.compProd_eq_iff, compProd_map_condDistrib (by fun_prop) (by fun_prop)] at h ⊢
  have : μ.map (fun a ↦ ((Z a, X a), Y a))
      = (μ.map (fun a ↦ ((X a, Z a), Y a))).map (fun p ↦ ((p.1.2, p.1.1), p.2)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [this, h]
  ext s hs
  rw [Measure.map_apply, Measure.compProd_apply, Measure.compProd_apply, lintegral_map,
    lintegral_map]
  · simp only [Kernel.prodMkLeft_apply, Kernel.prodMkRight_apply]
    congr
  · exact Kernel.measurable_kernel_prodMk_left hs
  · fun_prop
  · refine Kernel.measurable_kernel_prodMk_left ?_
    exact hs.preimage (by fun_prop)
  · fun_prop
  · exact hs
  · exact hs.preimage (by fun_prop)
  · fun_prop
  · exact hs

omit [StandardBorelSpace Ω'] [Nonempty Ω'] in
/-- If `Y` and `X` are conditionally independent given `Z` under `μ`, then `Y ∘ Prod.fst` and
`X ∘ Prod.fst` are conditionally independent given `Z ∘ Prod.fst` under `μ.prod ν`.

TODO: generalize to the image of `μ` by any measurable map, instead of `Prod.fst`. -/
lemma condIndepFun_fst_prod [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace γ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (ν : Measure γ) [IsProbabilityMeasure ν]
    (h_indep : CondIndepFun (mΩ'.comap Z) hZ.comap_le Y X μ) :
    CondIndepFun (mΩ'.comap (fun ω ↦ Z ω.1)) (hZ.comp measurable_fst).comap_le
      (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) (μ.prod ν) := by
  rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib (by fun_prop)
    (by fun_prop) (by fun_prop)] at h_indep ⊢
  have h1 : 𝓛[fun ω ↦ Y ω.1 | fun ω ↦ Z ω.1; μ.prod ν] =ᵐ[μ.map Z] 𝓛[Y | Z; μ] :=
    condDistrib_fst_prod (Y := Y) (X := Z) (ν := ν) (μ := μ) (by fun_prop) (by fun_prop)
  have h2 : 𝓛[fun ω ↦ X ω.1 | fun ω ↦ Z ω.1; μ.prod ν] =ᵐ[μ.map Z] 𝓛[X | Z; μ] :=
    condDistrib_fst_prod (Y := X) (X := Z) (ν := ν) (μ := μ) (by fun_prop) (by fun_prop)
  have h_fst1 : (μ.prod ν).map (fun ω ↦ Z ω.1) = μ.map Z := by
    conv_rhs => rw [← Measure.fst_prod (μ := μ) (ν := ν), Measure.fst,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have h_fst2 : (μ.prod ν).map (fun ω ↦ (Z ω.1, Y ω.1, X ω.1))
      = μ.map (fun ω ↦ (Z ω, Y ω, X ω)) := by
    conv_rhs => rw [← Measure.fst_prod (μ := μ) (ν := ν), Measure.fst,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [h_fst1, h_fst2, h_indep]
  refine Measure.bind_congr_right ?_
  filter_upwards [h1, h2] with x hx1 hx2
  simp_rw [Kernel.prod_apply]
  rw [hx1, ← hx2]

end IsFiniteMeasure

omit [Nonempty Ω'] in
lemma cond_of_condIndepFun [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β] [Countable β]
    [Countable Ω']
    [IsZeroOrProbabilityMeasure μ]
    (hZ : Measurable Z)
    (h : CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le Y X μ)
    (hX : Measurable X) (hY : Measurable Y) {b : β} {ω : Ω'}
    (hμ : μ (Z ⁻¹' {ω} ∩ X ⁻¹' {b}) ≠ 0) :
    (μ[|Z ⁻¹' {ω} ∩ X ⁻¹' {b}]).map Y = (μ[|Z ⁻¹' {ω}]).map Y := by
  symm at h
  have h := (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY hX hZ).mp h
  have h_left := condDistrib_ae_eq_cond (hZ.prodMk hX) hY (μ := μ)
  have h_right := condDistrib_ae_eq_cond hZ hY (μ := μ)
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h h_left h_right
  specialize h (ω, b)
  specialize h_left (ω, b)
  specialize h_right ω
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at h h_left h_right
  rw [← Set.singleton_prod_singleton, Set.mk_preimage_prod] at h h_left
  have hZ_ne : μ (Z ⁻¹' {ω}) ≠ 0 := fun h ↦ hμ (measure_mono_null Set.inter_subset_left h)
  rw [← h_right hZ_ne, ← h_left hμ, h hμ]
  simp

end CondDistrib

end ProbabilityTheory
