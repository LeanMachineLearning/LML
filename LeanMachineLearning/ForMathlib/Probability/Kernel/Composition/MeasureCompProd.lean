/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! # Lemmas about measure composition-product
-/

@[expose] public section

open ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ η : Kernel α β}

lemma dirac_compProd [IsSFiniteKernel κ] (a : α) :
    Measure.dirac a ⊗ₘ κ = (κ a).map (Prod.mk a) := by
  ext s hs
  rw [Measure.compProd_apply hs, lintegral_dirac' _ (Kernel.measurable_kernel_prodMk_left hs),
    Measure.map_apply measurable_prodMk_left hs]

section Prod

variable {γ : Type*} {mγ : MeasurableSpace γ}

lemma snd_compProd_prodMkLeft {μ : Measure (α × β)} [SFinite μ] {κ : Kernel β γ}
    [IsSFiniteKernel κ] :
    (μ ⊗ₘ (κ.prodMkLeft α)).snd = κ ∘ₘ μ.snd := by
  ext s hs
  rw [Measure.snd_apply hs, Measure.compProd_apply (hs.preimage (by fun_prop)),
    Measure.bind_apply hs (by fun_prop), Measure.snd,
    lintegral_map (κ.measurable_coe hs) (by fun_prop)]
  simp only [Kernel.prodMkLeft_apply]
  congr

lemma snd_compProd_prodMkRight {μ : Measure (α × β)} [SFinite μ] {κ : Kernel α γ}
    [IsSFiniteKernel κ] :
    (μ ⊗ₘ (κ.prodMkRight β)).snd = κ ∘ₘ μ.fst := by
  ext s hs
  rw [Measure.snd_apply hs, Measure.compProd_apply (hs.preimage (by fun_prop)),
    Measure.bind_apply hs (by fun_prop), Measure.fst,
    lintegral_map (κ.measurable_coe hs) (by fun_prop)]
  simp only [Kernel.prodMkRight_apply]
  congr

lemma snd_map_prodAssoc_compProd_prodMkLeft {μ : Measure (α × β)} [SFinite μ]
    {κ : Kernel β γ} [IsSFiniteKernel κ] :
    ((μ ⊗ₘ (κ.prodMkLeft α)).map MeasurableEquiv.prodAssoc).snd = μ.snd ⊗ₘ κ := by
  ext s hs
  rw [Measure.snd_apply hs, Measure.map_apply (by fun_prop) (hs.preimage (by fun_prop)),
    Measure.compProd_apply, Measure.compProd_apply hs, Measure.snd, lintegral_map _ (by fun_prop)]
  · simp only [Kernel.prodMkLeft_apply]
    congr
  · exact Kernel.measurable_kernel_prodMk_left hs
  · exact hs.preimage (by fun_prop)

/-- Forgetting the second coordinate of the first component of `μ ⊗ₘ κ.prodMkRight β` gives
`μ.fst ⊗ₘ κ`. -/
lemma map_prodMap_fst_compProd_prodMkRight {μ : Measure (α × β)} [SFinite μ] {κ : Kernel α γ}
    [IsSFiniteKernel κ] :
    (μ ⊗ₘ (κ.prodMkRight β)).map (Prod.map Prod.fst id) = μ.fst ⊗ₘ κ := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.compProd_apply hs,
    Measure.compProd_apply (hs.preimage (by fun_prop)), Measure.fst,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) (by fun_prop)]
  rfl

end Prod

section AbsolutelyContinuous

lemma AbsolutelyContinuous.compProd_left_apply {γ : Type*} {mγ : MeasurableSpace γ}
    [IsSFiniteKernel η] {a : α} (hac : κ a ≪ η a) (ξ : Kernel (α × β) γ) :
    (κ ⊗ₖ ξ) a ≪ (η ⊗ₖ ξ) a := by
  by_cases hκ : IsSFiniteKernel κ
  · by_cases hξ : IsSFiniteKernel ξ
    · simp_rw [Kernel.compProd_apply_eq_compProd_sectR, hac.compProd_left _]
    · simp [Kernel.compProd_of_not_isSFiniteKernel_right _ _ hξ]
  · simp [Kernel.compProd_of_not_isSFiniteKernel_left _ _ hκ]

end AbsolutelyContinuous

end MeasureTheory.Measure
