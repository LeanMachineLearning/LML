/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! # Lemmas about measure composition-product
-/

@[expose] public section

open ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ η : Kernel α β}

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

section Swap

variable {γ : Type*} {mγ : MeasurableSpace γ}

/-- Exchanging two conditionally independent coordinates: if `κ` and `η` are two kernels on `α`,
the joint law of `(a, b, c)` obtained by drawing `b` from `κ a` and then `c` from `η a` is, up to
the exchange of `b` and `c`, the one obtained by drawing `c` first. This is the measure-theoretic
content of "conditioning on a conditionally independent variable changes nothing". -/
lemma compProd_comap_fst_comm (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α γ) [IsSFiniteKernel η] :
    ((μ ⊗ₘ κ) ⊗ₘ η.prodMkRight β).map (fun p ↦ ((p.1.1, p.2), p.1.2))
      = (μ ⊗ₘ η) ⊗ₘ κ.prodMkRight γ := by
  have key : ∀ (a : α) (t : Set (β × γ)), MeasurableSet t →
      ∫⁻ b, η a (Prod.mk b ⁻¹' t) ∂(κ a) = ∫⁻ c, κ a ((fun b ↦ (b, c)) ⁻¹' t) ∂(η a) := by
    intro a t ht
    rw [← Measure.prod_apply ht, ← Measure.prod_apply_symm ht]
  ext s hs
  have hF : Measurable (fun p : (α × β) × γ ↦ ((p.1.1, p.2), p.1.2)) := by fun_prop
  rw [Measure.map_apply hF hs, Measure.compProd_apply (hs.preimage hF), Measure.compProd_apply hs,
    Measure.lintegral_compProd (Kernel.measurable_kernel_prodMk_left (hs.preimage hF)),
    Measure.lintegral_compProd (Kernel.measurable_kernel_prodMk_left hs)]
  refine lintegral_congr fun a ↦ ?_
  simp only [Kernel.prodMkRight_apply]
  exact key a {q : β × γ | ((a, q.2), q.1) ∈ s} (hs.preimage (by fun_prop))

/-- Recording a measurable function of the input and of the draw. -/
lemma compProd_map_prodMk (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    {F : α × β → γ} (hF : Measurable F) :
    (μ ⊗ₘ κ).map (fun p ↦ (p.1, F p)) = μ ⊗ₘ ((Kernel.id ×ₖ κ).map F) := by
  have hG : Measurable (fun p : α × β ↦ (p.1, F p)) := by fun_prop
  ext s hs
  rw [Measure.map_apply hG hs, Measure.compProd_apply (hs.preimage hG), Measure.compProd_apply hs]
  refine lintegral_congr fun a ↦ ?_
  have ht : MeasurableSet (F ⁻¹' (Prod.mk a ⁻¹' s)) := (measurable_prodMk_left hs).preimage hF
  rw [Kernel.map_apply' _ hF _ (measurable_prodMk_left hs), Kernel.prod_apply,
    Measure.prod_apply ht, Kernel.id_apply, lintegral_dirac' _ (measurable_measure_prodMk_left ht)]
  rfl

end Swap

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

/-- Recording a measurable function of a draw: mapping a kernel to the graph of `f` is the
composition-product of that kernel with the deterministic kernel given by `f`. This is how an
algorithm announces a variable that it then uses deterministically. -/
lemma map_graph (κ : Kernel α β) [IsSFiniteKernel κ] {f : β → γ} (hf : Measurable f) :
    κ.map (fun b ↦ (b, f b))
      = κ ⊗ₖ Kernel.deterministic (fun p : α × β ↦ f p.2) (by fun_prop) := by
  ext a : 1
  have h_sectR : (Kernel.deterministic (fun p : α × β ↦ f p.2) (by fun_prop)).sectR a
      = Kernel.deterministic f hf := by
    ext b : 1
    rw [Kernel.sectR_apply, Kernel.deterministic_apply, Kernel.deterministic_apply]
  rw [Kernel.map_apply _ (by fun_prop), Kernel.compProd_apply_eq_compProd_sectR, h_sectR,
    MeasureTheory.Measure.compProd_deterministic]

end ProbabilityTheory.Kernel
