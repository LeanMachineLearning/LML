/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Kernel.IndepFun

/-!
# Lemmas about independence of functions with respect to a kernel

## Main statements

* `Kernel.IndepFun.of_prod_right`, `Kernel.IndepFun.of_prod_left`: if `X` is independent of
  `(Y, T)`, then `X` is independent of `Y`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

lemma Kernel.IndepFun.of_prod_right {ε Ω : Type*} {mΩ : MeasurableSpace Ω} {mε : MeasurableSpace ε}
    {μ : Measure Ω} {κ : Kernel Ω α} {X : α → β} {Y : α → γ} {T : α → ε}
    (h : IndepFun X (fun ω ↦ (Y ω, T ω)) κ μ) :
    IndepFun X Y κ μ := by
  rw [Kernel.indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  specialize h s (t ×ˢ .univ) hs (ht.prod .univ)
  simpa [Set.mk_preimage_prod] using h

lemma Kernel.IndepFun.of_prod_left {ε Ω : Type*} {mΩ : MeasurableSpace Ω} {mε : MeasurableSpace ε}
    {μ : Measure Ω} {κ : Kernel Ω α} {X : α → β} {Y : α → γ} {T : α → ε}
    (h : IndepFun (fun ω ↦ (X ω, T ω)) Y κ μ) :
    IndepFun X Y κ μ := h.symm.of_prod_right.symm

end ProbabilityTheory
