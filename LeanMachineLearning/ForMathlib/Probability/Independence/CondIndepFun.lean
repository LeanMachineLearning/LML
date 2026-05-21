/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Conditional

@[expose] public section

/-! # Laws of `stepsUntil` and `rewardByCount`
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α β γ δ γ' δ' : Type*}
  {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {mδ : MeasurableSpace δ} {mγ' : MeasurableSpace γ'} {mδ' : MeasurableSpace δ'}
  [StandardBorelSpace δ'] [Nonempty δ'] [StandardBorelSpace γ'] [Nonempty γ']
  {μ : Measure α}
  {X : α → β} {hX : Measurable X} {Y : α → γ} {Z : α → δ} {Y' : α → γ'} {Z' : α → δ'}

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

lemma IndepFun.of_measurable (h_indep : Y ⟂ᵢ[μ] Z)
    (hY_meas : Measurable[mγ.comap Y] Y') (hZ_meas : Measurable[mδ.comap Z] Z') :
    Y' ⟂ᵢ[μ] Z' := by
  obtain ⟨φ, hφ_meas, h_eqY⟩ : ∃ φ, Measurable φ ∧ Y' = φ ∘ Y := hY_meas.exists_eq_measurable_comp
  obtain ⟨ψ, hψ_meas, h_eqZ⟩ : ∃ ψ, Measurable ψ ∧ Z' = ψ ∘ Z := hZ_meas.exists_eq_measurable_comp
  rw [h_eqY, h_eqZ]
  exact h_indep.comp hφ_meas hψ_meas

lemma IndepFun.of_measurable_left
    (h_indep : Y ⟂ᵢ[μ] Z) (hY_meas : Measurable[mγ.comap Y] Y') :
    Y' ⟂ᵢ[μ] Z := by
  obtain ⟨φ, hφ_meas, h_eqY⟩ : ∃ φ, Measurable φ ∧ Y' = φ ∘ Y := hY_meas.exists_eq_measurable_comp
  rw [h_eqY]
  exact h_indep.comp hφ_meas measurable_id

lemma IndepFun.of_measurable_right
    (h_indep : Y ⟂ᵢ[μ] Z) (hZ_meas : Measurable[mδ.comap Z] Z') :
    Y ⟂ᵢ[μ] Z' := by
  obtain ⟨ψ, hψ_meas, h_eqZ⟩ : ∃ ψ, Measurable ψ ∧ Z' = ψ ∘ Z := hZ_meas.exists_eq_measurable_comp
  rw [h_eqZ]
  exact h_indep.comp measurable_id hψ_meas

variable [StandardBorelSpace α] [IsFiniteMeasure μ]

lemma CondIndepFun.of_measurable (h_indep : Y ⟂ᵢ[X, hX; μ] Z)
    (hY_meas : Measurable[mγ.comap Y] Y') (hZ_meas : Measurable[mδ.comap Z] Z') :
    Y' ⟂ᵢ[X, hX; μ] Z' := by
  obtain ⟨φ, hφ_meas, h_eqY⟩ : ∃ φ, Measurable φ ∧ Y' = φ ∘ Y := hY_meas.exists_eq_measurable_comp
  obtain ⟨ψ, hψ_meas, h_eqZ⟩ : ∃ ψ, Measurable ψ ∧ Z' = ψ ∘ Z := hZ_meas.exists_eq_measurable_comp
  rw [h_eqY, h_eqZ]
  exact h_indep.comp hφ_meas hψ_meas

lemma CondIndepFun.of_measurable_left
    (h_indep : Y ⟂ᵢ[X, hX; μ] Z) (hY_meas : Measurable[mγ.comap Y] Y') :
    Y' ⟂ᵢ[X, hX; μ] Z := by
  obtain ⟨φ, hφ_meas, h_eqY⟩ : ∃ φ, Measurable φ ∧ Y' = φ ∘ Y := hY_meas.exists_eq_measurable_comp
  rw [h_eqY]
  exact h_indep.comp hφ_meas measurable_id

lemma CondIndepFun.of_measurable_right
    (h_indep : Y ⟂ᵢ[X, hX; μ] Z) (hZ_meas : Measurable[mδ.comap Z] Z') :
    Y ⟂ᵢ[X, hX; μ] Z' := by
  obtain ⟨ψ, hψ_meas, h_eqZ⟩ : ∃ ψ, Measurable ψ ∧ Z' = ψ ∘ Z := hZ_meas.exists_eq_measurable_comp
  rw [h_eqZ]
  exact h_indep.comp measurable_id hψ_meas

end ProbabilityTheory
