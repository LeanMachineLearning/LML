/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

open MeasureTheory Finset

namespace ProbabilityTheory

variable {α Ω Ω' E ι : Type*} [Countable ι] {mα : MeasurableSpace α}
  {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mE : MeasurableSpace E} {μ ν : Measure Ω}

@[simp]
lemma indepFun_zero_measure {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} (X : α → β) (Y : α → γ) :
    X ⟂ᵢ[(0 : Measure α)] Y := by
  simp [indepFun_iff_measure_inter_preimage_eq_mul]

lemma indepFun_cond_of_indepFun {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {μ : Measure α}
    {X : α → β} {Y : α → γ} (hXY : X ⟂ᵢ[μ] Y) (hY : Measurable Y) {s : Set γ}
    (hs : MeasurableSet s) :
    X ⟂ᵢ[μ[|Y ⁻¹' s]] Y := by
  by_cases h_zero : μ[|Y ⁻¹' s] = 0
  · simp [h_zero]
  rw [cond_eq_zero] at h_zero
  push Not at h_zero -- `h_zero : μ (Y ⁻¹' s) ≠ ⊤ ∧ μ (Y ⁻¹' s) ≠ 0`
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hXY ⊢
  intro u t hu ht
  rw [cond_apply (hs.preimage hY), cond_apply (hs.preimage hY), cond_apply (hs.preimage hY)]
  have h_eq : Y ⁻¹' s ∩ (X ⁻¹' u ∩ Y ⁻¹' t) = X ⁻¹' u ∩ Y ⁻¹' (s ∩ t) := by grind
  have hsu : μ (X ⁻¹' u ∩ Y ⁻¹' s) = μ (X ⁻¹' u) * μ (Y ⁻¹' s) := hXY u s hu hs
  rw [Set.inter_comm] at hsu
  have hust : μ (X ⁻¹' u ∩ Y ⁻¹' (s ∩ t)) = μ (X ⁻¹' u) * μ (Y ⁻¹' (s ∩ t)) :=
    hXY u (s ∩ t) hu (hs.inter ht)
  rw [hsu, h_eq, hust]
  simp_rw [mul_assoc]
  congr 1
  rw [← mul_assoc (μ (Y ⁻¹' s)), ENNReal.mul_inv_cancel h_zero.2 h_zero.1, one_mul]
  congr

lemma iIndepFun_nat_iff_forall_indepFun [IsProbabilityMeasure μ] {X : ℕ → Ω → E}
    (hX : ∀ n, AEMeasurable (X n) μ) :
    iIndepFun X μ ↔ ∀ n, X (n + 1) ⟂ᵢ[μ] fun ω (i : Iic n) ↦ X i ω := by
  constructor
  · intro h n
    exact (h.indepFun_finset₀ {n + 1} (Iic n) (by simp) hX).comp
      (measurable_pi_apply ⟨n + 1, by simp⟩) measurable_id
  · intro h
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro s sets hsets
    induction s using Finset.strongInductionOn with
    | _ s ih =>
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    · obtain hn_zero | hn_pos := (s.max' hs).eq_zero_or_pos
      · simp [eq_singleton_iff_unique_mem.mpr ⟨hn_zero ▸ max'_mem _ hs,
          fun j hj => Nat.le_zero.mp (hn_zero ▸ le_max' _ j hj)⟩]
      · have hs'_le : ∀ i ∈ s.erase (s.max' hs), i ∈ Iic (s.max' hs - 1) := fun i hi =>
          mem_Iic.mpr (Nat.lt_succ_iff.mp (Nat.succ_pred_eq_of_pos hn_pos ▸
            lt_max'_of_mem_erase_max' _ hs hi))
        let t : Set (Iic (s.max' hs - 1) → E) :=
          {f | ∀ i : s.erase (s.max' hs), f ⟨i.1, hs'_le i.1 i.2⟩ ∈ sets i.1}
        have ht : MeasurableSet t := by
          have : t = ⋂ i : s.erase (s.max' hs), (· ⟨i.1, hs'_le i.1 i.2⟩) ⁻¹' sets i.1 := by
            ext
            simp [t]
          exact this ▸ .iInter fun ⟨i, hi⟩ =>
            (hsets i (erase_subset _ _ hi)).preimage (measurable_pi_apply _)
        have heq : ⋂ i ∈ s.erase (s.max' hs), X i ⁻¹' sets i =
            (fun ω (j : Iic (s.max' hs - 1)) => X j ω) ⁻¹' t := by
          ext ω
          simp only [Set.mem_iInter, Set.mem_preimage, t]
          exact ⟨fun hω ⟨i, hi⟩ => hω i hi, fun hω i hi => hω ⟨i, hi⟩⟩
        have hind := h (s.max' hs - 1)
        rw [Nat.sub_add_cancel hn_pos] at hind
        rw [(insert_erase (max'_mem _ hs)).symm, set_biInter_insert, heq,
          hind.measure_inter_preimage_eq_mul _ _ (hsets _ (max'_mem _ hs)) ht, ← heq,
          ih _ (erase_ssubset (max'_mem _ hs)) fun i hi => hsets i (erase_subset _ _ hi),
          prod_insert (notMem_erase _ _)]

-- todo: kernel version?
lemma IndepFun_map_iff [IsFiniteMeasure μ] {X : Ω' → E} {Y : Ω' → E} {f : Ω → Ω'}
    (hf : AEMeasurable f μ) (hX : AEMeasurable X (μ.map f)) (hY : AEMeasurable Y (μ.map f)) :
    X ⟂ᵢ[μ.map f] Y ↔ (X ∘ f) ⟂ᵢ[μ] (Y ∘ f) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY,
    indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
  rw [AEMeasurable.map_map_of_aemeasurable hY hf, AEMeasurable.map_map_of_aemeasurable hX hf,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

lemma iIndepFun_map_iff [IsProbabilityMeasure μ] {X : ι → Ω' → E} {f : Ω → Ω'}
    (hf : AEMeasurable f μ) (hX : ∀ n, AEMeasurable (X n) (μ.map f)) :
    iIndepFun X (μ.map f) ↔ iIndepFun (fun n ↦ X n ∘ f) μ := by
  have := Measure.isProbabilityMeasure_map hf (μ := μ)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀' hX,
    iIndepFun_iff_map_fun_eq_infinitePi_map₀' (by fun_prop)]
  rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hf]
  congr! 3
  rw [AEMeasurable.map_map_of_aemeasurable (hX _) hf]

lemma identDistrib_map_right_iff {X : Ω → E} {Y : Ω' → E} {f : Ω → Ω'}
    (hf : AEMeasurable f ν) (hX : AEMeasurable X μ) (hY : AEMeasurable Y (ν.map f)) :
    IdentDistrib X Y μ (ν.map f) ↔ IdentDistrib X (Y ∘ f) μ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · constructor
    · exact hX
    · fun_prop
    · rw [h.map_eq, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hf]
  · constructor
    · exact hX
    · fun_prop
    · rw [h.map_eq, AEMeasurable.map_map_of_aemeasurable hY hf]

lemma identDistrib_comm (X : Ω → E) (Y : Ω' → E) {ν : Measure Ω'} :
    IdentDistrib X Y μ ν ↔ IdentDistrib Y X ν μ :=
  ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩

lemma identDistrib_map_left_iff {X : Ω → E} {Y : Ω' → E} {f : Ω → Ω'}
    (hf : AEMeasurable f ν) (hX : AEMeasurable X μ) (hY : AEMeasurable Y (ν.map f)) :
    IdentDistrib Y X (ν.map f) μ ↔ IdentDistrib (Y ∘ f) X ν μ := by
  rw [identDistrib_comm Y, identDistrib_comm _ X]
  exact identDistrib_map_right_iff hf hX hY

end ProbabilityTheory
