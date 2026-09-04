/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.InfinitePi

/-! # Lemmas about independence
-/

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

lemma indepFun_cond_comp {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} [MeasurableSingletonClass δ] {μ : Measure α}
    {X : α → β} {Y : α → γ} (hXY : X ⟂ᵢ[μ] Y) (hY : Measurable Y)
    {Z : γ → δ} (hZ : Measurable Z) (z : δ) :
    X ⟂ᵢ[μ[|(Z ∘ Y) ⁻¹' {z}]] Y := by
  have h_preim : (Z ∘ Y) ⁻¹' {z} = Y ⁻¹' (Z ⁻¹' {z}) := by grind
  simp_rw [h_preim]
  exact indepFun_cond_of_indepFun hXY hY (hZ (measurableSet_singleton z))

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

namespace ProbabilityTheory

section Prod

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

lemma hasLaw_fst_prod (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure ν] :
    HasLaw Prod.fst μ (μ.prod ν) where
  map_eq := Measure.fst_prod

lemma hasLaw_snd_prod (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [SFinite ν] :
    HasLaw Prod.snd ν (μ.prod ν) where
  map_eq := Measure.snd_prod

/-- Conditioning a product measure on an event of the first coordinate amounts to conditioning
the first measure. -/
lemma cond_prod_univ {μ : Measure α} [SFinite μ] {ν : Measure β} [IsProbabilityMeasure ν]
    (s : Set α) :
    (μ.prod ν)[|s ×ˢ Set.univ] = (μ[|s]).prod ν := by
  simp only [cond, Measure.prod_prod, measure_univ, mul_one, Measure.prod_smul_left,
    ← Measure.prod_restrict, Measure.restrict_univ]

/-- If `X` and `T` are independent under `ν`, then under `μ.prod ν` the function `X ∘ Prod.snd`
is independent of `(Prod.fst, T ∘ Prod.snd)`. -/
lemma IndepFun.snd_prod {μ : Measure α} [IsProbabilityMeasure μ] {ν : Measure β} [SFinite ν]
    {X : β → γ} {T : β → δ} (h : IndepFun X T ν) (hX : Measurable X) (hT : Measurable T) :
    IndepFun (fun p : α × β ↦ X p.2) (fun p ↦ (p.1, T p.2)) (μ.prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h
  have hXs : MeasurableSet ((fun p : α × β ↦ X p.2) ⁻¹' s) := hs.preimage (by fun_prop)
  have hYt : MeasurableSet ((fun p : α × β ↦ (p.1, T p.2)) ⁻¹' t) := ht.preimage (by fun_prop)
  rw [Measure.prod_apply (hXs.inter hYt), Measure.prod_apply hXs, Measure.prod_apply hYt]
  have h_eq : ∀ x, ν (Prod.mk x ⁻¹' ((fun p : α × β ↦ X p.2) ⁻¹' s ∩ (fun p ↦ (p.1, T p.2)) ⁻¹' t))
      = ν (X ⁻¹' s) * (ν.map T) (Prod.mk x ⁻¹' t) := fun x ↦ by
    rw [Measure.map_apply hT (ht.preimage measurable_prodMk_left)]
    exact h s _ hs (ht.preimage measurable_prodMk_left)
  have h_eq' : ∀ x, ν (Prod.mk x ⁻¹' ((fun p : α × β ↦ (p.1, T p.2)) ⁻¹' t))
      = (ν.map T) (Prod.mk x ⁻¹' t) := fun x ↦ by
    rw [Measure.map_apply hT (ht.preimage measurable_prodMk_left)]
    rfl
  have h_eq'' : ∀ x, ν (Prod.mk x ⁻¹' ((fun p : α × β ↦ X p.2) ⁻¹' s)) = ν (X ⁻¹' s) :=
    fun _ ↦ rfl
  simp_rw [h_eq, h_eq', h_eq'']
  rw [lintegral_const_mul _ (measurable_measure_prodMk_left ht), lintegral_const, measure_univ,
    mul_one]

/-- If `X` and `T` are independent under `μ`, then under `μ.prod ν` the function `X ∘ Prod.fst`
is independent of `(T ∘ Prod.fst, Prod.snd)`. -/
lemma IndepFun.fst_prod {μ : Measure α} [SFinite μ] {ν : Measure β} [IsProbabilityMeasure ν]
    {X : α → γ} {T : α → δ} (h : IndepFun X T μ) (hX : Measurable X) (hT : Measurable T) :
    IndepFun (fun p : α × β ↦ X p.1) (fun p ↦ (T p.1, p.2)) (μ.prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h
  have hXs : MeasurableSet ((fun p : α × β ↦ X p.1) ⁻¹' s) := hs.preimage (by fun_prop)
  have hYt : MeasurableSet ((fun p : α × β ↦ (T p.1, p.2)) ⁻¹' t) := ht.preimage (by fun_prop)
  rw [Measure.prod_apply_symm (hXs.inter hYt), Measure.prod_apply_symm hXs,
    Measure.prod_apply_symm hYt]
  have h_eq : ∀ y, μ ((fun x ↦ (x, y)) ⁻¹'
      ((fun p : α × β ↦ X p.1) ⁻¹' s ∩ (fun p ↦ (T p.1, p.2)) ⁻¹' t))
      = μ (X ⁻¹' s) * (μ.map T) ((fun x ↦ (x, y)) ⁻¹' t) := fun y ↦ by
    rw [Measure.map_apply hT (ht.preimage measurable_prodMk_right)]
    exact h s _ hs (ht.preimage measurable_prodMk_right)
  have h_eq' : ∀ y, μ ((fun x ↦ (x, y)) ⁻¹' ((fun p : α × β ↦ (T p.1, p.2)) ⁻¹' t))
      = (μ.map T) ((fun x ↦ (x, y)) ⁻¹' t) := fun y ↦ by
    rw [Measure.map_apply hT (ht.preimage measurable_prodMk_right)]
    rfl
  have h_eq'' : ∀ y, μ ((fun x ↦ (x, y)) ⁻¹' ((fun p : α × β ↦ X p.1) ⁻¹' s)) = μ (X ⁻¹' s) :=
    fun _ ↦ rfl
  simp_rw [h_eq, h_eq', h_eq'']
  rw [lintegral_const_mul _ (measurable_measure_prodMk_right ht), lintegral_const, measure_univ,
    mul_one]

end Prod

/-- A coordinate of an independent family is independent of any function that is measurable
with respect to the other coordinates. -/
lemma iIndepFun.indepFun_of_measurable_iSup_comap {ι Ω β : Type*} {𝓧 : ι → Type*}
    [∀ i, MeasurableSpace (𝓧 i)] {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β}
    {μ : Measure Ω} {X : ∀ i, Ω → 𝓧 i} (hX : iIndepFun X μ) (hXm : ∀ i, Measurable (X i))
    {S : Set ι} {i : ι} (hi : i ∉ S) {Y : Ω → β}
    (hY : Measurable[⨆ j ∈ S, MeasurableSpace.comap (X j) inferInstance] Y) :
    IndepFun (X i) Y μ := by
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right ?_ hY.comap_le
  have h := indep_iSup_of_disjoint (fun j ↦ (hXm j).comap_le) hX.iIndep (S := {i}) (T := S)
    (Set.disjoint_singleton_left.2 hi)
  simpa using h

end ProbabilityTheory
