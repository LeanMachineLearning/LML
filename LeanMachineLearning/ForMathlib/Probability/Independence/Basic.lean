/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.ForMathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic

/-! # Lemmas about independence

## Main statements

* `indepFun_cond_of_indepFun`: if `X` and `Y` are independent, they are still independent under
  the measure conditioned on an event about `Y`.
* `iIndepFun_nat_iff_forall_indepFun`: a sequence of random variables is independent iff each
  of them is independent of the previous ones.
* `indepFun_map_iff`: independence under an image measure.
* `IndepFun.comp_hasLaw`: independence is preserved by composition with a random variable with
  the right law.
* `IndepFun.of_measurable`: if `Y` and `Z` are independent, then so are any `Y'` measurable with
  respect to `σ(Y)` and any `Z'` measurable with respect to `σ(Z)`.
* `cond_of_indepFun`: if `X` and `T` are independent, conditioning on an event about `X` does not
  change the law of `T`.
-/

@[expose] public section

open MeasureTheory Finset

namespace ProbabilityTheory

variable {α Ω Ω' E : Type*} {mα : MeasurableSpace α}
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

/-- Under `μ` conditioned on the event `X = b`, the random variable `X` is almost surely constant,
hence independent of any other random variable. -/
lemma indepFun_cond_preimage_singleton_left {α β γ : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} [MeasurableSingletonClass β] {μ : Measure α}
    {X : α → β} (hX : Measurable X) (b : β) (Y : α → γ) :
    X ⟂ᵢ[μ[|X ⁻¹' {b}]] Y :=
  (indepFun_const_left b Y).congr
    (ae_cond_of_forall_mem (hX (measurableSet_singleton b)) fun x hx ↦ (hx : X x = b).symm)
    Filter.EventuallyEq.rfl

/-- Under `μ` conditioned on the event `X = b`, the random variable `X` is almost surely constant,
hence independent of any other random variable. -/
lemma indepFun_cond_preimage_singleton_right {α β γ : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} [MeasurableSingletonClass β] {μ : Measure α}
    {X : α → β} (hX : Measurable X) (b : β) (Y : α → γ) :
    Y ⟂ᵢ[μ[|X ⁻¹' {b}]] X :=
  (indepFun_cond_preimage_singleton_left hX b Y).symm

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

-- TODO: kernel version?
lemma indepFun_map_iff {F : Type*} {mF : MeasurableSpace F} [IsFiniteMeasure μ] {X : Ω' → E}
    {Y : Ω' → F} {f : Ω → Ω'}
    (hf : AEMeasurable f μ) (hX : AEMeasurable X (μ.map f)) (hY : AEMeasurable Y (μ.map f)) :
    X ⟂ᵢ[μ.map f] Y ↔ (X ∘ f) ⟂ᵢ[μ] (Y ∘ f) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY,
    indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
  rw [AEMeasurable.map_map_of_aemeasurable hY hf, AEMeasurable.map_map_of_aemeasurable hX hf,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

/-- If `X` and `Y` are independent under `μ'` and `f` has law `μ'` under `μ`, then `X ∘ f` and
`Y ∘ f` are independent under `μ`. -/
lemma IndepFun.comp_hasLaw {F : Type*} {mF : MeasurableSpace F} [IsFiniteMeasure μ]
    {μ' : Measure Ω'} {X : Ω' → E} {Y : Ω' → F} {f : Ω → Ω'} (h : X ⟂ᵢ[μ'] Y)
    (hf : HasLaw f μ' μ) (hX : AEMeasurable X μ') (hY : AEMeasurable Y μ') :
    (X ∘ f) ⟂ᵢ[μ] (Y ∘ f) := by
  rw [← hf.map_eq] at h hX hY
  exact (indepFun_map_iff hf.aemeasurable hX hY).1 h

end ProbabilityTheory

namespace ProbabilityTheory

section Prod

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

lemma indepFun_fst_prod {μ : Measure α} [IsFiniteMeasure μ] {X : α → γ} {Y : α → δ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (h_indep : IndepFun X Y μ)
    (ν : Measure β) [IsProbabilityMeasure ν] :
    IndepFun (fun ω ↦ X ω.1) (fun ω ↦ Y ω.1) (μ.prod ν) :=
  h_indep.comp_hasLaw (hasLaw_fst_prod μ ν) hX hY

lemma indepFun_snd_prod {μ : Measure α} [IsFiniteMeasure μ] {X : α → γ} {Y : α → δ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (h_indep : IndepFun X Y μ)
    (ν : Measure β) [IsProbabilityMeasure ν] :
    IndepFun (fun ω ↦ X ω.2) (fun ω ↦ Y ω.2) (ν.prod μ) :=
  h_indep.comp_hasLaw (hasLaw_snd_prod ν μ) hX hY

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

section OfMeasurable

variable {α γ δ γ' δ' : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
  {mδ : MeasurableSpace δ} {mγ' : MeasurableSpace γ'} {mδ' : MeasurableSpace δ'}
  {μ : Measure α} {Y : α → γ} {Z : α → δ} {Y' : α → γ'} {Z' : α → δ'}

lemma IndepFun.of_measurable_left
    (h_indep : Y ⟂ᵢ[μ] Z) (hY_meas : Measurable[mγ.comap Y] Y') :
    Y' ⟂ᵢ[μ] Z := by
  rw [IndepFun_iff_Indep] at h_indep ⊢
  exact indep_of_indep_of_le_left h_indep hY_meas.comap_le

lemma IndepFun.of_measurable_right
    (h_indep : Y ⟂ᵢ[μ] Z) (hZ_meas : Measurable[mδ.comap Z] Z') :
    Y ⟂ᵢ[μ] Z' := by
  rw [IndepFun_iff_Indep] at h_indep ⊢
  exact indep_of_indep_of_le_right h_indep hZ_meas.comap_le

lemma IndepFun.of_measurable (h_indep : Y ⟂ᵢ[μ] Z)
    (hY_meas : Measurable[mγ.comap Y] Y') (hZ_meas : Measurable[mδ.comap Z] Z') :
    Y' ⟂ᵢ[μ] Z' :=
  (h_indep.of_measurable_left hY_meas).of_measurable_right hZ_meas

end OfMeasurable

section Cond

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {X : α → β} {T : α → γ}

lemma cond_of_indepFun [IsZeroOrProbabilityMeasure μ] (h : IndepFun X T μ)
    (hX : Measurable X) (hT : Measurable T) {s : Set β} (hs : MeasurableSet s)
    (hμs : μ (X ⁻¹' s) ≠ 0) :
    (μ[|X ⁻¹' s]).map T = μ.map T := by
  ext t ht
  rw [Measure.map_apply (by fun_prop) ht, Measure.map_apply (by fun_prop) ht, cond_apply (hX hs),
    IndepSet.measure_inter_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
  · exact hμs
  · simp
  · rw [indepFun_iff_indepSet_preimage hX hT] at h
    exact h s t hs ht

end Cond

end ProbabilityTheory
