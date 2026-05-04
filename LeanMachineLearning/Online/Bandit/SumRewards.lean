/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.Bandit.ArrayProbSpace
public import LeanMachineLearning.Online.Bandit.Regret
public import LeanMachineLearning.Probability.Moments.SubGaussian

/-! # Law of the sum of rewards
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning
open scoped ENNReal NNReal

namespace Bandits

namespace ArrayModel

variable {α : Type*} {mα : MeasurableSpace α} [DecidableEq α] [Countable α]
  [StandardBorelSpace α] [Nonempty α]
  {alg : Algorithm α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]

local notation "A" => action alg
local notation "R" => reward alg
local notation "𝔓" => arrayMeasure ν

omit [DecidableEq α] [StandardBorelSpace α] [Nonempty α] in
lemma identDistrib_sum_range_snd (a : α) (k : ℕ) :
    IdentDistrib (fun ω ↦ ∑ i ∈ range k, ω.2 i a) (fun ω ↦ ∑ i ∈ range k, ω i a)
      𝔓 (streamMeasure ν) where
  aemeasurable_fst := by fun_prop
  aemeasurable_snd := (measurable_sum _ fun i _ ↦ by fun_prop).aemeasurable
  map_eq := by
    rw [← Measure.snd_prod (μ := (Measure.infinitePi fun (_ : ℕ) ↦ (volume : Measure unitInterval)))
      (ν := streamMeasure ν), Measure.snd, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl

lemma prob_pullCount_prod_sumRewards_mem_le (a : α) (n : ℕ)
    {s : Set (ℕ × ℝ)} [DecidablePred (· ∈ Prod.fst '' s)] (hs : MeasurableSet s) :
    𝔓 {ω | (pullCount A a n ω, sumRewards A R a n ω) ∈ s} ≤
      ∑ k ∈ (range (n + 1)).filter (· ∈ Prod.fst '' s),
        streamMeasure ν {ω | ∑ i ∈ range k, ω i a ∈ Prod.mk k ⁻¹' s} := by
  simp_rw [sumRewards_eq]
  calc 𝔓 ((fun ω ↦ (pullCount A a n ω, ∑ i ∈ range (pullCount A a n ω), ω.2 i a)) ⁻¹' s)
  _ ≤ 𝔓 {ω | ∃ k ≤ n, (k, ∑ i ∈ range k, ω.2 i a) ∈ s} := by
    refine measure_mono fun ω hω ↦ ?_
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact ⟨pullCount A a n ω, pullCount_le _ _ _, hω⟩
  _ = 𝔓 (⋃ k ∈ (range (n + 1)).filter (· ∈ Prod.fst '' s),
      {ω | (k, ∑ i ∈ range k, ω.2 i a) ∈ s}) := by congr 1; ext; simp; grind
  _ ≤ ∑ k ∈ (range (n + 1)).filter (· ∈ Prod.fst '' s),
      𝔓 {ω | ∑ i ∈ range k, ω.2 i a ∈ Prod.mk k ⁻¹' s} := measure_biUnion_finset_le _ _
  _ = ∑ k ∈ (range (n + 1)).filter (· ∈ Prod.fst '' s),
      (streamMeasure ν) {ω | ∑ i ∈ range k, ω i a ∈ Prod.mk k ⁻¹' s} := by
    congr with k
    have : (𝔓).map (fun ω ↦ ∑ i ∈ range k, ω.2 i a) =
        (streamMeasure ν).map (fun ω ↦ ∑ i ∈ range k, ω i a) :=
      (identDistrib_sum_range_snd a k).map_eq
    rw [Measure.ext_iff] at this
    specialize this (Prod.mk k ⁻¹' s) (hs.preimage (by fun_prop))
    rwa [Measure.map_apply (by fun_prop) (hs.preimage (by fun_prop)),
      Measure.map_apply (by fun_prop) (hs.preimage (by fun_prop))] at this

lemma prob_pullCount_mem_and_sumRewards_mem_le (a : α) (n : ℕ)
    {s : Set ℕ} [DecidablePred (· ∈ s)] (hs : MeasurableSet s) {B : Set ℝ} (hB : MeasurableSet B) :
    𝔓 {ω | pullCount A a n ω ∈ s ∧ sumRewards A R a n ω ∈ B} ≤
      ∑ k ∈ (range (n + 1)).filter (· ∈ s),
        streamMeasure ν {ω | ∑ i ∈ range k, ω i a ∈ B} := by
  classical
  rcases Set.eq_empty_or_nonempty B with h_empty | h_nonempty
  · simp [h_empty]
  convert prob_pullCount_prod_sumRewards_mem_le a n (hs.prod hB) (ν := ν) (alg := alg) with _ _ k hk
  · ext n
    have : ∃ x, x ∈ B := h_nonempty
    simp [this]
  · ext x
    simp only [Set.mem_image, Set.mem_prod, Prod.exists, exists_and_right, exists_and_left,
      exists_eq_right, mem_filter, mem_range] at hk
    simp [hk.2.1]

lemma prob_exists_pullCount_eq_and_sumRewards_mem_le (a : α) (m : ℕ) {B : Set ℝ}
    (hB : MeasurableSet B) : 𝔓 {ω | ∃ n, pullCount A a n ω = m ∧ sumRewards A R a n ω ∈ B} ≤
      streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B} :=
  calc
    _ ≤ 𝔓 {ω | ∑ i ∈ range m, ω.2 i a ∈ B} := by
        apply measure_mono
        intro ω ⟨n, hp, hn⟩
        rwa [sumRewards_eq alg a n ω, hp] at hn
    _ = streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B} :=
        (identDistrib_sum_range_snd a m).measure_mem_eq hB

lemma prob_sumRewards_le_sumRewards_le [Fintype α] (a : α) (n m₁ m₂ : ℕ) :
    (𝔓) {ω | pullCount A (bestArm ν) n ω = m₁ ∧ pullCount A a n ω = m₂ ∧
        sumRewards A R (bestArm ν) n ω ≤ sumRewards A R a n ω} ≤
      streamMeasure ν
        {ω | ∑ i ∈ range m₁, ω i (bestArm ν) ≤ ∑ i ∈ range m₂, ω i a} := by
  simp_rw [sumRewards_eq]
  calc 𝔓 {ω | pullCount A (bestArm ν) n ω = m₁ ∧ pullCount A a n ω = m₂ ∧
      ∑ i ∈ range (pullCount A (bestArm ν) n ω), ω.2 i (bestArm ν) ≤
        ∑ i ∈ range (pullCount A a n ω), ω.2 i a}
  _ ≤ 𝔓 ((fun ω ↦ (∑ i ∈ range m₁, ω.2 i (bestArm ν), ∑ i ∈ range m₂, ω.2 i a)) ⁻¹'
        {p | p.1 ≤ p.2}) := by
      refine measure_mono fun ω hω ↦ ?_
      simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq] at hω ⊢
      grind
  _ = streamMeasure ν
      {ω | ∑ i ∈ range m₁, ω i (bestArm ν) ≤ ∑ i ∈ range m₂, ω i a} := by
    rw [← Measure.snd_prod (μ := (Measure.infinitePi fun (_ : ℕ) ↦ (volume : Measure unitInterval)))
      (ν := streamMeasure ν), Measure.snd, Measure.map_apply (by fun_prop)]
    · rfl
    simp only [measurableSet_setOf]
    fun_prop

lemma probReal_sumRewards_le_sumRewards_le [Fintype α] (a : α) (n m₁ m₂ : ℕ) :
    (𝔓).real {ω | pullCount A (bestArm ν) n ω = m₁ ∧ pullCount A a n ω = m₂ ∧
        sumRewards A R (bestArm ν) n ω ≤ sumRewards A R a n ω} ≤
      (streamMeasure ν).real
        {ω | ∑ i ∈ range m₁, ω i (bestArm ν) ≤ ∑ i ∈ range m₂, ω i a} := by
  simp_rw [measureReal_def]
  gcongr
  · finiteness
  · exact prob_sumRewards_le_sumRewards_le a n m₁ m₂

end ArrayModel

variable {α Ω Ω' : Type*} [DecidableEq α] {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
  {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {alg : Algorithm α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]
  {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {A₂ : ℕ → Ω' → α} {R₂ : ℕ → Ω' → ℝ}
  {ω : Ω} {m n t : ℕ} {a : α}

lemma sumRewards_eq_comp :
    sumRewards A R a n =
     (fun p ↦ ∑ i ∈ range n, if (p i).1 = a then (p i).2 else 0) ∘ (fun ω n ↦ (A n ω, R n ω)) := by
  ext
  simp [sumRewards]

lemma pullCount_eq_comp :
    pullCount A a n =
      (fun p ↦ ∑ i ∈ range n, if (p i).1 = a then 1 else 0) ∘ (fun ω n ↦ (A n ω, R n ω)) := by
  ext
  simp [pullCount]

variable [StandardBorelSpace α] [Nonempty α]

-- todo: write those lemmas with IdentDistrib instead of equality of maps
lemma _root_.Learning.IsAlgEnvSeq.law_sumRewards_unique
    (h1 : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (h2 : IsAlgEnvSeq A₂ R₂ alg (stationaryEnv ν) P') :
    P.map (sumRewards A R a n) = P'.map (sumRewards A₂ R₂ a n) := by
  have hA := h1.measurable_A
  have hR := h1.measurable_R
  have hA2 := h2.measurable_A
  have hR2 := h2.measurable_R
  have h_unique := isAlgEnvSeq_unique h1 h2
  rw [sumRewards_eq_comp, sumRewards_eq_comp, ← Measure.map_map, h_unique, Measure.map_map,
    ← sumRewards_eq_comp]
  · refine measurable_sum _ fun i hi ↦ Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  · rw [measurable_pi_iff]
    exact fun n ↦ Measurable.prodMk (hA2 n) (hR2 n)
  · refine measurable_sum _ fun i hi ↦ Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  · rw [measurable_pi_iff]
    exact fun n ↦ Measurable.prodMk (hA n) (hR n)

lemma _root_.Learning.IsAlgEnvSeq.law_pullCount_sumRewards_unique'
    (h1 : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (h2 : IsAlgEnvSeq A₂ R₂ alg (stationaryEnv ν) P') :
    IdentDistrib (fun ω a ↦ (pullCount A a n ω, sumRewards A R a n ω))
      (fun ω a ↦ (pullCount A₂ a n ω, sumRewards A₂ R₂ a n ω)) P P' := by
  have hA := h1.measurable_A
  have hR := h1.measurable_R
  have hA2 := h2.measurable_A
  have hR2 := h2.measurable_R
  constructor
  · refine Measurable.aemeasurable ?_
    rw [measurable_pi_iff]
    exact fun a ↦ Measurable.prod (by fun_prop) (measurable_sumRewards hA hR _ _)
  · refine Measurable.aemeasurable ?_
    rw [measurable_pi_iff]
    exact fun a ↦ Measurable.prod (by fun_prop) (measurable_sumRewards hA2 hR2 _ _)
  have h_unique := isAlgEnvSeq_unique h1 h2
  let f := fun (p : ℕ → α × ℝ ) (a : α) ↦ (∑ i ∈ range n, if (p i).1 = a then 1 else 0,
    ∑ i ∈ range n, if (p i).1 = a then (p i).2 else 0)
  have hf : Measurable f := by
    rw [measurable_pi_iff]
    intro a
    refine Measurable.prod ?_ ?_
    · simp only [f]
      refine measurable_sum _ fun i hi ↦ Measurable.ite ?_ (by fun_prop) (by fun_prop)
      exact (measurableSet_singleton _).preimage (by fun_prop)
    · simp only [f]
      refine measurable_sum _ fun i hi ↦ Measurable.ite ?_ (by fun_prop) (by fun_prop)
      exact (measurableSet_singleton _).preimage (by fun_prop)
  have h_eq_comp : (fun ω a ↦ (pullCount A a n ω, sumRewards A R a n ω))
      = f ∘ (fun ω n ↦ (A n ω, R n ω)) := by
    ext ω a : 2
    rw [pullCount_eq_comp (R := R), sumRewards_eq_comp]
    grind
  have h_eq_comp2 : (fun ω a ↦ (pullCount A₂ a n ω, sumRewards A₂ R₂ a n ω))
      = f ∘ (fun ω n ↦ (A₂ n ω, R₂ n ω)) := by
    ext ω a : 2
    rw [pullCount_eq_comp (R := R₂), sumRewards_eq_comp]
    grind
  rw [h_eq_comp, h_eq_comp2, ← Measure.map_map hf, h_unique, Measure.map_map hf,
    ← h_eq_comp2]
  · rw [measurable_pi_iff]
    exact fun n ↦ Measurable.prodMk (hA2 n) (hR2 n)
  · rw [measurable_pi_iff]
    exact fun n ↦ Measurable.prodMk (hA n) (hR n)

lemma _root_.Learning.IsAlgEnvSeq.law_pullCount_sumRewards_unique
    (h1 : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (h2 : IsAlgEnvSeq A₂ R₂ alg (stationaryEnv ν) P') :
    P.map (fun ω ↦ (pullCount A a n ω, sumRewards A R a n ω)) =
      P'.map (fun ω ↦ (pullCount A₂ a n ω, sumRewards A₂ R₂ a n ω)) :=
  ((h1.law_pullCount_sumRewards_unique' h2 (n := n)).comp (u := fun f ↦ f a) (by fun_prop)).map_eq

lemma _root_.Learning.IsAlgEnvSeq.identDistrib_pullCount_sumRewards
    (h1 : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (h2 : IsAlgEnvSeq A₂ R₂ alg (stationaryEnv ν) P') :
    IdentDistrib (fun ω n a ↦ (pullCount A a n ω, sumRewards A R a n ω))
      (fun ω' n a ↦ (pullCount A₂ a n ω', sumRewards A₂ R₂ a n ω')) P P' := by
  let f (τ : ℕ → α × ℝ) (n : ℕ) (a : α) : ℕ × ℝ :=
    (∑ i ∈ range n, if (τ i).1 = a then 1 else 0,
     ∑ i ∈ range n, if (τ i).1 = a then (τ i).2 else 0)
  have hc1 : (fun ω n a ↦ (pullCount A a n ω, sumRewards A R a n ω)) =
      f ∘ (fun ω n ↦ (A n ω, R n ω)) := by
    ext ω n a : 3
    simp_rw [Function.comp, f, pullCount, card_filter, sumRewards]
  have hc2 : (fun ω' n a ↦ (pullCount A₂ a n ω', sumRewards A₂ R₂ a n ω')) =
      f ∘ (fun ω' n ↦ (A₂ n ω', R₂ n ω')) := by
    ext ω' n a : 3
    simp_rw [Function.comp, f, pullCount, card_filter, sumRewards]
  have hf : Measurable f := by
    simp_rw [f, measurable_pi_iff]
    intro n a
    apply Measurable.prod
    · dsimp only
      exact measurable_sum _
        (fun _ _ ↦ Measurable.ite (by measurability) (by fun_prop) (by fun_prop))
    · dsimp only
      exact measurable_sum _
        (fun _ _ ↦ Measurable.ite (by measurability) (by fun_prop) (by fun_prop))
  rw [hc1, hc2]
  exact (h1.identDistrib_trajectory h2).comp hf

-- this is what we will use for UCB
lemma prob_pullCount_prod_sumRewards_mem_le [Countable α]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {s : Set (ℕ × ℝ)} [DecidablePred (· ∈ Prod.fst '' s)] (hs : MeasurableSet s) :
    P {ω | (pullCount A a n ω, sumRewards A R a n ω) ∈ s} ≤
      ∑ k ∈ (range (n + 1)).filter (· ∈ Prod.fst '' s),
        streamMeasure ν {ω | ∑ i ∈ range k, ω i a ∈ Prod.mk k ⁻¹' s} := by
  have hA := h.measurable_A
  have hR := h.measurable_R
  calc P {ω | (pullCount A a n ω, sumRewards A R a n ω) ∈ s}
  _ = (P.map (fun ω ↦ (pullCount A a n ω, sumRewards A R a n ω))) s := by
      rw [Measure.map_apply (by fun_prop) hs]; rfl
  _ = ((ArrayModel.arrayMeasure ν).map
      (fun ω ↦ (pullCount (ArrayModel.action alg) a n ω,
        sumRewards (ArrayModel.action alg) (ArrayModel.reward alg) a n ω))) s := by
    rw [h.law_pullCount_sumRewards_unique (ArrayModel.isAlgEnvSeq_arrayMeasure alg ν)]
  _ = (ArrayModel.arrayMeasure ν) {ω | (pullCount (ArrayModel.action alg) a n ω,
      sumRewards (ArrayModel.action alg) (ArrayModel.reward alg) a n ω) ∈ s} := by
    rw [Measure.map_apply (by fun_prop) hs]; rfl
  _ ≤ ∑ k ∈ (range (n + 1)).filter (· ∈ Prod.fst '' s),
      streamMeasure ν {ω | ∑ i ∈ range k, ω i a ∈ Prod.mk k ⁻¹' s} :=
    ArrayModel.prob_pullCount_prod_sumRewards_mem_le a n hs

lemma prob_pullCount_mem_and_sumRewards_mem_le [Countable α]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {s : Set ℕ} [DecidablePred (· ∈ s)] (hs : MeasurableSet s) {B : Set ℝ} (hB : MeasurableSet B) :
    P {ω | pullCount A a n ω ∈ s ∧ sumRewards A R a n ω ∈ B} ≤
      ∑ k ∈ (range (n + 1)).filter (· ∈ s),
        streamMeasure ν {ω | ∑ i ∈ range k, ω i a ∈ B} := by
  classical
  rcases Set.eq_empty_or_nonempty B with h_empty | h_nonempty
  · simp [h_empty]
  convert prob_pullCount_prod_sumRewards_mem_le h (hs.prod hB) (ν := ν) (alg := alg) with _ _ k hk
  · ext n
    have : ∃ x, x ∈ B := h_nonempty
    simp [this]
  · ext x
    simp only [Set.mem_image, Set.mem_prod, Prod.exists, exists_and_right, exists_and_left,
      exists_eq_right, mem_filter, mem_range] at hk
    simp [hk.2.1]

lemma prob_sumRewards_mem_le [Countable α] (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {B : Set ℝ} (hB : MeasurableSet B) :
    P (sumRewards A R a n ⁻¹' B) ≤
      ∑ k ∈ range (n + 1), streamMeasure ν {ω | ∑ i ∈ range k, ω i a ∈ B} := by
  classical
  have h_le := prob_pullCount_mem_and_sumRewards_mem_le h .univ hB (a := a) (n := n)
  simpa using h_le

lemma prob_pullCount_eq_and_sumRewards_mem_le [Countable α]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {m : ℕ} (hm : m ≤ n) {B : Set ℝ} (hB : MeasurableSet B) :
    P {ω | pullCount A a n ω = m ∧ sumRewards A R a n ω ∈ B} ≤
      streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B} := by
  have h_le := prob_pullCount_mem_and_sumRewards_mem_le h (s := {m}) (by simp) hB (a := a) (n := n)
  have hm' : m < n + 1 := by lia
  simpa [hm'] using h_le

lemma prob_exists_pullCount_eq_and_sumRewards_mem_le [Countable α]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : α) (m : ℕ) {B : Set ℝ}
    (hB : MeasurableSet B) :
    P {ω | ∃ n, pullCount A a n ω = m ∧ sumRewards A R a n ω ∈ B} ≤
      streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B} :=
  let s := {p : ℕ → α → ℕ × ℝ | ∃ n, (p n a).1 = m ∧ (p n a).2 ∈ B}
  have : s = ⋃ n, (fun p ↦ p n a) ⁻¹' ({m} ×ˢ B) := by
    ext p
    simp [s]
  have hs : MeasurableSet s := by measurability
  calc P {ω | ∃ n, pullCount A a n ω = m ∧ sumRewards A R a n ω ∈ B}
    _ = (ArrayModel.arrayMeasure ν) {ω | ∃ n, pullCount (ArrayModel.action alg) a n ω = m ∧
            sumRewards (ArrayModel.action alg) (ArrayModel.reward alg) a n ω ∈ B} :=
        (h.identDistrib_pullCount_sumRewards
          (ArrayModel.isAlgEnvSeq_arrayMeasure alg ν)).measure_mem_eq hs
    _ ≤ _ := ArrayModel.prob_exists_pullCount_eq_and_sumRewards_mem_le a m hB

lemma probReal_sumRewards_le_sumRewards_le [Fintype α] (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (a : α) (n m₁ m₂ : ℕ) :
    P.real {ω | pullCount A (bestArm ν) n ω = m₁ ∧ pullCount A a n ω = m₂ ∧
        sumRewards A R (bestArm ν) n ω ≤ sumRewards A R a n ω} ≤
      (streamMeasure ν).real
        {ω | ∑ i ∈ range m₁, ω i (bestArm ν) ≤ ∑ i ∈ range m₂, ω i a} := by
  have hA := h.measurable_A
  have hR := h.measurable_R
  refine le_trans (le_of_eq ?_)
    (ArrayModel.probReal_sumRewards_le_sumRewards_le (alg := alg) a n m₁ m₂)
  let s := {p : ℕ × ℕ × ℝ × ℝ | p.1 = m₁ ∧ p.2.1 = m₂ ∧ p.2.2.1 ≤ p.2.2.2}
  have hs : MeasurableSet s := by simp only [measurableSet_setOf, s]; fun_prop
  change P.real ((fun ω ↦ (pullCount A (bestArm ν) n ω,
      pullCount A a n ω, sumRewards A R (bestArm ν) n ω, sumRewards A R a n ω)) ⁻¹' s) =
    (ArrayModel.arrayMeasure ν).real
      ((fun ω ↦ (pullCount (ArrayModel.action alg) (bestArm ν) n ω,
        pullCount (ArrayModel.action alg) a n ω,
        sumRewards (ArrayModel.action alg) (ArrayModel.reward alg) (bestArm ν) n ω,
        sumRewards (ArrayModel.action alg) (ArrayModel.reward alg) a n ω)) ⁻¹' s)
  simp_rw [measureReal_def]
  congr 1
  rw [← Measure.map_apply ?_ hs, ← Measure.map_apply (by fun_prop) hs]
  swap
  · refine Measurable.prod (by fun_prop) (Measurable.prod (by fun_prop) ?_)
    exact (measurable_sumRewards hA hR _ _).prod (measurable_sumRewards hA hR _ _)
  congr 1
  refine IdentDistrib.map_eq ?_
  have h_eq := h.law_pullCount_sumRewards_unique' (ArrayModel.isAlgEnvSeq_arrayMeasure alg ν)
    (n := n)
  exact h_eq.comp (u := fun p ↦ ((p (bestArm ν)).1, (p a).1, (p (bestArm ν)).2, (p a).2))
    (by fun_prop)

section Subgaussian

namespace StreamMeasure

omit [DecidableEq α] [StandardBorelSpace α] [Nonempty α]

lemma prob_sum_range_sub_ge_le_of_HasSubgaussianMGF {σ2 : ℝ≥0}
    (h : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    streamMeasure ν {ω | ε ≤ ∑ k ∈ range n, (ω k a - (ν a)[id])} ≤
      ENNReal.ofReal (Real.exp (-ε ^ 2 / (2 * n * σ2))) := by
  rw [← ofReal_measureReal]
  gcongr
  apply HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun _ _ hε
  · exact (iIndepFun_eval_streamMeasure'' ν a).comp (fun _ x ↦ x - (ν a)[id]) (by fun_prop)
  · intro _ _
    exact h.congr_identDistrib ((identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _)

lemma prob_sum_range_sub_le_le_of_HasSubgaussianMGF {σ2 : ℝ≥0}
    (h : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    streamMeasure ν {ω | ∑ k ∈ range n, (ω k a - (ν a)[id]) ≤ -ε} ≤
      ENNReal.ofReal (Real.exp (-ε ^ 2 / (2 * n * σ2))) := by
  rw [← ofReal_measureReal]
  gcongr
  apply HasSubgaussianMGF.measure_sum_range_le_le_of_iIndepFun _ _ hε
  · exact (iIndepFun_eval_streamMeasure'' ν a).comp (fun _ x ↦ x - (ν a)[id]) (by fun_prop)
  · intro _ _
    exact h.congr_identDistrib ((identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _)

/-- Auxiliary lemma for `prob_sum_range_sub_*_le_of_HasSubgaussianMGF'`. -/
private lemma exp_neg_sqrt_sq_div_le {σ2 : ℝ≥0} (hσ2 : 0 < σ2) {δ : ℝ} (hδ : 0 < δ) (hn : 0 < n) :
    Real.exp (-√(2 * n * σ2 * Real.log (1 / δ)) ^ 2 / (2 * n * σ2)) ≤ δ := by
  by_cases hd : δ < 1
  · have hl : 0 < Real.log (1 / δ) := Real.log_pos ((one_lt_div hδ).2 hd)
    rw [Real.sq_sqrt (by positivity)]
    field_simp
    simp [Real.exp_log hδ]
  · push Not at hd
    have hl : Real.log (1 / δ) ≤ 0 := Real.log_nonpos (by positivity) (div_le_one_of_le₀ hd (hδ.le))
    rw [Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hl)]
    simp [hd]

lemma prob_sum_range_sub_ge_le_of_HasSubgaussianMGF' {σ2 : ℝ≥0} (hσ2 : 0 < σ2)
    (h : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {δ : ℝ} (hδ : 0 < δ) (hn : 0 < n) :
    streamMeasure ν {ω | √(2 * n * σ2 * Real.log (1 / δ)) ≤
      ∑ k ∈ range n, (ω k a - (ν a)[id])} ≤ ENNReal.ofReal δ :=
  calc
  _ ≤ ENNReal.ofReal (Real.exp (-√(2 * n * σ2 * Real.log (1 / δ)) ^ 2 / (2 * n * σ2))) :=
    prob_sum_range_sub_ge_le_of_HasSubgaussianMGF h (by positivity) n
  _ ≤ ENNReal.ofReal δ := by
    gcongr
    exact exp_neg_sqrt_sq_div_le hσ2 hδ hn

lemma prob_sum_range_sub_le_le_of_HasSubgaussianMGF' {σ2 : ℝ≥0} (hσ2 : 0 < σ2)
    (h : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {δ : ℝ} (hδ : 0 < δ) (hn : 0 < n) :
    streamMeasure ν {ω | ∑ k ∈ range n, (ω k a - (ν a)[id]) ≤
      -√(2 * n * σ2 * Real.log (1 / δ))} ≤ ENNReal.ofReal δ :=
  calc
  _ ≤ ENNReal.ofReal (Real.exp (-√(2 * n * σ2 * Real.log (1 / δ)) ^ 2 / (2 * n * σ2))) :=
    prob_sum_range_sub_le_le_of_HasSubgaussianMGF h (by positivity) n
  _ ≤ ENNReal.ofReal δ := by
    gcongr
    exact exp_neg_sqrt_sq_div_le hσ2 hδ hn

end StreamMeasure

lemma prob_sumRewards_sub_pullCount_mul_ge_le [Countable α] {σ2 : ℝ≥0} (hσ2 : 0 < σ2)
    (ha : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a))
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) {δ : ℝ} (hδ : 0 < δ) :
    P {ω | ∃ t < n, pullCount A a t ω ≠ 0 ∧ √(2 * pullCount A a t ω * σ2 * Real.log (1 / δ)) ≤
      sumRewards A R a t ω - pullCount A a t ω * (ν a)[id]} ≤ ENNReal.ofReal ((n - 1) * δ) :=
  let B (m : ℕ) := {x : ℝ | √(2 * m * σ2 * Real.log (1 / δ)) ≤ x - m * (ν a)[id]}
  calc
    _ ≤ P (⋃ m ∈ Icc 1 (n - 1), {ω | ∃ t, t < n ∧ pullCount A a t ω = m ∧
            sumRewards A R a t ω ∈ B m}) := by
        apply measure_mono
        intro ω ⟨t, ht, hp, hb⟩
        have hm : pullCount A a t ω ∈ Icc 1 (n - 1) := mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hp,
          (pullCount_le a t ω).trans (Nat.le_sub_one_of_lt ht)⟩
        exact Set.mem_biUnion hm ⟨t, ht, rfl, hb⟩
    _ ≤ ∑ m ∈ Icc 1 (n - 1), P {ω | ∃ t, t < n ∧ pullCount A a t ω = m ∧
          sumRewards A R a t ω ∈ B m} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ m ∈ Icc 1 (n - 1), P {ω | ∃ t, pullCount A a t ω = m ∧ sumRewards A R a t ω ∈ B m} :=
        sum_le_sum (fun _ _ ↦ measure_mono (fun _ ⟨t, _, hps⟩ ↦ ⟨t, hps⟩))
    _ ≤ ∑ m ∈ Icc 1 (n - 1), streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B m} := by
        apply sum_le_sum
        exact (fun m _ ↦ prob_exists_pullCount_eq_and_sumRewards_mem_le h a m (by measurability))
    _ ≤ ∑ m ∈ Icc 1 (n - 1), ENNReal.ofReal δ := by
      apply sum_le_sum
      intro m hm
      convert StreamMeasure.prob_sum_range_sub_ge_le_of_HasSubgaussianMGF' hσ2 ha hδ
        (mem_Icc.mp hm).1 using 2
      simp [B]
    _ = ENNReal.ofReal ((n - 1) * δ) := by
      by_cases hn : n = 0
      · simp [hn, hδ.le]
      · rw [sum_const, Nat.card_Icc, add_tsub_cancel_right, ← ENNReal.ofReal_nsmul, nsmul_eq_mul,
          Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn)]
        ring_nf

lemma prob_sumRewards_sub_pullCount_mul_le_le [Countable α] {σ2 : ℝ≥0} (hσ2 : 0 < σ2)
    (ha : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a))
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) {δ : ℝ} (hδ : 0 < δ) :
    P {ω | ∃ t < n, pullCount A a t ω ≠ 0 ∧
      sumRewards A R a t ω - pullCount A a t ω * (ν a)[id] ≤
        -√(2 * pullCount A a t ω * σ2 * Real.log (1 / δ))} ≤ ENNReal.ofReal ((n - 1) * δ) :=
  let B (m : ℕ) := {x : ℝ | x - m * (ν a)[id] ≤ -√(2 * m * σ2 * Real.log (1 / δ))}
  calc
    _ ≤ P (⋃ m ∈ Icc 1 (n - 1), {ω | ∃ t, t < n ∧ pullCount A a t ω = m ∧
            sumRewards A R a t ω ∈ B m}) := by
        apply measure_mono
        intro ω ⟨t, ht, hp, hb⟩
        have hm : pullCount A a t ω ∈ Icc 1 (n - 1) := mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hp,
          (pullCount_le a t ω).trans (Nat.le_sub_one_of_lt ht)⟩
        exact Set.mem_biUnion hm ⟨t, ht, rfl, hb⟩
    _ ≤ ∑ m ∈ Icc 1 (n - 1), P {ω | ∃ t, t < n ∧ pullCount A a t ω = m ∧
          sumRewards A R a t ω ∈ B m} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ m ∈ Icc 1 (n - 1), P {ω | ∃ t, pullCount A a t ω = m ∧ sumRewards A R a t ω ∈ B m} :=
        sum_le_sum (fun _ _ ↦ measure_mono (fun _ ⟨t, _, hps⟩ ↦ ⟨t, hps⟩))
    _ ≤ ∑ m ∈ Icc 1 (n - 1), streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B m} := by
        apply sum_le_sum
        exact (fun m _ ↦ prob_exists_pullCount_eq_and_sumRewards_mem_le h a m (by measurability))
    _ ≤ ∑ m ∈ Icc 1 (n - 1), ENNReal.ofReal δ := by
      apply sum_le_sum
      intro m hm
      convert StreamMeasure.prob_sum_range_sub_le_le_of_HasSubgaussianMGF' hσ2 ha hδ
        (mem_Icc.mp hm).1 using 2
      simp [B]
    _ = ENNReal.ofReal ((n - 1) * δ) := by
      by_cases hn : n = 0
      · simp [hn, hδ.le]
      · rw [sum_const, Nat.card_Icc, add_tsub_cancel_right, ← ENNReal.ofReal_nsmul, nsmul_eq_mul,
          Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn)]
        ring_nf

lemma prob_sumRewards_sub_pullCount_mul_ge_le_of_Fintype [Fintype α] {σ2 : ℝ≥0} (hσ2 : 0 < σ2)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a))
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) {δ : ℝ} (hδ : 0 < δ) :
    P {ω | ∃ a, ∃ t < n, pullCount A a t ω ≠ 0 ∧
        √(2 * pullCount A a t ω * σ2 * Real.log (1 / δ)) ≤
          sumRewards A R a t ω - pullCount A a t ω * (ν a)[id]} ≤
            ENNReal.ofReal (Fintype.card α * (n - 1) * δ) :=
  calc
    _ ≤ ∑ a, P {ω | ∃ t < n, pullCount A a t ω ≠ 0 ∧
                √(2 * pullCount A a t ω * σ2 * Real.log (1 / δ)) ≤
                  sumRewards A R a t ω - pullCount A a t ω * (ν a)[id]} := by
        rw [Set.setOf_exists]
        exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ a, ENNReal.ofReal ((n - 1) * δ) :=
        sum_le_sum fun a _ ↦ prob_sumRewards_sub_pullCount_mul_ge_le hσ2 (hν a) h hδ
    _ = ENNReal.ofReal (Fintype.card α * (n - 1) * δ) := by
      rw [sum_const, Finset.card_univ, ← ENNReal.ofReal_nsmul, nsmul_eq_mul]
      ring_nf

omit [DecidableEq α] [StandardBorelSpace α] in
lemma probReal_sum_le_sum_streamMeasure [Fintype α] {c : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) c (ν a)) (a : α) (m : ℕ) :
    (streamMeasure ν).real
        {ω | ∑ s ∈ range m, ω s (bestArm ν) ≤ ∑ s ∈ range m, ω s a} ≤
      Real.exp (-↑m * gap ν a ^ 2 / (4 * c)) := by
  by_cases ha : a = bestArm ν
  · simp [ha]
  refine (HasSubgaussianMGF.measure_sum_le_sum_le' (cX := fun _ ↦ c) (cY := fun _ ↦ c)
    ?_ ?_ ?_ ?_ ?_ ?_).trans_eq ?_
  · exact iIndepFun_eval_streamMeasure'' ν (bestArm ν)
  · exact iIndepFun_eval_streamMeasure'' ν a
  · intro i him
    simp_rw [integral_eval_streamMeasure]
    refine (hν (bestArm ν)).congr_identDistrib ?_
    exact (identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _
  · intro i him
    simp_rw [integral_eval_streamMeasure]
    refine (hν a).congr_identDistrib ?_
    exact (identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _
  · exact indepFun_eval_streamMeasure' ν (Ne.symm ha)
  · gcongr 1 with i him
    simp_rw [integral_eval_streamMeasure]
    exact le_bestArm a
  · congr 1
    simp_rw [integral_eval_streamMeasure]
    simp only [id_eq, sum_const, card_range, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast,
      gap_eq_bestArm_sub, neg_mul]
    field_simp
    ring

omit [DecidableEq α] [StandardBorelSpace α] [Nonempty α] in
lemma prob_sum_le_sqrt_log {σ2 : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a))
    (hσ2 : σ2 ≠ 0) {c : ℝ} (hc : 0 ≤ c) (a : α) (k : ℕ) (hk : k ≠ 0) :
    streamMeasure ν
        {ω | (∑ s ∈ range k, (ω s a - (ν a)[id])) ≤ - √(2 * c * k * σ2 * Real.log (n + 1))} ≤
      1 / (n + 1) ^ c := by
  calc
    streamMeasure ν
      {ω | (∑ s ∈ range k, (ω s a - (ν a)[id])) ≤ - √(2 * c * k * σ2 * Real.log (n + 1))}
  _ ≤ ENNReal.ofReal (Real.exp (-(√(2 * c * k * σ2 * Real.log (n + 1))) ^ 2 / (2 * k * σ2))) := by
    rw [← ofReal_measureReal]
    gcongr
    refine (HasSubgaussianMGF.measure_sum_range_le_le_of_iIndepFun (c := σ2) ?_ ?_ (by positivity))
    · exact (iIndepFun_eval_streamMeasure'' ν a).comp (fun i ω ↦ ω - (ν a)[id])
        (fun _ ↦ by fun_prop)
    · intro i him
      refine (hν a).congr_identDistrib ?_
      exact (identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _
  _ = 1 / (n + 1) ^ c := by
    rw [Real.sq_sqrt]
    swap; · exact mul_nonneg (by positivity) (Real.log_nonneg (by simp))
    field_simp
    rw [← Real.log_rpow (by positivity), ← Real.log_inv,
      Real.exp_log (by positivity), one_div, ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    norm_cast

omit [DecidableEq α] [StandardBorelSpace α] [Nonempty α] in
lemma prob_sum_ge_sqrt_log {σ2 : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a))
    (hσ2 : σ2 ≠ 0) {c : ℝ} (hc : 0 ≤ c) (a : α) (k : ℕ) (hk : k ≠ 0) :
    streamMeasure ν
        {ω | √(2 * c * k * σ2 * Real.log (n + 1)) ≤ (∑ s ∈ range k, (ω s a - (ν a)[id]))} ≤
      1 / (n + 1) ^ c := by
  calc
    streamMeasure ν
      {ω | √(2 * c * k * σ2 * Real.log (n + 1)) ≤ (∑ s ∈ range k, (ω s a - (ν a)[id]))}
  _ ≤ ENNReal.ofReal (Real.exp (-(√(2 * c * k * σ2 * Real.log (n + 1))) ^ 2 / (2 * k * σ2))) := by
    rw [← ofReal_measureReal]
    gcongr
    refine (HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun (c := σ2) ?_ ?_ (by positivity))
    · exact (iIndepFun_eval_streamMeasure'' ν a).comp (fun i ω ↦ ω - (ν a)[id])
        (fun _ ↦ by fun_prop)
    · intro i him
      refine (hν a).congr_identDistrib ?_
      exact (identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _
  _ = 1 / (n + 1) ^ c := by
    rw [Real.sq_sqrt]
    swap; · exact mul_nonneg (by positivity) (Real.log_nonneg (by simp))
    field_simp
    rw [← Real.log_rpow (by positivity), ← Real.log_inv,
      Real.exp_log (by positivity), one_div, ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    norm_cast

open Real

omit [DecidableEq α] [StandardBorelSpace α] [Nonempty α] in
lemma todo {σ2 : ℝ≥0} {c : ℝ}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0)
    (hc : 0 ≤ c) (a : α) (n k : ℕ) (hk : k ≠ 0) :
    streamMeasure ν {ω | (∑ m ∈ range k, ω m a) / k + √(2 * c * σ2 * log (n + 1) / k) ≤ (ν a)[id]} ≤
      1 / (n + 1) ^ c := by
  have h_log_nonneg : 0 ≤ log (n + 1) := log_nonneg (by simp)
  calc
    streamMeasure ν {ω | (∑ m ∈ range k, ω m a) / k + √(2 * c * σ2 * log (n + 1) / k) ≤ (ν a)[id]}
  _ = streamMeasure ν
      {ω | (∑ s ∈ range k, (ω s a - (ν a)[id])) / k ≤ - √(2 * c * σ2 * log (n + 1) / k)} := by
    congr with ω
    field_simp
    rw [Finset.sum_sub_distrib]
    simp
    grind
  _ = streamMeasure ν
      {ω | (∑ s ∈ range k, (ω s a - (ν a)[id])) ≤ - √(2 * c * k * σ2 * log (n + 1))} := by
    congr with ω
    field_simp
    congr! 2
    rw [sqrt_div (by positivity), ← mul_div_assoc, mul_comm, mul_div_assoc, div_sqrt,
      mul_assoc (k : ℝ), mul_assoc (k : ℝ), mul_assoc (k : ℝ),
      sqrt_mul (x := (k : ℝ)) (by positivity), mul_comm]
  _ ≤ 1 / (n + 1) ^ c := prob_sum_le_sqrt_log hν hσ2 hc a k hk

omit [DecidableEq α] [StandardBorelSpace α] [Nonempty α] in
lemma todo' {σ2 : ℝ≥0} {c : ℝ}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0)
    (hc : 0 ≤ c) (a : α) (n k : ℕ) (hk : k ≠ 0) :
    streamMeasure ν
        {ω | (ν a)[id] ≤ (∑ m ∈ range k, ω m a) / k - √(2 * c * σ2 *log (n + 1) / k)} ≤
      1 / (n + 1) ^ c := by
  have h_log_nonneg : 0 ≤ log (n + 1) := log_nonneg (by simp)
  calc
    streamMeasure ν {ω | (ν a)[id] ≤ (∑ m ∈ range k, ω m a) / k - √(2 * c * σ2 * log (n + 1) / k)}
  _ = streamMeasure ν
      {ω | √(2 * c * σ2 * log (n + 1) / k) ≤ (∑ s ∈ range k, (ω s a - (ν a)[id])) / k} := by
    congr with ω
    field_simp
    rw [Finset.sum_sub_distrib]
    simp
    grind
  _ = streamMeasure ν
      {ω | √(2 * c * k * σ2 * log (n + 1)) ≤ (∑ s ∈ range k, (ω s a - (ν a)[id]))} := by
    congr with ω
    field_simp
    congr! 1
    rw [sqrt_div (by positivity), ← mul_div_assoc, mul_comm, mul_div_assoc, div_sqrt,
      mul_comm _ (k : ℝ), sqrt_mul (x := (k : ℝ)) (by positivity), mul_comm]
  _ ≤ 1 / (n + 1) ^ c := prob_sum_ge_sqrt_log hν hσ2 hc a k hk

end Subgaussian

end Bandits
