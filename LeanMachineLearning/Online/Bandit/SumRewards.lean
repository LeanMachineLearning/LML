/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.Bandit.ArrayProbSpace
public import LeanMachineLearning.Online.Bandit.Regret
public import LeanMachineLearning.Probability.Moments.SubGaussian
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

/-! # Law of the sum of rewards
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning
open scoped ENNReal NNReal

namespace Bandits

namespace ArrayModel

lemma sum_Icc_one_eq_sum_range {m : ℕ} {f : ℕ → ℝ} :
    ∑ i ∈ Icc 1 m, f (i - 1) = ∑ i ∈ range m, f i := by
  have h : Icc 1 m = (range m).image (· + 1) := by
    ext x; simp only [mem_Icc, mem_image, mem_range]; constructor
    · intro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; omega
  rw [h, Finset.sum_image (fun _ _ _ _ h => by omega)]
  simp

variable {𝓐 : Type*} {m𝓐 : MeasurableSpace 𝓐} [DecidableEq 𝓐] [Countable 𝓐]
  [StandardBorelSpace 𝓐] [Nonempty 𝓐]
  {alg : Algorithm 𝓐 ℝ} {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]

local notation "A" => action alg
local notation "R" => reward alg
local notation "𝔓" => arrayMeasure ν

lemma identDistrib_pullCount_prod_sum_Icc_rewardByCount' (n : ℕ) :
    IdentDistrib (fun ω a ↦ (pullCount A a n ω.1,
        ∑ i ∈ Icc 1 (pullCount A a n ω.1), rewardByCount A R a i ω))
      (fun ω a ↦ (pullCount A a n ω, ∑ i ∈ Icc 1 (pullCount A a n ω), ω.2 (i - 1) a))
      ((𝔓).prod (streamMeasure ν)) 𝔓 where
  aemeasurable_fst := by
    refine Measurable.aemeasurable ?_
    rw [measurable_pi_iff]
    refine fun a ↦ Measurable.prod (by fun_prop) ?_
    exact measurable_sum_Icc_of_le (n := n) (pullCount_le _ _) (by fun_prop) (by fun_prop)
  aemeasurable_snd := by
    refine Measurable.aemeasurable ?_
    rw [measurable_pi_iff]
    refine fun a ↦ Measurable.prod (by fun_prop) ?_
    exact measurable_sum_Icc_of_le (n := n) (pullCount_le _ _) (by fun_prop) (by fun_prop)
  map_eq := by
    by_cases hn : n = 0
    · simp [hn]
    have h_eq (a : 𝓐) (i : ℕ) (ω : probSpace 𝓐 ℝ × (ℕ → 𝓐 → ℝ))
        (hi : i ∈ Icc 1 (pullCount A a n ω.1)) :
        rewardByCount A R a i ω = ω.1.2 (i - 1) a := by
      rw [rewardByCount_of_stepsUntil_ne_top]
      · simp only [reward_eq]
        have h_exists : ∃ s, pullCount A a (s + 1) ω.1 = i :=
          exists_pullCount_eq_of_le (n := n - 1) (by grind) (by grind)
        have h_action : A (stepsUntil A a i ω.1).toNat ω.1 = a :=
          action_stepsUntil («A» := A) (by grind) h_exists
        congr!
        rw [h_action, pullCount_stepsUntil (by grind) h_exists]
      · have : stepsUntil A a (pullCount A a (n + 1) ω.1) ω.1 ≠ ⊤ := by
          refine ne_top_of_le_ne_top ?_ (stepsUntil_pullCount_le _ _ _)
          simp
        refine ne_top_of_le_ne_top this ?_
        refine stepsUntil_mono a ω.1 (by grind) ?_
        simp only [mem_Icc] at hi
        refine hi.2.trans ?_
        exact pullCount_mono _ (by grind) _
    have h_sum_eq (a : 𝓐) (ω : probSpace 𝓐 ℝ × (ℕ → 𝓐 → ℝ)) :
        ∑ i ∈ Icc 1 (pullCount A a n ω.1), rewardByCount A R a i ω =
        ∑ i ∈ Icc 1 (pullCount A a n ω.1), ω.1.2 (i - 1) a :=
      Finset.sum_congr rfl fun i hi ↦ h_eq a i ω hi
    simp_rw [h_sum_eq]
    conv_rhs => rw [← Measure.fst_prod (μ := 𝔓) (ν := streamMeasure ν),
      Measure.fst]
    rw [AEMeasurable.map_map_of_aemeasurable _ (by fun_prop)]
    · rfl
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
    refine Measurable.aemeasurable ?_
    rw [measurable_pi_iff]
    refine fun a ↦ Measurable.prod (by fun_prop) ?_
    exact measurable_sum_Icc_of_le (n := n) (pullCount_le _ _) (by fun_prop) (by fun_prop)

lemma identDistrib_pullCount_prod_sum_Icc_rewardByCount (n : ℕ) :
    IdentDistrib (fun ω a ↦ (pullCount A a n ω.1,
        ∑ i ∈ Icc 1 (pullCount A a n ω.1), rewardByCount A R a i ω))
      (fun ω a ↦ (pullCount A a n ω, ∑ i ∈ range (pullCount A a n ω), ω.2 i a))
      ((𝔓).prod (streamMeasure ν)) 𝔓 := by
  convert identDistrib_pullCount_prod_sum_Icc_rewardByCount' n using 2 with ω
  rotate_left
  · infer_instance
  · infer_instance
  ext a : 1
  congr 1
  exact sum_Icc_one_eq_sum_range.symm

lemma identDistrib_pullCount_prod_sumRewards (n : ℕ) :
    IdentDistrib (fun ω a ↦ (pullCount A a n ω, sumRewards A R a n ω))
      (fun ω a ↦ (pullCount A a n ω, ∑ i ∈ range (pullCount A a n ω), ω.2 i a)) 𝔓 𝔓 := by
  suffices IdentDistrib (fun ω a ↦ (pullCount A a n ω.1, sumRewards A R a n ω.1))
      (fun ω a ↦ (pullCount A a n ω, ∑ i ∈ range (pullCount A a n ω), ω.2 i a))
      ((𝔓).prod (streamMeasure ν)) 𝔓 by
    -- todo: missing lemma about IdentDistrib?
    constructor
    · refine Measurable.aemeasurable ?_
      fun_prop
    · refine Measurable.aemeasurable ?_
      rw [measurable_pi_iff]
      refine fun a ↦ Measurable.prod (by fun_prop) ?_
      exact measurable_sum_range_of_le (n := n) (pullCount_le _ _) (by fun_prop) (by fun_prop)
    have h_eq := this.map_eq
    nth_rw 1 [← Measure.fst_prod (μ := 𝔓) (ν := streamMeasure ν), Measure.fst,
      Measure.map_map (by fun_prop) (by fun_prop)]
    exact h_eq
  simp_rw [← sum_rewardByCount_eq_sumRewards]
  exact identDistrib_pullCount_prod_sum_Icc_rewardByCount n

lemma identDistrib_pullCount_prod_sumRewards_arm (a : 𝓐) (n : ℕ) :
    IdentDistrib (fun ω ↦ (pullCount A a n ω, sumRewards A R a n ω))
      (fun ω ↦ (pullCount A a n ω, ∑ i ∈ range (pullCount A a n ω), ω.2 i a)) 𝔓 𝔓 := by
  have h1 : (fun ω ↦ (pullCount A a n ω, sumRewards A R a n ω)) =
    (fun p ↦ p a) ∘ (fun ω a ↦ (pullCount A a n ω, sumRewards A R a n ω)) := rfl
  have h2 : (fun ω ↦ (pullCount A a n ω, ∑ i ∈ range (pullCount A a n ω), ω.2 i a)) =
      (fun p ↦ p a) ∘
        (fun ω a ↦ (pullCount A a n ω, ∑ i ∈ range (pullCount A a n ω), ω.2 i a)) := rfl
  rw [h1, h2]
  refine (identDistrib_pullCount_prod_sumRewards n).comp ?_
  fun_prop

lemma identDistrib_pullCount_prod_sumRewards_two_arms (a b : 𝓐) (n : ℕ) :
    IdentDistrib (fun ω ↦ (pullCount A a n ω, pullCount A b n ω,
        sumRewards A R a n ω, sumRewards A R b n ω))
      (fun ω ↦ (pullCount A a n ω, pullCount A b n ω,
        ∑ i ∈ range (pullCount A a n ω), ω.2 i a,
        ∑ i ∈ range (pullCount A b n ω), ω.2 i b)) 𝔓 𝔓 := by
  have h_ident := identDistrib_pullCount_prod_sumRewards (ν := ν) (alg := alg) n
  exact h_ident.comp (u := fun p ↦ ((p a).1, (p b).1, (p a).2, (p b).2)) (by fun_prop)

lemma identDistrib_sumRewards (n : ℕ) :
    IdentDistrib (fun ω a ↦ sumRewards A R a n ω)
      (fun ω a ↦ ∑ i ∈ range (pullCount A a n ω), ω.2 i a) 𝔓 𝔓 := by
  have h_ident := identDistrib_pullCount_prod_sumRewards (ν := ν) (alg := alg) n
  exact h_ident.comp (u := fun p a ↦ (p a).2) (by fun_prop)

lemma identDistrib_sumRewards_arm (a : 𝓐) (n : ℕ) :
    IdentDistrib (sumRewards A R a n)
      (fun ω ↦ ∑ i ∈ range (pullCount A a n ω), ω.2 i a) 𝔓 𝔓 := by
  have h1 : sumRewards A R a n = (fun p ↦ p a) ∘ (fun ω a ↦ sumRewards A R a n ω) := rfl
  have h2 : (fun ω ↦ ∑ i ∈ range (pullCount A a n ω), ω.2 i a) =
      (fun p ↦ p a) ∘ (fun ω a ↦ ∑ i ∈ range (pullCount A a n ω), ω.2 i a) := rfl
  rw [h1, h2]
  refine (identDistrib_sumRewards n).comp ?_
  fun_prop

omit [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐] in
lemma identDistrib_sum_range_snd (a : 𝓐) (k : ℕ) :
    IdentDistrib (fun ω ↦ ∑ i ∈ range k, ω.2 i a) (fun ω ↦ ∑ i ∈ range k, ω i a)
      𝔓 (streamMeasure ν) where
  aemeasurable_fst := by fun_prop
  aemeasurable_snd := (measurable_sum _ fun i _ ↦ by fun_prop).aemeasurable
  map_eq := by
    rw [← Measure.snd_prod (μ := (Measure.infinitePi fun (_ : ℕ) ↦ (volume : Measure unitInterval)))
      (ν := streamMeasure ν), Measure.snd, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl

lemma prob_pullCount_prod_sumRewards_mem_le (a : 𝓐) (n : ℕ)
    {s : Set (ℕ × ℝ)} [DecidablePred (· ∈ Prod.fst '' s)] (hs : MeasurableSet s) :
    𝔓 {ω | (pullCount A a n ω, sumRewards A R a n ω) ∈ s} ≤
      ∑ k ∈ (range (n + 1)).filter (· ∈ Prod.fst '' s),
        streamMeasure ν {ω | ∑ i ∈ range k, ω i a ∈ Prod.mk k ⁻¹' s} := by
  have h_ident := identDistrib_pullCount_prod_sumRewards_arm a n (ν := ν) (alg := alg)
  have : 𝔓 {ω | (pullCount A a n ω, sumRewards A R a n ω) ∈ s} =
      (𝔓).map (fun ω ↦ (pullCount A a n ω, sumRewards A R a n ω)) s := by
    rw [Measure.map_apply (by fun_prop) hs]
    rfl
  rw [this, h_ident.map_eq, Measure.map_apply ?_ hs]
  swap
  · refine Measurable.prod (by fun_prop) ?_
    exact measurable_sum_range_of_le (n := n) (pullCount_le _ _) (by fun_prop) (by fun_prop)
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

lemma prob_pullCount_mem_and_sumRewards_mem_le (a : 𝓐) (n : ℕ)
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

lemma prob_sumRewards_le_sumRewards_le [Fintype 𝓐] (a : 𝓐) (n m₁ m₂ : ℕ) :
    (𝔓) {ω | pullCount A (bestArm ν) n ω = m₁ ∧ pullCount A a n ω = m₂ ∧
        sumRewards A R (bestArm ν) n ω ≤ sumRewards A R a n ω} ≤
      streamMeasure ν
        {ω | ∑ i ∈ range m₁, ω i (bestArm ν) ≤ ∑ i ∈ range m₂, ω i a} := by
  have h_ident := identDistrib_pullCount_prod_sumRewards_two_arms (bestArm ν) a n
    (ν := ν) (alg := alg)
  let s := {p : ℕ × ℕ × ℝ × ℝ | p.1 = m₁ ∧ p.2.1 = m₂ ∧ p.2.2.1 ≤ p.2.2.2}
  have hs : MeasurableSet s := by simp only [measurableSet_setOf, s]; fun_prop
  calc 𝔓 {ω | pullCount A (bestArm ν) n ω = m₁ ∧ pullCount A a n ω = m₂ ∧
      sumRewards A R (bestArm ν) n ω ≤ sumRewards A R a n ω}
  _ = 𝔓 ((fun ω ↦ (pullCount A (bestArm ν) n ω, pullCount A a n ω,
        sumRewards A R (bestArm ν) n ω, sumRewards A R a n ω)) ⁻¹'
        {p | p.1 = m₁ ∧ p.2.1 = m₂ ∧ p.2.2.1 ≤ p.2.2.2}) := rfl
  _ = 𝔓 ((fun ω ↦ (pullCount A (bestArm ν) n ω, pullCount A a n ω,
        ∑ i ∈ range (pullCount A (bestArm ν) n ω), ω.2 i (bestArm ν),
        ∑ i ∈ range (pullCount A a n ω), ω.2 i a)) ⁻¹'
        {p | p.1 = m₁ ∧ p.2.1 = m₂ ∧ p.2.2.1 ≤ p.2.2.2}) := by
      rw [← Measure.map_apply (by fun_prop) hs, h_ident.map_eq,
        Measure.map_apply _ hs]
      refine Measurable.prod (by fun_prop) (Measurable.prod (by fun_prop) ?_)
      refine Measurable.prod ?_ ?_
      · exact measurable_sum_range_of_le (n := n) (pullCount_le _ _) (by fun_prop) (by fun_prop)
      · exact measurable_sum_range_of_le (n := n) (pullCount_le _ _) (by fun_prop) (by fun_prop)
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

lemma probReal_sumRewards_le_sumRewards_le [Fintype 𝓐] (a : 𝓐) (n m₁ m₂ : ℕ) :
    (𝔓).real {ω | pullCount A (bestArm ν) n ω = m₁ ∧ pullCount A a n ω = m₂ ∧
        sumRewards A R (bestArm ν) n ω ≤ sumRewards A R a n ω} ≤
      (streamMeasure ν).real
        {ω | ∑ i ∈ range m₁, ω i (bestArm ν) ≤ ∑ i ∈ range m₂, ω i a} := by
  simp_rw [measureReal_def]
  gcongr
  · finiteness
  · exact prob_sumRewards_le_sumRewards_le a n m₁ m₂

end ArrayModel

variable {𝓐 Ω Ω' : Type*} [DecidableEq 𝓐] {m𝓐 : MeasurableSpace 𝓐} {mΩ : MeasurableSpace Ω}
  {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {alg : Algorithm 𝓐 ℝ} {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {A : ℕ → Ω → 𝓐} {R : ℕ → Ω → ℝ} {A₂ : ℕ → Ω' → 𝓐} {R₂ : ℕ → Ω' → ℝ}
  {ω : Ω} {m n t : ℕ} {a : 𝓐}

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

variable [StandardBorelSpace 𝓐] [Nonempty 𝓐]

-- todo: write those lemmas with IdentDistrib instead of equality of maps
lemma _root_.Learning.IsAlgEnvSeq.law_sumRewards_unique
    (h1 : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (h2 : IsAlgEnvSeq A₂ R₂ alg (stationaryEnv ν) P') :
    P.map (sumRewards A R a n) = P'.map (sumRewards A₂ R₂ a n) := by
  have hA := h1.measurable_action
  have hR := h1.measurable_feedback
  have hA2 := h2.measurable_action
  have hR2 := h2.measurable_feedback
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
  have hA := h1.measurable_action
  have hR := h1.measurable_feedback
  have hA2 := h2.measurable_action
  have hR2 := h2.measurable_feedback
  constructor
  · refine Measurable.aemeasurable ?_
    rw [measurable_pi_iff]
    exact fun a ↦ Measurable.prod (by fun_prop) (measurable_sumRewards hA hR _ _)
  · refine Measurable.aemeasurable ?_
    rw [measurable_pi_iff]
    exact fun a ↦ Measurable.prod (by fun_prop) (measurable_sumRewards hA2 hR2 _ _)
  have h_unique := isAlgEnvSeq_unique h1 h2
  let f := fun (p : ℕ → 𝓐 × ℝ ) (a : 𝓐) ↦ (∑ i ∈ range n, if (p i).1 = a then 1 else 0,
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

-- this is what we will use for UCB
lemma prob_pullCount_prod_sumRewards_mem_le [Countable 𝓐]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {s : Set (ℕ × ℝ)} [DecidablePred (· ∈ Prod.fst '' s)] (hs : MeasurableSet s) :
    P {ω | (pullCount A a n ω, sumRewards A R a n ω) ∈ s} ≤
      ∑ k ∈ (range (n + 1)).filter (· ∈ Prod.fst '' s),
        streamMeasure ν {ω | ∑ i ∈ range k, ω i a ∈ Prod.mk k ⁻¹' s} := by
  have hA := h.measurable_action
  have hR := h.measurable_feedback
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

lemma prob_pullCount_mem_and_sumRewards_mem_le [Countable 𝓐]
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

lemma prob_sumRewards_mem_le [Countable 𝓐] (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {B : Set ℝ} (hB : MeasurableSet B) :
    P (sumRewards A R a n ⁻¹' B) ≤
      ∑ k ∈ range (n + 1), streamMeasure ν {ω | ∑ i ∈ range k, ω i a ∈ B} := by
  classical
  have h_le := prob_pullCount_mem_and_sumRewards_mem_le h .univ hB (a := a) (n := n)
  simpa using h_le

lemma prob_pullCount_eq_and_sumRewards_mem_le [Countable 𝓐]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {m : ℕ} (hm : m ≤ n) {B : Set ℝ} (hB : MeasurableSet B) :
    P {ω | pullCount A a n ω = m ∧ sumRewards A R a n ω ∈ B} ≤
      streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B} := by
  have h_le := prob_pullCount_mem_and_sumRewards_mem_le h (s := {m}) (by simp) hB (a := a) (n := n)
  have hm' : m < n + 1 := by lia
  simpa [hm'] using h_le

lemma probReal_sumRewards_le_sumRewards_le [Fintype 𝓐] (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (a : 𝓐) (n m₁ m₂ : ℕ) :
    P.real {ω | pullCount A (bestArm ν) n ω = m₁ ∧ pullCount A a n ω = m₂ ∧
        sumRewards A R (bestArm ν) n ω ≤ sumRewards A R a n ω} ≤
      (streamMeasure ν).real
        {ω | ∑ i ∈ range m₁, ω i (bestArm ν) ≤ ∑ i ∈ range m₂, ω i a} := by
  have hA := h.measurable_action
  have hR := h.measurable_feedback
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

omit [DecidableEq 𝓐] [StandardBorelSpace 𝓐] in
lemma probReal_sum_le_sum_streamMeasure [Fintype 𝓐] {c : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) c (ν a)) (a : 𝓐) (m : ℕ) :
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

omit [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐] in
lemma prob_sum_le_sqrt_log {σ2 : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a))
    (hσ2 : σ2 ≠ 0) {c : ℝ} (hc : 0 ≤ c) (a : 𝓐) (k : ℕ) (hk : k ≠ 0) :
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

omit [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐] in
lemma prob_sum_ge_sqrt_log {σ2 : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a))
    (hσ2 : σ2 ≠ 0) {c : ℝ} (hc : 0 ≤ c) (a : 𝓐) (k : ℕ) (hk : k ≠ 0) :
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

omit [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐] in
lemma todo {σ2 : ℝ≥0} {c : ℝ}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0)
    (hc : 0 ≤ c) (a : 𝓐) (n k : ℕ) (hk : k ≠ 0) :
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

omit [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐] in
lemma todo' {σ2 : ℝ≥0} {c : ℝ}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0)
    (hc : 0 ≤ c) (a : 𝓐) (n k : ℕ) (hk : k ≠ 0) :
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
