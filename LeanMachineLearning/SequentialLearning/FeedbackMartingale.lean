/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.ActionIndicator
public import LeanMachineLearning.SequentialLearning.Means

/-!
# Martingale decomposition of the sum of rewards

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning

open scoped ENNReal

namespace Learning

variable {Ω 𝓞 𝓐 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓞 : MeasurableSpace 𝓞}
  {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  [NormedAddCommGroup 𝓨] [NormedSpace ℝ 𝓨]
  {P : Measure Ω} [IsFiniteMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}

/-- The sum of noise terms for action `k`.
This is the martingale part of `sumRewards A Y k` for the filtration
`IsAlgEnvSeq.filtrationAction`. -/
noncomputable
def noiseSum (env : Environment 𝓞 𝓐 𝓨) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (k : 𝓐) (n : ℕ) (ω : Ω) : 𝓨 :=
  ∑ m ∈ range n, {ω | A m ω = k}.indicator (fun ω ↦ Y m ω - env.means O A Y (A m ω) m ω) ω

/-- The sum of mean terms for action `k`.
This is the predictable part of `sumRewards A Y k` for the filtration
`IsAlgEnvSeq.filtrationAction`. -/
noncomputable
def meanSum (env : Environment 𝓞 𝓐 𝓨) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (k : 𝓐) (n : ℕ) (ω : Ω) : 𝓨 :=
  ∑ m ∈ range n, {ω | A m ω = k}.indicator (fun ω ↦ env.means O A Y (A m ω) m ω) ω

lemma noiseSum_add_meanSum' (k : 𝓐) (n : ℕ) (ω : Ω) :
    noiseSum env O A Y k n ω + meanSum env O A Y k n ω =
      ∑ m ∈ range n, {ω | A m ω = k}.indicator (Y m) ω := by
  simp only [noiseSum, meanSum, ← sum_add_distrib]
  congr with m
  by_cases h : A m ω = k <;> simp [h]

lemma noiseSum_add_meanSum [DecidableEq 𝓐] (k : 𝓐) (n : ℕ) (ω : Ω) :
    noiseSum env O A Y k n ω + meanSum env O A Y k n ω = sumRewards A Y k n ω := by
  unfold sumRewards
  rw [noiseSum_add_meanSum' k n ω]
  congr with m
  by_cases h : A m ω = k <;> simp [h]

@[simp]
lemma noiseSum_zero (k : 𝓐) : noiseSum env O A Y k 0 = fun _ ↦ 0 := by unfold noiseSum; simp

@[simp]
lemma meanSum_zero (k : 𝓐) : meanSum env O A Y k 0 = fun _ ↦ 0 := by unfold meanSum; simp

lemma noiseSum_succ (k : 𝓐) (n : ℕ) :
    noiseSum env O A Y k (n + 1) = noiseSum env O A Y k n +
      {ω | A n ω = k}.indicator (fun ω ↦ Y n ω - env.means O A Y (A n ω) n ω) := by
  ext ω
  simp [noiseSum, Finset.sum_range_succ]

lemma noiseSum_succ_sub (k : 𝓐) (n : ℕ) (ω : Ω) :
    noiseSum env O A Y k (n + 1) ω - noiseSum env O A Y k n ω
      = {ω | A n ω = k}.indicator (fun ω ↦ Y n ω - env.means O A Y (A n ω) n ω) ω := by
  simp [noiseSum_succ]

lemma meanSum_succ (k : 𝓐) (n : ℕ) :
    meanSum env O A Y k (n + 1) = meanSum env O A Y k n +
      {ω | A n ω = k}.indicator (fun ω ↦ env.means O A Y (A n ω) n ω) := by
  ext ω
  simp [meanSum, Finset.sum_range_succ]

lemma meanSum_succ_sub (k : 𝓐) (n : ℕ) (ω : Ω) :
    meanSum env O A Y k (n + 1) ω - meanSum env O A Y k n ω
      = {ω | A n ω = k}.indicator (fun ω ↦ env.means O A Y (A n ω) n ω) ω := by
  simp [meanSum_succ]

variable [MeasurableSingletonClass 𝓐] [SecondCountableTopology 𝓨]

@[fun_prop]
lemma IsAlgEnvSeq.integrable_noiseSum_increment [OpensMeasurableSpace 𝓨]
    {m : ℕ} (h : IsAlgEnvSeq O A Y alg env P) (hint : Integrable (Y m) P) (k : 𝓐) :
    Integrable (fun ω ↦ {ω | A m ω = k}.indicator
      (fun ω ↦ Y m ω - env.means O A Y (A m ω) m ω) ω) P := by
  exact (hint.sub (h.integrable_means_action hint)).indicator
    (h.measurable_action _ (measurableSet_singleton k))

@[fun_prop]
lemma IsAlgEnvSeq.integrable_meanSum_increment [OpensMeasurableSpace 𝓨]
    {m : ℕ} (h : IsAlgEnvSeq O A Y alg env P) (hint : Integrable (Y m) P) (k : 𝓐) :
    Integrable (fun ω ↦ {ω | A m ω = k}.indicator (fun ω ↦ env.means O A Y (A m ω) m ω) ω) P := by
  exact (h.integrable_means_action hint).indicator
    (h.measurable_action _ (measurableSet_singleton k))

@[fun_prop]
lemma IsAlgEnvSeq.integrable_noiseSum [OpensMeasurableSpace 𝓨]
    (h : IsAlgEnvSeq O A Y alg env P) (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) (n : ℕ) :
    Integrable (noiseSum env O A Y k n) P :=
  integrable_finsetSum _ fun m _ ↦ h.integrable_noiseSum_increment (hint m) k

@[fun_prop]
lemma IsAlgEnvSeq.integrable_meanSum [OpensMeasurableSpace 𝓨]
    (h : IsAlgEnvSeq O A Y alg env P) (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) (n : ℕ) :
    Integrable (meanSum env O A Y k n) P :=
  integrable_finsetSum _ fun m _ ↦ h.integrable_meanSum_increment (hint m) k

lemma IsAlgEnvSeq.memLp_noiseSum_increment [BorelSpace 𝓨]
    {m : ℕ} (k : 𝓐) (h : IsAlgEnvSeq O A Y alg env P) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ∞)
    (hY : MemLp (Y m) p P) :
    MemLp ({ω | A m ω = k}.indicator (fun ω ↦ Y m ω - env.means O A Y (A m ω) m ω)) p P := by
  refine (hY.sub ?_).indicator (h.measurable_action _ (measurableSet_singleton k))
  exact h.memLp_means_action hp1 hp_top hY

lemma IsAlgEnvSeq.memLp_meanSum_increment [BorelSpace 𝓨]
    {m : ℕ} (k : 𝓐) (h : IsAlgEnvSeq O A Y alg env P) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ∞)
    (hY : MemLp (Y m) p P) :
    MemLp ({ω | A m ω = k}.indicator (fun ω ↦ env.means O A Y (A m ω) m ω)) p P := by
  exact (h.memLp_means_action hp1 hp_top hY).indicator
    (h.measurable_action _ (measurableSet_singleton k))

lemma IsAlgEnvSeq.memLp_noiseSum [BorelSpace 𝓨]
    (h : IsAlgEnvSeq O A Y alg env P) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ∞)
    (hY : ∀ n, MemLp (Y n) p P) (k : 𝓐) (n : ℕ) :
    MemLp (noiseSum env O A Y k n) p P :=
  memLp_finsetSum _ fun m _ ↦ memLp_noiseSum_increment k h hp1 hp_top (hY m)

lemma IsAlgEnvSeq.memLp_meanSum [BorelSpace 𝓨]
    (h : IsAlgEnvSeq O A Y alg env P) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ∞)
    (hY : ∀ n, MemLp (Y n) p P) (k : 𝓐) (n : ℕ) :
    MemLp (meanSum env O A Y k n) p P :=
  memLp_finsetSum _ fun m _ ↦ memLp_meanSum_increment k h hp1 hp_top (hY m)

section Martingale

variable [BorelSpace 𝓨]

lemma IsAlgEnvSeq.adapted_noiseSum (h : IsAlgEnvSeq O A Y alg env P) (k : 𝓐) :
    Adapted h.filtrationAction (noiseSum env O A Y k) := by
  refine fun n ↦ Finset.measurable_fun_sum _ fun m hm ↦ ?_
  have hAm : Measurable[h.filtrationAction n] (A m) :=
    h.adapted_action_filtrationAction.measurable_le (by grind)
  have hYm : Measurable[h.filtrationAction n] (Y m) :=
    h.measurable_feedback_filtrationAction_of_lt (by grind)
  refine (hYm.sub ?_).indicator (hAm (measurableSet_singleton k))
  exact h.adapted_means_filtrationAction.measurable_le (by grind)

lemma IsAlgEnvSeq.stronglyAdapted_noiseSum (h : IsAlgEnvSeq O A Y alg env P) (k : 𝓐) :
    StronglyAdapted h.filtrationAction (noiseSum env O A Y k) :=
  (adapted_noiseSum h k).stronglyAdapted

lemma IsAlgEnvSeq.isStronglyPredictable_meanSum (h : IsAlgEnvSeq O A Y alg env P) (k : 𝓐) :
    IsStronglyPredictable h.filtrationAction (meanSum env O A Y k) := by
  refine .of_measurable_add_one ?_ fun n ↦ ?_
  · simp only [meanSum_zero]
    fun_prop
  · refine Finset.stronglyMeasurable_fun_sum _ fun m hm ↦ ?_
    have hAm : Measurable[h.filtrationAction n] (A m) :=
      h.adapted_action_filtrationAction.measurable_le (by grind)
    refine StronglyMeasurable.indicator ?_ (hAm (measurableSet_singleton k))
    exact (h.stronglyAdapted_means_filtrationAction m).mono (h.filtrationAction.mono (by grind))

lemma IsAlgEnvSeq.condExp_noiseSum_increment [CompleteSpace 𝓨]
    (h : IsAlgEnvSeq O A Y alg env P) (k : 𝓐) (i : ℕ) (hint : Integrable (Y i) P) :
    P[{ω | A i ω = k}.indicator (fun ω ↦ Y i ω - env.means O A Y (A i ω) i ω)
        | h.filtrationAction i] =ᵐ[P] 0 := by
  let c : Ω → ℝ := actionIndicator A k i
  let g : Ω → 𝓨 := fun ω ↦ Y i ω - env.means O A Y (A i ω) i ω
  have h_smul : c • g
      = {ω | A i ω = k}.indicator (fun ω ↦ Y i ω - env.means O A Y (A i ω) i ω) := by
    ext ω
    by_cases hω : A i ω = k <;> simp [c, g, actionIndicator, hω]
  have hAG : Measurable[h.filtrationAction i] (A i) := h.adapted_action_filtrationAction i
  have hcG : StronglyMeasurable[h.filtrationAction i] c :=
    (h.adapted_actionIndicator_filtrationAction k i).stronglyMeasurable
  have hgint : Integrable g P := hint.sub (h.integrable_means_action hint)
  have hcint : Integrable (c • g) P := by
    rw [h_smul]
    exact integrable_noiseSum_increment h hint k
  have hcondg : P[g | h.filtrationAction i] =ᵐ[P] 0 := by
    refine (condExp_sub hint (h.integrable_means_action hint) _).trans ?_
    have h1 := h.condExp_feedback i hint
    grw [h1]
    rw [condExp_of_stronglyMeasurable]
    · simp
    · exact h.adapted_means_filtrationAction.stronglyAdapted i
    · exact h.integrable_means_action hint
  have hpull := condExp_smul_of_aestronglyMeasurable_left hcG.aestronglyMeasurable hcint hgint
  filter_upwards [hpull, hcondg] with ω hp hcg
  rw [← h_smul, hp]
  simp only [Pi.smul_apply', hcg, Pi.ofNat_apply, smul_eq_zero]
  rcases eq_or_ne (A i ω) k with hak | hak
  · simp
  · simp [c, actionIndicator, hak]

lemma IsAlgEnvSeq.martingale_noiseSum [CompleteSpace 𝓨]
    (h : IsAlgEnvSeq O A Y alg env P) (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) :
    Martingale (noiseSum env O A Y k) h.filtrationAction P := by
  have hInt : ∀ n, Integrable (noiseSum env O A Y k n) P := h.integrable_noiseSum (hint) k
  refine martingale_nat (h.stronglyAdapted_noiseSum k) hInt fun i ↦ ?_
  rw [noiseSum_succ]
  symm
  have hadd := condExp_add (hInt i)
    (integrable_noiseSum_increment h (hint i) k) (h.filtrationAction i)
  have hself : P[noiseSum env O A Y k i | h.filtrationAction i] = noiseSum env O A Y k i :=
    condExp_of_stronglyMeasurable (h.filtrationAction.le i)
      (h.stronglyAdapted_noiseSum k i) (hInt i)
  have hincr := condExp_noiseSum_increment h k i (hint i)
  filter_upwards [hadd, hincr] with ω ha hin
  rw [ha, Pi.add_apply, congrFun hself ω]
  simp only [add_eq_left]
  rw [hin, Pi.zero_apply]

end Martingale

end Learning
