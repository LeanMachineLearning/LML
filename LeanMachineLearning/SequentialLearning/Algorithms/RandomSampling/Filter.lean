
/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib
public import LeanMachineLearning.SequentialLearning.Algorithms.RandomSampling.Basic
public import LeanMachineLearning.SequentialLearning.EvaluationEnv
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.ForMathlib.Order.Interval.Finset
public import LeanMachineLearning.ForMathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Random Sampling convergence lemmas

This file contains several convergence lemmas for the `randomSampling` algorithm along with an
`evalEnv` environment, that evaluates the actions using a measurable function.

## Main statements

* `hasLaw_rewards`: Each reward follows the distribution μ.map f.
* `iIndep_rewards`: Rewards are mutually independent across time steps.
* `actions_tendsto_any`: The minimum distance from sampled actions to any point in α tends to zero
  in measure.
* `rewards_tendsto_any`: The minimum distance from rewards to any value of `f` tends to zero in
  measure.
* `tendsto_min`: The minimum reward converges in measure to the global minimum value.
* `tendsto_max`: The maximum reward converges in measure to the global maximum value.
-/

@[expose] public section

open Learning MeasureTheory ProbabilityTheory Filter Finset ENNReal

open scoped Topology

namespace Learning.randomSampling

variable {𝓐 𝓨 Ω : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {mΩ : MeasurableSpace Ω} {μ : Measure 𝓐} [IsProbabilityMeasure μ] {P : Measure Ω}
  [IsProbabilityMeasure P] {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {env : Environment 𝓐 𝓨}
  {f : 𝓐 → 𝓨} {hf : Measurable f}

section rewards

variable [StandardBorelSpace 𝓨] [Nonempty 𝓨]

/-- Each reward follows the distribution μ.map f. -/
lemma hasLaw_rewards (h : IsAlgEnvSeq A Y (randomSampling μ) (evalEnv f hf) P) (n : ℕ) :
    HasLaw (Y n) (μ.map f) P := by
  refine HasLaw.congr ?_ (feedback_evalEnv_ae_eq_eval_action h n)
  have hA := h.measurable_action n
  refine ⟨by fun_prop, ?_⟩
  rw [← Measure.map_map hf hA, (hasLaw_action h n).map_eq]

/-- Rewards are mutually independent. -/
lemma iIndep_rewards (h : IsAlgEnvSeq A Y (randomSampling μ) (evalEnv f hf) P) :
    iIndepFun Y P :=
  have (n : ℕ) : f ∘ A n =ᵐ[P] Y n :=
    (feedback_evalEnv_ae_eq_eval_action h n).symm
  iIndepFun.congr this <| (iIndep_action h).comp _ (fun _ ↦ hf)

end rewards

variable [PseudoMetricSpace 𝓐] [SecondCountableTopology 𝓐] [OpensMeasurableSpace 𝓐]
  [μ.IsOpenPosMeasure]

/-- The minimum distance from sampled actions to any point tends to zero. -/
theorem actions_tendsto_any (h : IsAlgEnvSeq A Y (randomSampling μ) (evalEnv f hf) P) (a : 𝓐) :
    ∀ ε, 0 < ε → Tendsto (fun i => P
      {x | ε ≤ (fun (j : Iic i) ↦ dist (A j.1 x) a).min}) atTop (𝓝 0) := by
  set randomSampling_alg := randomSampling (𝓨 := 𝓨) μ
  intro ε hε
  refine tendsto_zero_le (g := fun n ↦ P (⋂ i ∈ Iic n, {x | ε ≤ dist (A i x) a})) ?_ ?_
  · have inter_prod (n : ℕ) : P (⋂ j ∈ Iic n, {x | ε ≤ dist (A j x) a}) =
        ∏ j ∈ Iic n, P {x | ε ≤ dist (A j x) a} := by
      refine iIndepSet.meas_biInter ?_ _
      rw [iIndepSet_iff_meas_biInter fun i ↦ ?_]
      · intro s
        have iIndep_actions := randomSampling.iIndep_action h
        rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at iIndep_actions
        have meas_dist : ∀ i ∈ s, MeasurableSet {x | ε ≤ dist x a} := by
          intro i hs
          measurability
        specialize iIndep_actions s meas_dist
        simpa [Set.preimage] using iIndep_actions
      · have hAi := h.measurable_action i
        measurability
    simp_rw [inter_prod]
    have prod_law (n : ℕ) : ∏ j ∈ Iic n, P {x | ε ≤ dist (A j x) a} =
        ∏ j ∈ Iic n, μ {x | ε ≤ dist x a} := by
      refine prod_congr rfl fun j hj ↦ ?_
      have hlaw (n : ℕ) : HasLaw (A n) μ P := randomSampling.hasLaw_action h n
      rw [← (hlaw j).map_eq, P.map_apply]
      · simp
      · exact h.measurable_action j
      · measurability
    simp_rw [prod_law]
    simp only [prod_const, Nat.card_Iic]
    refine tendsto_pow_atTop_nhds_zero_of_lt_one ?_ |> Tendsto.comp <| tendsto_add_atTop_nat 1
    have compl : {x | ε ≤ dist x a} = {x | dist x a < ε}ᶜ := by
      ext a
      simp
    rw [compl, measure_compl (by measurability) (by simp), measure_univ]
    refine ENNReal.sub_lt_self (by simp) (by simp) ?_
    exact (Metric.measure_ball_pos μ a hε).ne'
  · intro n
    refine measure_mono ?_
    simp only [mem_Iic, Set.subset_iInter_iff, Set.setOf_subset_setOf]
    intro i hi ω (hω : ε ≤ (fun (j : Iic n) ↦ dist (A j.1 ω) a).min)
    simp_all only [univ_eq_attach, le_inf'_iff, mem_attach, forall_const, Subtype.forall, mem_Iic]

variable [PseudoMetricSpace 𝓨] [BorelSpace 𝓨] (hfc : Continuous f)

/-- The minimum distance from image of actions to any function value tends to zero. -/
lemma image_actions_tendsto_any
    (h : IsAlgEnvSeq A Y (randomSampling μ) (evalEnv f hfc.measurable) P)
    (a : 𝓐) : ∀ ε, 0 < ε → Tendsto (fun i => P
      {x | ε ≤ (fun (j : Iic i) ↦ dist (f (A j.1 x)) (f a)).min}) atTop (𝓝 0) := by
  intro ε hε
  have hf := hfc.measurable
  rw [Metric.continuous_iff] at hfc
  obtain ⟨δ, hδ, hfc⟩ := hfc a ε hε
  refine actions_tendsto_any h a δ hδ |> tendsto_zero_le <| ?_
  intro n
  refine measure_mono ?_
  simp only [Set.setOf_subset_setOf]
  intro ω hω
  rw [← argmin_spec]
  set j := argmin (fun (i : Iic n) ↦ dist (A i.1 ω) a)
  by_contra! h_contra
  specialize hfc (A j.1 ω) h_contra
  have := (fun (j : Iic n) ↦ dist (f (A (j) ω)) (f a)).min_le j
  linarith

variable [StandardBorelSpace 𝓨] [Nonempty 𝓨]

/-- The minimum distance from rewards to any function value tends to zero. -/
lemma rewards_tendsto_any (h : IsAlgEnvSeq A Y (randomSampling μ) (evalEnv f hfc.measurable) P)
    (a : 𝓐) : ∀ ε, 0 < ε → Tendsto (fun i => P
      {x | ε ≤ (fun (j : Iic i) ↦ dist (Y j.1 x) (f a)).min}) atTop (𝓝 0) := by
  intro ε hε
  convert image_actions_tendsto_any hfc h a ε hε using 2 with n
  refine measure_congr ?_
  let g : ((Iic n) → 𝓨) → ℝ := fun r ↦ (fun i ↦ dist (r i) (f a)).min
  filter_upwards [feedback_evalEnv_ae_eq_eval_action_comp h g] with ω hω
  simp only [eq_iff_iff]
  change ε ≤ (fun (j : Iic n) ↦ dist (Y j ω) (f a)).min ↔
    ε ≤ (fun (j : Iic n) ↦ dist (f (A j ω)) (f a)).min
  simp [g, hω]

variable {R : ℕ → Ω → ℝ} {f : 𝓐 → ℝ} (hfc : Continuous f) {a : 𝓐}

/-- The minimum image action converges to the function's global minimum. -/
lemma tendsto_min₀ (h : IsAlgEnvSeq A R (randomSampling μ) (evalEnv f hfc.measurable) P)
    (hf_min : ∀ x, f a ≤ f x) : TendstoInMeasure P (fun n ω ↦
      (fun (i : Iic n) ↦ f (A i.1 ω)).min) atTop (fun _ ↦ f a) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine image_actions_tendsto_any hfc h a ε hε |> tendsto_zero_le <| ?_
  intro n
  refine measure_mono ?_
  simp only [Set.setOf_subset_setOf]
  intro ω hω
  rw [← argmin_spec]
  set j := argmin (fun (i : Iic n) ↦ dist (f (A i ω)) (f a))
  refine hω.trans ?_
  rw [← argmin_spec]
  set k := argmin (fun (i : Iic n) ↦ f (A i ω))
  have := hf_min (A k ω)
  have : f (A k ω) ≤ f (A j ω) := isMinOn_argmin (fun (i : Iic n) ↦ f (A i ω)) j
  simp [Real.dist_eq]
  grind

/-- The minimum reward converges to the function's global minimum. -/
lemma tendsto_min (h : IsAlgEnvSeq A R (randomSampling μ) (evalEnv f hfc.measurable) P)
    (hf_min : ∀ x, f a ≤ f x) : TendstoInMeasure P (fun n ω ↦
      (fun (i : Iic n) ↦ R i.1 ω).min) atTop (fun _ ↦ f a) := by
  refine TendstoInMeasure.congr_left (fun n ↦ ?_) <| tendsto_min₀ hfc h hf_min
  filter_upwards [feedback_evalEnv_ae_eq_eval_action_comp h Function.min] with ω hω
  rw [← hω]

/-- The maximum image action converges to the function's global maximum. -/
lemma tendsto_max₀ (h : IsAlgEnvSeq A R (randomSampling μ) (evalEnv f hfc.measurable) P)
    (hf_max : ∀ x, f x ≤ f a) : TendstoInMeasure P (fun n ω ↦
      (fun (i : Iic n) ↦ f (A i.1 ω)).max) atTop (fun _ ↦ f a) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine image_actions_tendsto_any hfc h a ε hε |> tendsto_zero_le <| ?_
  intro n
  refine measure_mono ?_
  simp only [Set.setOf_subset_setOf]
  intro ω hω
  rw [← argmin_spec]
  set j := argmin (fun (i : Iic n) ↦ dist (f (A i ω)) (f a))
  refine hω.trans ?_
  rw [← argmax_spec]
  set k := argmax (fun (i : Iic n) ↦ f (A i ω))
  have := hf_max (A k ω)
  have : f (A j ω) ≤ f (A k ω) :=
    isMaxOn_argmax (fun (i : Iic n) ↦ f (A i ω)) j
  simp [Real.dist_eq]
  grind

/-- The maximum reward converges to the function's global maximum. -/
lemma tendsto_max (h : IsAlgEnvSeq A R (randomSampling μ) (evalEnv f hfc.measurable) P)
    (hf_max : ∀ x, f x ≤ f a) :
    TendstoInMeasure P (fun n ω ↦ (fun (i : Iic n) ↦ R i.1 ω).max) atTop (fun _ ↦ f a) := by
  refine TendstoInMeasure.congr_left (fun n ↦ ?_) <| tendsto_max₀ hfc h hf_max
  filter_upwards [feedback_evalEnv_ae_eq_eval_action_comp h Function.max] with ω hω
  rw [← hω]

end Learning.randomSampling
