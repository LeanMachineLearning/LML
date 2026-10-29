/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber, Rémy Degenne
-/
module

public import LeanMachineLearning.Online.Bandit.Algorithms.TS
public import LeanMachineLearning.Online.Bandit.Concentration

/-!
# Bayesian regret of Thompson sampling

This file provides a Bayesian regret upper bound (`integral_regret_le`) for Thompson sampling under
the assumption (among others) that it has the correct prior over environments.

The Bayesian regret upper bound relies on a clipped upper confidence bound whose definition
and properties are also given in this file.

## Main definitions

* `ucb A R l u σ2 δ a n` : clipped upper confidence bound used in the regret analysis of Thompson
  sampling for a sequence of actions `A : ℕ → Ω → Fin K`, rewards `R : ℕ → Ω → ℝ`, reward lower
  bound `l : ℝ`, reward upper bound `u : ℝ`, sub-Gaussian variance proxy `σ2 : ℝ≥0`, confidence
  parameter `δ : ℝ`, action `a : Fin K`, and time `n : ℕ`.
* `ucb' n h l u σ2 δ a`: clipped upper confidence bound for action `a : Fin K` at time `n : ℕ` given
  the history `h : Hist Unit (Fin K) ℝ n` (rather than the entire sequences of actions and
  rewards).

## Main statements

* `IsBayesAlgEnvSeq.prob_empMean_sub_actionMean_ge_le`,
  `IsBayesAlgEnvSeq.prob_empMean_bestAction_sub_actionMean_le_le`: for sub-Gaussian rewards, the
  empirical means of the actions are close to their means with high probability, uniformly in
  time.
* `TS.integral_regret_le`: if Thompson sampling has the correct prior over environments, in every
  environment each of the `K` actions has a mean reward between `l` and `u`, and in almost every
  environment (under the prior) the reward distribution of each action is sub-Gaussian with
  variance proxy `σ2` after its mean is subtracted, then the Bayesian regret at time `n` is at most
  `(2 * K + 1) * (u - l) + 8 * √(σ2 * K * n * log n)`.

## Implementation notes

The proof follows the upper confidence bound argument of Russo and Van Roy. Since the action played
and the best action have the same conditional law given the history, the upper confidence bounds
of the two actions have the same expectation, and the Bayesian regret is the sum of the expected
differences between the mean of the best action and its upper confidence bound, and between the
upper confidence bound and the mean of the action played (`TS.integral_regret_eq_add`). The first
sum is controlled by concentration, the second one by the widths of the confidence intervals.

## References

* D. Russo and B. Van Roy, *Learning to optimize via posterior sampling*, Mathematics of
  Operations Research, 2014.
* T. Lattimore and C. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Theorem 36.1.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning
open scoped NNReal

/-! ### Concentration of the empirical means in a Bayesian bandit -/

namespace Learning.IsBayesAlgEnvSeq

variable {𝓔 Ω : Type*} [MeasurableSpace 𝓔] [MeasurableSpace Ω]
variable {K : ℕ} [Nonempty (Fin K)]
variable {Q : Measure 𝓔} [IsProbabilityMeasure Q] {κ : Kernel (𝓔 × Fin K) ℝ} [IsMarkovKernel κ]
variable {alg : Algorithm Unit (Fin K) ℝ}
variable {E : Ω → 𝓔} {A : ℕ → Ω → (Fin K)} {R : ℕ → Ω → ℝ}
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Auxiliary lemma for `prob_empMean_sub_actionMean_ge_le`. -/
private lemma sqrt_two_mul_le_sub {k : ℕ} (hk : k ≠ 0) {s μ σ l : ℝ}
    (h : √(2 * σ * l / k) ≤ s / k - μ) : √(2 * k * σ * l) ≤ s - k * μ := by
  have hkp : (0 : ℝ) < k := by positivity
  calc √(2 * k * σ * l)
    _ = √(2 * σ * l / k * k ^ 2) := by
      field_simp
    _ = √(2 * σ * l / k) * k := by
      rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hkp.le]
    _ ≤ (s / k - μ) * k := by
      nlinarith
    _ = s - k * μ := by
      field_simp

lemma prob_empMean_sub_actionMean_ge_le (h : IsBayesAlgEnvSeq Q κ alg E A R P) {σ2 : ℝ≥0}
    (hs : ∀ᵐ e ∂Q, ∀ a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    (hσ2 : σ2 ≠ 0) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    P {ω | ∃ t < n, ∃ a, pullCount A a t ω ≠ 0 ∧
      √(2 * σ2 * Real.log (1 / δ) / pullCount A a t ω) ≤ empMean A R a t ω - actionMean κ E a ω}
      ≤ ENNReal.ofReal (K * (n - 1) * δ) := by
  have := h.measurable_param
  have := h.measurable_action
  have := h.measurable_feedback
  let S : Set (𝓔 × (ℕ → Round Unit (Fin K) ℝ)) :=
    {(e, τ) | ∃ a, ∃ t < n, pullCount IT.action a t τ ≠ 0 ∧
    √(2 * pullCount IT.action a t τ * σ2 * Real.log (1 / δ)) ≤
      sumRewards IT.action IT.feedback a t τ - pullCount IT.action a t τ * actionMean κ id a e}
  calc
    _ ≤ (P.map (fun ω ↦ (E ω, trajectory (noObs Ω) A R ω))) S := by
        rw [Measure.map_apply (by fun_prop) (by measurability)]
        apply measure_mono
        intro ω ⟨t, ht, a, hpc, hle⟩
        rw [empMean] at hle
        exact ⟨a, t, ht, hpc, sqrt_two_mul_le_sub hpc hle⟩
    _ = (P.map E ⊗ₘ condDistrib (trajectory (noObs Ω) A R) E P) S := by
        rw [← compProd_map_condDistrib (by fun_prop) (by fun_prop)]
    _ = ∫⁻ e, condDistrib (trajectory (noObs Ω) A R) E P e (Prod.mk e ⁻¹' S) ∂(P.map E) :=
        Measure.compProd_apply (by measurability)
    _ ≤ ∫⁻ e, ENNReal.ofReal (Fintype.card (Fin K) * (n - 1) * δ) ∂(P.map E) := by
        apply lintegral_mono_ae
        rw [h.hasLaw_env.map_eq]
        filter_upwards [h.ae_isAlgEnvSeq, hs] with e he hse
        exact Bandits.prob_exists_sumRewards_sub_pullCount_mul_ge_le he hse hσ2 hδ
    _ = ENNReal.ofReal (K * (n - 1) * δ) := by
      simp [Measure.map_apply h.measurable_param]

/-- Auxiliary lemma for `prob_empMean_bestAction_sub_actionMean_le_le`. -/
private lemma sub_le_neg_sqrt_two_mul {k : ℕ} (hk : k ≠ 0) {s μ σ l : ℝ}
    (h : s / k - μ ≤ -√(2 * σ * l / k)) : s - k * μ ≤ -√(2 * k * σ * l) := by
  have : √(2 * k * σ * l) ≤ -s - k * -μ := sqrt_two_mul_le_sub hk (by grind)
  linarith

lemma prob_empMean_bestAction_sub_actionMean_le_le (h : IsBayesAlgEnvSeq Q κ alg E A R P)
    {σ2 : ℝ≥0} (hs : ∀ᵐ e ∂Q, ∀ a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    (hσ2 : σ2 ≠ 0) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    P {ω | ∃ t < n, pullCount A (bestAction κ E ω) t ω ≠ 0 ∧
        empMean A R (bestAction κ E ω) t ω - actionMean κ E (bestAction κ E ω) ω ≤
          -√(2 * σ2 * Real.log (1 / δ) / (pullCount A (bestAction κ E ω) t ω))}
      ≤ ENNReal.ofReal ((n - 1) * δ) := by
  have := h.measurable_param
  have := h.measurable_action
  have := h.measurable_feedback
  let S : Set (𝓔 × (ℕ → Round Unit (Fin K) ℝ)) :=
    {(e, τ) | ∃ t < n, pullCount IT.action (bestAction κ id e) t τ ≠ 0 ∧
    sumRewards IT.action IT.feedback (bestAction κ id e) t τ -
        pullCount IT.action (bestAction κ id e) t τ * actionMean κ id (bestAction κ id e) e ≤
          -√(2 * pullCount IT.action (bestAction κ id e) t τ * σ2 * Real.log (1 / δ))}
  calc
    _ ≤ (P.map (fun ω ↦ (E ω, trajectory (noObs Ω) A R ω))) S := by
        rw [Measure.map_apply (by fun_prop) (by measurability)]
        apply measure_mono
        intro ω ⟨t, ht, hpc, hle⟩
        rw [empMean] at hle
        exact ⟨t, ht, hpc, sub_le_neg_sqrt_two_mul hpc hle⟩
    _ = (P.map E ⊗ₘ condDistrib (trajectory (noObs Ω) A R) E P) S := by
        rw [← compProd_map_condDistrib (by fun_prop) (by fun_prop)]
    _ = ∫⁻ e, condDistrib (trajectory (noObs Ω) A R) E P e (Prod.mk e ⁻¹' S) ∂(P.map E) :=
        Measure.compProd_apply (by measurability)
    _ ≤ ∫⁻ e, ENNReal.ofReal ((n - 1) * δ) ∂(P.map E) := by
        apply lintegral_mono_ae
        rw [h.hasLaw_env.map_eq]
        filter_upwards [h.ae_isAlgEnvSeq, hs] with e he hse
        exact Bandits.prob_sumRewards_sub_pullCount_mul_le_le (ν := κ.sectR e) he (hse _) hσ2 hδ
    _ = ENNReal.ofReal ((n - 1) * δ) := by
      simp [Measure.map_apply h.measurable_param]

end Learning.IsBayesAlgEnvSeq

open IsBayesAlgEnvSeq (bestAction actionMean)

namespace Bandits

namespace ClippedUCB

variable {K : ℕ} {l u δ : ℝ} {σ2 : ℝ≥0}
variable {Ω : Type*} {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}

/-- Clipped upper confidence bound used in the regret analysis of Thompson sampling. -/
noncomputable
def ucb (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (l u : ℝ) (σ2 : ℝ≥0) (δ : ℝ) (a : Fin K) (n : ℕ)
    (ω : Ω) : ℝ :=
  if pullCount A a n ω = 0 then u
  else max l (min u (empMean A R a n ω + √(2 * σ2 * Real.log (1 / δ) / (pullCount A a n ω))))

@[simp]
lemma ucb_zero {a : Fin K} {ω : Ω} : ucb A R l u σ2 δ a 0 ω = u := by
  simp [ucb]

lemma ucb_mem_Icc (h : l ≤ u) {a : Fin K} {n : ℕ} {ω : Ω} :
    ucb A R l u σ2 δ a n ω ∈ Set.Icc l u := by
  unfold ucb
  grind

@[fun_prop]
lemma measurable_ucb [MeasurableSpace Ω] {a : Fin K} {n : ℕ} (hA : ∀ t, Measurable (A t))
    (hR : ∀ t, Measurable (R t)) : Measurable (ucb A R l u σ2 δ a n) :=
  Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

@[fun_prop]
lemma measurable_uncurry_ucb_comp [MeasurableSpace Ω] (hA : ∀ t, Measurable (A t))
    (hR : ∀ t, Measurable (R t)) {f : Ω → Fin K} (hf : Measurable f) {g : Ω → ℕ}
    (hg : Measurable g) : Measurable (fun ω ↦ ucb A R l u σ2 δ (f ω) (g ω) ω) := by
  -- write the function as a composition with `fun ω ↦ (f ω, ω)`, then with `fun ω ↦ (g ω, ω)`
  change Measurable ((fun aω ↦ ucb A R l u σ2 δ aω.1 (g aω.2) aω.2) ∘ fun ω ↦ (f ω, ω))
  apply Measurable.comp _ (by fun_prop)
  apply measurable_from_prod_countable_right
  intro a
  change Measurable ((fun tω ↦ ucb A R l u σ2 δ a tω.1 tω.2) ∘ fun ω ↦ (g ω, ω))
  apply Measurable.comp _ (by fun_prop)
  exact measurable_from_prod_countable_right (fun _ ↦ measurable_ucb hA hR)

@[fun_prop]
lemma integrable_uncurry_ucb_comp [MeasurableSpace Ω] (hA : ∀ t, Measurable (A t))
    (hR : ∀ t, Measurable (R t)) {f : Ω → Fin K} (hf : Measurable f) {g : Ω → ℕ}
    (hg : Measurable g) {P : Measure Ω} [IsFiniteMeasure P] :
    Integrable (fun ω ↦ ucb A R l u σ2 δ (f ω) (g ω) ω) P := by
  refine ⟨(measurable_uncurry_ucb_comp hA hR hf hg).aestronglyMeasurable, ?_⟩
  apply HasFiniteIntegral.of_bounded (C := max |l| |u|)
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  unfold ucb
  grind

/-- Clipped upper confidence bound (history-based version). -/
noncomputable
def ucb' (n : ℕ) (h : Hist Unit (Fin K) ℝ n) (l u : ℝ) (σ2 : ℝ≥0) (δ : ℝ) (a : Fin K) : ℝ :=
  if pullCount' n h a = 0 then u
  else max l (min u (empMean' n h a + √(2 * σ2 * Real.log (1 / δ) / (pullCount' n h a))))

@[fun_prop]
lemma measurable_uncurry_ucb' {n : ℕ} :
    Measurable (fun p : Hist Unit (Fin K) ℝ n × Fin K ↦ ucb' n p.1 l u σ2 δ p.2) :=
  Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

lemma ucb_eq_ucb' {O : ℕ → Ω → Unit} {a : Fin K} {n : ℕ} {ω : Ω} :
    ucb A R l u σ2 δ a n ω = ucb' n (history O A R n ω) l u σ2 δ a := by
  have hp : pullCount A a n ω = pullCount' n (history O A R n ω) a := pullCount_eq_pullCount'
  have he : empMean A R a n ω = empMean' n (history O A R n ω) a := empMean_eq_empMean'
  rw [ucb, ucb', hp, he]

/-- Helper for `sum_ucb_sub_mean_le`. -/
private lemma sum_sqrt_le {ι : Type*} {c : ι → ℝ} (s : Finset ι) (hc : ∀ i, 0 ≤ c i) :
    ∑ i ∈ s, √(c i) ≤ √(#s * ∑ i ∈ s, c i) := by
  have h := Real.sum_sqrt_mul_sqrt_le s hc (fun _ => zero_le_one)
  simp only [Real.sqrt_one, mul_one, sum_const, nsmul_eq_mul] at h
  rwa [Real.sqrt_mul (by positivity), mul_comm]

/-- Helper for `sum_ucb_sub_mean_le`. -/
private lemma sum_inv_sqrt_le {n : ℕ} (h : 0 < n) : ∑ k ∈ range (n + 1), 1 / √k ≤ 2 * √n - 1 := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    rw [sum_range_succ]
    by_cases hn : n = 0
    · rw [hn]
      simp
      norm_num
    · have hi := ih (Nat.pos_of_ne_zero hn)
      suffices 1 / √↑(n + 1) ≤ 2 * (√↑(n + 1) - √n) by linarith
      push_cast
      field_simp
      have : √(n + 1) * √(n + 1) = (n + 1) := Real.mul_self_sqrt (by positivity)
      have : √n * √n = n := Real.mul_self_sqrt (by positivity)
      nlinarith

lemma sum_ucb_sub_mean_le {n : ℕ} {ω : Ω} (μ : Fin K → ℝ) (hμ : ∀ a, μ a ∈ Set.Icc l u)
    (hc : ∀ s < n, pullCount A (A s ω) s ω ≠ 0 → empMean A R (A s ω) s ω - μ (A s ω)
      < √(2 * σ2 * Real.log (1 / δ) / (pullCount A (A s ω) s ω))) :
    ∑ s ∈ range n, (ucb A R l u σ2 δ (A s ω) s ω - μ (A s ω))
      ≤ (u - l) * K + 4 * √(2 * σ2 * Real.log (1 / δ) * K * n) := by
  -- if `n = 0` both sides are `0` when `K = 0`, and otherwise `l ≤ u` follows from `hμ`
  obtain hK | hK := K.eq_zero_or_pos
  · subst hK
    cases n with
    | zero => simp
    | succ n => exact (A 0 ω).elim0
  have hi : l ≤ u := Set.nonempty_Icc.mp ⟨_, hμ ⟨0, hK⟩⟩
  let S₀ := {s ∈ range n | pullCount A (A s ω) s ω = 0}
  let S₁ := {s ∈ range n | pullCount A (A s ω) s ω ≠ 0}
  have hu : S₀ ∪ S₁ = range n := filter_union_filter_not_eq _ _
  have hd : Disjoint S₀ S₁ := disjoint_filter_filter_not _ _ _
  rw [← hu, sum_union hd]
  gcongr
  · calc ∑ s ∈ S₀, (ucb A R l u σ2 δ (A s ω) s ω - μ (A s ω))
        ≤ ∑ s ∈ S₀, (u - l) :=
          have (s : ℕ) : ucb A R l u σ2 δ (A s ω) s ω ∈ Set.Icc l u := ucb_mem_Icc hi
          sum_le_sum (by grind)
      _ = ∑ s ∈ range n, if pullCount A (A s ω) s ω = 0 then (u - l) else 0 := by
          rw [sum_filter]
      _ = ∑ a, ∑ j ∈ range (pullCount A a n ω), if j = 0 then (u - l) else 0 :=
          sum_comp_pullCount (fun j => if j = 0 then (u - l) else 0) n ω
      _ ≤ ∑ a, (u - l) := by
          gcongr
          rw [sum_ite_eq']
          grind
      _ = (u - l) * K := by
          rw [Fin.sum_const, nsmul_eq_mul, mul_comm]
  · calc ∑ s ∈ S₁, (ucb A R l u σ2 δ (A s ω) s ω - μ (A s ω))
          ≤ ∑ s ∈ S₁, 2 * √(2 * σ2 * Real.log (1 / δ) / (pullCount A (A s ω) s ω)) := by
            gcongr with s hs
            unfold ucb
            have : 0 ≤ √(2 * σ2 * Real.log (1 / δ) / (pullCount A (A s ω) s ω)) := by positivity
            grind
        _ ≤ ∑ s ∈ range n, 2 * √(2 * σ2 * Real.log (1 / δ) / (pullCount A (A s ω) s ω)) :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
        _ = 2 * √(2 * σ2 * Real.log (1 / δ)) * ∑ s ∈ range n, (1 / √(pullCount A (A s ω) s ω)) := by
            rw [mul_sum]
            congr with s
            rw [Real.sqrt_div' _ (by positivity)]
            ring
        _ = 2 * √(2 * σ2 * Real.log (1 / δ)) *
              ∑ a, ∑ j ∈ range (pullCount A a n ω), (1 / √j) := by
            rw [sum_comp_pullCount (fun j => 1 / √j)]
        _ ≤ 2 * √(2 * σ2 * Real.log (1 / δ)) * (2 * ∑ a, √(pullCount A a n ω)) := by -- loose
            rw [mul_sum _ _ 2]
            gcongr with a
            by_cases ha : pullCount A a n ω = 0
            · simp [ha]
            · have hi := sum_inv_sqrt_le (Nat.pos_of_ne_zero ha)
              rw [sum_range_succ] at hi
              have : 0 ≤ 1 / √(pullCount A a n ω) := by positivity
              linarith
        _ ≤ 2 * √(2 * σ2 * Real.log (1 / δ)) * (2 * √(K * ∑ a, (pullCount A a n ω))) := by
            gcongr
            have h := sum_sqrt_le Finset.univ (fun a => Nat.cast_nonneg (pullCount A a n ω))
            rw [Finset.card_fin] at h
            exact_mod_cast h
        _ = 2 * √(2 * σ2 * Real.log (1 / δ)) * (2 * √(K * n)) := by
            congr
            exact sum_pullCount (ω := ω)
        _ = 4 * √(2 * σ2 * Real.log (1 / δ) * K * n) := by
            ring_nf
            rw [← Real.sqrt_mul' _ (by positivity)]
            ring_nf

variable [Nonempty (Fin K)]
variable [MeasurableSpace Ω]
variable {𝓔 : Type*} [MeasurableSpace 𝓔]
variable {E : Ω → 𝓔}
variable {Q : Measure 𝓔} [IsProbabilityMeasure Q] {κ : Kernel (𝓔 × Fin K) ℝ} [IsMarkovKernel κ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

lemma integral_sum_range_actionMean_bestAction_sub_ucb_bestAction_le
    {alg : Algorithm Unit (Fin K) ℝ} (h : IsBayesAlgEnvSeq Q κ alg E A R P)
    (hm : ∀ e a, (κ (e, a))[id] ∈ (Set.Icc l u))
    (hs : ∀ᵐ e ∂Q, ∀ a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    (hσ2 : σ2 ≠ 0) (hδ : 0 < δ) (n : ℕ) :
    P[fun ω ↦ ∑ t ∈ range n,
      (actionMean κ E (bestAction κ E ω) ω - ucb A R l u σ2 δ (bestAction κ E ω) t ω)] ≤
        (u - l) * (n - 1) * n * δ := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure P
  have hlu : l ≤ u := Set.nonempty_Icc.mp ⟨_, hm (E ω₀) (Classical.arbitrary _)⟩
  by_cases hn : n = 0
  · simp [hn]
  -- `F` is the event on which the confidence interval of the best action fails at some time
  -- `t < n`. On its complement, each term of the sum is nonpositive. On `F`, each term is at most
  -- `u - l`, and `F` has probability at most `(n - 1) * δ`.
  let F := {ω | ∃ t < n, pullCount A (bestAction κ E ω) t ω ≠ 0 ∧
    empMean A R (bestAction κ E ω) t ω - actionMean κ E (bestAction κ E ω) ω ≤
      -√(2 * σ2 * Real.log (1 / δ) / (pullCount A (bestAction κ E ω) t ω))}
  have := h.measurable_action
  have := h.measurable_param
  have := h.measurable_feedback
  have hF : MeasurableSet F := by measurability
  have : Integrable (fun ω ↦ actionMean κ E (bestAction κ E ω) ω) P :=
      IsBayesAlgEnvSeq.integrable_uncurry_actionMean_comp (by fun_prop) (by fun_prop) hm
  calc
    _ ≤ ∫ ω in F, ∑ t ∈ range n,
          (actionMean κ E (bestAction κ E ω) ω - ucb A R l u σ2 δ (bestAction κ E ω) t ω) ∂P := by
        rw [← integral_add_compl hF (by fun_prop)]
        apply add_le_of_nonpos_right
        apply setIntegral_nonpos hF.compl
        intro ω hω
        apply sum_nonpos
        intro t ht
        rw [Set.mem_compl_iff, Set.mem_ofPred_eq] at hω
        push Not at hω
        grind [hω t (mem_range.mp ht), ucb, actionMean]
    _ ≤ ∫ ω in F, ∑ t ∈ range n, (u - l) ∂P := by
        apply setIntegral_mono_on (Integrable.integrableOn (by fun_prop))
          (Integrable.integrableOn (by fun_prop)) hF
        intro ω hω
        apply sum_le_sum
        intro t ht
        grind [actionMean, ucb]
    _ = P.real F * (n * (u - l)) := by
        simp_rw [sum_const, card_range, nsmul_eq_mul, setIntegral_const, smul_eq_mul]
    _ ≤ ((n - 1) * δ) * (n * (u - l)) := by
        gcongr
        have : (1 : ℝ) ≤ n := by simp [Nat.one_le_iff_ne_zero, hn]
        apply ENNReal.toReal_le_of_le_ofReal (by nlinarith)
        exact h.prob_empMean_bestAction_sub_actionMean_le_le hs hσ2 hδ n
    _ = _ := by
      ring

lemma integral_sum_range_ucb_action_sub_actionMean_action_le {alg : Algorithm Unit (Fin K) ℝ}
    (h : IsBayesAlgEnvSeq Q κ alg E A R P)
    (hm : ∀ e a, (κ (e, a))[id] ∈ (Set.Icc l u))
    (hs : ∀ᵐ e ∂Q, ∀ a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    (hσ2 : σ2 ≠ 0) (hδ : 0 < δ) (n : ℕ) :
    P[fun ω ↦ ∑ t ∈ range n, (ucb A R l u σ2 δ (A t ω) t ω - actionMean κ E (A t ω) ω)] ≤
      (u - l) * K + 4 * √(2 * σ2 * Real.log (1 / δ) * K * n) + (u - l) * K * (n - 1) * n * δ := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure P
  have hlu : l ≤ u := Set.nonempty_Icc.mp ⟨_, hm (E ω₀) (Classical.arbitrary _)⟩
  by_cases hn : n = 0
  · simp [hn, hlu, mul_nonneg]
  -- `F` is the event on which the confidence interval of some action fails at some time `t < n`.
  -- On `F`, each term of the sum is at most `u - l`, and `F` has probability at most
  -- `K * (n - 1) * δ`. On its complement, the sum is bounded by `sum_ucb_sub_mean_le`.
  let F := {ω | ∃ t < n, ∃ a, pullCount A a t ω ≠ 0 ∧
    √(2 * σ2 * Real.log (1 / δ) / pullCount A a t ω) ≤ empMean A R a t ω - actionMean κ E a ω}
  have := h.measurable_action
  have := h.measurable_param
  have := h.measurable_feedback
  have hF : MeasurableSet F := by measurability
  have : ∀ t, Integrable (fun ω ↦ actionMean κ E (A t ω) ω) P :=
    fun t ↦ IsBayesAlgEnvSeq.integrable_uncurry_actionMean_comp (by fun_prop) (by fun_prop) hm
  calc
    _ ≤ (∫ ω in F, ∑ t ∈ range n, (u - l) ∂P) +
          ∫ ω in Fᶜ, (u - l) * K + 4 * √(2 * σ2 * Real.log (1 / δ) * K * n) ∂P := by
        rw [← integral_add_compl hF (by fun_prop)]
        apply add_le_add
        · apply setIntegral_mono_on (Integrable.integrableOn (by fun_prop))
            (Integrable.integrableOn (by fun_prop)) hF
          intro ω hω
          apply sum_le_sum
          intro t ht
          grind [ucb, actionMean]
        · apply setIntegral_mono_on (Integrable.integrableOn (by fun_prop))
            (Integrable.integrableOn (by fun_prop)) hF.compl
          intro ω hω
          rw [Set.mem_compl_iff, Set.mem_ofPred_eq] at hω
          push Not at hω
          exact sum_ucb_sub_mean_le (fun a ↦ (κ (E ω, a))[id]) (hm (E ω))
            (fun t ht hpc ↦ hω t ht (A t ω) hpc)
    _ = P.real F * (n * (u - l)) +
          P.real Fᶜ * ((u - l) * K + 4 * √(2 * σ2 * Real.log (1 / δ) * K * n)) := by
        simp_rw [sum_const, card_range, nsmul_eq_mul, setIntegral_const, smul_eq_mul]
    _ ≤ (K * (n - 1) * δ) * (n * (u - l)) +
          1 * ((u - l) * K + 4 * √(2 * σ2 * Real.log (1 / δ) * K * n)) := by
        have : 0 ≤ u - l := sub_nonneg.2 hlu
        gcongr
        · have : (0 : ℝ) ≤ n - 1 := by simp [Nat.one_le_iff_ne_zero, hn]
          apply ENNReal.toReal_le_of_le_ofReal (by positivity)
          exact h.prob_empMean_sub_actionMean_ge_le hs hσ2 hδ n
        · exact measureReal_le_one
    _ = _ := by
        ring

end ClippedUCB

namespace TS

open ClippedUCB

variable {K : ℕ} [NeZero K]
variable {l u δ : ℝ} {σ2 : ℝ≥0}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {𝓔 : Type*} [MeasurableSpace 𝓔] [StandardBorelSpace 𝓔] [Nonempty 𝓔]
variable {Q : Measure 𝓔} [IsProbabilityMeasure Q] {κ : Kernel (𝓔 × Fin K) ℝ} [IsMarkovKernel κ]
variable {E : Ω → 𝓔} {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
variable {P : Measure Ω} [IsProbabilityMeasure P]

lemma integral_ucb_action_eq_integral_ucb_bestAction
    (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm Q κ) E A R P) (n : ℕ) :
    P[fun ω ↦ ucb A R l u σ2 δ (A n ω) n ω] =
      P[fun ω ↦ ucb A R l u σ2 δ (bestAction κ E ω) n ω] := by
  have := h.measurable_action
  have := h.measurable_param
  have := h.measurable_feedback
  let uc (ha : Hist Unit (Fin K) ℝ n × Fin K) := ucb' n ha.1 l u σ2 δ ha.2
  calc
    _  = P[fun ω ↦ uc (history (noObs Ω) A R n ω, A n ω)] := by
        simp_rw [uc, ucb_eq_ucb' (O := noObs Ω)]
    _ = ∫ ha, uc ha ∂P.map (fun ω ↦ (history (noObs Ω) A R n ω, A n ω)) := by
        rw [← integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ ha, uc ha ∂P.map (fun ω ↦ (history (noObs Ω) A R n ω, bestAction κ E ω)) := by
        rw [← compProd_map_condDistrib (by fun_prop) (by fun_prop),
          ← compProd_map_condDistrib (by fun_prop) (by fun_prop),
            Measure.compProd_congr (hasCondDistrib_action h n).condDistrib_ae_eq]
    _ = P[fun ω ↦ ucb A R l u σ2 δ (bestAction κ E ω) n ω] := by
        rw [integral_map (by fun_prop) (by fun_prop)]
        simp_rw [uc, ucb_eq_ucb' (O := noObs Ω)]

lemma integral_regret_eq_add (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm Q κ) E A R P)
    (hm : ∀ e a, (κ (e, a))[id] ∈ (Set.Icc l u)) (n : ℕ) :
    P[IsBayesAlgEnvSeq.regret κ E A n] =
      P[fun ω ↦ ∑ t ∈ range n,
        (actionMean κ E (bestAction κ E ω) ω - ucb A R l u σ2 δ (bestAction κ E ω) t ω)] +
      P[fun ω ↦ ∑ t ∈ range n,
        (ucb A R l u σ2 δ (A t ω) t ω - actionMean κ E (A t ω) ω)] := by
  have hua (t : ℕ) : Integrable (fun ω ↦ ucb A R l u σ2 δ (A t ω) t ω) P :=
    integrable_uncurry_ucb_comp h.measurable_action h.measurable_feedback (h.measurable_action t)
      measurable_const
  have hub (t : ℕ) : Integrable (fun ω ↦ ucb A R l u σ2 δ (bestAction κ E ω) t ω) P :=
    integrable_uncurry_ucb_comp h.measurable_action h.measurable_feedback
      (IsBayesAlgEnvSeq.measurable_bestAction h.measurable_param) measurable_const
  have haa (t : ℕ) : Integrable (fun ω ↦ actionMean κ E (A t ω) ω) P :=
    IsBayesAlgEnvSeq.integrable_uncurry_actionMean_comp h.measurable_param
      (h.measurable_action t) hm
  have hab : Integrable (fun ω ↦ actionMean κ E (bestAction κ E ω) ω) P :=
      IsBayesAlgEnvSeq.integrable_uncurry_actionMean_comp h.measurable_param
        (IsBayesAlgEnvSeq.measurable_bestAction h.measurable_param) hm
  calc
    _  = (∑ t ∈ range n, ∫ ω, actionMean κ E (bestAction κ E ω) ω ∂P) -
            ∑ t ∈ range n, ∫ ω, actionMean κ E (A t ω) ω ∂P := by
        simp_rw [IsBayesAlgEnvSeq.regret_eq_sum_gap, IsBayesAlgEnvSeq.gap_eq_sub]
        rw [integral_finsetSum _ (by fun_prop), ← Finset.sum_sub_distrib]
        simp_rw [integral_sub hab (haa _)]
    _ = ((∑ t ∈ range n, ∫ ω, actionMean κ E (bestAction κ E ω) ω ∂P) -
            ∑ t ∈ range n, ∫ ω, ucb A R l u σ2 δ (bestAction κ E ω) t ω ∂P) +
          ((∑ t ∈ range n, ∫ ω, ucb A R l u σ2 δ (A t ω) t ω ∂P) -
            ∑ t ∈ range n, ∫ ω, actionMean κ E (A t ω) ω ∂P) := by
        simp [integral_ucb_action_eq_integral_ucb_bestAction h]
    _ = (∑ t ∈ range n, ∫ ω, actionMean κ E (bestAction κ E ω) ω -
              ucb A R l u σ2 δ (bestAction κ E ω) t ω ∂P) +
          ∑ t ∈ range n, ∫ ω, ucb A R l u σ2 δ (A t ω) t ω -
            actionMean κ E (A t ω) ω ∂P := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        simp_rw [← integral_sub hab (hub _), ← integral_sub (hua _) (haa _)]
    _ = _ := by
        rw [← integral_finsetSum _ (by fun_prop), ← integral_finsetSum _ (by fun_prop)]

/-- **Bayesian regret of Thompson sampling.** If Thompson sampling has the correct prior over
environments, in every environment each of the `K` actions has a mean reward between `l` and `u`,
and in almost every environment (under the prior) the reward distribution of each action is
sub-Gaussian with variance proxy `σ2` after its mean is subtracted, then the Bayesian regret at
time `n` is at most `(2 * K + 1) * (u - l) + 8 * √(σ2 * K * n * Real.log n)`. -/
theorem integral_regret_le (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm Q κ) E A R P)
    (hm : ∀ e a, (κ (e, a))[id] ∈ (Set.Icc l u))
    (hs : ∀ᵐ e ∂Q, ∀ a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    (hσ2 : σ2 ≠ 0) (n : ℕ) :
    P[IsBayesAlgEnvSeq.regret κ E A n]
      ≤ (2 * K + 1) * (u - l) + 8 * √(σ2 * K * n * Real.log n) := by
  have hlu : l ≤ u := Set.nonempty_Icc.mp ⟨_, hm (Classical.arbitrary 𝓔) 0⟩
  by_cases hn : n = 0
  · simp [hn, IsBayesAlgEnvSeq.regret, Bandits.regret]
    nlinarith
  have hδ : (0 : ℝ) < 1 / n ^ 2 := by positivity
  calc P[IsBayesAlgEnvSeq.regret κ E A n]
      = _ :=
        integral_regret_eq_add h hm n
    _ ≤ _ :=
        add_le_add
          (integral_sum_range_actionMean_bestAction_sub_ucb_bestAction_le h hm hs hσ2 hδ n)
          (integral_sum_range_ucb_action_sub_actionMean_action_le h hm hs hσ2 hδ n)
    _ = K * (u - l) + (K + 1) * (u - l) * ((n - 1) / n)
          + 4 * √((2 : ℝ) ^ 2 * (σ2 * K * n * Real.log n)) := by
        field_simp
        rw [Real.log_pow]
        ring_nf
    _ = K * (u - l) + (K + 1) * (u - l) * ((n - 1) / n) + 8 * √(σ2 * K * n * Real.log n) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
        ring
    _ ≤ K * (u - l) + (K + 1) * (u - l) * 1 + 8 * √(σ2 * K * n * Real.log n) := by -- loose
        have : 0 ≤ u - l := sub_nonneg.2 hlu
        gcongr
        rw [div_le_one (by positivity)]
        linarith
    _ = _ := by
        ring

end TS

end Bandits
