/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.SubGaussian
public import LeanMachineLearning.Online.Bandit.ArrayProbSpace
public import LeanMachineLearning.Online.Bandit.BayesRegret
public import LeanMachineLearning.Online.Bandit.Regret
public import LeanMachineLearning.SequentialLearning.BayesStationaryEnv

/-! # Concentration of the sums of rewards

For a stochastic bandit, we bound the probability of events involving the number of pulls
`pullCount A a n` and the sum of rewards `sumRewards A R a n` of an action by probabilities of
events about sums of i.i.d. rewards under `streamMeasure ν`. The bounds are first proved in the
array model `ArrayModel.arrayMeasure ν`, in which the sum of rewards of action `a` after `k` pulls
is the sum of the first `k` entries of row `a` of the reward array, then transferred to any
algorithm-environment sequence since the joint law of the numbers of pulls and of the sums of
rewards does not depend on the probability space (`IsAlgEnvSeq.identDistrib_pullCount_sumRewards`).

We then specialize those bounds to sub-Gaussian rewards, for the analysis of the ETC, UCB and
Thompson sampling algorithms, and transfer them to Bayesian bandits by conditioning on the
environment (`IsBayesAlgEnvSeq.measure_mem_le_of_forall_isAlgEnvSeq`).

## Main statements

* `prob_exists_sumRewards_mem_le`: union bound over the number of pulls, uniformly in time. The
  probability that at some time `t < n` the sum of rewards of an action lies in a set that depends
  on its number of pulls is at most a sum over `m < n` of probabilities of events about the sum of
  `m` i.i.d. rewards.
* `prob_exists_sqrt_le_empMean_sub_le`, `prob_exists_empMean_sub_le_neg_sqrt_le`: for sub-Gaussian
  rewards with variance proxy `σ2`, the probability that at some time `t < n` the empirical mean of
  an action deviates from its mean by at least `√(2 * σ2 * L / pullCount A a t ω)` is at most
  `(n - 1) * exp (-L)`.
* `probReal_sum_le_sum_streamMeasure`: for sub-Gaussian rewards, bound on the probability that the
  sum of `m` rewards of the best arm is at most the sum of `m` rewards of another arm.
* `IsBayesAlgEnvSeq.prob_empMean_sub_actionMean_ge_le`,
  `IsBayesAlgEnvSeq.prob_empMean_bestAction_sub_actionMean_le_le`: in a Bayesian bandit with
  sub-Gaussian rewards, the empirical means of the actions are close to their means with high
  probability, uniformly in time.

## References

* T. Lattimore and C. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapters 5 to 8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning
open scoped ENNReal NNReal

namespace Bandits

namespace ArrayModel

variable {𝓐 : Type*} {m𝓐 : MeasurableSpace 𝓐} [DecidableEq 𝓐] [Countable 𝓐]
  [StandardBorelSpace 𝓐] [Nonempty 𝓐]
  {alg : Algorithm Unit 𝓐 ℝ} {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]

local notation "A" => action alg
local notation "R" => reward alg
local notation "𝔓" => arrayMeasure ν

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

lemma prob_exists_pullCount_eq_and_sumRewards_mem_le (a : 𝓐) (m : ℕ) {B : Set ℝ}
    (hB : MeasurableSet B) : 𝔓 {ω | ∃ n, pullCount A a n ω = m ∧ sumRewards A R a n ω ∈ B} ≤
      streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B} :=
  calc
    _ ≤ 𝔓 {ω | ∑ i ∈ range m, ω.2 i a ∈ B} := by
        apply measure_mono
        intro ω ⟨n, hp, hn⟩
        rwa [sumRewards_eq alg a n ω, hp] at hn
    _ = streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B} :=
        (identDistrib_sum_range_snd a m).measure_mem_eq hB

lemma prob_sumRewards_le_sumRewards_le (a b : 𝓐) (n m₁ m₂ : ℕ) :
    (𝔓) {ω | pullCount A a n ω = m₁ ∧ pullCount A b n ω = m₂ ∧
        sumRewards A R a n ω ≤ sumRewards A R b n ω} ≤
      streamMeasure ν {ω | ∑ i ∈ range m₁, ω i a ≤ ∑ i ∈ range m₂, ω i b} := by
  simp_rw [sumRewards_eq]
  calc 𝔓 {ω | pullCount A a n ω = m₁ ∧ pullCount A b n ω = m₂ ∧
      ∑ i ∈ range (pullCount A a n ω), ω.2 i a ≤ ∑ i ∈ range (pullCount A b n ω), ω.2 i b}
  _ ≤ 𝔓 ((fun ω ↦ (∑ i ∈ range m₁, ω.2 i a, ∑ i ∈ range m₂, ω.2 i b)) ⁻¹' {p | p.1 ≤ p.2}) := by
      refine measure_mono fun ω hω ↦ ?_
      simp only [Set.preimage_ofPred_eq, Set.mem_ofPred_eq] at hω ⊢
      grind
  _ = streamMeasure ν {ω | ∑ i ∈ range m₁, ω i a ≤ ∑ i ∈ range m₂, ω i b} := by
    rw [← Measure.snd_prod (μ := (Measure.infinitePi fun (_ : ℕ) ↦ (volume : Measure unitInterval)))
      (ν := streamMeasure ν), Measure.snd, Measure.map_apply (by fun_prop)]
    · rfl
    simp only [measurableSet_setOfPred]
    fun_prop

lemma probReal_sumRewards_le_sumRewards_le (a b : 𝓐) (n m₁ m₂ : ℕ) :
    (𝔓).real {ω | pullCount A a n ω = m₁ ∧ pullCount A b n ω = m₂ ∧
        sumRewards A R a n ω ≤ sumRewards A R b n ω} ≤
      (streamMeasure ν).real {ω | ∑ i ∈ range m₁, ω i a ≤ ∑ i ∈ range m₂, ω i b} := by
  simp_rw [measureReal_def]
  gcongr
  · finiteness
  · exact prob_sumRewards_le_sumRewards_le a b n m₁ m₂

end ArrayModel

variable {𝓐 Ω : Type*} [DecidableEq 𝓐] {m𝓐 : MeasurableSpace 𝓐} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {alg : Algorithm Unit 𝓐 ℝ} {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {R : ℕ → Ω → ℝ} {a : 𝓐}

variable [Nonempty 𝓐]

/-- The probability that the sum of rewards of action `a` lies in `B` at some time at which `a` has
been pulled `m` times is at most the probability that the sum of `m` i.i.d. rewards of `a` lies
in `B`. -/
lemma prob_exists_pullCount_eq_and_sumRewards_mem_le [Countable 𝓐] [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : 𝓐) (m : ℕ) {B : Set ℝ}
    (hB : MeasurableSet B) :
    P {ω | ∃ n, pullCount A a n ω = m ∧ sumRewards A R a n ω ∈ B} ≤
      streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B} :=
  let s := {p : ℕ → 𝓐 → ℕ × ℝ | ∃ n, (p n a).1 = m ∧ (p n a).2 ∈ B}
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

/-- **Union bound over the number of pulls**, uniformly in time: the probability that at some time
`t < n` the sum of rewards of action `a` lies in `B (pullCount A a t ω)` is at most the sum over
`m < n` of the probabilities that the sum of `m` i.i.d. rewards of `a` lies in `B m`. -/
lemma prob_exists_sumRewards_mem_le [Countable 𝓐] [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : 𝓐) (n : ℕ) {B : ℕ → Set ℝ}
    (hB : ∀ m, MeasurableSet (B m)) :
    P {ω | ∃ t < n, sumRewards A R a t ω ∈ B (pullCount A a t ω)} ≤
      ∑ m ∈ range n, streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B m} :=
  calc
    _ ≤ P (⋃ m ∈ range n, {ω | ∃ t, pullCount A a t ω = m ∧ sumRewards A R a t ω ∈ B m}) := by
        refine measure_mono ?_
        rintro ω ⟨t, ht, hB⟩
        exact Set.mem_biUnion (mem_range.2 ((pullCount_le a t ω).trans_lt ht)) ⟨t, rfl, hB⟩
    _ ≤ ∑ m ∈ range n, P {ω | ∃ t, pullCount A a t ω = m ∧ sumRewards A R a t ω ∈ B m} :=
        measure_biUnion_finset_le _ _
    _ ≤ _ := sum_le_sum fun m _ ↦ prob_exists_pullCount_eq_and_sumRewards_mem_le h a m (hB m)

/-- Union bound over the number of pulls at time `n`: the probability that the number of pulls and
the sum of rewards of action `a` at time `n` lie in `s` is at most the sum over `k ≤ n` of the
probabilities that `k` and the sum of `k` i.i.d. rewards of `a` lie in `s`. -/
lemma prob_pullCount_prod_sumRewards_mem_le [Countable 𝓐] [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : 𝓐) (n : ℕ) {s : Set (ℕ × ℝ)}
    (hs : MeasurableSet s) :
    P {ω | (pullCount A a n ω, sumRewards A R a n ω) ∈ s} ≤
      ∑ k ∈ range (n + 1), streamMeasure ν {ω | (k, ∑ i ∈ range k, ω i a) ∈ s} := by
  refine le_trans (measure_mono ?_) (prob_exists_sumRewards_mem_le h a (n + 1)
    (B := fun k ↦ Prod.mk k ⁻¹' s) fun _ ↦ measurable_prodMk_left hs)
  exact fun _ hω ↦ ⟨n, n.lt_add_one, hω⟩

/-- Union bound over the number of pulls at time `n`: the probability that the number of pulls of
action `a` at time `n` lies in `s` and its sum of rewards lies in `B` is at most the sum over
`k ≤ n` with `k ∈ s` of the probabilities that the sum of `k` i.i.d. rewards of `a` lies in `B`. -/
lemma prob_pullCount_mem_and_sumRewards_mem_le [Countable 𝓐] [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : 𝓐) (n : ℕ) (s : Set ℕ)
    [DecidablePred (· ∈ s)] {B : Set ℝ} (hB : MeasurableSet B) :
    P {ω | pullCount A a n ω ∈ s ∧ sumRewards A R a n ω ∈ B} ≤
      ∑ k ∈ (range (n + 1)).filter (· ∈ s), streamMeasure ν {ω | ∑ i ∈ range k, ω i a ∈ B} := by
  refine (prob_pullCount_prod_sumRewards_mem_le h a n
    (MeasurableSet.of_discrete.prod hB)).trans_eq ?_
  rw [sum_filter]
  refine sum_congr rfl fun k _ ↦ ?_
  split_ifs with hk <;> simp [hk]

/-- Union bound over the number of pulls at time `n`: the probability that the sum of rewards of
action `a` at time `n` lies in `B` is at most the sum over `k ≤ n` of the probabilities that the
sum of `k` i.i.d. rewards of `a` lies in `B`. -/
lemma prob_sumRewards_mem_le [Countable 𝓐] [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : 𝓐) (n : ℕ) {B : Set ℝ}
    (hB : MeasurableSet B) :
    P (sumRewards A R a n ⁻¹' B) ≤
      ∑ k ∈ range (n + 1), streamMeasure ν {ω | ∑ i ∈ range k, ω i a ∈ B} := by
  refine le_trans (measure_mono ?_)
    (prob_exists_sumRewards_mem_le h a (n + 1) (B := fun _ ↦ B) fun _ ↦ hB)
  exact fun _ hω ↦ ⟨n, n.lt_add_one, hω⟩

/-- Union bound over the number of pulls, uniformly in time, for an action that has been pulled:
if, for all `m ≠ 0`, the sum of `m` i.i.d. rewards of action `a` lies in `B m` with probability at
most `δ`, then the probability that at some time `t < n` the action `a` has been pulled and the
sum of its rewards lies in `B (pullCount A a t ω)` is at most `(n - 1) * δ`. -/
lemma prob_exists_pullCount_ne_zero_and_sumRewards_mem_le [Countable 𝓐]
    [MeasurableSingletonClass 𝓐] (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : 𝓐)
    (n : ℕ) {B : ℕ → Set ℝ} (hB : ∀ m, MeasurableSet (B m)) {δ : ℝ}
    (h_le : ∀ m, m ≠ 0 → streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ B m} ≤ ENNReal.ofReal δ) :
    P {ω | ∃ t < n, pullCount A a t ω ≠ 0 ∧ sumRewards A R a t ω ∈ B (pullCount A a t ω)} ≤
      ENNReal.ofReal ((n - 1) * δ) :=
  calc
    _ ≤ ∑ m ∈ range n, streamMeasure ν {ω | ∑ i ∈ range m, ω i a ∈ {x | m ≠ 0 ∧ x ∈ B m}} :=
        prob_exists_sumRewards_mem_le h a n (B := fun m ↦ {x | m ≠ 0 ∧ x ∈ B m})
          fun m ↦ (MeasurableSet.const _).inter (hB m)
    _ ≤ ∑ m ∈ range n, if m = 0 then 0 else ENNReal.ofReal δ := by
        gcongr with m
        split_ifs with hm
        · simp [hm]
        · refine (measure_mono ?_).trans (h_le m hm)
          exact fun _ hω ↦ hω.2
    _ ≤ ENNReal.ofReal ((n - 1) * δ) := by
        cases n with
        | zero => simp
        | succ n => simp [sum_range_succ', ENNReal.ofReal_mul]

/-- The probability that actions `a` and `b` have been pulled `m₁` and `m₂` times at time `n` and
that the sum of rewards of `a` is at most that of `b` is at most the probability that the sum of
`m₁` i.i.d. rewards of `a` is at most the sum of `m₂` i.i.d. rewards of `b`. -/
lemma probReal_sumRewards_le_sumRewards_le [Countable 𝓐] [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a b : 𝓐) (n m₁ m₂ : ℕ) :
    P.real {ω | pullCount A a n ω = m₁ ∧ pullCount A b n ω = m₂ ∧
        sumRewards A R a n ω ≤ sumRewards A R b n ω} ≤
      (streamMeasure ν).real {ω | ∑ i ∈ range m₁, ω i a ≤ ∑ i ∈ range m₂, ω i b} := by
  refine le_trans (le_of_eq ?_)
    (ArrayModel.probReal_sumRewards_le_sumRewards_le (alg := alg) a b n m₁ m₂)
  let s := {p : ℕ × ℕ × ℝ × ℝ | p.1 = m₁ ∧ p.2.1 = m₂ ∧ p.2.2.1 ≤ p.2.2.2}
  have hs : MeasurableSet s := by simp only [measurableSet_setOfPred, s]; fun_prop
  simp_rw [measureReal_def]
  congr 1
  exact ((h.identDistrib_pi_pullCount_sumRewards (ArrayModel.isAlgEnvSeq_arrayMeasure alg ν) n).comp
    (u := fun p ↦ ((p a).1, (p b).1, (p a).2, (p b).2)) (by fun_prop)).measure_mem_eq hs

section Subgaussian

namespace StreamMeasure

omit [DecidableEq 𝓐] [Nonempty 𝓐]

lemma prob_sum_range_sub_ge_le_of_hasSubgaussianMGF {σ2 : ℝ≥0}
    (h : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    streamMeasure ν {ω | ε ≤ ∑ k ∈ range n, (ω k a - (ν a)[id])} ≤
      ENNReal.ofReal (Real.exp (-ε ^ 2 / (2 * n * σ2))) := by
  rw [← ofReal_measureReal]
  gcongr
  apply HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun _ _ hε
  · exact (iIndepFun_eval_streamMeasure'' ν a).comp (fun _ x ↦ x - (ν a)[id]) (by fun_prop)
  · intro _ _
    exact h.congr_identDistrib ((identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _)

lemma prob_sum_range_sub_le_le_of_hasSubgaussianMGF {σ2 : ℝ≥0}
    (h : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    streamMeasure ν {ω | ∑ k ∈ range n, (ω k a - (ν a)[id]) ≤ -ε} ≤
      ENNReal.ofReal (Real.exp (-ε ^ 2 / (2 * n * σ2))) := by
  rw [← ofReal_measureReal]
  gcongr
  apply HasSubgaussianMGF.measure_sum_range_le_le_of_iIndepFun _ _ hε
  · exact (iIndepFun_eval_streamMeasure'' ν a).comp (fun _ x ↦ x - (ν a)[id]) (by fun_prop)
  · intro _ _
    exact h.congr_identDistrib ((identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _)

/-- Auxiliary lemma for `prob_sqrt_le_sum_range_sub_le` and `prob_sum_range_sub_le_neg_sqrt_le`. -/
private lemma exp_neg_sqrt_sq_div_le {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0) {k : ℕ} (hk : k ≠ 0) (L : ℝ) :
    Real.exp (-√(2 * k * σ2 * L) ^ 2 / (2 * k * σ2)) ≤ Real.exp (-L) := by
  rcases le_or_gt 0 L with hL | hL
  · rw [Real.sq_sqrt (by positivity)]
    gcongr
    field_simp
    rfl
  · rw [Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hL.le)]
    simpa using hL.le

/-- Upper tail of the sum of `k` i.i.d. rewards of action `a`: if the rewards are sub-Gaussian with
variance proxy `σ2`, then the sum of the centered rewards is at least `√(2 * k * σ2 * L)` with
probability at most `exp (-L)`. -/
lemma prob_sqrt_le_sum_range_sub_le {σ2 : ℝ≥0}
    (h : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0) {k : ℕ} (hk : k ≠ 0)
    (L : ℝ) :
    streamMeasure ν {ω | √(2 * k * σ2 * L) ≤ ∑ i ∈ range k, (ω i a - (ν a)[id])} ≤
      ENNReal.ofReal (Real.exp (-L)) :=
  (prob_sum_range_sub_ge_le_of_hasSubgaussianMGF h (by positivity) k).trans
    (ENNReal.ofReal_le_ofReal (exp_neg_sqrt_sq_div_le hσ2 hk L))

/-- Lower tail of the sum of `k` i.i.d. rewards of action `a`: if the rewards are sub-Gaussian with
variance proxy `σ2`, then the sum of the centered rewards is at most `-√(2 * k * σ2 * L)` with
probability at most `exp (-L)`. -/
lemma prob_sum_range_sub_le_neg_sqrt_le {σ2 : ℝ≥0}
    (h : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0) {k : ℕ} (hk : k ≠ 0)
    (L : ℝ) :
    streamMeasure ν {ω | ∑ i ∈ range k, (ω i a - (ν a)[id]) ≤ -√(2 * k * σ2 * L)} ≤
      ENNReal.ofReal (Real.exp (-L)) :=
  (prob_sum_range_sub_le_le_of_hasSubgaussianMGF h (by positivity) k).trans
    (ENNReal.ofReal_le_ofReal (exp_neg_sqrt_sq_div_le hσ2 hk L))

end StreamMeasure

/-- Auxiliary lemma for `prob_exists_sqrt_le_empMean_sub_le`: a deviation of the mean `s / k` of
`k` values is a deviation of their sum `s`. -/
private lemma sqrt_le_div_sub_iff {k : ℕ} (hk : k ≠ 0) {s μ σ L : ℝ} :
    √(2 * σ * L / k) ≤ s / k - μ ↔ √(2 * k * σ * L) ≤ s - k * μ := by
  have hk' : (0 : ℝ) < k := by positivity
  have h_sqrt : √(2 * k * σ * L) = √(2 * σ * L / k) * k :=
    calc √(2 * k * σ * L)
    _ = √(2 * σ * L / k * k ^ 2) := by field_simp
    _ = √(2 * σ * L / k) * k := by rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hk'.le]
  rw [h_sqrt, show s - k * μ = (s / k - μ) * k by field_simp, mul_le_mul_iff_of_pos_right hk']

/-- Uniform in time concentration of the empirical mean of action `a`, for rewards that are
sub-Gaussian with variance proxy `σ2`: the probability that at some time `t < n` the action `a`
has been pulled and its empirical mean exceeds its mean by at least
`√(2 * σ2 * L / pullCount A a t ω)` is at most `(n - 1) * exp (-L)`. -/
lemma prob_exists_sqrt_le_empMean_sub_le [Countable 𝓐] [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) {σ2 : ℝ≥0}
    (ha : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0) (L : ℝ) (n : ℕ) :
    P {ω | ∃ t < n, pullCount A a t ω ≠ 0 ∧
      √(2 * σ2 * L / pullCount A a t ω) ≤ empMean A R a t ω - (ν a)[id]} ≤
        ENNReal.ofReal ((n - 1) * Real.exp (-L)) := by
  refine le_trans (measure_mono ?_) (prob_exists_pullCount_ne_zero_and_sumRewards_mem_le h a n
    (B := fun m ↦ {x | √(2 * m * σ2 * L) ≤ x - m * (ν a)[id]})
    (fun _ ↦ measurableSet_le (by fun_prop) (by fun_prop)) fun m hm ↦
      le_of_eq_of_le (by simp) (StreamMeasure.prob_sqrt_le_sum_range_sub_le ha hσ2 hm L))
  rintro ω ⟨t, ht, h0, hle⟩
  exact ⟨t, ht, h0, (sqrt_le_div_sub_iff h0).1 hle⟩

/-- Uniform in time concentration of the empirical mean of action `a`, for rewards that are
sub-Gaussian with variance proxy `σ2`: the probability that at some time `t < n` the action `a`
has been pulled and its empirical mean is below its mean by at least
`√(2 * σ2 * L / pullCount A a t ω)` is at most `(n - 1) * exp (-L)`. -/
lemma prob_exists_empMean_sub_le_neg_sqrt_le [Countable 𝓐] [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) {σ2 : ℝ≥0}
    (ha : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0) (L : ℝ) (n : ℕ) :
    P {ω | ∃ t < n, pullCount A a t ω ≠ 0 ∧
      empMean A R a t ω - (ν a)[id] ≤ -√(2 * σ2 * L / pullCount A a t ω)} ≤
        ENNReal.ofReal ((n - 1) * Real.exp (-L)) := by
  refine le_trans (measure_mono ?_) (prob_exists_pullCount_ne_zero_and_sumRewards_mem_le h a n
    (B := fun m ↦ {x | x - m * (ν a)[id] ≤ -√(2 * m * σ2 * L)})
    (fun _ ↦ measurableSet_le (by fun_prop) (by fun_prop)) fun m hm ↦
      le_of_eq_of_le (by simp) (StreamMeasure.prob_sum_range_sub_le_neg_sqrt_le ha hσ2 hm L))
  rintro ω ⟨t, ht, h0, hle⟩
  have div_sub_le_neg_sqrt_iff {k : ℕ} (hk : k ≠ 0) {s μ σ L : ℝ} :
      s / k - μ ≤ -√(2 * σ * L / k) ↔ s - k * μ ≤ -√(2 * k * σ * L) := by
    have h := sqrt_le_div_sub_iff hk (s := -s) (μ := -μ) (σ := σ) (L := L)
    rw [neg_div] at h
    constructor
    · exact fun h' ↦ by linarith [h.1 (by linarith)]
    · exact fun h' ↦ by linarith [h.2 (by linarith)]
  exact ⟨t, ht, h0, (div_sub_le_neg_sqrt_iff h0).1 hle⟩

/-- Union bound over the actions in `prob_exists_sqrt_le_empMean_sub_le`. -/
lemma prob_exists_action_sqrt_le_empMean_sub_le [Fintype 𝓐] [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) {σ2 : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0) (L : ℝ)
    (n : ℕ) :
    P {ω | ∃ a, ∃ t < n, pullCount A a t ω ≠ 0 ∧
      √(2 * σ2 * L / pullCount A a t ω) ≤ empMean A R a t ω - (ν a)[id]} ≤
        ENNReal.ofReal (Fintype.card 𝓐 * (n - 1) * Real.exp (-L)) :=
  calc
    _ ≤ ∑ a, P {ω | ∃ t < n, pullCount A a t ω ≠ 0 ∧
          √(2 * σ2 * L / pullCount A a t ω) ≤ empMean A R a t ω - (ν a)[id]} := by
        rw [Set.ofPred_exists]
        exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ a, ENNReal.ofReal ((n - 1) * Real.exp (-L)) :=
        sum_le_sum fun a _ ↦ prob_exists_sqrt_le_empMean_sub_le h (hν a) hσ2 L n
    _ = ENNReal.ofReal (Fintype.card 𝓐 * (n - 1) * Real.exp (-L)) := by
      rw [sum_const, Finset.card_univ, ← ENNReal.ofReal_nsmul, nsmul_eq_mul]
      ring_nf

omit [DecidableEq 𝓐] in
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

end Subgaussian

end Bandits

/-! ### Concentration of the empirical means in a Bayesian bandit -/

namespace Learning.IsBayesAlgEnvSeq

variable {𝓔 𝓐 Ω : Type*} [MeasurableSpace 𝓔] [MeasurableSpace 𝓐] [MeasurableSpace Ω]
  [Fintype 𝓐] [DecidableEq 𝓐] [Nonempty 𝓐] [MeasurableSingletonClass 𝓐]
  {Q : Measure 𝓔} [IsProbabilityMeasure Q] {κ : Kernel (𝓔 × 𝓐) ℝ} [IsMarkovKernel κ]
  {alg : Algorithm Unit 𝓐 ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → 𝓐} {R : ℕ → Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- Uniform in time concentration of the empirical means in a Bayesian bandit: if for almost every
environment the rewards are sub-Gaussian with variance proxy `σ2`, then the probability that at
some time `t < n` the empirical mean of some action that has been pulled exceeds its mean by at
least `√(2 * σ2 * log (1 / δ) / pullCount A a t ω)` is at most `|𝓐| * (n - 1) * δ`. -/
lemma prob_empMean_sub_actionMean_ge_le (h : IsBayesAlgEnvSeq Q κ alg E A R P) {σ2 : ℝ≥0}
    (hs : ∀ᵐ e ∂Q, ∀ a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    (hσ2 : σ2 ≠ 0) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    P {ω | ∃ t < n, ∃ a, pullCount A a t ω ≠ 0 ∧
      √(2 * σ2 * Real.log (1 / δ) / pullCount A a t ω) ≤ empMean A R a t ω - actionMean κ E a ω}
      ≤ ENNReal.ofReal (Fintype.card 𝓐 * (n - 1) * δ) := by
  let S : Set (𝓔 × (ℕ → Round Unit 𝓐 ℝ)) :=
    {p | ∃ a, ∃ t < n, pullCount IT.action a t p.2 ≠ 0 ∧
      √(2 * σ2 * Real.log (1 / δ) / pullCount IT.action a t p.2) ≤
        empMean IT.action IT.feedback a t p.2 - actionMean κ id a p.1}
  refine le_trans (measure_mono ?_) (h.measure_mem_le_of_forall_isAlgEnvSeq (S := S)
    (by measurability) ?_)
  · rintro ω ⟨t, ht, a, hpc, hle⟩
    exact ⟨a, t, ht, hpc, hle⟩
  · filter_upwards [hs] with e hse P' _ he
    refine (Bandits.prob_exists_action_sqrt_le_empMean_sub_le he hse hσ2 _ n).trans_eq ?_
    simp [Real.exp_log hδ]

/-- Uniform in time concentration of the empirical mean of the best action in a Bayesian bandit: if
for almost every environment the rewards are sub-Gaussian with variance proxy `σ2`, then the
probability that at some time `t < n` the empirical mean of the best action, if it has been
pulled, is below its mean by at least `√(2 * σ2 * log (1 / δ) / pullCount A a t ω)` is at most
`(n - 1) * δ`. -/
lemma prob_empMean_bestAction_sub_actionMean_le_le (h : IsBayesAlgEnvSeq Q κ alg E A R P)
    {σ2 : ℝ≥0} (hs : ∀ᵐ e ∂Q, ∀ a, HasSubgaussianMGF (fun x ↦ x - (κ (e, a))[id]) σ2 (κ (e, a)))
    (hσ2 : σ2 ≠ 0) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    P {ω | ∃ t < n, pullCount A (bestAction κ E ω) t ω ≠ 0 ∧
        empMean A R (bestAction κ E ω) t ω - actionMean κ E (bestAction κ E ω) ω ≤
          -√(2 * σ2 * Real.log (1 / δ) / (pullCount A (bestAction κ E ω) t ω))}
      ≤ ENNReal.ofReal ((n - 1) * δ) := by
  let S : Set (𝓔 × (ℕ → Round Unit 𝓐 ℝ)) :=
    {p | ∃ t < n, pullCount IT.action (bestAction κ id p.1) t p.2 ≠ 0 ∧
      empMean IT.action IT.feedback (bestAction κ id p.1) t p.2 -
          actionMean κ id (bestAction κ id p.1) p.1 ≤
        -√(2 * σ2 * Real.log (1 / δ) / pullCount IT.action (bestAction κ id p.1) t p.2)}
  refine h.measure_mem_le_of_forall_isAlgEnvSeq (S := S) (by measurability) ?_
  filter_upwards [hs] with e hse P' _ he
  refine (Bandits.prob_exists_empMean_sub_le_neg_sqrt_le (ν := κ.sectR e) (a := bestAction κ id e)
    he (hse _) hσ2 _ n).trans_eq ?_
  simp [Real.exp_log hδ]

end Learning.IsBayesAlgEnvSeq
