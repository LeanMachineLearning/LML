/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.Bandit.SumRewards
public import LeanMachineLearning.SequentialLearning.Algorithms.RoundRobin
public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.BorelSpace.MeasurableArgMax

/-! # The Explore-Then-Commit Algorithm

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning
open scoped ENNReal NNReal

namespace Bandits

variable {K : ℕ}

section AlgorithmDefinition

/-- Arm pulled by the ETC algorithm at time `n + 1`.
For `n < K * m - 1`, this is arm `(n + 1) % K`.
For `n = K * m - 1`, this is the arm with the highest empirical mean after the exploration phase.
For `n ≥ K * m`, this is the same arm as at time `n`. -/
noncomputable
def ETC.nextArm (hK : 0 < K) (m n : ℕ) (h : Iic n → Fin K × ℝ) : Fin K :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  if hn : n < K * m - 1 then RoundRobin.nextAction hK n
  else
    if hn_eq : n = K * m - 1 then measurableArgmax (empMean' n) h
    else (h ⟨n, by simp⟩).1

/-- The next arm pulled by ETC is chosen in a measurable way. -/
@[fun_prop]
lemma ETC.measurable_nextArm (hK : 0 < K) (m n : ℕ) : Measurable (nextArm hK m n) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  unfold nextArm
  simp only [dite_eq_ite]
  refine Measurable.ite (by simp) (by fun_prop) ?_
  refine Measurable.ite (by simp) ?_ (by fun_prop)
  exact measurable_measurableArgmax fun a ↦ by fun_prop

/-- The Explore-Then-Commit algorithm: deterministic algorithm that chooses the next arm according
to `ETC.nextArm`. -/
noncomputable
def etcAlgorithm (hK : 0 < K) (m : ℕ) : Algorithm (Fin K) ℝ :=
  detAlgorithm (ETC.nextArm hK m) (by fun_prop) ⟨0, hK⟩

end AlgorithmDefinition

namespace ETC

variable {hK : 0 < K} {m : ℕ} {ν : Kernel (Fin K) ℝ} [IsMarkovKernel ν]
  {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
  {σ2 : ℝ≥0}

/-- Until round `K * m - 1`, the ETC algorithm behaves like the Round-Robin algorithm. -/
lemma isAlgEnvSeqUntil_roundRobinAlgorithm
    (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv ν) P) :
    IsAlgEnvSeqUntil A R (roundRobinAlgorithm hK) (stationaryEnv ν) P (K * m - 1) where
  measurable_action := h.measurable_action
  measurable_feedback := h.measurable_feedback
  hasLaw_action_zero := h.hasLaw_action_zero
  hasCondDistrib_feedback_zero := h.hasCondDistrib_feedback_zero
  hasCondDistrib_action n hn := by
    convert h.hasCondDistrib_action n using 1
    simp only [roundRobinAlgorithm, detAlgorithm_policy, etcAlgorithm]
    congr 1 with h
    simp [ETC.nextArm, hn]
  hasCondDistrib_feedback n _ := h.hasCondDistrib_feedback n

section AlgorithmBehavior

lemma arm_zero (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv ν) P) :
    A 0 =ᵐ[P] fun _ ↦ ⟨0, hK⟩ :=
  RoundRobin.action_zero ((isAlgEnvSeqUntil_roundRobinAlgorithm h).mono zero_le)

lemma arm_ae_eq_etcNextArm (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv ν) P) (n : ℕ) :
    A (n + 1) =ᵐ[P] fun ω ↦ nextArm hK m n (history A R n ω) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact h.action_detAlgorithm_ae_eq n

/-- For `n < K * m`, the arm pulled at time `n` is the arm `n % K`. -/
lemma arm_of_lt (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv ν) P)
    {n : ℕ} (hn : n < K * m) :
    A n =ᵐ[P] fun _ ↦ ⟨n % K, Nat.mod_lt _ hK⟩ :=
  RoundRobin.action_ae_eq n ((isAlgEnvSeqUntil_roundRobinAlgorithm h).mono (by grind))

/-- The arm pulled at time `K * m` is the arm with the highest empirical mean after the exploration
phase. -/
lemma arm_mul [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv ν) P) (hm : m ≠ 0) :
    A (K * m) =ᵐ[P] fun ω ↦ measurableArgmax (empMean' (K * m - 1))
      (history A R (K * m - 1) ω) := by
  have : K * m = (K * m - 1) + 1 := by
    have : 0 < K * m := Nat.mul_pos hK hm.bot_lt
    grind
  rw [this]
  filter_upwards [arm_ae_eq_etcNextArm h (K * m - 1)] with ω hn_eq
  rw [hn_eq, nextArm, dif_neg (by simp), dif_pos rfl]
  exact this ▸ rfl

/-- For `n ≥ K * m`, the arm pulled at time `n + 1` is the same as the arm pulled at time `n`. -/
lemma arm_add_one_of_ge (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv ν) P)
    {n : ℕ} (hm : m ≠ 0) (hn : K * m ≤ n) :
    A (n + 1) =ᵐ[P] fun ω ↦ A n ω := by
  filter_upwards [arm_ae_eq_etcNextArm h n] with ω hn_eq
  rw [hn_eq, nextArm, dif_neg (by grind), dif_neg]
  · rfl
  · have : 0 < K * m := Nat.mul_pos hK hm.bot_lt
    grind

/-- For `n ≥ K * m`, the arm pulled at time `n` is the same as the arm pulled at time `K * m`. -/
lemma arm_of_ge (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv ν) P)
    {n : ℕ} (hm : m ≠ 0) (hn : K * m ≤ n) :
    A n =ᵐ[P] A (K * m) := by
  have h_ae n : K * m ≤ n → A (n + 1) =ᵐ[P] fun ω ↦ A n ω := arm_add_one_of_ge h hm
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at h_ae
  filter_upwards [h_ae] with ω h_ae
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hmn h_ind => rw [h_ae n hmn, h_ind]

/-- At time `K * m`, the number of pulls of each arm is equal to `m`. -/
lemma pullCount_mul (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv ν) P) (a : Fin K) :
    pullCount A a (K * m) =ᵐ[P] fun _ ↦ m :=
  RoundRobin.pullCount_mul m (isAlgEnvSeqUntil_roundRobinAlgorithm h) a

lemma pullCount_add_one_of_ge (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv ν) P)
    (a : Fin K) (hm : m ≠ 0) {n : ℕ} (hn : K * m ≤ n) :
    pullCount A a (n + 1)
      =ᵐ[P] fun ω ↦ pullCount A a n ω + {ω' | A (K * m) ω' = a}.indicator (fun _ ↦ 1) ω := by
  simp_rw [Filter.EventuallyEq, pullCount_add_one]
  filter_upwards [arm_of_ge h hm hn] with ω h_arm
  congr 3

/-- For `n ≥ K * m`, the number of pulls of each arm `a` at time `n` is equal to `m` plus
`n - K * m` if arm `a` is the best arm after the exploration phase. -/
lemma pullCount_of_ge (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv ν) P)
    (a : Fin K) (hm : m ≠ 0) {n : ℕ} (hn : K * m ≤ n) :
    pullCount A a n
      =ᵐ[P] fun ω ↦ m + (n - K * m) * {ω' | A (K * m) ω' = a}.indicator (fun _ ↦ 1) ω := by
  have h_ae n : K * m ≤ n → pullCount A a (n + 1)
      =ᵐ[P] fun ω ↦ pullCount A a n ω + {ω' | A (K * m) ω' = a}.indicator (fun _ ↦ 1) ω :=
    pullCount_add_one_of_ge h a hm
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at h_ae
  have h_ae_Km : pullCount A a (K * m) =ᵐ[P] fun _ ↦ m := pullCount_mul h a
  filter_upwards [h_ae_Km, h_ae] with ω h_Km h_ae
  induction n, hn using Nat.le_induction with
  | base => simp [h_Km]
  | succ n hmn h_ind =>
    rw [h_ae n hmn, h_ind, add_assoc, ← add_one_mul]
    congr
    grind

/-- If at time `K * m` the algorithm chooses arm `a`, then the total reward obtained by pulling
arm `a` is at least the total reward obtained by pulling the best arm. -/
lemma sumRewards_bestArm_le_of_arm_mul_eq [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv ν) P) (a : Fin K) (hm : m ≠ 0) :
    ∀ᵐ h ∂P, A (K * m) h = a → sumRewards A R (bestArm ν) (K * m) h ≤
      sumRewards A R a (K * m) h := by
  filter_upwards [arm_mul h hm, pullCount_mul h a, pullCount_mul h (bestArm ν)]
    with h h_arm ha h_best h_eq
  have h_max := isMaxOn_measurableArgmax (empMean' (K * m - 1)) (history A R (K * m - 1) h)
    (bestArm ν)
  rw [← h_arm, h_eq] at h_max
  rw [sumRewards_eq_pullCount_mul_empMean, sumRewards_eq_pullCount_mul_empMean, ha, h_best]
  · gcongr
    have : 0 < K * m := Nat.mul_pos hK hm.bot_lt
    rwa [empMean_eq_empMean' this.ne', empMean_eq_empMean' this.ne']
  · simp [ha, hm]
  · simp [h_best, hm]

end AlgorithmBehavior

section Regret

lemma probReal_sumRewards_le_sumRewards_le [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (a : Fin K) :
    P.real {ω | sumRewards A R (bestArm ν) (K * m) ω ≤ sumRewards A R a (K * m) ω} ≤
      Real.exp (-↑m * gap ν a ^ 2 / (4 * σ2)) := by
  have h1 := Bandits.probReal_sumRewards_le_sumRewards_le h a (K * m) m m
  have h2 := probReal_sum_le_sum_streamMeasure hν a m
  refine le_trans (le_of_eq ?_) (h1.trans h2)
  simp_rw [measureReal_def]
  congr 1
  refine measure_congr ?_
  rw [Filter.eventuallyEq_set]
  filter_upwards [pullCount_mul h a, pullCount_mul h (bestArm ν)] with ω ha h_best
  simp [ha, h_best]

/-- The probability that at time `K * m` the ETC algorithm chooses arm `a` is at most
`exp(- m * Δ_a^2 / 4)`. -/
lemma prob_arm_mul_eq_le [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (a : Fin K)
    (hm : m ≠ 0) :
    P.real {ω | A (K * m) ω = a} ≤ Real.exp (- (m : ℝ) * gap ν a ^ 2 / (4 * σ2)) := by
  have h_pos : 0 < K * m := Nat.mul_pos hK hm.bot_lt
  have h_le : P.real {ω | A (K * m) ω = a}
      ≤ P.real {ω | sumRewards A R (bestArm ν) (K * m) ω ≤ sumRewards A R a (K * m) ω} := by
    simp_rw [measureReal_def]
    gcongr 1
    · simp
    refine measure_mono_ae ?_
    exact sumRewards_bestArm_le_of_arm_mul_eq h a hm
  exact h_le.trans (probReal_sumRewards_le_sumRewards_le h hν a)

/-- Bound on the expectation of the number of pulls of each arm by the ETC algorithm. -/
lemma expectation_pullCount_le [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a))
    (a : Fin K) (hm : m ≠ 0) {n : ℕ} (hn : K * m ≤ n) :
    P[fun ω ↦ (pullCount A a n ω : ℝ)]
      ≤ m + (n - K * m) * Real.exp (- (m : ℝ) * gap ν a ^ 2 / (4 * σ2)) := by
  have hA := h.measurable_action
  have : (fun ω ↦ (pullCount A a n ω : ℝ))
      =ᵐ[P] fun ω ↦ m + (n - K * m) * {ω' | A (K * m) ω' = a}.indicator (fun _ ↦ 1) ω := by
    filter_upwards [pullCount_of_ge h a hm hn] with ω h
    simp only [h, Set.indicator_apply, Set.mem_setOf_eq, mul_ite, mul_one, mul_zero, Nat.cast_add,
      Nat.cast_ite, CharP.cast_eq_zero, add_right_inj]
    norm_cast
  rw [integral_congr_ae this, integral_add (integrable_const _), integral_const_mul]
  swap
  · refine Integrable.const_mul ?_ _
    rw [integrable_indicator_iff]
    · exact integrableOn_const
    · exact (measurableSet_singleton _).preimage (by fun_prop)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, neg_mul, add_le_add_iff_left]
  gcongr
  · norm_cast
    simp
  rw [integral_indicator_const, smul_eq_mul, mul_one]
  · rw [← neg_mul]
    exact prob_arm_mul_eq_le h hν a hm
  · exact (measurableSet_singleton _).preimage (by fun_prop)

/-- Regret bound for the ETC algorithm. -/
theorem regret_le [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hm : m ≠ 0)
    (n : ℕ) (hn : K * m ≤ n) :
    P[regret ν A n] ≤
      ∑ a, gap ν a * (m + (n - K * m) * Real.exp (- (m : ℝ) * gap ν a ^ 2 / (4 * σ2))) :=
  integral_regret_le_of_forall_integral_pullCount_le h
    (fun a _ ↦ expectation_pullCount_le h hν a hm hn)

end Regret

end ETC

end Bandits
