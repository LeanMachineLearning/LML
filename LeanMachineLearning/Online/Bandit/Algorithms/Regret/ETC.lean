/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.Bandit.Algorithms.ETC
public import LeanMachineLearning.Online.Bandit.SumRewards

/-! # Regret bound for the Explore-Then-Commit algorithm

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning
open scoped ENNReal NNReal

namespace Bandits.ETC

variable {K : ℕ} [NeZero K] {m : ℕ} {ν : Kernel (Fin K) ℝ} [IsMarkovKernel ν]
  {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
  {σ2 : ℝ≥0}

lemma probReal_sumRewards_le_sumRewards_le
    (h : IsAlgEnvSeq O A R (etcAlgorithm K m) (Environment.bandit ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (a : Fin K) :
    P.real {ω | sumRewards A R (bestArm ν) (K * m) ω ≤ sumRewards A R a (K * m) ω} ≤
      Real.exp (-↑m * gap ν a ^ 2 / (4 * σ2)) := by
  have h1 := Bandits.probReal_sumRewards_le_sumRewards_le h a (K * m) m m
  have h2 := probReal_sum_le_sum_streamMeasure hν a m
  refine le_trans (le_of_eq ?_) (h1.trans h2)
  simp_rw [measureReal_def]
  congr 1
  refine measure_congr ?_
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [pullCount_mul h a, pullCount_mul h (bestArm ν)] with ω ha h_best
  simp [ha, h_best]

/-- The probability that at time `K * m` the ETC algorithm chooses arm `a` is at most
`exp(- m * Δ_a^2 / (4 * σ2))`. -/
lemma prob_arm_mul_eq_le (h : IsAlgEnvSeq O A R (etcAlgorithm K m) (Environment.bandit ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (a : Fin K)
    (hm : m ≠ 0) :
    P.real {ω | A (K * m) ω = a} ≤ Real.exp (- (m : ℝ) * gap ν a ^ 2 / (4 * σ2)) := by
  have h_pos : 0 < K * m := Nat.mul_pos (Nat.pos_of_neZero K) hm.bot_lt
  have h_le : P.real {ω | A (K * m) ω = a}
      ≤ P.real {ω | sumRewards A R (bestArm ν) (K * m) ω ≤ sumRewards A R a (K * m) ω} := by
    simp_rw [measureReal_def]
    gcongr 1
    · simp
    refine measure_mono_ae ?_
    exact sumRewards_bestArm_le_of_arm_mul_eq h a hm
  exact h_le.trans (probReal_sumRewards_le_sumRewards_le h hν a)

/-- Bound on the expectation of the number of pulls of each arm by the ETC algorithm. -/
lemma expectation_pullCount_le (h : IsAlgEnvSeq O A R (etcAlgorithm K m) (Environment.bandit ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a))
    (a : Fin K) (hm : m ≠ 0) {n : ℕ} (hn : K * m ≤ n) :
    P[fun ω ↦ (pullCount A a n ω : ℝ)]
      ≤ m + (n - K * m) * Real.exp (- (m : ℝ) * gap ν a ^ 2 / (4 * σ2)) := by
  have hA := h.measurable_action
  have : (fun ω ↦ (pullCount A a n ω : ℝ))
      =ᵐ[P] fun ω ↦ m + (n - K * m) * {ω' | A (K * m) ω' = a}.indicator 1 ω := by
    filter_upwards [pullCount_of_ge h a hn] with ω h
    simp only [h, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, mul_ite, mul_one, mul_zero,
      Nat.cast_add, Nat.cast_ite, CharP.cast_eq_zero, add_right_inj]
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
  rw [integral_indicator_one]
  · rw [← neg_mul]
    exact prob_arm_mul_eq_le h hν a hm
  · exact (measurableSet_singleton _).preimage (by fun_prop)

/-- Regret bound for the ETC algorithm. -/
theorem regret_le (h : IsAlgEnvSeq O A R (etcAlgorithm K m) (Environment.bandit ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hm : m ≠ 0)
    (n : ℕ) (hn : K * m ≤ n) :
    P[regret ν A n] ≤
      ∑ a, gap ν a * (m + (n - K * m) * Real.exp (- (m : ℝ) * gap ν a ^ 2 / (4 * σ2))) :=
  integral_regret_le_of_forall_integral_pullCount_le h
    (fun a _ ↦ expectation_pullCount_le h hν a hm hn)

end Bandits.ETC
