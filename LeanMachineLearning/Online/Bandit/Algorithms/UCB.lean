/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.Bandit.Regret
public import LeanMachineLearning.SequentialLearning.Algorithms.RoundRobin
public import LeanMachineLearning.SequentialLearning.SumRewards
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg

/-!
# UCB algorithm

The Upper Confidence Bound (UCB) algorithm with exploration parameter `c` for a bandit with `K`
arms pulls each arm once (in rounds `0` to `K - 1`), then at each time `n ≥ K` pulls an arm that
maximizes the index `empMean A R a n + √(2 * c * log (n + 1) / pullCount A a n)`: the empirical
mean of the arm plus an exploration bonus, which is the width of a confidence interval for the mean.

## Main definitions

* `UCB.ucbWidth' c n h a`: exploration bonus of arm `a` at time `n`, given the history `h`.
* `UCB.nextArm K c n h`: arm pulled by UCB at time `n`, given the history `h` before `n`.
* `ucbAlgorithm K c`: the UCB algorithm.

## Main statements

* `UCB.ucbIndex_le_ucbIndex_arm`: for `n ≥ K`, the index of the arm pulled at time `n` is at least
  the index of any other arm.

## References

* P. Auer, N. Cesa-Bianchi and P. Fischer, *Finite-time analysis of the multiarmed bandit problem*,
  Machine Learning, 2002.
* T. Lattimore and C. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapters 7 and 8.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset Learning

open scoped ENNReal NNReal

namespace Bandits

variable {K : ℕ}

section Algorithm

/-- The exploration bonus of the UCB algorithm, which corresponds to the width of
a confidence interval. -/
noncomputable def UCB.ucbWidth' (c : ℝ) (n : ℕ) (h : Hist Unit (Fin K) ℝ n) (a : Fin K) : ℝ :=
  √(2 * c * log (n + 1) / pullCount' n h a)

@[fun_prop]
lemma UCB.measurable_ucbWidth' (c : ℝ) (n : ℕ) (a : Fin K) :
    Measurable (fun h : Hist Unit (Fin K) ℝ n ↦ ucbWidth' c n h a) := by
  unfold ucbWidth'
  fun_prop

/-- Arm pulled by the UCB algorithm at time `n`, as a function of the history before `n`. -/
noncomputable
def UCB.nextArm (K : ℕ) [NeZero K] (c : ℝ) (n : ℕ) (h : Hist Unit (Fin K) ℝ n) : Fin K :=
  if n < K then RoundRobin.nextAction K n else
  argmax (fun a ↦ empMean' n h a + ucbWidth' c n h a)

/-- The next-arm function of UCB is measurable. -/
@[fun_prop]
lemma UCB.measurable_nextArm [NeZero K] (c : ℝ) (n : ℕ) : Measurable (nextArm K c n) := by
  unfold nextArm
  split_ifs <;> fun_prop

variable (K) in
/-- The UCB algorithm. -/
noncomputable
def ucbAlgorithm [NeZero K] (c : ℝ) : Algorithm Unit (Fin K) ℝ :=
  Algorithm.deterministic (fun n p ↦ UCB.nextArm K c n p.1) (by fun_prop)
end Algorithm

namespace UCB

variable [NeZero K] {c : ℝ} {ν : Kernel (Fin K) ℝ} [IsMarkovKernel ν]
  {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
  {σ2 : ℝ≥0} {n : ℕ} {ω : Ω}

omit [IsProbabilityMeasure P] in
/-- Before round `K`, the UCB algorithm behaves like the Round-Robin algorithm. -/
lemma isAlgEnvSeqUntil_roundRobin
    (h : IsAlgEnvSeq O A R (ucbAlgorithm K c) (Environment.bandit ν) P) :
    IsAlgEnvSeqUntil O A R (Algorithm.roundRobin K) (Environment.bandit ν) P K := by
  refine h.isAlgEnvSeqUntil_of_policy_eq fun n hn ↦ ?_
  simp only [Algorithm.roundRobin, Algorithm.deterministic_policy, ucbAlgorithm]
  congr 1 with p
  simp [UCB.nextArm, hn]

section AlgorithmBehavior

/-- The exploration bonus of the UCB algorithm, which corresponds to the width of
a confidence interval. -/
noncomputable def ucbWidth (A : ℕ → Ω → Fin K) (c : ℝ) (a : Fin K) (n : ℕ) (ω : Ω) : ℝ :=
  √(2 * c * log (n + 1) / pullCount A a n ω)

omit [NeZero K] in
@[fun_prop]
lemma measurable_ucbWidth (hA : ∀ n, Measurable (A n)) (c : ℝ) (a : Fin K) :
    Measurable (ucbWidth A c a n) := by
  unfold ucbWidth
  fun_prop

omit [NeZero K] in
lemma ucbWidth_eq_ucbWidth' (c : ℝ) (a : Fin K) (n : ℕ) (ω : Ω) :
    ucbWidth A c a n ω = ucbWidth' c n (history O A R n ω) a := by
  rw [ucbWidth, ucbWidth', pullCount_eq_pullCount' (O := O) (A := A) (R' := R)]

lemma arm_zero (h : IsAlgEnvSeq O A R (ucbAlgorithm K c) (Environment.bandit ν) P) :
    A 0 =ᵐ[P] fun _ ↦ 0 :=
  RoundRobin.action_zero ((isAlgEnvSeqUntil_roundRobin h).mono (Nat.pos_of_neZero K))

lemma arm_ae_eq_nextArm (h : IsAlgEnvSeq O A R (ucbAlgorithm K c) (Environment.bandit ν) P)
    (n : ℕ) :
    A n =ᵐ[P] fun ω ↦ nextArm K c n (history O A R n ω) :=
  h.action_ae_eq_deterministic n

lemma ucbIndex_le_ucbIndex_arm
    (h : IsAlgEnvSeq O A R (ucbAlgorithm K c) (Environment.bandit ν) P) (a : Fin K) (hn : K ≤ n) :
    ∀ᵐ ω ∂P, empMean A R a n ω + ucbWidth A c a n ω ≤
      empMean A R (A n ω) n ω + ucbWidth A c (A n ω) n ω := by
  filter_upwards [arm_ae_eq_nextArm h n] with ω h_arm
  have h_not_lt : ¬ n < K := by grind
  simp only [nextArm, h_not_lt, ↓reduceIte] at h_arm
  simp_rw [h_arm, empMean_eq_empMean' (O := O), ucbWidth_eq_ucbWidth' (O := O) (A := A) (R := R)]
  exact isMaxOn_univ_iff.1 (isMaxOn_argmax (fun a ↦ empMean' n (history O A R n ω) a
    + ucbWidth' c n (history O A R n ω) a)) _

lemma forall_arm_eq_mod_of_lt (h : IsAlgEnvSeq O A R (ucbAlgorithm K c) (Environment.bandit ν) P) :
    ∀ᵐ ω ∂P, ∀ n < K, A n ω = RoundRobin.nextAction K n := by
  simp_rw [ae_all_iff]
  intro n hn
  filter_upwards [arm_ae_eq_nextArm h n] with ω h_eq
  rw [h_eq]
  simp only [nextArm, hn, ↓reduceIte]

lemma forall_ucbIndex_le_ucbIndex_arm
    (h : IsAlgEnvSeq O A R (ucbAlgorithm K c) (Environment.bandit ν) P) (a : Fin K) :
    ∀ᵐ ω ∂P, ∀ n, K ≤ n →
      empMean A R a n ω + ucbWidth A c a n ω ≤
        empMean A R (A n ω) n ω + ucbWidth A c (A n ω) n ω := by
  simp_rw [ae_all_iff]
  exact fun _ ↦ ucbIndex_le_ucbIndex_arm h a

lemma time_gt_of_pullCount_gt_one
    (h : IsAlgEnvSeq O A R (ucbAlgorithm K c) (Environment.bandit ν) P) (a : Fin K) :
    ∀ᵐ ω ∂P, ∀ n, 1 < pullCount A a n ω → K < n :=
  RoundRobin.time_gt_of_pullCount_gt_one (isAlgEnvSeqUntil_roundRobin h) a

lemma pullCount_pos_of_pullCount_gt_one
    (h : IsAlgEnvSeq O A R (ucbAlgorithm K c) (Environment.bandit ν) P) (a : Fin K) :
    ∀ᵐ ω ∂P, ∀ n, 1 < pullCount A a n ω → ∀ b : Fin K, 0 < pullCount A b n ω :=
  RoundRobin.pullCount_pos_of_pullCount_gt_one (isAlgEnvSeqUntil_roundRobin h) a

end AlgorithmBehavior

end UCB

end Bandits
