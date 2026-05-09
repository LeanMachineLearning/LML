/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.Probability.Kernel.Composition.MapComap
public import LeanMachineLearning.SequentialLearning.Algorithm

/-!
# Oblivious and stationary environments

An oblivious environment is an environment in which the distribution of the next reward depends only
on the last action (and not on the past history).
If the kernel that gives the distribution of the next reward given the last action is the same at
every time step, then we say that the environment is stationary.

## Main definitions

We define a `Prop`-valued typeclass `IsObliviousEnv` to express that an environment is oblivious,
and we define two constructors for oblivious environments.

Typeclass and related definitions:
* `IsObliviousEnv env`: the environment `env` is oblivious.
* `feedbackCondAction env n`: the kernel representing the conditional distribution of the feedback
  given the action at time `n` in an oblivious environment `env`.

Constructors for oblivious environments:
* `obliviousEnv ν`: an oblivious environment, in which the distribution of the next reward depends
  only on the last action, but in a possibly time-dependent manner, and is given by a sequence of
  Markov kernels `ν : ℕ → Kernel α R`.
* `stationaryEnv ν`: a stationary environment, in which the distribution of the next reward depends
  only on the last action (and not on the past history), and is given by a Markov kernel
  `ν : Kernel α R`.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Learning

variable {α R : Type*} {mα : MeasurableSpace α} {mR : MeasurableSpace R}

/-- An environment is oblivious if the distribution of the next feedback depends only on
the last action and not on the past history. -/
class IsObliviousEnv (env : Environment α R) : Prop where
  exists_eq_prodMkLeft : ∃ ν : ℕ → Kernel α R, (∀ n, IsMarkovKernel (ν n)) ∧
    (env.ν0 = ν 0) ∧ (∀ n, env.feedback n = (ν (n + 1)).prodMkLeft _)

/-- The kernel representing the conditional distribution of the feedback given the action
at time `n` in an oblivious environment. -/
noncomputable
def feedbackCondAction (env : Environment α R) [h_obl : IsObliviousEnv env] (n : ℕ) : Kernel α R :=
  h_obl.exists_eq_prodMkLeft.choose n

instance (env : Environment α R) [IsObliviousEnv env] (n : ℕ) :
    IsMarkovKernel (feedbackCondAction env n) :=
  IsObliviousEnv.exists_eq_prodMkLeft.choose_spec.1 n

lemma ν0_eq_feedbackCondAction (env : Environment α R) [IsObliviousEnv env] :
    env.ν0 = feedbackCondAction env 0 :=
  IsObliviousEnv.exists_eq_prodMkLeft.choose_spec.2.1

lemma feedback_eq_feedbackCondAction (env : Environment α R) [IsObliviousEnv env] (n : ℕ) :
    env.feedback n = (feedbackCondAction env (n + 1)).prodMkLeft _ :=
  IsObliviousEnv.exists_eq_prodMkLeft.choose_spec.2.2 n

namespace IsObliviousEnv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
  {alg : Algorithm α R} {env : Environment α R} {P : Measure Ω} [IsFiniteMeasure P]
  {A : ℕ → Ω → α} {R' : ℕ → Ω → R} {n N : ℕ}
  {ν : ℕ → Kernel α R} [∀ n, IsMarkovKernel (ν n)]

lemma hasCondDistrib_reward [IsObliviousEnv env] (h : IsAlgEnvSeq A R' alg env P) (n : ℕ) :
    HasCondDistrib (R' n) (A n) (feedbackCondAction env n) P := by
  have hA := h.measurable_action
  have hR' := h.measurable_feedback
  cases n with
  | zero => rw [← ν0_eq_feedbackCondAction]; exact h.hasCondDistrib_feedback_zero
  | succ n =>
    refine ⟨by fun_prop, by fun_prop, ?_⟩
    have h_eq := (h.hasCondDistrib_feedback n).condDistrib_eq
    rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)] at h_eq ⊢
    have : P.map (A (n + 1)) =
        (P.map (fun x ↦ (IsAlgEnvSeq.hist A R' n x, A (n + 1) x))).snd := by
      rw [Measure.snd_map_prodMk (by fun_prop)]
    simp only [feedback_eq_feedbackCondAction] at h_eq
    rw [this, ← Measure.snd_prodAssoc_compProd_prodMkLeft, ← h_eq,
      Measure.snd_map_prodMk (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    congr

/-- The reward at time `n + 1` is conditionally independent of the history up to time `n`
given the action at time `n + 1`. -/
lemma condIndepFun_reward_hist_action [StandardBorelSpace Ω]
        [IsObliviousEnv env] (h : IsAlgEnvSeq A R' alg env P) (n : ℕ) :
    R' (n + 1) ⟂ᵢ[A (n + 1), h.measurable_action _ ; P] IsAlgEnvSeq.hist A R' n := by
  have hA := h.measurable_action
  have hR' := h.measurable_feedback
  refine condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    (η := feedbackCondAction env (n + 1))
    (by fun_prop) (by fun_prop) (by fun_prop) ?_
  refine HasCondDistrib.condDistrib_eq ?_
  rw [← feedback_eq_feedbackCondAction]
  exact h.hasCondDistrib_feedback n

lemma condIndepFun_reward_hist_action_action [StandardBorelSpace Ω]
    [IsObliviousEnv env] (h : IsAlgEnvSeq A R' alg env P) (n : ℕ) :
    R' (n + 1) ⟂ᵢ[A (n + 1), h.measurable_action (n + 1); P]
      (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω)) := by
  have h_indep : R' (n + 1) ⟂ᵢ[A (n + 1), h.measurable_action (n + 1); P] IsAlgEnvSeq.hist A R' n :=
    condIndepFun_reward_hist_action h n
  have hA := h.measurable_action
  have hR' := h.measurable_feedback
  exact h_indep.prod_right (by fun_prop) (by fun_prop) (by fun_prop)

lemma condIndepFun_reward_hist_action_action' [StandardBorelSpace Ω]
        [IsObliviousEnv env] (h : IsAlgEnvSeq A R' alg env P) (n : ℕ) (hn : n ≠ 0) :
    R' n ⟂ᵢ[A n, h.measurable_action n; P] (fun ω ↦ (IsAlgEnvSeq.hist A R' (n - 1) ω, A n ω)) := by
  have := condIndepFun_reward_hist_action_action h (n - 1)
  grind

end IsObliviousEnv

/-- An oblivious environment, in which the distribution of the next reward depends only on the last
action, but in a possibly time-dependent manner. -/
@[simps]
-- ANCHOR: obliviousEnv
def obliviousEnv (ν : ℕ → Kernel α R) [∀ n, IsMarkovKernel (ν n)] : Environment α R where
  feedback n := (ν (n + 1)).prodMkLeft _
  ν0 := ν 0
-- ANCHOR_END: obliviousEnv

@[simp]
lemma feedback_obliviousEnv (ν : ℕ → Kernel α R) [∀ n, IsMarkovKernel (ν n)] (n : ℕ) :
    (obliviousEnv ν).feedback n = (ν (n + 1)).prodMkLeft _ := by simp [obliviousEnv]

@[simp]
lemma ν0_obliviousEnv (ν : ℕ → Kernel α R) [∀ n, IsMarkovKernel (ν n)] :
    (obliviousEnv ν).ν0 = ν 0 := by simp [obliviousEnv]

instance (ν : ℕ → Kernel α R) [∀ n, IsMarkovKernel (ν n)] :
    IsObliviousEnv (obliviousEnv ν) where
  exists_eq_prodMkLeft := ⟨fun n ↦ ν n, inferInstance,rfl, fun _ ↦ rfl⟩

@[simp]
lemma feedbackCondAction_obliviousEnv (ν : ℕ → Kernel α R) [hν : ∀ n, IsMarkovKernel (ν n)]
    (n : ℕ) :
    feedbackCondAction (obliviousEnv ν) n = ν n := by
  rcases isEmpty_or_nonempty α with hα | hα
  · ext a : 1
    exact hα.elim a
  rcases isEmpty_or_nonempty R with hR | hR
  · refine absurd (hν 0) ?_
    simp only [Subsingleton.eq_zero ν, Pi.zero_apply]
    exact Kernel.not_isMarkovKernel_zero
  have : Nonempty (Iic n → α × R) := ⟨fun _ ↦ (hα.some, hR.some)⟩
  have h_eq_zero := ν0_eq_feedbackCondAction (obliviousEnv ν)
  have h_eq := feedback_eq_feedbackCondAction (obliviousEnv ν) (n - 1)
  cases n with
  | zero => exact h_eq_zero.symm
  | succ n =>
    simp only [Nat.add_one_sub_one, obliviousEnv_feedback, add_tsub_cancel_right] at h_eq
    rw [← Kernel.prodMkLeft_inj (γ := Iic n → α × R)]
    exact h_eq.symm

/-- A stationary environment, in which the distribution of the next reward depends only on the last
action. -/
-- ANCHOR: stationaryEnv
def stationaryEnv (ν : Kernel α R) [IsMarkovKernel ν] : Environment α R := obliviousEnv fun _ ↦ ν
-- ANCHOR_END: stationaryEnv

@[simp]
lemma feedback_stationaryEnv (ν : Kernel α R) [IsMarkovKernel ν] (n : ℕ) :
    (stationaryEnv ν).feedback n = ν.prodMkLeft _ := by simp [stationaryEnv]

@[simp]
lemma ν0_stationaryEnv (ν : Kernel α R) [IsMarkovKernel ν] : (stationaryEnv ν).ν0 = ν := by
  simp [stationaryEnv]

instance (ν : Kernel α R) [IsMarkovKernel ν] : IsObliviousEnv (stationaryEnv ν) where
  exists_eq_prodMkLeft := ⟨fun _ ↦ ν, inferInstance, rfl, fun _ ↦ rfl⟩

@[simp]
lemma feedbackCondAction_stationaryEnv (ν : Kernel α R) [hν : IsMarkovKernel ν] (n : ℕ) :
    feedbackCondAction (stationaryEnv ν) n = ν := feedbackCondAction_obliviousEnv _ _

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
  {alg : Algorithm α R} {ν : Kernel α R} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → α} {R' : ℕ → Ω → R}

namespace IsAlgEnvSeq

/-- The conditional distribution of the reward at time `n` given the action at time `n` is `ν`. -/
lemma hasCondDistrib_reward_stationaryEnv
    (h : IsAlgEnvSeq A R' alg (stationaryEnv ν) P) (n : ℕ) :
    HasCondDistrib (R' n) (A n) ν P := by
  simpa using IsObliviousEnv.hasCondDistrib_reward h n

/-- The conditional distribution of the reward at time `n` given the action at time `n` is `ν`. -/
lemma condDistrib_reward_stationaryEnv
    (h : IsAlgEnvSeq A R' alg (stationaryEnv ν) P) (n : ℕ) :
    condDistrib (R' n) (A n) P =ᵐ[P.map (A n)] ν :=
  (hasCondDistrib_reward_stationaryEnv h n).condDistrib_eq

/-- The reward at time `n + 1` is conditionally independent of the history up to time `n`
given the action at time `n + 1`. -/
lemma condIndepFun_reward_hist_action [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A R' alg (stationaryEnv ν) P) (n : ℕ) :
    R' (n + 1) ⟂ᵢ[A (n + 1), h.measurable_action _ ; P] hist A R' n :=
  IsObliviousEnv.condIndepFun_reward_hist_action h n

lemma condIndepFun_reward_hist_action_action [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A R' alg (stationaryEnv ν) P) (n : ℕ) :
    R' (n + 1) ⟂ᵢ[A (n + 1), h.measurable_action (n + 1); P]
      (fun ω ↦ (hist A R' n ω, A (n + 1) ω)) :=
  IsObliviousEnv.condIndepFun_reward_hist_action_action h n

lemma condIndepFun_reward_hist_action_action' [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A R' alg (stationaryEnv ν) P) (n : ℕ) (hn : n ≠ 0) :
    R' n ⟂ᵢ[A n, h.measurable_action n; P] (fun ω ↦ (hist A R' (n - 1) ω, A n ω)) :=
  IsObliviousEnv.condIndepFun_reward_hist_action_action' h n hn

end IsAlgEnvSeq

end Learning
