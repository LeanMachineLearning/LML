/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Kernel.Basic
public import LeanMachineLearning.SequentialLearning.Algorithm

/-!
# Deterministic algorithms and environments

A deterministic algorithm chooses its action in a deterministic way. That is, that action is given
by a measurable function of the history and of the current observation instead of a general Markov
kernel. Similarly, a deterministic environment gives feedback in a deterministic way.

## Main definitions

We introduce two typeclasses `Algorithm.IsDeterministic` and
`Environment.HasDeterministicFeedback` to express that an algorithm is deterministic or that an
environment gives deterministic feedback. We also give definitions for the initial action
and the next action of a deterministic algorithm, and for the feedback functions of a deterministic
environment. Finally, we give a construction of a deterministic algorithm and environment from
measurable functions.

* `Algorithm.IsDeterministic alg`: a typeclass expressing that the algorithm `alg` is
  deterministic.
* `Environment.HasDeterministicFeedback env`: a typeclass expressing that the feedback of the
  environment `env` is deterministic.
* `Algorithm.nextAction alg n`: the function that gives the action of a deterministic algorithm
  `alg` at step `n`, as a function of the history before `n` and of the observation at step `n`.
* `Algorithm.actionZero alg`: the initial action of a deterministic algorithm `alg`, as a function
  of the first observation. This is `alg.nextAction 0` applied to the empty history.
* `Environment.feedbackFun env n`: the function that gives the feedback of a deterministic
  environment `env` at step `n`, as a function of the history, the current observation and the
  current action.
* `Environment.feedbackFunZero env`: the function that gives the initial feedback of a
  deterministic environment `env`. This is `env.feedbackFun 0` applied to the empty history.

* `Algorithm.deterministic nextA h_next`: a deterministic algorithm that chooses its action
  according to the measurable function `nextA` (with proof of measurability `h_next`).
  The initial action is `fun o ↦ nextA 0 (default, o)`.
* `Environment.detFeedback obs f hf`: an environment with observation kernels `obs`, that gives
  deterministic feedback according to the measurable function `f` (with proof of measurability
  `hf`).

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}

/-- An algorithm is deterministic if its actions are determined by measurable functions of the
history and of the current observation (and not possibly random kernels). -/
class Algorithm.IsDeterministic (alg : Algorithm 𝓞 𝓐 𝓨) : Prop where
  exists_nextAction n : ∃ (nextAction : (Hist 𝓞 𝓐 𝓨 n × 𝓞) → 𝓐) (h_meas : Measurable nextAction),
    alg.policy n = Kernel.deterministic nextAction h_meas

namespace Algorithm

/-- The action of a deterministic algorithm at step `n`, as a function of the history before `n`
and of the observation at step `n`. -/
noncomputable
def nextAction (alg : Algorithm 𝓞 𝓐 𝓨) [h_det : alg.IsDeterministic] (n : ℕ) :
    (Hist 𝓞 𝓐 𝓨 n × 𝓞) → 𝓐 :=
  (h_det.exists_nextAction n).choose

/-- The initial action of a deterministic algorithm, as a function of the first observation. -/
noncomputable
def actionZero (alg : Algorithm 𝓞 𝓐 𝓨) [alg.IsDeterministic] : 𝓞 → 𝓐 :=
  fun o ↦ alg.nextAction 0 (default, o)

@[fun_prop]
lemma measurable_nextAction (alg : Algorithm 𝓞 𝓐 𝓨) [alg.IsDeterministic] (n : ℕ) :
    Measurable (alg.nextAction n) :=
  (IsDeterministic.exists_nextAction n).choose_spec.choose

@[fun_prop]
lemma measurable_actionZero (alg : Algorithm 𝓞 𝓐 𝓨) [alg.IsDeterministic] :
    Measurable alg.actionZero :=
  (alg.measurable_nextAction 0).comp (measurable_const.prodMk measurable_id)

lemma policy_eq_deterministic (alg : Algorithm 𝓞 𝓐 𝓨) [h_det : alg.IsDeterministic] (n : ℕ) :
    alg.policy n = Kernel.deterministic (alg.nextAction n) (alg.measurable_nextAction n) :=
  (IsDeterministic.exists_nextAction n).choose_spec.choose_spec

lemma nextAction_zero (alg : Algorithm 𝓞 𝓐 𝓨) [alg.IsDeterministic] (h : Hist 𝓞 𝓐 𝓨 0)
    (o : 𝓞) :
    alg.nextAction 0 (h, o) = alg.actionZero o := by
  rw [Unique.eq_default h]
  rfl

lemma policyZero_eq_deterministic (alg : Algorithm 𝓞 𝓐 𝓨) [alg.IsDeterministic] :
    alg.policyZero = Kernel.deterministic alg.actionZero alg.measurable_actionZero := by
  ext o : 1
  rw [policyZero_apply, policy_eq_deterministic, Kernel.deterministic_apply,
    Kernel.deterministic_apply]
  rfl

end Algorithm

namespace Algorithm.IsDeterministic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨} {P : Measure Ω} [IsFiniteMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {n N : ℕ}

lemma action_ae_eq_of_IsAlgEnvSeqUntil [MeasurableEq 𝓐]
    [h_det : alg.IsDeterministic] (h : IsAlgEnvSeqUntil O A Y alg env P N) (hn : n < N) :
    A n =ᵐ[P] fun ω ↦ alg.nextAction n (history O A Y n ω, O n ω) := by
  have h_eq := (h.hasCondDistrib_action n hn)
  rw [alg.policy_eq_deterministic n] at h_eq
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  exact ae_eq_of_hasCondDistrib_deterministic (measurable_nextAction _ _) (by fun_prop)
    (by fun_prop) h_eq

lemma action_zero_of_IsAlgEnvSeqUntil [MeasurableEq 𝓐] [h_det : alg.IsDeterministic]
    (h : IsAlgEnvSeqUntil O A Y alg env P N) (hN : 0 < N) :
    A 0 =ᵐ[P] fun ω ↦ alg.actionZero (O 0 ω) := by
  filter_upwards [action_ae_eq_of_IsAlgEnvSeqUntil h hN] with ω hω
  rw [hω, nextAction_zero]

lemma hasCondDistrib_action_zero_of_IsAlgEnvSeqUntil [h_det : alg.IsDeterministic]
    (h : IsAlgEnvSeqUntil O A Y alg env P N) (hN : 0 < N) :
    HasCondDistrib (A 0) (O 0)
      (Kernel.deterministic alg.actionZero alg.measurable_actionZero) P := by
  rw [← policyZero_eq_deterministic]
  exact h.hasCondDistrib_action_zero hN

lemma hasCondDistrib_action_zero [h_det : alg.IsDeterministic]
    (h : IsAlgEnvSeq O A Y alg env P) :
    HasCondDistrib (A 0) (O 0)
      (Kernel.deterministic alg.actionZero alg.measurable_actionZero) P :=
  hasCondDistrib_action_zero_of_IsAlgEnvSeqUntil (h.isAlgEnvSeqUntil 1) zero_lt_one

lemma action_ae_eq [MeasurableEq 𝓐] [h_det : alg.IsDeterministic]
    (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    A n =ᵐ[P] fun ω ↦ alg.nextAction n (history O A Y n ω, O n ω) :=
  action_ae_eq_of_IsAlgEnvSeqUntil (h.isAlgEnvSeqUntil (n + 1)) n.lt_succ_self

lemma action_zero_ae_eq [MeasurableEq 𝓐] [h_det : alg.IsDeterministic]
    (h : IsAlgEnvSeq O A Y alg env P) :
    A 0 =ᵐ[P] fun ω ↦ alg.actionZero (O 0 ω) :=
  action_zero_of_IsAlgEnvSeqUntil (h.isAlgEnvSeqUntil 1) zero_lt_one

lemma action_ae_all_eq [MeasurableEq 𝓐] [h_det : alg.IsDeterministic]
    (h : IsAlgEnvSeq O A Y alg env P) :
    ∀ᵐ ω ∂P, ∀ n, A n ω = alg.nextAction n (history O A Y n ω, O n ω) :=
  ae_all_iff.mpr (action_ae_eq h)

end Algorithm.IsDeterministic

/-- An environment has deterministic feedback if its feedbacks are determined by measurable
functions of the history, the observation and the action (and not possibly random kernels). -/
class Environment.HasDeterministicFeedback (env : Environment 𝓞 𝓐 𝓨) : Prop where
  exists_f : ∀ n, ∃ (f : ((Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐) → 𝓨) (hf : Measurable f),
    env.feedback n = Kernel.deterministic f hf

namespace Environment

/-- The feedback function of a deterministic environment at step `n`. -/
noncomputable
def feedbackFun (env : Environment 𝓞 𝓐 𝓨) [h_det : env.HasDeterministicFeedback] (n : ℕ) :
    ((Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐) → 𝓨 :=
  (h_det.exists_f n).choose

@[fun_prop]
lemma measurable_feedbackFun (env : Environment 𝓞 𝓐 𝓨) [env.HasDeterministicFeedback] (n : ℕ) :
    Measurable (env.feedbackFun n) :=
  (HasDeterministicFeedback.exists_f n).choose_spec.choose

lemma feedback_eq_deterministic (env : Environment 𝓞 𝓐 𝓨) [env.HasDeterministicFeedback] (n : ℕ) :
    env.feedback n = Kernel.deterministic (env.feedbackFun n) (env.measurable_feedbackFun n) :=
  (HasDeterministicFeedback.exists_f n).choose_spec.choose_spec

/-- The initial feedback function of a deterministic environment, as a function of the first
observation and the first action. -/
noncomputable
def feedbackFunZero (env : Environment 𝓞 𝓐 𝓨) [env.HasDeterministicFeedback] : 𝓞 × 𝓐 → 𝓨 :=
  fun p ↦ env.feedbackFun 0 ((default, p.1), p.2)

@[fun_prop]
lemma measurable_feedbackFunZero (env : Environment 𝓞 𝓐 𝓨) [env.HasDeterministicFeedback] :
    Measurable env.feedbackFunZero :=
  (env.measurable_feedbackFun 0).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)

lemma feedbackFun_zero (env : Environment 𝓞 𝓐 𝓨) [env.HasDeterministicFeedback] (h : Hist 𝓞 𝓐 𝓨 0)
    (o : 𝓞) (a : 𝓐) :
    env.feedbackFun 0 ((h, o), a) = env.feedbackFunZero (o, a) := by
  rw [Unique.eq_default h]
  rfl

lemma feedbackZero_eq_deterministic (env : Environment 𝓞 𝓐 𝓨) [env.HasDeterministicFeedback] :
    env.feedbackZero = Kernel.deterministic env.feedbackFunZero env.measurable_feedbackFunZero := by
  ext p : 1
  rw [feedbackZero_def, Kernel.comap_apply, feedback_eq_deterministic, Kernel.deterministic_apply,
    Kernel.deterministic_apply]
  rfl

end Environment

namespace Environment.HasDeterministicFeedback

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨} {P : Measure Ω} [IsFiniteMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

lemma hasCondDistrib_feedback [h_det : env.HasDeterministicFeedback]
    (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    HasCondDistrib (Y n) (fun ω ↦ ((history O A Y n ω, O n ω), A n ω))
      (Kernel.deterministic (env.feedbackFun n) (env.measurable_feedbackFun n)) P := by
  rw [← feedback_eq_deterministic]
  exact h.hasCondDistrib_feedback n

lemma hasCondDistrib_feedback_zero [h_det : env.HasDeterministicFeedback]
    (h : IsAlgEnvSeq O A Y alg env P) :
    HasCondDistrib (Y 0) (fun ω ↦ (O 0 ω, A 0 ω))
      (Kernel.deterministic env.feedbackFunZero env.measurable_feedbackFunZero) P := by
  rw [← feedbackZero_eq_deterministic]
  exact h.hasCondDistrib_feedback_zero

lemma feedback_ae_eq [MeasurableEq 𝓨] [h_det : env.HasDeterministicFeedback]
    (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    Y n =ᵐ[P] fun ω ↦ env.feedbackFun n ((history O A Y n ω, O n ω), A n ω) := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  exact ae_eq_of_hasCondDistrib_deterministic (measurable_feedbackFun _ _) (by fun_prop)
    (by fun_prop) (hasCondDistrib_feedback h n)

end Environment.HasDeterministicFeedback

variable {nextA : (n : ℕ) → (Hist 𝓞 𝓐 𝓨 n × 𝓞) → 𝓐} {h_next : ∀ n, Measurable (nextA n)}
  {env : Environment 𝓞 𝓐 𝓨}
  {obs : (n : ℕ) → Kernel (Hist 𝓞 𝓐 𝓨 n) 𝓞} [∀ n, IsMarkovKernel (obs n)]
  {f : (n : ℕ) → ((Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐) → 𝓨} {hf : ∀ n, Measurable (f n)}

/-- A deterministic algorithm, which chooses the action given by the function `nextA`.
The initial action is `fun o ↦ nextA 0 (default, o)`. -/
@[simps]
noncomputable
def Algorithm.deterministic (nextA : (n : ℕ) → (Hist 𝓞 𝓐 𝓨 n × 𝓞) → 𝓐)
    (h_next : ∀ n, Measurable (nextA n)) :
    Algorithm 𝓞 𝓐 𝓨 where
  policy n := Kernel.deterministic (nextA n) (h_next n)

instance : (Algorithm.deterministic nextA h_next).IsDeterministic where
  exists_nextAction n := ⟨nextA n, h_next n, rfl⟩

@[simp]
lemma policyZero_deterministic :
    (Algorithm.deterministic nextA h_next).policyZero
      = Kernel.deterministic (fun o ↦ nextA 0 (default, o))
        ((h_next 0).comp (measurable_const.prodMk measurable_id)) := by
  ext o : 1
  rw [Algorithm.policyZero_apply, Algorithm.deterministic_policy, Kernel.deterministic_apply,
    Kernel.deterministic_apply]

@[simp]
lemma nextAction_deterministic [MeasurableSpace.SeparatesPoints 𝓐] (n : ℕ) :
    (Algorithm.deterministic nextA h_next).nextAction n = nextA n := by
  have h_eq := (Algorithm.deterministic nextA h_next).policy_eq_deterministic n
  simpa [Algorithm.deterministic] using h_eq.symm

@[simp]
lemma actionZero_deterministic [MeasurableSpace.SeparatesPoints 𝓐] :
    (Algorithm.deterministic nextA h_next).actionZero = fun o ↦ nextA 0 (default, o) := by
  unfold Algorithm.actionZero
  rw [nextAction_deterministic]

/-- A deterministic environment, where the feedback is given by evaluating
fixed measurable functions. -/
noncomputable def Environment.detFeedback (obs : (n : ℕ) → Kernel (Hist 𝓞 𝓐 𝓨 n) 𝓞)
    [∀ n, IsMarkovKernel (obs n)]
    (f : (n : ℕ) → ((Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐) → 𝓨) (hf : ∀ n, Measurable (f n)) :
    Environment 𝓞 𝓐 𝓨 where
  obs := obs
  feedback n := (Kernel.deterministic (f n) (hf n))

@[simp]
lemma obs_detFeedback (n : ℕ) : (Environment.detFeedback obs f hf).obs n = obs n := rfl

@[simp]
lemma feedback_detFeedback (n : ℕ) :
    (Environment.detFeedback obs f hf).feedback n = Kernel.deterministic (f n) (hf n) := rfl

instance : (Environment.detFeedback obs f hf).HasDeterministicFeedback where
  exists_f n := ⟨f n, hf n, rfl⟩

@[simp]
lemma feedbackFun_detFeedback [MeasurableSpace.SeparatesPoints 𝓨] (n : ℕ) :
    (Environment.detFeedback obs f hf).feedbackFun n = f n := by
  simpa [Environment.detFeedback] using
    ((Environment.detFeedback obs f hf).feedback_eq_deterministic n).symm

@[simp]
lemma feedbackFunZero_detFeedback [MeasurableSpace.SeparatesPoints 𝓨] :
    (Environment.detFeedback obs f hf).feedbackFunZero = fun p ↦ f 0 ((default, p.1), p.2) := by
  unfold Environment.feedbackFunZero
  rw [feedbackFun_detFeedback]

namespace IsAlgEnvSeq

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {alg : Algorithm 𝓞 𝓐 𝓨} {ν : Kernel (𝓞 × 𝓐) 𝓨} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

lemma hasCondDistrib_action_zero_deterministic
    (h : IsAlgEnvSeq O A Y (Algorithm.deterministic nextA h_next) env P) :
    HasCondDistrib (A 0) (O 0)
      (Kernel.deterministic (fun o ↦ nextA 0 (default, o))
        ((h_next 0).comp (measurable_const.prodMk measurable_id))) P := by
  rw [← policyZero_deterministic]
  exact h.hasCondDistrib_action_zero

lemma action_deterministic_ae_eq [MeasurableEq 𝓐]
    (h : IsAlgEnvSeq O A Y (Algorithm.deterministic nextA h_next) env P) (n : ℕ) :
    A n =ᵐ[P] fun ω ↦ nextA n (history O A Y n ω, O n ω) :=
  (Algorithm.IsDeterministic.action_ae_eq h n).trans (by simp)

lemma action_zero_deterministic [MeasurableEq 𝓐]
    (h : IsAlgEnvSeq O A Y (Algorithm.deterministic nextA h_next) env P) :
    A 0 =ᵐ[P] fun ω ↦ nextA 0 (default, O 0 ω) :=
  (Algorithm.IsDeterministic.action_zero_ae_eq h).trans (by simp)

lemma action_deterministic_ae_all_eq [MeasurableEq 𝓐]
    (h : IsAlgEnvSeq O A Y (Algorithm.deterministic nextA h_next) env P) :
    ∀ᵐ ω ∂P, ∀ n, A n ω = nextA n (history O A Y n ω, O n ω) :=
  ae_all_iff.mpr (action_deterministic_ae_eq h)

end IsAlgEnvSeq

namespace IsAlgEnvSeqUntil

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {alg : Algorithm 𝓞 𝓐 𝓨} {ν : Kernel (𝓞 × 𝓐) 𝓨} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {N n : ℕ}

lemma hasCondDistrib_action_zero_deterministic
    (h : IsAlgEnvSeqUntil O A Y (Algorithm.deterministic nextA h_next) env P N) (hN : 0 < N) :
    HasCondDistrib (A 0) (O 0)
      (Kernel.deterministic (fun o ↦ nextA 0 (default, o))
        ((h_next 0).comp (measurable_const.prodMk measurable_id))) P := by
  rw [← policyZero_deterministic]
  exact h.hasCondDistrib_action_zero hN

lemma action_deterministic_ae_eq [MeasurableEq 𝓐]
    (h : IsAlgEnvSeqUntil O A Y (Algorithm.deterministic nextA h_next) env P N) (hn : n < N) :
    A n =ᵐ[P] fun ω ↦ nextA n (history O A Y n ω, O n ω) :=
  (Algorithm.IsDeterministic.action_ae_eq_of_IsAlgEnvSeqUntil h hn).trans (by simp)

lemma action_zero_deterministic [MeasurableEq 𝓐]
    (h : IsAlgEnvSeqUntil O A Y (Algorithm.deterministic nextA h_next) env P N) (hN : 0 < N) :
    A 0 =ᵐ[P] fun ω ↦ nextA 0 (default, O 0 ω) :=
  (Algorithm.IsDeterministic.action_zero_of_IsAlgEnvSeqUntil h hN).trans (by simp)

end IsAlgEnvSeqUntil

end Learning
