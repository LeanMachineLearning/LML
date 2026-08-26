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
by a measurable function of the history instead of a general Markov kernel.
Similarly, a deterministic environment gives feedback in a deterministic way.

## Main definitions

We introduce two typeclasses `IsDeterministicAlg` and `IsDeterministicEnv` to express that
an algorithm or an environment is deterministic. We also give definitions for the initial action
and the next action of a deterministic algorithm, and for the feedback functions of a deterministic
environment. Finally, we give a construction of a deterministic algorithm and environment from
measurable functions.

* `IsDeterministicAlg alg`: a typeclass expressing that the algorithm `alg` is deterministic.
* `IsDeterministicEnv env`: a typeclass expressing that the environment `env` is deterministic.
* `nextAction alg n`: the function that gives the action of a deterministic algorithm `alg`
  at step `n`, as a function of the history before `n`.
* `actionZero alg`: the initial action of a deterministic algorithm `alg`. This is
  `nextAction alg 0` applied to the empty history.
* `feedbackFun env n`: the function that gives the feedback of a deterministic environment `env`
  at step `n`, as a function of the history and the current action.
* `feedbackFunZero env`: the function that gives the initial feedback of a deterministic
  environment `env`. This is `feedbackFun env 0` applied to the empty history.

* `detAlgorithm nextA h_next`: a deterministic algorithm that chooses its action
  according to the measurable function `nextA` (with proof of measurability `h_next`).
  The initial action is `nextA 0 default`.
* `detEnvironment f hf`: a deterministic environment that gives feedback according to the
  measurable function `f` (with proof of measurability `hf`).

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Learning

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}

/-- An algorithm is deterministic if its actions are determined by measurable functions of the
history (and not possibly random kernels). -/
class IsDeterministicAlg (alg : Algorithm 𝓐 𝓨) : Prop where
  exists_nextAction n : ∃ (nextAction : (Fin n → 𝓐 × 𝓨) → 𝓐) (h_meas : Measurable nextAction),
    alg.policy n = Kernel.deterministic nextAction h_meas

/-- The action of a deterministic algorithm at step `n`, as a function of the history before `n`. -/
noncomputable
def nextAction (alg : Algorithm 𝓐 𝓨) [h_det : IsDeterministicAlg alg] (n : ℕ) :
    (Fin n → 𝓐 × 𝓨) → 𝓐 :=
  (h_det.exists_nextAction n).choose

/-- The initial action of a deterministic algorithm. -/
noncomputable
def actionZero (alg : Algorithm 𝓐 𝓨) [IsDeterministicAlg alg] : 𝓐 :=
  nextAction alg 0 default

@[fun_prop]
lemma measurable_nextAction (alg : Algorithm 𝓐 𝓨) [IsDeterministicAlg alg] (n : ℕ) :
    Measurable (nextAction alg n) :=
  (IsDeterministicAlg.exists_nextAction n).choose_spec.choose

lemma policy_eq_deterministic (alg : Algorithm 𝓐 𝓨) [h_det : IsDeterministicAlg alg] (n : ℕ) :
    alg.policy n = Kernel.deterministic (nextAction alg n) (measurable_nextAction alg n) :=
  (IsDeterministicAlg.exists_nextAction n).choose_spec.choose_spec

lemma nextAction_zero (alg : Algorithm 𝓐 𝓨) [IsDeterministicAlg alg] (h : Fin 0 → 𝓐 × 𝓨) :
    nextAction alg 0 h = actionZero alg := by
  rw [Unique.eq_default h]
  rfl

lemma p0_eq_dirac (alg : Algorithm 𝓐 𝓨) [IsDeterministicAlg alg] :
    alg.p0 = Measure.dirac (actionZero alg) := by
  rw [Algorithm.p0_def, policy_eq_deterministic, Kernel.deterministic_apply]
  rfl

namespace IsDeterministicAlg

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {alg : Algorithm 𝓐 𝓨} {env : Environment 𝓐 𝓨} {P : Measure Ω} [IsFiniteMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {n N : ℕ}

lemma action_ae_eq_of_IsAlgEnvSeqUntil [MeasurableEq 𝓐]
    [h_det : IsDeterministicAlg alg] (h : IsAlgEnvSeqUntil A Y alg env P N) (hn : n < N) :
    A n =ᵐ[P] fun ω ↦ nextAction alg n (history A Y n ω) := by
  have h_eq := (h.hasCondDistrib_action n hn)
  rw [policy_eq_deterministic alg n] at h_eq
  exact ae_eq_of_hasCondDistrib_deterministic (measurable_nextAction _ _) (by fun_prop)
    (by fun_prop) h_eq

lemma action_zero_of_IsAlgEnvSeqUntil [MeasurableEq 𝓐] [h_det : IsDeterministicAlg alg]
    (h : IsAlgEnvSeqUntil A Y alg env P N) (hN : 0 < N) :
    A 0 =ᵐ[P] fun _ ↦ actionZero alg := by
  filter_upwards [action_ae_eq_of_IsAlgEnvSeqUntil h hN] with ω hω
  rw [hω, nextAction_zero]

lemma hasLaw_action_zero_of_IsAlgEnvSeqUntil [IsProbabilityMeasure P]
    [h_det : IsDeterministicAlg alg] (h : IsAlgEnvSeqUntil A Y alg env P N) (hN : 0 < N) :
    HasLaw (A 0) (Measure.dirac (actionZero alg)) P where
  aemeasurable := have hA := h.measurable_action; by fun_prop
  map_eq := (h.hasLaw_action_zero hN).map_eq.trans (p0_eq_dirac alg)

lemma hasLaw_action_zero [IsProbabilityMeasure P] [h_det : IsDeterministicAlg alg]
    (h : IsAlgEnvSeq A Y alg env P) :
    HasLaw (A 0) (Measure.dirac (actionZero alg)) P :=
  hasLaw_action_zero_of_IsAlgEnvSeqUntil (h.isAlgEnvSeqUntil 1) zero_lt_one

lemma action_ae_eq [MeasurableEq 𝓐] [h_det : IsDeterministicAlg alg]
    (h : IsAlgEnvSeq A Y alg env P) (n : ℕ) :
    A n =ᵐ[P] fun ω ↦ nextAction alg n (history A Y n ω) :=
  action_ae_eq_of_IsAlgEnvSeqUntil (h.isAlgEnvSeqUntil (n + 1)) n.lt_succ_self

lemma action_zero_ae_eq [MeasurableEq 𝓐] [h_det : IsDeterministicAlg alg]
    (h : IsAlgEnvSeq A Y alg env P) :
    A 0 =ᵐ[P] fun _ ↦ actionZero alg :=
  action_zero_of_IsAlgEnvSeqUntil (h.isAlgEnvSeqUntil 1) zero_lt_one

lemma action_ae_all_eq [MeasurableEq 𝓐] [h_det : IsDeterministicAlg alg]
    (h : IsAlgEnvSeq A Y alg env P) :
    ∀ᵐ ω ∂P, ∀ n, A n ω = nextAction alg n (history A Y n ω) :=
  ae_all_iff.mpr (action_ae_eq h)

end IsDeterministicAlg

/-- An environment is deterministic if its feedbacks are determined by measurable functions of
the history and the action (and not possibly random kernels). -/
class IsDeterministicEnv (env : Environment 𝓐 𝓨) : Prop where
  exists_f : ∀ n, ∃ (f : ((Fin n → 𝓐 × 𝓨) × 𝓐) → 𝓨) (hf : Measurable f),
    env.feedback n = Kernel.deterministic f hf

/-- The feedback function of a deterministic environment at step `n`. -/
noncomputable
def feedbackFun (env : Environment 𝓐 𝓨) [h_det : IsDeterministicEnv env] (n : ℕ) :
    ((Fin n → 𝓐 × 𝓨) × 𝓐) → 𝓨 :=
  (h_det.exists_f n).choose

@[fun_prop]
lemma measurable_feedbackFun (env : Environment 𝓐 𝓨) [IsDeterministicEnv env] (n : ℕ) :
    Measurable (feedbackFun env n) :=
  (IsDeterministicEnv.exists_f n).choose_spec.choose

lemma feedback_eq_deterministic (env : Environment 𝓐 𝓨) [IsDeterministicEnv env] (n : ℕ) :
    env.feedback n = Kernel.deterministic (feedbackFun env n) (measurable_feedbackFun env n) :=
  (IsDeterministicEnv.exists_f n).choose_spec.choose_spec

/-- The initial feedback function of a deterministic environment. -/
noncomputable
def feedbackFunZero (env : Environment 𝓐 𝓨) [IsDeterministicEnv env] : 𝓐 → 𝓨 :=
  fun a ↦ feedbackFun env 0 (default, a)

@[fun_prop]
lemma measurable_feedbackFunZero (env : Environment 𝓐 𝓨) [IsDeterministicEnv env] :
    Measurable (feedbackFunZero env) :=
  (measurable_feedbackFun env 0).comp (measurable_const.prodMk measurable_id)

lemma feedbackFun_zero (env : Environment 𝓐 𝓨) [IsDeterministicEnv env] (h : Fin 0 → 𝓐 × 𝓨)
    (a : 𝓐) :
    feedbackFun env 0 (h, a) = feedbackFunZero env a := by
  rw [Unique.eq_default h]
  rfl

lemma ν0_eq_deterministic (env : Environment 𝓐 𝓨) [IsDeterministicEnv env] :
    env.ν0 = Kernel.deterministic (feedbackFunZero env) (measurable_feedbackFunZero env) := by
  ext a : 1
  rw [Environment.ν0_apply, feedback_eq_deterministic, Kernel.deterministic_apply,
    Kernel.deterministic_apply]
  rfl

namespace IsDeterministicEnv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {alg : Algorithm 𝓐 𝓨} {env : Environment 𝓐 𝓨} {P : Measure Ω} [IsFiniteMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

lemma hasCondDistrib_feedback [h_det : IsDeterministicEnv env]
    (h : IsAlgEnvSeq A Y alg env P) (n : ℕ) :
    HasCondDistrib (Y n) (fun ω ↦ (history A Y n ω, A n ω))
      (Kernel.deterministic (feedbackFun env n) (measurable_feedbackFun env n)) P := by
  rw [← feedback_eq_deterministic]
  exact h.hasCondDistrib_feedback n

lemma hasCondDistrib_feedback_zero [h_det : IsDeterministicEnv env]
    (h : IsAlgEnvSeq A Y alg env P) :
    HasCondDistrib (Y 0) (A 0)
      (Kernel.deterministic (feedbackFunZero env) (measurable_feedbackFunZero env)) P := by
  rw [← ν0_eq_deterministic]
  exact h.hasCondDistrib_feedback_zero

lemma feedback_ae_eq [MeasurableEq 𝓨] [h_det : IsDeterministicEnv env]
    (h : IsAlgEnvSeq A Y alg env P) (n : ℕ) :
    Y n =ᵐ[P] fun ω ↦ feedbackFun env n (history A Y n ω, A n ω) := by
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  exact ae_eq_of_hasCondDistrib_deterministic (measurable_feedbackFun _ _) (by fun_prop)
    (by fun_prop) (hasCondDistrib_feedback h n)

end IsDeterministicEnv

variable {nextA : (n : ℕ) → (Fin n → 𝓐 × 𝓨) → 𝓐} {h_next : ∀ n, Measurable (nextA n)}
  {env : Environment 𝓐 𝓨}
  {f : (n : ℕ) → ((Fin n → 𝓐 × 𝓨) × 𝓐) → 𝓨} {hf : ∀ n, Measurable (f n)}

/-- A deterministic algorithm, which chooses the action given by the function `nextA`.
The initial action is `nextA 0 default`. -/
@[simps]
noncomputable
def detAlgorithm (nextA : (n : ℕ) → (Fin n → 𝓐 × 𝓨) → 𝓐)
    (h_next : ∀ n, Measurable (nextA n)) :
    Algorithm 𝓐 𝓨 where
  policy n := Kernel.deterministic (nextA n) (h_next n)

instance : IsDeterministicAlg (detAlgorithm nextA h_next) where
  exists_nextAction n := ⟨nextA n, h_next n, rfl⟩

@[simp]
lemma p0_detAlgorithm : (detAlgorithm nextA h_next).p0 = Measure.dirac (nextA 0 default) := by
  rw [Algorithm.p0_def, detAlgorithm_policy, Kernel.deterministic_apply]

@[simp]
lemma nextAction_detAlgorithm [MeasurableSpace.SeparatesPoints 𝓐] (n : ℕ) :
    nextAction (detAlgorithm nextA h_next) n = nextA n := by
  have h_eq := policy_eq_deterministic (detAlgorithm nextA h_next) n
  simpa [detAlgorithm] using h_eq.symm

@[simp]
lemma actionZero_detAlgorithm [MeasurableSpace.SeparatesPoints 𝓐] :
    actionZero (detAlgorithm nextA h_next) = nextA 0 default := by
  rw [actionZero, nextAction_detAlgorithm]

/-- A deterministic environment, where the feedback is given by evaluating
fixed measurable functions. -/
noncomputable def detEnvironment
    (f : (n : ℕ) → ((Fin n → 𝓐 × 𝓨) × 𝓐) → 𝓨) (hf : ∀ n, Measurable (f n)) :
    Environment 𝓐 𝓨 where
  feedback n := (Kernel.deterministic (f n) (hf n))

instance : IsDeterministicEnv (detEnvironment f hf) where
  exists_f n := ⟨f n, hf n, rfl⟩

@[simp]
lemma feedbackFun_detEnvironment [MeasurableSpace.SeparatesPoints 𝓨] (n : ℕ) :
    feedbackFun (detEnvironment f hf) n = f n := by
  simpa [detEnvironment] using (feedback_eq_deterministic (detEnvironment f hf) n).symm

@[simp]
lemma feedbackFunZero_detEnvironment [MeasurableSpace.SeparatesPoints 𝓨] :
    feedbackFunZero (detEnvironment f hf) = fun a ↦ f 0 (default, a) := by
  unfold feedbackFunZero
  rw [feedbackFun_detEnvironment]

namespace IsAlgEnvSeq

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {alg : Algorithm 𝓐 𝓨} {ν : Kernel 𝓐 𝓨} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

lemma hasLaw_action_zero_detAlgorithm [MeasurableEq 𝓐]
    (h : IsAlgEnvSeq A Y (detAlgorithm nextA h_next) env P) :
    HasLaw (A 0) (Measure.dirac (nextA 0 default)) P := by
  simpa using IsDeterministicAlg.hasLaw_action_zero h

lemma action_detAlgorithm_ae_eq [MeasurableEq 𝓐]
    (h : IsAlgEnvSeq A Y (detAlgorithm nextA h_next) env P) (n : ℕ) :
    A n =ᵐ[P] fun ω ↦ nextA n (history A Y n ω) :=
  (IsDeterministicAlg.action_ae_eq h n).trans (by simp)

lemma action_zero_detAlgorithm [MeasurableEq 𝓐]
    (h : IsAlgEnvSeq A Y (detAlgorithm nextA h_next) env P) :
    A 0 =ᵐ[P] fun _ ↦ nextA 0 default :=
  (IsDeterministicAlg.action_zero_ae_eq h).trans (by simp)

lemma action_detAlgorithm_ae_all_eq [MeasurableEq 𝓐]
    (h : IsAlgEnvSeq A Y (detAlgorithm nextA h_next) env P) :
    ∀ᵐ ω ∂P, ∀ n, A n ω = nextA n (history A Y n ω) :=
  ae_all_iff.mpr (action_detAlgorithm_ae_eq h)

end IsAlgEnvSeq

namespace IsAlgEnvSeqUntil

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {alg : Algorithm 𝓐 𝓨} {ν : Kernel 𝓐 𝓨} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {N n : ℕ}

lemma hasLaw_action_zero_detAlgorithm [MeasurableEq 𝓐]
    (h : IsAlgEnvSeqUntil A Y (detAlgorithm nextA h_next) env P N) (hN : 0 < N) :
    HasLaw (A 0) (Measure.dirac (nextA 0 default)) P := by
  simpa using IsDeterministicAlg.hasLaw_action_zero_of_IsAlgEnvSeqUntil h hN

lemma action_detAlgorithm_ae_eq [MeasurableEq 𝓐]
    (h : IsAlgEnvSeqUntil A Y (detAlgorithm nextA h_next) env P N) (hn : n < N) :
    A n =ᵐ[P] fun ω ↦ nextA n (history A Y n ω) :=
  (IsDeterministicAlg.action_ae_eq_of_IsAlgEnvSeqUntil h hn).trans (by simp)

lemma action_zero_detAlgorithm [MeasurableEq 𝓐]
    (h : IsAlgEnvSeqUntil A Y (detAlgorithm nextA h_next) env P N) (hN : 0 < N) :
    A 0 =ᵐ[P] fun _ ↦ nextA 0 default :=
  (IsDeterministicAlg.action_zero_of_IsAlgEnvSeqUntil h hN).trans (by simp)

end IsAlgEnvSeqUntil

end Learning
