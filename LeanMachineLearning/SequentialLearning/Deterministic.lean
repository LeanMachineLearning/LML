/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Probability.Kernel.Basic
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

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
* `actionZero alg`: the initial action of a deterministic algorithm `alg`.
* `nextAction alg n`: the function that gives the next action of a deterministic algorithm `alg`
  at step `n`, as a function of the history.
* `feedbackFunZero env`: the function that gives the initial feedback of a deterministic
  environment `env`.
* `feedbackFun env n`: the function that gives the feedback of a deterministic environment `env`
  at step `n`, as a function of the history and the current action.

* `detAlgorithm nextA h_next action0`: a deterministic algorithm that chooses its action
  according to the measurable function `nextA` (with proof of measurability `h_next`),
  with initial action `action0`.

## Notes

The `ANCHOR` comments are used to mark code that appears in the tutorials.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Learning

variable {α R : Type*} {mα : MeasurableSpace α} {mR : MeasurableSpace R}

/-- An algorithm is deterministic if its initial action and subsequent actions are determined by
measurable functions (and not possibly random kernels). -/
class IsDeterministicAlg (alg : Algorithm α R) : Prop where
  exists_action0 : ∃ action0, alg.p0 = Measure.dirac action0
  exists_nextAction n : ∃ (nextAction : (Iic n → α × R) → α) (h_meas : Measurable nextAction),
    alg.policy n = Kernel.deterministic nextAction h_meas

/-- The initial action of a deterministic algorithm. -/
noncomputable
def actionZero (alg : Algorithm α R) [h_det : IsDeterministicAlg alg] : α :=
  h_det.exists_action0.choose

/-- The next action of a deterministic algorithm after step `n`. -/
noncomputable
def nextAction (alg : Algorithm α R) [h_det : IsDeterministicAlg alg] (n : ℕ) :
    (Iic n → α × R) → α :=
  (h_det.exists_nextAction n).choose

@[fun_prop]
lemma measurable_nextAction (alg : Algorithm α R) [IsDeterministicAlg alg] (n : ℕ) :
    Measurable (nextAction alg n) :=
  (IsDeterministicAlg.exists_nextAction n).choose_spec.choose

lemma p0_eq_dirac (alg : Algorithm α R) [h_det : IsDeterministicAlg alg] :
    alg.p0 = Measure.dirac (actionZero alg) :=
  h_det.exists_action0.choose_spec

lemma policy_eq_deterministic (alg : Algorithm α R) [h_det : IsDeterministicAlg alg] (n : ℕ) :
    alg.policy n = Kernel.deterministic (nextAction alg n) (measurable_nextAction alg n) :=
  (IsDeterministicAlg.exists_nextAction n).choose_spec.choose_spec

namespace IsDeterministicAlg

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
  {alg : Algorithm α R} {env : Environment α R} {P : Measure Ω} [IsFiniteMeasure P]
  {A : ℕ → Ω → α} {R' : ℕ → Ω → R} {n N : ℕ}

lemma hasLaw_action_zero_of_IsAlgEnvSeqUntil [h_det : IsDeterministicAlg alg]
    (h : IsAlgEnvSeqUntil A R' alg env P N) :
    HasLaw (A 0) (Measure.dirac (actionZero alg)) P where
  aemeasurable := have hA := h.measurable_A; by fun_prop
  map_eq := (h.hasLaw_action_zero).map_eq.trans (p0_eq_dirac alg)

lemma action_zero_of_IsAlgEnvSeqUntil [h_det : IsDeterministicAlg alg]
    (h : IsAlgEnvSeqUntil A R' alg env P N) :
    A 0 =ᵐ[P] fun _ ↦ actionZero alg := by
  have h_eq : ∀ᵐ x ∂(P.map (A 0)), x = actionZero alg := by
    simp [(hasLaw_action_zero_of_IsAlgEnvSeqUntil h).map_eq]
  have hA := h.measurable_A
  exact ae_of_ae_map (by fun_prop) h_eq

lemma action_ae_eq_of_IsAlgEnvSeqUntil [h_det : IsDeterministicAlg alg]
    (h : IsAlgEnvSeqUntil A R' alg env P N) (hn : n < N) :
    A (n + 1) =ᵐ[P] fun ω ↦ nextAction alg n (IsAlgEnvSeq.hist A R' n ω) := by
  have hA := h.measurable_A
  have hR' := h.measurable_R
  have h_eq := (h.hasCondDistrib_action n hn).condDistrib_eq
  rw [policy_eq_deterministic alg n] at h_eq
  refine ae_eq_of_condDistrib_eq_deterministic (by fun_prop : Measurable (nextAction alg n))
    (by fun_prop) (by fun_prop) h_eq

lemma hasLaw_action_zero [h_det : IsDeterministicAlg alg] (h : IsAlgEnvSeq A R' alg env P) :
    HasLaw (A 0) (Measure.dirac (actionZero alg)) P where
  aemeasurable := have hA := h.measurable_A; by fun_prop
  map_eq := (h.hasLaw_action_zero).map_eq.trans (p0_eq_dirac alg)

lemma action_zero_ae_eq [h_det : IsDeterministicAlg alg] (h : IsAlgEnvSeq A R' alg env P) :
    A 0 =ᵐ[P] fun _ ↦ actionZero alg :=
  action_zero_of_IsAlgEnvSeqUntil (h.isAlgEnvSeqUntil 0)

lemma action_ae_eq [h_det : IsDeterministicAlg alg] (h : IsAlgEnvSeq A R' alg env P) (n : ℕ) :
    A (n + 1) =ᵐ[P] fun ω ↦ nextAction alg n (IsAlgEnvSeq.hist A R' n ω) :=
  action_ae_eq_of_IsAlgEnvSeqUntil (h.isAlgEnvSeqUntil (n + 1)) (by simp)

lemma action_ae_all_eq [h_det : IsDeterministicAlg alg] (h : IsAlgEnvSeq A R' alg env P) :
    ∀ᵐ ω ∂P, A 0 ω = actionZero alg ∧
      ∀ n, A (n + 1) ω = nextAction alg n (IsAlgEnvSeq.hist A R' n ω) := by
  rw [eventually_and, ae_all_iff]
  exact ⟨action_zero_ae_eq h, action_ae_eq h⟩

end IsDeterministicAlg

/-- An environment is deterministic if its initial feedbacks are determined by
measurable functions (and not possibly random kernels). -/
class IsDeterministicEnv (env : Environment α R) : Prop where
  exists_f0 : ∃ (f0 : α → R) (hf0 : Measurable f0), env.ν0 = Kernel.deterministic f0 hf0
  exists_f : ∀ n, ∃ (f : ((Iic n → α × R) × α) → R) (hf : Measurable f),
    env.feedback n = Kernel.deterministic f hf

/-- The initial feedback function of a deterministic environment. -/
noncomputable
def feedbackFunZero (env : Environment α R) [h_det : IsDeterministicEnv env] : α → R :=
  h_det.exists_f0.choose

@[fun_prop]
lemma measurable_feedbackFunZero (env : Environment α R) [IsDeterministicEnv env] :
    Measurable (feedbackFunZero env) :=
  (IsDeterministicEnv.exists_f0).choose_spec.choose

lemma ν0_eq_deterministic (env : Environment α R) [IsDeterministicEnv env] :
    env.ν0 = Kernel.deterministic (feedbackFunZero env) (measurable_feedbackFunZero env) :=
  (IsDeterministicEnv.exists_f0).choose_spec.choose_spec

/-- The feedback function of a deterministic environment at step `n`. -/
noncomputable
def feedbackFun (env : Environment α R) [h_det : IsDeterministicEnv env] (n : ℕ) :
    ((Iic n → α × R) × α) → R :=
  (h_det.exists_f n).choose

@[fun_prop]
lemma measurable_feedbackFun (env : Environment α R) [IsDeterministicEnv env] (n : ℕ) :
    Measurable (feedbackFun env n) :=
  (IsDeterministicEnv.exists_f n).choose_spec.choose

lemma feedback_eq_deterministic (env : Environment α R) [IsDeterministicEnv env] (n : ℕ) :
    env.feedback n = Kernel.deterministic (feedbackFun env n) (measurable_feedbackFun env n) :=
  (IsDeterministicEnv.exists_f n).choose_spec.choose_spec

namespace IsDeterministicEnv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
  {alg : Algorithm α R} {env : Environment α R} {P : Measure Ω} [IsFiniteMeasure P]
  {A : ℕ → Ω → α} {R' : ℕ → Ω → R}
  {f : (n : ℕ) → ((Iic n → α × R) × α) → R} {hf : ∀ n, Measurable (f n)}
  {f0 : α → R} {hf0 : Measurable f0}

lemma hasCondDistrib_reward_zero [h_det : IsDeterministicEnv env]
    (h : IsAlgEnvSeq A R' alg env P) :
    HasCondDistrib (R' 0) (A 0)
      (Kernel.deterministic (feedbackFunZero env) (measurable_feedbackFunZero env)) P := by
  rw [← ν0_eq_deterministic]
  exact h.hasCondDistrib_reward_zero

lemma hasCondDistrib_reward [h_det : IsDeterministicEnv env]
    (h : IsAlgEnvSeq A R' alg env P) (n : ℕ) :
    HasCondDistrib (R' (n + 1)) (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω))
      (Kernel.deterministic (feedbackFun env n) (measurable_feedbackFun env n)) P := by
  rw [← feedback_eq_deterministic]
  exact h.hasCondDistrib_reward n

end IsDeterministicEnv

variable {nextA : (n : ℕ) → (Iic n → α × R) → α} {h_next : ∀ n, Measurable (nextA n)}
  {action0 : α} {env : Environment α R}
  {f0 : α → R} {hf0 : Measurable f0}
  {f : (n : ℕ) → ((Iic n → α × R) × α) → R} {hf : ∀ n, Measurable (f n)}

/-- A deterministic algorithm, which chooses the action given by the function `nextAction`. -/
@[simps]
noncomputable
-- ANCHOR: detAlgorithm
def detAlgorithm (nextA : (n : ℕ) → (Iic n → α × R) → α)
    (h_next : ∀ n, Measurable (nextA n)) (action0 : α) :
    Algorithm α R where
  policy n := Kernel.deterministic (nextA n) (h_next n)
  p0 := Measure.dirac action0
-- ANCHOR_END: detAlgorithm

instance : IsDeterministicAlg (detAlgorithm nextA h_next action0) where
  exists_action0 := ⟨action0, rfl⟩
  exists_nextAction n := ⟨nextA n, h_next n, rfl⟩

@[simp]
lemma actionZero_detAlgorithm [MeasurableSpace.SeparatesPoints α] :
    actionZero (detAlgorithm nextA h_next action0) = action0 := by
  have h_eq := p0_eq_dirac (detAlgorithm nextA h_next action0)
  simp only [detAlgorithm] at h_eq
  rw [dirac_eq_dirac_iff] at h_eq
  exact h_eq.symm

@[simp]
lemma nextAction_detAlgorithm [MeasurableSpace.SeparatesPoints α] (n : ℕ) :
    nextAction (detAlgorithm nextA h_next action0) n = nextA n := by
  have h_eq := policy_eq_deterministic (detAlgorithm nextA h_next action0) n
  simpa [detAlgorithm] using h_eq.symm

/-- A deterministic environment, where the feedback is given by evaluating
fixed measurable functions. -/
noncomputable def detEnvironment
    (f0 : α → R) (hf0 : Measurable f0)
    (f : (n : ℕ) → ((Iic n → α × R) × α) → R) (hf : ∀ n, Measurable (f n)) :
    Environment α R where
  feedback n := (Kernel.deterministic (f n) (hf n))
  ν0 := Kernel.deterministic f0 hf0

instance : IsDeterministicEnv (detEnvironment f0 hf0 f hf) where
  exists_f0 := ⟨f0, hf0, rfl⟩
  exists_f n := ⟨f n, hf n, rfl⟩

@[simp]
lemma feedbackFunZero_detEnvironment [MeasurableSpace.SeparatesPoints R] :
    feedbackFunZero (detEnvironment f0 hf0 f hf) = f0 := by
  simpa [detEnvironment] using (ν0_eq_deterministic (detEnvironment f0 hf0 f hf)).symm

@[simp]
lemma feedbackFun_detEnvironment [MeasurableSpace.SeparatesPoints R] (n : ℕ) :
    feedbackFun (detEnvironment f0 hf0 f hf) n = f n := by
  simpa [detEnvironment] using (feedback_eq_deterministic (detEnvironment f0 hf0 f hf) n).symm

namespace IsAlgEnvSeq

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
  {alg : Algorithm α R} {ν : Kernel α R} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → α} {R' : ℕ → Ω → R}

lemma hasLaw_action_zero_detAlgorithm
    (h : IsAlgEnvSeq A R' (detAlgorithm nextA h_next action0) env P) :
    HasLaw (A 0) (Measure.dirac action0) P := by
  simpa using IsDeterministicAlg.hasLaw_action_zero h

lemma action_zero_detAlgorithm
    (h : IsAlgEnvSeq A R' (detAlgorithm nextA h_next action0) env P) :
    A 0 =ᵐ[P] fun _ ↦ action0 :=
  (IsDeterministicAlg.action_zero_ae_eq h).trans (by simp)

lemma action_detAlgorithm_ae_eq
    (h : IsAlgEnvSeq A R' (detAlgorithm nextA h_next action0) env P) (n : ℕ) :
    A (n + 1) =ᵐ[P] fun ω ↦ nextA n (hist A R' n ω) :=
  (IsDeterministicAlg.action_ae_eq h n).trans (by simp)

lemma action_detAlgorithm_ae_all_eq
    (h : IsAlgEnvSeq A R' (detAlgorithm nextA h_next action0) env P) :
    ∀ᵐ ω ∂P, A 0 ω = action0 ∧ ∀ n, A (n + 1) ω = nextA n (hist A R' n ω) := by
  filter_upwards [IsDeterministicAlg.action_ae_all_eq h] with ω hω using by simp [hω]


end IsAlgEnvSeq

namespace IsAlgEnvSeqUntil

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
  {alg : Algorithm α R} {ν : Kernel α R} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → α} {R' : ℕ → Ω → R} {N n : ℕ}

lemma hasLaw_action_zero_detAlgorithm
    (h : IsAlgEnvSeqUntil A R' (detAlgorithm nextA h_next action0) env P N) :
    HasLaw (A 0) (Measure.dirac action0) P := by
  simpa using IsDeterministicAlg.hasLaw_action_zero_of_IsAlgEnvSeqUntil h

lemma action_zero_detAlgorithm
    (h : IsAlgEnvSeqUntil A R' (detAlgorithm nextA h_next action0) env P N) :
    A 0 =ᵐ[P] fun _ ↦ action0 :=
  (IsDeterministicAlg.action_zero_of_IsAlgEnvSeqUntil h).trans (by simp)

lemma action_detAlgorithm_ae_eq
    (h : IsAlgEnvSeqUntil A R' (detAlgorithm nextA h_next action0) env P N) (hn : n < N) :
    A (n + 1) =ᵐ[P] fun ω ↦ nextA n (IsAlgEnvSeq.hist A R' n ω) :=
  (IsDeterministicAlg.action_ae_eq_of_IsAlgEnvSeqUntil h hn).trans (by simp)

end IsAlgEnvSeqUntil

namespace IT

local notation "𝔓" => trajMeasure (detAlgorithm nextA h_next action0) env

lemma HasLaw_action_zero_detAlgorithm : HasLaw (IT.action 0) (Measure.dirac action0) 𝔓 where
  map_eq := (IT.hasLaw_action_zero _ _).map_eq

lemma action_zero_detAlgorithm [MeasurableSingletonClass α] :
    IT.action 0 =ᵐ[𝔓] fun _ ↦ action0 := by
  have h_eq : ∀ᵐ x ∂((𝔓).map (IT.action 0)), x = action0 := by
    rw [(IT.hasLaw_action_zero _ _).map_eq]
    simp [detAlgorithm]
  exact ae_of_ae_map (by fun_prop) h_eq

lemma action_detAlgorithm_ae_eq [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R]
    [Nonempty R] (n : ℕ) : IT.action (n + 1) =ᵐ[𝔓] fun h ↦ nextA n (IT.hist n h) :=
  ae_eq_of_condDistrib_eq_deterministic (by fun_prop) (by fun_prop) (by fun_prop)
    (IT.condDistrib_action (detAlgorithm nextA h_next action0) env n)

lemma action_detAlgorithm_ae_all_eq
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R] :
    ∀ᵐ h ∂𝔓, IT.action 0 h = action0 ∧ ∀ n, IT.action (n + 1) h = nextA n (IT.hist n h) := by
  rw [eventually_and, ae_all_iff]
  exact ⟨action_zero_detAlgorithm, action_detAlgorithm_ae_eq⟩

end IT

end Learning
