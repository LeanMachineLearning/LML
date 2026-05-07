/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Deterministic
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import LeanMachineLearning.Probability.Independence.CondDistrib

/-!
# Function evaluation environments

We define two environments, `onlineEvalEnv` and `evalEnv`, where the reward is given by evaluating
a measurable function at the chosen action. The first one allows the function to change at every
time step, while the second one uses a fixed function at every time step.

## Main definitions

* `onlineEvalEnv g hg`: A stationary environment where the reward at time `n` is given by a
  deterministic kernel that evaluates the measurable function `g n` at the chosen action.
* `evalEnv f hf`: A stationary environment where the reward is given by a deterministic kernel that
  evaluates a fixed measurable function `f` at the chosen action.

They both satisfy the typeclasses `IsObliviousEnv` and `IsDeterministicEnv`.

## Main statements

* `forall_reward_onlineEvalEnv_ae_eq_eval_action`: For almost all `ω`, the reward at time `n` is
  equal to `g n` evaluated at the action taken at time `n`.
* `forall_reward_evalEnv_ae_eq_eval_action`: For almost all `ω`, the reward at time `n` is equal to
  `f` evaluated at the action taken at time `n`.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {α R : Type*} {mα : MeasurableSpace α} {mR : MeasurableSpace R}
  {g : ℕ → α → R} {hg : ∀ n, Measurable (g n)}
  {f : α → R} {hf : Measurable f}

/-- The evaluation environment where the reward is given by evaluating a fixed measurable function
`f` at the chosen action. -/
noncomputable def onlineEvalEnv (g : ℕ → α → R) (hg : ∀ n, Measurable (g n)) :=
  obliviousEnv (fun n ↦ Kernel.deterministic (g n) (hg n))

instance : IsObliviousEnv (onlineEvalEnv g hg) :=
  ⟨⟨fun n ↦ Kernel.deterministic (g n) (hg n), fun _ ↦ inferInstance, rfl, fun _ ↦ rfl⟩⟩

instance : IsDeterministicEnv (onlineEvalEnv g hg) where
  exists_f0 := ⟨g 0, hg 0, rfl⟩
  exists_f n := ⟨fun p ↦ g (n + 1) p.2, by fun_prop, rfl⟩

@[simp]
lemma feedbackCondAction_onlineEvalEnv (n : ℕ) :
    feedbackCondAction (onlineEvalEnv g hg) n = Kernel.deterministic (g n) (hg n) := by
  simp [onlineEvalEnv]

@[simp]
lemma feedbackFunZero_onlineEvalEnv [MeasurableSpace.SeparatesPoints R] :
    feedbackFunZero (onlineEvalEnv g hg) = g 0 := by
  have h_eq := ν0_eq_deterministic (onlineEvalEnv g hg)
  simpa only [onlineEvalEnv, ν0_obliviousEnv, Kernel.prodMkLeft_deterministic,
    Kernel.deterministic_inj] using h_eq.symm

@[simp]
lemma feedbackFun_onlineEvalEnv [MeasurableSpace.SeparatesPoints R] (n : ℕ) :
    feedbackFun (onlineEvalEnv g hg) n = fun p ↦ g (n + 1) p.2 := by
  have h_eq := feedback_eq_deterministic (onlineEvalEnv g hg) n
  simpa only [onlineEvalEnv, feedback_obliviousEnv, Kernel.prodMkLeft_deterministic,
    Kernel.deterministic_inj] using h_eq.symm

section OnlineEvalEnv

variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm α R}
  {g : ℕ → α → R} {hg : ∀ n, Measurable (g n)}
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → α} {R' : ℕ → Ω → R}

lemma hascondDistrib_reward_onlineEvalEnv
    (h : IsAlgEnvSeq A R' alg (onlineEvalEnv g hg) P) (n : ℕ) :
    HasCondDistrib (R' n) (A n) (Kernel.deterministic (g n) (hg n)) P := by
  simpa using IsObliviousEnv.hasCondDistrib_reward h n

lemma reward_onlineEvalEnv_ae_eq_eval_action
    (h : IsAlgEnvSeq A R' alg (onlineEvalEnv g hg) P) (n : ℕ) :
    R' n =ᵐ[P] g n ∘ A n :=
  ae_eq_of_condDistrib_eq_deterministic (hg n) (h.measurable_A n).aemeasurable
    (h.measurable_R n).aemeasurable (hascondDistrib_reward_onlineEvalEnv h n).condDistrib_eq

lemma forall_reward_onlineEvalEnv_ae_eq_eval_action
    (h : IsAlgEnvSeq A R' alg (onlineEvalEnv g hg) P) :
    ∀ᵐ ω ∂P, ∀ n, R' n ω = g n (A n ω) := by
  rw [ae_all_iff]
  intro n
  exact reward_onlineEvalEnv_ae_eq_eval_action h n

end OnlineEvalEnv

/-- The evaluation environment where the reward is given by evaluating a fixed measurable function
`f` at the chosen action. -/
noncomputable def evalEnv (f : α → R) (hf : Measurable f) := onlineEvalEnv (fun _ ↦ f) (fun _ ↦ hf)

instance : IsObliviousEnv (evalEnv f hf) := by unfold evalEnv; infer_instance

instance : IsDeterministicEnv (evalEnv f hf) := by unfold evalEnv; infer_instance

@[simp]
lemma feedbackCondAction_evalEnv (n : ℕ) :
    feedbackCondAction (evalEnv f hf) n = Kernel.deterministic f hf := by simp [evalEnv]

@[simp]
lemma feedbackFunZero_evalEnv [MeasurableSpace.SeparatesPoints R] :
    feedbackFunZero (evalEnv f hf) = f := by simp [evalEnv]

@[simp]
lemma feedbackFun_evalEnv [MeasurableSpace.SeparatesPoints R] (n : ℕ) :
    feedbackFun (evalEnv f hf) n = fun p ↦ f p.2 := by simp [evalEnv]

section EvalEnv

variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm α R} {f : α → R} {hf : Measurable f}
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → α} {R' : ℕ → Ω → R}

lemma hascondDistrib_reward_evalEnv (h : IsAlgEnvSeq A R' alg (evalEnv f hf) P) (n : ℕ) :
    HasCondDistrib (R' n) (A n) (Kernel.deterministic f hf) P := by
  simpa using IsObliviousEnv.hasCondDistrib_reward h n

lemma reward_evalEnv_ae_eq_eval_action (h : IsAlgEnvSeq A R' alg (evalEnv f hf) P) (n : ℕ) :
    R' n =ᵐ[P] f ∘ A n := reward_onlineEvalEnv_ae_eq_eval_action h n

lemma forall_reward_evalEnv_ae_eq_eval_action (h : IsAlgEnvSeq A R' alg (evalEnv f hf) P) :
    ∀ᵐ ω ∂P, ∀ n, R' n ω = f (A n ω) := forall_reward_onlineEvalEnv_ae_eq_eval_action h

open Finset in
lemma reward_evalEnv_ae_eq_eval_action_comp {β : Type*}
    (h : IsAlgEnvSeq A R' alg (evalEnv f hf) P) {n : ℕ} (g : (Iic n → R) → β) :
    ∀ᵐ ω ∂P, g (fun i ↦ R' i ω) = g (fun i ↦ f (A i ω)) := by
  filter_upwards [forall_reward_evalEnv_ae_eq_eval_action h] with ω hω
  simp_rw [hω]

end EvalEnv

end Learning
