/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Deterministic
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import LeanMachineLearning.ForMathlib.Probability.Independence.CondDistrib

/-!
# Function evaluation environments

We define two environments, `onlineEvalEnv` and `evalEnv`, where the feedback is given by evaluating
a measurable function at the chosen action. The first one allows the function to change at every
time step, while the second one uses a fixed function at every time step.

## Main definitions

* `onlineEvalEnv g hg`: A stationary environment where the feedback at time `n` is given by a
  deterministic kernel that evaluates the measurable function `g n` at the chosen action.
* `evalEnv f hf`: A stationary environment where the feedback is given by a deterministic kernel
  that evaluates a fixed measurable function `f` at the chosen action.

They both satisfy the typeclasses `IsObliviousEnv` and `IsDeterministicEnv`.

## Main statements

* `forall_feedback_onlineEvalEnv_ae_eq_eval_action`: For almost all `ω`, the feedback at time `n` is
  equal to `g n` evaluated at the action taken at time `n`.
* `forall_feedback_evalEnv_ae_eq_eval_action`: For almost all `ω`, the feedback at time `n` is equal
  to `f` evaluated at the action taken at time `n`.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {g : ℕ → 𝓐 → 𝓨} {hg : ∀ n, Measurable (g n)}
  {f : 𝓐 → 𝓨} {hf : Measurable f}

/-- The evaluation environment where the feedback is given by evaluating a fixed measurable function
`f` at the chosen action. -/
noncomputable def onlineEvalEnv (g : ℕ → 𝓐 → 𝓨) (hg : ∀ n, Measurable (g n)) :=
  Environment.banditSeq (fun n ↦ Kernel.deterministic (g n) (hg n))

instance : IsObliviousEnv (onlineEvalEnv g hg) :=
  inferInstanceAs (IsObliviousEnv (Environment.banditSeq fun n ↦ Kernel.deterministic (g n) (hg n)))

instance : IsDeterministicEnv (onlineEvalEnv g hg) where
  exists_f n := ⟨fun p ↦ g n p.2, by fun_prop, rfl⟩

@[simp]
lemma feedbackCondObsAction_onlineEvalEnv (n : ℕ) :
    (onlineEvalEnv g hg).feedbackCondObsAction n
      = Kernel.deterministic (fun p ↦ g n p.2) (by fun_prop) := by
  simp [onlineEvalEnv]

@[simp]
lemma feedbackFun_onlineEvalEnv [MeasurableSpace.SeparatesPoints 𝓨] (n : ℕ) :
    feedbackFun (onlineEvalEnv g hg) n = fun p ↦ g n p.2 := by
  have h_eq := feedback_eq_deterministic (onlineEvalEnv g hg) n
  simpa only [onlineEvalEnv, feedback_banditSeq, Kernel.prodMkLeft_deterministic,
    Kernel.deterministic_inj] using h_eq.symm

@[simp]
lemma feedbackFunZero_onlineEvalEnv [MeasurableSpace.SeparatesPoints 𝓨] :
    feedbackFunZero (onlineEvalEnv g hg) = fun p ↦ g 0 p.2 := by
  unfold feedbackFunZero
  rw [feedbackFun_onlineEvalEnv]

section OnlineEvalEnv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm Unit 𝓐 𝓨}
  {g : ℕ → 𝓐 → 𝓨} {hg : ∀ n, Measurable (g n)}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

lemma hasCondDistrib_feedback_onlineEvalEnv
    (h : IsAlgEnvSeq O A Y alg (onlineEvalEnv g hg) P) (n : ℕ) :
    HasCondDistrib (Y n) (A n) (Kernel.deterministic (g n) (hg n)) P :=
  h.hasCondDistrib_feedback_banditSeq n

lemma feedback_onlineEvalEnv_ae_eq_eval_action [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (h : IsAlgEnvSeq O A Y alg (onlineEvalEnv g hg) P) (n : ℕ) :
    Y n =ᵐ[P] g n ∘ A n :=
  ae_eq_of_condDistrib_eq_deterministic (hg n) (h.measurable_action n).aemeasurable
    (h.measurable_feedback n).aemeasurable
    (hasCondDistrib_feedback_onlineEvalEnv h n).condDistrib_eq

lemma forall_feedback_onlineEvalEnv_ae_eq_eval_action [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (h : IsAlgEnvSeq O A Y alg (onlineEvalEnv g hg) P) :
    ∀ᵐ ω ∂P, ∀ n, Y n ω = g n (A n ω) := by
  rw [ae_all_iff]
  intro n
  exact feedback_onlineEvalEnv_ae_eq_eval_action h n

end OnlineEvalEnv

/-- The evaluation environment where the feedback is given by evaluating a fixed measurable function
`f` at the chosen action. -/
noncomputable def evalEnv (f : 𝓐 → 𝓨) (hf : Measurable f) := onlineEvalEnv (fun _ ↦ f) (fun _ ↦ hf)

instance : IsObliviousEnv (evalEnv f hf) := by unfold evalEnv; infer_instance

instance : IsDeterministicEnv (evalEnv f hf) := by unfold evalEnv; infer_instance

@[simp]
lemma feedbackCondObsAction_evalEnv (n : ℕ) :
    (evalEnv f hf).feedbackCondObsAction n
      = Kernel.deterministic (fun p ↦ f p.2) (by fun_prop) := by
  simp [evalEnv]

@[simp]
lemma feedbackFunZero_evalEnv [MeasurableSpace.SeparatesPoints 𝓨] :
    feedbackFunZero (evalEnv f hf) = fun p ↦ f p.2 := by simp [evalEnv]

@[simp]
lemma feedbackFun_evalEnv [MeasurableSpace.SeparatesPoints 𝓨] (n : ℕ) :
    feedbackFun (evalEnv f hf) n = fun p ↦ f p.2 := by simp [evalEnv]

section EvalEnv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm Unit 𝓐 𝓨}
  {f : 𝓐 → 𝓨} {hf : Measurable f}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

lemma hasCondDistrib_feedback_evalEnv (h : IsAlgEnvSeq O A Y alg (evalEnv f hf) P) (n : ℕ) :
    HasCondDistrib (Y n) (A n) (Kernel.deterministic f hf) P :=
  h.hasCondDistrib_feedback_banditSeq n

lemma feedback_evalEnv_ae_eq_eval_action [StandardBorelSpace 𝓨] [Nonempty 𝓨]
  (h : IsAlgEnvSeq O A Y alg (evalEnv f hf) P) (n : ℕ) :
    Y n =ᵐ[P] f ∘ A n := feedback_onlineEvalEnv_ae_eq_eval_action h n

lemma forall_feedback_evalEnv_ae_eq_eval_action [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (h : IsAlgEnvSeq O A Y alg (evalEnv f hf) P) :
    ∀ᵐ ω ∂P, ∀ n, Y n ω = f (A n ω) := forall_feedback_onlineEvalEnv_ae_eq_eval_action h

open Finset in
lemma feedback_evalEnv_ae_eq_eval_action_comp {β : Type*} [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (h : IsAlgEnvSeq O A Y alg (evalEnv f hf) P) {n : ℕ} (g : (Iic n → 𝓨) → β) :
    ∀ᵐ ω ∂P, g (fun i ↦ Y i ω) = g (fun i ↦ f (A i ω)) := by
  filter_upwards [forall_feedback_evalEnv_ae_eq_eval_action h] with ω hω
  simp_rw [hω]

end EvalEnv

end Learning
