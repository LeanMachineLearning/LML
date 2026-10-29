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

We define two environments, `Environment.evalSeq` and `Environment.eval`, where the feedback is
given by evaluating a measurable function at the chosen action. The first one allows the function
to change at every time step, while the second one uses a fixed function at every time step.

## Main definitions

* `Environment.evalSeq g hg`: A stationary environment where the feedback at time `n` is given by a
  deterministic kernel that evaluates the measurable function `g n` at the chosen action.
* `Environment.eval f hf`: A stationary environment where the feedback is given by a deterministic
  kernel that evaluates a fixed measurable function `f` at the chosen action.

They both satisfy the typeclasses `Environment.IsOblivious` and
`Environment.HasDeterministicFeedback`, and `Environment.eval f hf` is also
`Environment.IsStationary`.

## Main statements

* `forall_feedback_evalSeq_ae_eq_eval_action`: For almost all `ω`, the feedback at time `n` is
  equal to `g n` evaluated at the action taken at time `n`.
* `forall_feedback_eval_ae_eq_eval_action`: For almost all `ω`, the feedback at time `n` is equal
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
noncomputable def Environment.evalSeq (g : ℕ → 𝓐 → 𝓨) (hg : ∀ n, Measurable (g n)) :=
  Environment.banditSeq (fun n ↦ Kernel.deterministic (g n) (hg n))

instance : (Environment.evalSeq g hg).IsOblivious :=
  inferInstanceAs (Environment.banditSeq fun n ↦ Kernel.deterministic (g n) (hg n)).IsOblivious

instance : (Environment.evalSeq g hg).HasDeterministicFeedback where
  exists_f n := ⟨fun p ↦ g n p.2, by fun_prop, rfl⟩

@[simp]
lemma feedbackCondObsAction_evalSeq (n : ℕ) :
    (Environment.evalSeq g hg).feedbackCondObsAction n
      = Kernel.deterministic (fun p ↦ g n p.2) (by fun_prop) := by
  simp [Environment.evalSeq]

@[simp]
lemma feedbackFun_evalSeq [MeasurableSpace.SeparatesPoints 𝓨] (n : ℕ) :
    (Environment.evalSeq g hg).feedbackFun n = fun p ↦ g n p.2 := by
  have h_eq := (Environment.evalSeq g hg).feedback_eq_deterministic n
  simpa only [Environment.evalSeq, feedback_banditSeq, Kernel.prodMkLeft_deterministic,
    Kernel.deterministic_inj] using h_eq.symm

@[simp]
lemma feedbackFunZero_evalSeq [MeasurableSpace.SeparatesPoints 𝓨] :
    (Environment.evalSeq g hg).feedbackFunZero = fun p ↦ g 0 p.2 := by
  unfold Environment.feedbackFunZero
  rw [feedbackFun_evalSeq]

section OnlineEvalEnv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm Unit 𝓐 𝓨}
  {g : ℕ → 𝓐 → 𝓨} {hg : ∀ n, Measurable (g n)}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

lemma hasCondDistrib_feedback_evalSeq
    (h : IsAlgEnvSeq O A Y alg (Environment.evalSeq g hg) P) (n : ℕ) :
    HasCondDistrib (Y n) (A n) (Kernel.deterministic (g n) (hg n)) P :=
  h.hasCondDistrib_feedback_banditSeq n

lemma feedback_evalSeq_ae_eq_eval_action [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.evalSeq g hg) P) (n : ℕ) :
    Y n =ᵐ[P] g n ∘ A n :=
  ae_eq_of_condDistrib_eq_deterministic (hg n) (h.measurable_action n).aemeasurable
    (h.measurable_feedback n).aemeasurable
    (hasCondDistrib_feedback_evalSeq h n).condDistrib_eq

lemma forall_feedback_evalSeq_ae_eq_eval_action [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.evalSeq g hg) P) :
    ∀ᵐ ω ∂P, ∀ n, Y n ω = g n (A n ω) := by
  rw [ae_all_iff]
  intro n
  exact feedback_evalSeq_ae_eq_eval_action h n

end OnlineEvalEnv

/-- The evaluation environment where the feedback is given by evaluating a fixed measurable function
`f` at the chosen action. -/
noncomputable def Environment.eval (f : 𝓐 → 𝓨) (hf : Measurable f) :=
  Environment.evalSeq (fun _ ↦ f) (fun _ ↦ hf)

instance : (Environment.eval f hf).IsStationary where
  exists_obs_eq_const := ⟨Measure.dirac (), inferInstance, fun _ ↦ rfl⟩
  exists_feedback_eq_comap :=
    ⟨(Kernel.deterministic f hf).prodMkLeft Unit, inferInstance, fun _ ↦ rfl⟩

instance : (Environment.eval f hf).IsOblivious := by unfold Environment.eval; infer_instance

instance : (Environment.eval f hf).HasDeterministicFeedback := by
  unfold Environment.eval; infer_instance

@[simp]
lemma feedbackCondObsAction_eval (n : ℕ) :
    (Environment.eval f hf).feedbackCondObsAction n
      = Kernel.deterministic (fun p ↦ f p.2) (by fun_prop) := by
  simp [Environment.eval]

@[simp]
lemma feedbackFunZero_eval [MeasurableSpace.SeparatesPoints 𝓨] :
    (Environment.eval f hf).feedbackFunZero = fun p ↦ f p.2 := by simp [Environment.eval]

@[simp]
lemma feedbackFun_eval [MeasurableSpace.SeparatesPoints 𝓨] (n : ℕ) :
    (Environment.eval f hf).feedbackFun n = fun p ↦ f p.2 := by simp [Environment.eval]

section EvalEnv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm Unit 𝓐 𝓨}
  {f : 𝓐 → 𝓨} {hf : Measurable f}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

lemma hasCondDistrib_feedback_eval (h : IsAlgEnvSeq O A Y alg (Environment.eval f hf) P) (n : ℕ) :
    HasCondDistrib (Y n) (A n) (Kernel.deterministic f hf) P :=
  h.hasCondDistrib_feedback_banditSeq n

lemma feedback_eval_ae_eq_eval_action [StandardBorelSpace 𝓨] [Nonempty 𝓨]
  (h : IsAlgEnvSeq O A Y alg (Environment.eval f hf) P) (n : ℕ) :
    Y n =ᵐ[P] f ∘ A n := feedback_evalSeq_ae_eq_eval_action h n

lemma forall_feedback_eval_ae_eq_eval_action [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.eval f hf) P) :
    ∀ᵐ ω ∂P, ∀ n, Y n ω = f (A n ω) := forall_feedback_evalSeq_ae_eq_eval_action h

open Finset in
lemma feedback_eval_ae_eq_eval_action_comp {β : Type*} [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.eval f hf) P) {n : ℕ} (g : (Iic n → 𝓨) → β) :
    ∀ᵐ ω ∂P, g (fun i ↦ Y i ω) = g (fun i ↦ f (A i ω)) := by
  filter_upwards [forall_feedback_eval_ae_eq_eval_action h] with ω hω
  simp_rw [hω]

end EvalEnv

end Learning
