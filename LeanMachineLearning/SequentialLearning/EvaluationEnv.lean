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
lemma feedbackFunZero_onlineEvalEnv [MeasurableSpace.SeparatesPoints 𝓨] :
    feedbackFunZero (onlineEvalEnv g hg) = g 0 := by
  have h_eq := ν0_eq_deterministic (onlineEvalEnv g hg)
  simpa only [onlineEvalEnv, ν0_obliviousEnv, Kernel.prodMkLeft_deterministic,
    Kernel.deterministic_inj] using h_eq.symm

@[simp]
lemma feedbackFun_onlineEvalEnv [MeasurableSpace.SeparatesPoints 𝓨] (n : ℕ) :
    feedbackFun (onlineEvalEnv g hg) n = fun p ↦ g (n + 1) p.2 := by
  have h_eq := feedback_eq_deterministic (onlineEvalEnv g hg) n
  simpa only [onlineEvalEnv, feedback_obliviousEnv, Kernel.prodMkLeft_deterministic,
    Kernel.deterministic_inj] using h_eq.symm

section OnlineEvalEnv

variable [StandardBorelSpace 𝓐] [Nonempty 𝓐] [StandardBorelSpace 𝓨] [Nonempty 𝓨]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm 𝓐 𝓨}
  {g : ℕ → 𝓐 → 𝓨} {hg : ∀ n, Measurable (g n)}
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

lemma hascondDistrib_feedback_onlineEvalEnv
    (h : IsAlgEnvSeq A Y alg (onlineEvalEnv g hg) P) (n : ℕ) :
    HasCondDistrib (Y n) (A n) (Kernel.deterministic (g n) (hg n)) P := by
  simpa using IsObliviousEnv.hasCondDistrib_feedback h n

lemma feedback_onlineEvalEnv_ae_eq_eval_action
    (h : IsAlgEnvSeq A Y alg (onlineEvalEnv g hg) P) (n : ℕ) :
    Y n =ᵐ[P] g n ∘ A n :=
  ae_eq_of_condDistrib_eq_deterministic (hg n) (h.measurable_action n).aemeasurable
    (h.measurable_feedback n).aemeasurable
    (hascondDistrib_feedback_onlineEvalEnv h n).condDistrib_eq

lemma forall_feedback_onlineEvalEnv_ae_eq_eval_action
    (h : IsAlgEnvSeq A Y alg (onlineEvalEnv g hg) P) :
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
lemma feedbackCondAction_evalEnv (n : ℕ) :
    feedbackCondAction (evalEnv f hf) n = Kernel.deterministic f hf := by simp [evalEnv]

@[simp]
lemma feedbackFunZero_evalEnv [MeasurableSpace.SeparatesPoints 𝓨] :
    feedbackFunZero (evalEnv f hf) = f := by simp [evalEnv]

@[simp]
lemma feedbackFun_evalEnv [MeasurableSpace.SeparatesPoints 𝓨] (n : ℕ) :
    feedbackFun (evalEnv f hf) n = fun p ↦ f p.2 := by simp [evalEnv]

section EvalEnv

variable [StandardBorelSpace 𝓐] [Nonempty 𝓐] [StandardBorelSpace 𝓨] [Nonempty 𝓨]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm 𝓐 𝓨} {f : 𝓐 → 𝓨} {hf : Measurable f}
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

lemma hascondDistrib_feedback_evalEnv (h : IsAlgEnvSeq A Y alg (evalEnv f hf) P) (n : ℕ) :
    HasCondDistrib (Y n) (A n) (Kernel.deterministic f hf) P := by
  simpa using IsObliviousEnv.hasCondDistrib_feedback h n

lemma feedback_evalEnv_ae_eq_eval_action (h : IsAlgEnvSeq A Y alg (evalEnv f hf) P) (n : ℕ) :
    Y n =ᵐ[P] f ∘ A n := feedback_onlineEvalEnv_ae_eq_eval_action h n

lemma forall_feedback_evalEnv_ae_eq_eval_action (h : IsAlgEnvSeq A Y alg (evalEnv f hf) P) :
    ∀ᵐ ω ∂P, ∀ n, Y n ω = f (A n ω) := forall_feedback_onlineEvalEnv_ae_eq_eval_action h

open Finset in
lemma feedback_evalEnv_ae_eq_eval_action_comp {β : Type*}
    (h : IsAlgEnvSeq A Y alg (evalEnv f hf) P) {n : ℕ} (g : (Iic n → 𝓨) → β) :
    ∀ᵐ ω ∂P, g (fun i ↦ Y i ω) = g (fun i ↦ f (A i ω)) := by
  filter_upwards [forall_feedback_evalEnv_ae_eq_eval_action h] with ω hω
  simp_rw [hω]

end EvalEnv

end Learning
