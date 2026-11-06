/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Deterministic
public import LeanMachineLearning.SequentialLearning.StationaryEnv

/-!
# Function evaluation environments

We define environments `Environment.evalSeq` and `Environment.eval`, where the feedback is given by
evaluating a measurable function at the chosen action. The first one allows the function to change
at every time step, while the second one uses a fixed function at every time step.
`Environment.evalSeqObs` extends `Environment.evalSeq` with a fixed sequence of observations.

## Main definitions

* `Environment.evalSeq g hg`: an oblivious environment without observations where the feedback at
  time `n` is given by a deterministic kernel that evaluates the measurable function `g n` at the
  chosen action.
* `Environment.eval f hf`: a stationary environment without observations where the feedback is
  given by a deterministic kernel that evaluates a fixed measurable function `f` at the chosen
  action.
* `Environment.evalSeqObs o g hg`: the oblivious environment whose observation at time `n` is
  `o n` and whose feedback at time `n` is `g n` evaluated at the chosen action.

They all satisfy the typeclasses `Environment.IsOblivious` and
`Environment.HasDeterministicFeedback`, and `Environment.eval f hf` is also
`Environment.IsStationary`.

## Main statements

* `IsAlgEnvSeq.feedback_ae_all_eq_evalSeq`: For almost all `ω`, the feedback at time `n` is
  equal to `g n` evaluated at the action taken at time `n`.
* `IsAlgEnvSeq.feedback_ae_all_eq_eval`: For almost all `ω`, the feedback at time `n` is equal
  to `f` evaluated at the action taken at time `n`.
* `IsAlgEnvSeq.obs_ae_all_eq_evalSeqObs`, `IsAlgEnvSeq.feedback_ae_all_eq_evalSeqObs`: For almost
  all `ω`, the observation at time `n` is `o n` and the feedback at time `n` is `g n` evaluated
  at the action taken at time `n`.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {g : ℕ → 𝓐 → 𝓨} {hg : ∀ n, Measurable (g n)}
  {f : 𝓐 → 𝓨} {hf : Measurable f}

/-- The evaluation environment where the feedback at time `n` is given by evaluating the measurable
function `g n` at the chosen action. -/
noncomputable def Environment.evalSeq (g : ℕ → 𝓐 → 𝓨) (hg : ∀ n, Measurable (g n)) :
    Environment Unit 𝓐 𝓨 :=
  Environment.banditSeq (fun n ↦ Kernel.deterministic (g n) (hg n))

instance : (Environment.evalSeq g hg).IsOblivious :=
  inferInstanceAs (Environment.banditSeq fun n ↦ Kernel.deterministic (g n) (hg n)).IsOblivious

instance : (Environment.evalSeq g hg).HasDeterministicFeedback where
  exists_f n := ⟨fun p ↦ g n p.2, by fun_prop, rfl⟩

@[simp]
lemma obs_evalSeq (n : ℕ) :
    (Environment.evalSeq g hg).obs n = Kernel.const _ (Measure.dirac ()) := rfl

@[simp]
lemma feedback_evalSeq (n : ℕ) :
    (Environment.evalSeq g hg).feedback n
      = Kernel.deterministic (fun p ↦ g n p.2) (by fun_prop) := rfl

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

/-- The evaluation environment `Environment.evalSeq g hg` is the deterministic adaptive
adversary without observations whose reward tables `g n` do not depend on the history. -/
lemma Environment.evalSeq_eq_deterministic :
    Environment.evalSeq g hg =
      Environment.deterministic (fun _ _ ↦ ()) (fun _ ↦ measurable_const) (fun n p ↦ g n p.2)
        (fun n ↦ (hg n).comp measurable_snd) := by
  ext n : 2
  · ext h : 1
    rw [obs_evalSeq, obs_deterministic, Kernel.const_apply, Kernel.deterministic_apply]
  · rw [feedback_evalSeq, feedback_deterministic]

section EvalSeq

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm Unit 𝓐 𝓨}
  {P : Measure Ω} [SFinite P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

lemma IsAlgEnvSeq.hasCondDistrib_feedback_evalSeq
    (h : IsAlgEnvSeq O A Y alg (Environment.evalSeq g hg) P) (n : ℕ) :
    HasCondDistrib (Y n) (A n) (Kernel.deterministic (g n) (hg n)) P :=
  h.hasCondDistrib_feedback_banditSeq n

lemma IsAlgEnvSeq.feedback_ae_eq_evalSeq [MeasurableEq 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.evalSeq g hg) P) (n : ℕ) :
    Y n =ᵐ[P] g n ∘ A n :=
  (h.hasCondDistrib_feedback_evalSeq n).ae_eq_of_deterministic

lemma IsAlgEnvSeq.feedback_ae_all_eq_evalSeq [MeasurableEq 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.evalSeq g hg) P) :
    ∀ᵐ ω ∂P, ∀ n, Y n ω = g n (A n ω) := by
  rw [ae_all_iff]
  intro n
  exact h.feedback_ae_eq_evalSeq n

end EvalSeq

section EvalSeqObs

variable {𝓞 : Type*} [MeasurableSpace 𝓞] {o : ℕ → 𝓞}

/-- The evaluation environment with observations: at time `n`, the observation is `o n` and the
feedback is given by evaluating the measurable function `g n` at the chosen action, whatever the
history. It is the oblivious environment with Dirac observation laws and deterministic feedback
kernels. In a bandit with expert advice, `o n` is the advice of the experts and `g n a` the reward
of arm `a` at time `n`. -/
noncomputable def Environment.evalSeqObs (o : ℕ → 𝓞) (g : ℕ → 𝓐 → 𝓨)
    (hg : ∀ n, Measurable (g n)) : Environment 𝓞 𝓐 𝓨 :=
  Environment.oblivious (fun n ↦ Measure.dirac (o n))
    (fun n ↦ Kernel.deterministic (fun p ↦ g n p.2) (by fun_prop))

instance : (Environment.evalSeqObs o g hg).IsOblivious :=
  inferInstanceAs (Environment.oblivious _ _).IsOblivious

instance : (Environment.evalSeqObs o g hg).HasDeterministicFeedback where
  exists_f n := ⟨fun p ↦ g n p.2, by fun_prop, rfl⟩

@[simp]
lemma obs_evalSeqObs (n : ℕ) :
    (Environment.evalSeqObs o g hg).obs n = Kernel.const _ (Measure.dirac (o n)) := rfl

@[simp]
lemma feedback_evalSeqObs (n : ℕ) :
    (Environment.evalSeqObs o g hg).feedback n
      = Kernel.deterministic (fun p ↦ g n p.2) (by fun_prop) := rfl

@[simp]
lemma feedbackCondObsAction_evalSeqObs (n : ℕ) :
    (Environment.evalSeqObs o g hg).feedbackCondObsAction n
      = Kernel.deterministic (fun p ↦ g n p.2) (by fun_prop) := by
  simp [Environment.evalSeqObs]

/-- Without observations, `Environment.evalSeqObs` is `Environment.evalSeq`. -/
lemma Environment.evalSeqObs_eq_evalSeq :
    Environment.evalSeqObs (fun _ ↦ ()) g hg = Environment.evalSeq g hg := by
  ext n : 2 <;> simp

/-- `Environment.evalSeqObs o g hg` is the deterministic environment whose observations `o n` and
feedback functions `g n` do not depend on the history. -/
lemma Environment.evalSeqObs_eq_deterministic :
    Environment.evalSeqObs o g hg =
      Environment.deterministic (fun n _ ↦ o n) (fun _ ↦ measurable_const) (fun n p ↦ g n p.2)
        (fun n ↦ (hg n).comp measurable_snd) := by
  ext n : 2
  · ext h : 1
    rw [obs_evalSeqObs, obs_deterministic, Kernel.const_apply, Kernel.deterministic_apply]
  · rw [feedback_evalSeqObs, feedback_deterministic]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm 𝓞 𝓐 𝓨} {P : Measure Ω}
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

/-- Along a run against `Environment.evalSeqObs o g hg`, the observation at time `n` is almost
surely `o n`. -/
lemma IsAlgEnvSeq.obs_ae_eq_evalSeqObs [IsProbabilityMeasure P] [MeasurableSingletonClass 𝓞]
    (h : IsAlgEnvSeq O A Y alg (Environment.evalSeqObs o g hg) P) (n : ℕ) :
    O n =ᵐ[P] fun _ ↦ o n :=
  (h.hasCondDistrib_obs n).hasLaw_of_const.ae_eq_of_dirac

/-- Along a run against `Environment.evalSeqObs o g hg`, the observations are almost surely the
sequence `o`. -/
lemma IsAlgEnvSeq.obs_ae_all_eq_evalSeqObs [IsProbabilityMeasure P] [MeasurableSingletonClass 𝓞]
    (h : IsAlgEnvSeq O A Y alg (Environment.evalSeqObs o g hg) P) :
    ∀ᵐ ω ∂P, ∀ n, O n ω = o n :=
  ae_all_iff.2 h.obs_ae_eq_evalSeqObs

/-- Along a run against `Environment.evalSeqObs o g hg`, the feedback at time `n` is almost surely
`g n` evaluated at the action at time `n`. -/
lemma IsAlgEnvSeq.feedback_ae_eq_evalSeqObs [SFinite P] [MeasurableEq 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.evalSeqObs o g hg) P) (n : ℕ) :
    Y n =ᵐ[P] g n ∘ A n := by
  have hY := h.hasCondDistrib_feedback_feedbackCondObsAction n
  rw [feedbackCondObsAction_evalSeqObs] at hY
  exact hY.ae_eq_of_deterministic

/-- Along a run against `Environment.evalSeqObs o g hg`, the feedback at every time is almost
surely `g` evaluated at the action at that time. -/
lemma IsAlgEnvSeq.feedback_ae_all_eq_evalSeqObs [SFinite P] [MeasurableEq 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.evalSeqObs o g hg) P) :
    ∀ᵐ ω ∂P, ∀ n, Y n ω = g n (A n ω) :=
  ae_all_iff.2 h.feedback_ae_eq_evalSeqObs

end EvalSeqObs

/-- The evaluation environment where the feedback is given by evaluating a fixed measurable function
`f` at the chosen action. -/
noncomputable def Environment.eval (f : 𝓐 → 𝓨) (hf : Measurable f) : Environment Unit 𝓐 𝓨 :=
  Environment.evalSeq (fun _ ↦ f) (fun _ ↦ hf)

instance : (Environment.eval f hf).IsStationary where
  exists_obs_eq_const := ⟨Measure.dirac (), inferInstance, fun _ ↦ rfl⟩
  exists_feedback_eq_comap :=
    ⟨(Kernel.deterministic f hf).prodMkLeft Unit, inferInstance, fun _ ↦ rfl⟩

instance : (Environment.eval f hf).IsOblivious := by unfold Environment.eval; infer_instance

instance : (Environment.eval f hf).HasDeterministicFeedback := by
  unfold Environment.eval; infer_instance

@[simp]
lemma obs_eval (n : ℕ) : (Environment.eval f hf).obs n = Kernel.const _ (Measure.dirac ()) := rfl

@[simp]
lemma feedback_eval (n : ℕ) :
    (Environment.eval f hf).feedback n = Kernel.deterministic (fun p ↦ f p.2) (by fun_prop) := rfl

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

section Eval

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm Unit 𝓐 𝓨}
  {P : Measure Ω} [SFinite P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

lemma IsAlgEnvSeq.hasCondDistrib_feedback_eval (h : IsAlgEnvSeq O A Y alg (Environment.eval f hf) P)
    (n : ℕ) :
    HasCondDistrib (Y n) (A n) (Kernel.deterministic f hf) P :=
  h.hasCondDistrib_feedback_banditSeq n

lemma IsAlgEnvSeq.feedback_ae_eq_eval [MeasurableEq 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.eval f hf) P) (n : ℕ) :
    Y n =ᵐ[P] f ∘ A n := h.feedback_ae_eq_evalSeq n

lemma IsAlgEnvSeq.feedback_ae_all_eq_eval [MeasurableEq 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.eval f hf) P) :
    ∀ᵐ ω ∂P, ∀ n, Y n ω = f (A n ω) := h.feedback_ae_all_eq_evalSeq

open Finset in
lemma IsAlgEnvSeq.comp_feedback_ae_eq_eval {β : Type*} [MeasurableEq 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.eval f hf) P) {n : ℕ} (g : (Iic n → 𝓨) → β) :
    ∀ᵐ ω ∂P, g (fun i ↦ Y i ω) = g (fun i ↦ f (A i ω)) := by
  filter_upwards [h.feedback_ae_all_eq_eval] with ω hω
  simp_rw [hω]

end Eval

end Learning
