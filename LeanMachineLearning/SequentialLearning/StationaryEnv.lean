/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Kernel.Composition.MapComap
public import LeanMachineLearning.SequentialLearning.Algorithm

/-!
# Oblivious and stationary environments

An oblivious environment is an environment in which the distributions of the observation and of
the feedback do not depend on the past history: at time `n`, the observation has law
`env.obsLaw n`, and the feedback depends only on the current observation and action, through the
Markov kernel `env.feedbackCondObsAction n`.
If there are no observations (`𝓞 = Unit`) and the kernel that gives the distribution of the
feedback given the action is the same at every time step, then we say that the environment is
stationary.

## Main definitions

We define a `Prop`-valued typeclass `Environment.IsOblivious` to express that an environment is
oblivious, and we define constructors for oblivious environments, with and without observations.

Typeclass and related definitions:
* `Environment.IsOblivious env`: the environment `env` is oblivious.
* `Environment.obsLaw env n`: the law of the observation at time `n` in an oblivious
  environment `env`.
* `Environment.feedbackCondObsAction env n`: the kernel representing the conditional distribution
  of the feedback given the observation and the action at time `n` in an oblivious
  environment `env`.

Constructors for oblivious environments:
* `Environment.oblivious μ ν`: the oblivious environment in which the observation at time `n` has
  law `μ n` and the feedback at time `n` is drawn from the Markov kernel `ν n : Kernel (𝓞 × 𝓐) 𝓨`
  applied to the observation and the action at time `n`.
* `Environment.stationary μ ν`: the oblivious environment with constant sequences: the observations
  have law `μ` and the feedback is drawn from `ν` applied to the observation and the action.
* `Environment.banditSeq ν`, `Environment.bandit ν`: the versions without observations
  (`𝓞 = Unit`), in which the feedback at time `n` is drawn from `ν n : Kernel 𝓐 𝓨`
  (respectively from `ν : Kernel 𝓐 𝓨`) applied to the action at time `n`.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}

/-- An environment is oblivious if the distributions of the next observation and feedback
don't depend on the past history: the observation at time `n` has a fixed law, and the feedback
at time `n` depends only on the observation and the action at time `n`. -/
class Environment.IsOblivious (env : Environment 𝓞 𝓐 𝓨) : Prop where
  exists_obs_eq_const : ∃ μ : ℕ → Measure 𝓞, (∀ n, IsProbabilityMeasure (μ n)) ∧
    ∀ n, env.obs n = Kernel.const _ (μ n)
  exists_feedback_eq_comap : ∃ ν : ℕ → Kernel (𝓞 × 𝓐) 𝓨, (∀ n, IsMarkovKernel (ν n)) ∧
    ∀ n, env.feedback n = (ν n).comap (fun p ↦ (p.1.2, p.2)) (by fun_prop)

namespace Environment

/-- The law of the observation at time `n` in an oblivious environment. -/
noncomputable
def obsLaw (env : Environment 𝓞 𝓐 𝓨) [h_obl : env.IsOblivious] (n : ℕ) : Measure 𝓞 :=
  h_obl.exists_obs_eq_const.choose n

instance (env : Environment 𝓞 𝓐 𝓨) [env.IsOblivious] (n : ℕ) :
    IsProbabilityMeasure (env.obsLaw n) :=
  IsOblivious.exists_obs_eq_const.choose_spec.1 n

lemma obs_eq_const_obsLaw (env : Environment 𝓞 𝓐 𝓨) [env.IsOblivious] (n : ℕ) :
    env.obs n = Kernel.const _ (env.obsLaw n) :=
  IsOblivious.exists_obs_eq_const.choose_spec.2 n

lemma obsZero_eq_obsLaw (env : Environment 𝓞 𝓐 𝓨) [env.IsOblivious] :
    env.obsZero = env.obsLaw 0 := by
  rw [Environment.obsZero_def, obs_eq_const_obsLaw, Kernel.const_apply]

/-- The kernel representing the conditional distribution of the feedback given the observation and
the action at time `n` in an oblivious environment. -/
noncomputable
def feedbackCondObsAction (env : Environment 𝓞 𝓐 𝓨) [h_obl : env.IsOblivious] (n : ℕ) :
    Kernel (𝓞 × 𝓐) 𝓨 :=
  h_obl.exists_feedback_eq_comap.choose n

instance (env : Environment 𝓞 𝓐 𝓨) [env.IsOblivious] (n : ℕ) :
    IsMarkovKernel (env.feedbackCondObsAction n) :=
  IsOblivious.exists_feedback_eq_comap.choose_spec.1 n

lemma feedback_eq_comap_feedbackCondObsAction (env : Environment 𝓞 𝓐 𝓨) [env.IsOblivious]
    (n : ℕ) :
    env.feedback n = (env.feedbackCondObsAction n).comap (fun p ↦ (p.1.2, p.2)) (by fun_prop) :=
  IsOblivious.exists_feedback_eq_comap.choose_spec.2 n

lemma feedbackZero_eq_feedbackCondObsAction (env : Environment 𝓞 𝓐 𝓨) [env.IsOblivious] :
    env.feedbackZero = env.feedbackCondObsAction 0 := by
  ext p : 1
  rw [Environment.feedbackZero_def, Kernel.comap_apply, feedback_eq_comap_feedbackCondObsAction,
    Kernel.comap_apply]

end Environment

namespace Environment.IsOblivious

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨} {P : Measure Ω}
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {n N : ℕ}

/-- The observation at time `n` has law `env.obsLaw n`. -/
lemma hasLaw_obs [IsProbabilityMeasure P] [env.IsOblivious]
    (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    HasLaw (O n) (env.obsLaw n) P := by
  have h' := h.hasCondDistrib_obs n
  rw [env.obs_eq_const_obsLaw] at h'
  exact h'.hasLaw_of_const

variable [IsFiniteMeasure P]

lemma hasCondDistrib_feedback_history_action [env.IsOblivious]
    (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    HasCondDistrib (Y n) (fun ω ↦ ((history O A Y n ω, O n ω), A n ω))
      ((env.feedbackCondObsAction n).comap (fun p ↦ (p.1.2, p.2)) (by fun_prop)
        : Kernel ((Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐) 𝓨) P := by
  rw [← env.feedback_eq_comap_feedbackCondObsAction]
  exact h.hasCondDistrib_feedback n

/-- The conditional distribution of the feedback at time `n` given the observation and the action
at time `n` is `env.feedbackCondObsAction n`. -/
lemma hasCondDistrib_feedback [env.IsOblivious] (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    HasCondDistrib (Y n) (fun ω ↦ (O n ω, A n ω)) (env.feedbackCondObsAction n) P :=
  (hasCondDistrib_feedback_history_action h n).comp_right

/-- Conditionally on an event determined by the history before time `n`, the observation and the
action at time `n`, on which the observation-action pair is equal to `b`, the feedback at time `n`
has law `env.feedbackCondObsAction n b`. -/
lemma hasLaw_feedback_cond [env.IsOblivious] (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ)
    {s : Set ((Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐)} (hs : MeasurableSet s) {b : 𝓞 × 𝓐}
    (hsb : ∀ u ∈ s, (u.1.2, u.2) = b)
    (hP : P ((fun ω ↦ ((history O A Y n ω, O n ω), A n ω)) ⁻¹' s) ≠ 0) :
    HasLaw (Y n) (env.feedbackCondObsAction n b)
      P[|(fun ω ↦ ((history O A Y n ω, O n ω), A n ω)) ⁻¹' s] := by
  refine (hasCondDistrib_feedback_history_action h n).hasLaw_cond (h.measurable_feedback _) hs
    (fun u hu ↦ ?_) hP
  rw [Kernel.comap_apply, hsb u hu]

/-- Conditionally on an event determined by the history before time `n`, the observation and the
action at time `n`, on which the observation-action pair is constant, the feedback at time `n` is
independent of the history before time `n`, the observation and the action at time `n`. -/
lemma indepFun_history_action_feedback_cond [env.IsOblivious]
    (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ)
    {s : Set ((Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐)} (hs : MeasurableSet s) {b : 𝓞 × 𝓐}
    (hsb : ∀ u ∈ s, (u.1.2, u.2) = b) :
    (fun ω ↦ ((history O A Y n ω, O n ω), A n ω))
      ⟂ᵢ[P[|(fun ω ↦ ((history O A Y n ω, O n ω), A n ω)) ⁻¹' s]] Y n := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  refine (hasCondDistrib_feedback_history_action h n).indepFun_cond (by fun_prop) hs
    (η := env.feedbackCondObsAction n b) fun u hu ↦ ?_
  rw [Kernel.comap_apply, hsb u hu]

variable [StandardBorelSpace 𝓞] [Nonempty 𝓞] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
  [StandardBorelSpace 𝓨] [Nonempty 𝓨]

/-- The feedback at time `n` is conditionally independent of the history before time `n`, given
the observation and the action at time `n`. -/
lemma condIndepFun_feedback_history [StandardBorelSpace Ω]
    [env.IsOblivious] (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    Y n ⟂ᵢ[fun ω ↦ (O n ω, A n ω), (h.measurable_obs n).prodMk (h.measurable_action n); P]
      history O A Y n := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  refine condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    (η := env.feedbackCondObsAction n) (by fun_prop) (by fun_prop) (by fun_prop) ?_
  refine HasCondDistrib.condDistrib_eq ?_
  have h' := hasCondDistrib_feedback_history_action h n
  have hκ : ((env.feedbackCondObsAction n).comap (fun p ↦ (p.1.2, p.2)) (by fun_prop)
        : Kernel ((Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐) 𝓨)
      = ((env.feedbackCondObsAction n).prodMkLeft (Hist 𝓞 𝓐 𝓨 n)).comap
          (fun p ↦ (p.1.1, (p.1.2, p.2))) (by fun_prop) := rfl
  rw [hκ] at h'
  exact h'.comp_right

/-- The feedback at time `n` is conditionally independent of the history before time `n`, the
observation and the action at time `n`, given the observation and the action at time `n`. -/
lemma condIndepFun_feedback_history_obs_action [StandardBorelSpace Ω]
    [env.IsOblivious] (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    Y n ⟂ᵢ[fun ω ↦ (O n ω, A n ω), (h.measurable_obs n).prodMk (h.measurable_action n); P]
      (fun ω ↦ (history O A Y n ω, (O n ω, A n ω))) := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  exact (condIndepFun_feedback_history h n).prod_right (by fun_prop) (by fun_prop) (by fun_prop)

end Environment.IsOblivious

section Oblivious

variable {μ : ℕ → Measure 𝓞} [∀ n, IsProbabilityMeasure (μ n)]
  {ν : ℕ → Kernel (𝓞 × 𝓐) 𝓨} [hν : ∀ n, IsMarkovKernel (ν n)]

/-- The oblivious environment in which the observation at time `n` has law `μ n` and the feedback
at time `n` is drawn from `ν n` applied to the observation and the action at time `n`, whatever the
past history. -/
noncomputable
def Environment.oblivious (μ : ℕ → Measure 𝓞) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : ℕ → Kernel (𝓞 × 𝓐) 𝓨) [∀ n, IsMarkovKernel (ν n)] : Environment 𝓞 𝓐 𝓨 where
  obs n := Kernel.const _ (μ n)
  feedback n := (ν n).comap (fun p ↦ (p.1.2, p.2)) (by fun_prop)

@[simp]
lemma obs_oblivious (n : ℕ) : (Environment.oblivious μ ν).obs n = Kernel.const _ (μ n) := rfl

@[simp]
lemma feedback_oblivious (n : ℕ) :
    (Environment.oblivious μ ν).feedback n = (ν n).comap (fun p ↦ (p.1.2, p.2)) (by fun_prop) := rfl

@[simp]
lemma obsZero_oblivious : (Environment.oblivious μ ν).obsZero = μ 0 := rfl

@[simp]
lemma feedbackZero_oblivious : (Environment.oblivious μ ν).feedbackZero = ν 0 := by
  ext p : 1
  rw [Environment.feedbackZero_def, Kernel.comap_apply, feedback_oblivious, Kernel.comap_apply]

lemma stepKernel_oblivious (alg : Algorithm 𝓞 𝓐 𝓨) (n : ℕ) :
    stepKernel alg (Environment.oblivious μ ν) n
      = Kernel.const _ (μ n)
        ⊗ₖ (alg.policy n ⊗ₖ (ν n).comap (fun p ↦ (p.1.2, p.2)) (by fun_prop)) :=
  rfl

instance : (Environment.oblivious μ ν).IsOblivious where
  exists_obs_eq_const := ⟨μ, inferInstance, fun _ ↦ rfl⟩
  exists_feedback_eq_comap := ⟨ν, inferInstance, fun _ ↦ rfl⟩

/-- The law of the observations of `Environment.oblivious μ ν` is `μ`. The nonemptiness assumptions
ensure that there are histories of every length, so that the observation kernels determine `μ`. -/
@[simp]
lemma obsLaw_oblivious [Nonempty 𝓐] [Nonempty 𝓨] (n : ℕ) :
    (Environment.oblivious μ ν).obsLaw n = μ n := by
  have : Nonempty 𝓞 := Measure.nonempty_of_neZero (μ n)
  have h_eq := (Environment.oblivious μ ν).obs_eq_const_obsLaw n
  rw [obs_oblivious, Kernel.ext_iff] at h_eq
  simpa using (h_eq (Classical.arbitrary _)).symm

@[simp]
lemma feedbackCondObsAction_oblivious (n : ℕ) :
    (Environment.oblivious μ ν).feedbackCondObsAction n = ν n := by
  rcases isEmpty_or_nonempty 𝓞 with h𝓞 | h𝓞
  · ext p : 1
    exact h𝓞.elim p.1
  rcases isEmpty_or_nonempty 𝓐 with h𝓐 | h𝓐
  · ext p : 1
    exact h𝓐.elim p.2
  rcases isEmpty_or_nonempty 𝓨 with h𝓨 | h𝓨
  · refine absurd (hν 0) ?_
    simp only [Subsingleton.eq_zero ν, Pi.zero_apply]
    exact Kernel.not_isMarkovKernel_zero
  have h_eq := (Environment.oblivious μ ν).feedback_eq_comap_feedbackCondObsAction n
  rw [feedback_oblivious, Kernel.ext_iff] at h_eq
  ext p : 1
  obtain ⟨o, a⟩ := p
  exact (h_eq ((Classical.arbitrary _, o), a)).symm

end Oblivious

section Stationary

variable {μ : Measure 𝓞} [IsProbabilityMeasure μ] {ν : Kernel (𝓞 × 𝓐) 𝓨} [IsMarkovKernel ν]

/-- The stationary environment in which the observations have law `μ` and the feedback is drawn
from `ν` applied to the observation and the action, whatever the past history. -/
noncomputable
def Environment.stationary (μ : Measure 𝓞) [IsProbabilityMeasure μ] (ν : Kernel (𝓞 × 𝓐) 𝓨)
    [IsMarkovKernel ν] : Environment 𝓞 𝓐 𝓨 :=
  Environment.oblivious (fun _ ↦ μ) (fun _ ↦ ν)

lemma Environment.stationary_def :
    Environment.stationary μ ν = Environment.oblivious (fun _ ↦ μ) (fun _ ↦ ν) := rfl

@[simp]
lemma obs_stationary (n : ℕ) : (Environment.stationary μ ν).obs n = Kernel.const _ μ := rfl

@[simp]
lemma feedback_stationary (n : ℕ) :
    (Environment.stationary μ ν).feedback n = ν.comap (fun p ↦ (p.1.2, p.2)) (by fun_prop) := rfl

@[simp]
lemma obsZero_stationary : (Environment.stationary μ ν).obsZero = μ := rfl

@[simp]
lemma feedbackZero_stationary : (Environment.stationary μ ν).feedbackZero = ν :=
  feedbackZero_oblivious

lemma stepKernel_stationary (alg : Algorithm 𝓞 𝓐 𝓨) (n : ℕ) :
    stepKernel alg (Environment.stationary μ ν) n
      = Kernel.const _ μ ⊗ₖ (alg.policy n ⊗ₖ ν.comap (fun p ↦ (p.1.2, p.2)) (by fun_prop)) :=
  rfl

instance : (Environment.stationary μ ν).IsOblivious :=
  inferInstanceAs (Environment.oblivious _ _).IsOblivious

@[simp]
lemma obsLaw_stationary [Nonempty 𝓐] [Nonempty 𝓨] (n : ℕ) :
    (Environment.stationary μ ν).obsLaw n = μ :=
  obsLaw_oblivious n

@[simp]
lemma feedbackCondObsAction_stationary (n : ℕ) :
    (Environment.stationary μ ν).feedbackCondObsAction n = ν :=
  feedbackCondObsAction_oblivious n

end Stationary

section BanditSeq

variable {ν : ℕ → Kernel 𝓐 𝓨} [∀ n, IsMarkovKernel (ν n)]

/-- The oblivious environment without observations in which the feedback at time `n` is drawn from
`ν n` applied to the action at time `n`, whatever the past history. -/
noncomputable
def Environment.banditSeq (ν : ℕ → Kernel 𝓐 𝓨) [∀ n, IsMarkovKernel (ν n)] :
    Environment Unit 𝓐 𝓨 :=
  Environment.oblivious (fun _ ↦ Measure.dirac ()) (fun n ↦ (ν n).prodMkLeft Unit)

lemma Environment.banditSeq_def :
    Environment.banditSeq ν
      = Environment.oblivious (fun _ ↦ Measure.dirac ()) (fun n ↦ (ν n).prodMkLeft Unit) :=
  rfl

@[simp]
lemma obs_banditSeq (n : ℕ) :
    (Environment.banditSeq ν).obs n = Kernel.const _ (Measure.dirac ()) := rfl

@[simp]
lemma feedback_banditSeq (n : ℕ) : (Environment.banditSeq ν).feedback n = (ν n).prodMkLeft _ := rfl

@[simp]
lemma obsZero_banditSeq : (Environment.banditSeq ν).obsZero = Measure.dirac () := rfl

@[simp]
lemma feedbackZero_banditSeq : (Environment.banditSeq ν).feedbackZero = (ν 0).prodMkLeft Unit :=
  feedbackZero_oblivious

instance : (Environment.banditSeq ν).IsOblivious :=
  inferInstanceAs (Environment.oblivious _ _).IsOblivious

@[simp]
lemma obsLaw_banditSeq (n : ℕ) : (Environment.banditSeq ν).obsLaw n = Measure.dirac () :=
  Measure.eq_dirac_unit _

@[simp]
lemma feedbackCondObsAction_banditSeq (n : ℕ) :
    (Environment.banditSeq ν).feedbackCondObsAction n = (ν n).prodMkLeft Unit :=
  feedbackCondObsAction_oblivious n

end BanditSeq

section Bandit

variable {ν : Kernel 𝓐 𝓨} [IsMarkovKernel ν]

/-- The stationary environment without observations in which the feedback is drawn from `ν`
applied to the action, whatever the past history: a stochastic bandit. -/
noncomputable
def Environment.bandit (ν : Kernel 𝓐 𝓨) [IsMarkovKernel ν] : Environment Unit 𝓐 𝓨 :=
  Environment.stationary (Measure.dirac ()) (ν.prodMkLeft Unit)

lemma Environment.bandit_def :
    Environment.bandit ν = Environment.stationary (Measure.dirac ()) (ν.prodMkLeft Unit) := rfl

lemma Environment.bandit_eq_banditSeq : Environment.bandit ν = Environment.banditSeq fun _ ↦ ν :=
  rfl

@[simp]
lemma obs_bandit (n : ℕ) : (Environment.bandit ν).obs n = Kernel.const _ (Measure.dirac ()) := rfl

@[simp]
lemma feedback_bandit (n : ℕ) : (Environment.bandit ν).feedback n = ν.prodMkLeft _ := rfl

lemma stepKernel_bandit (alg : Algorithm Unit 𝓐 𝓨) (n : ℕ) :
    stepKernel alg (Environment.bandit ν) n
      = Kernel.const _ (Measure.dirac ()) ⊗ₖ (alg.policy n ⊗ₖ ν.prodMkLeft _) := by
  rw [stepKernel_def, obs_bandit, feedback_bandit]

@[simp]
lemma obsZero_bandit : (Environment.bandit ν).obsZero = Measure.dirac () := rfl

@[simp]
lemma feedbackZero_bandit : (Environment.bandit ν).feedbackZero = ν.prodMkLeft Unit :=
  feedbackZero_oblivious

instance : (Environment.bandit ν).IsOblivious :=
  inferInstanceAs (Environment.oblivious _ _).IsOblivious

@[simp]
lemma obsLaw_bandit (n : ℕ) : (Environment.bandit ν).obsLaw n = Measure.dirac () :=
  Measure.eq_dirac_unit _

@[simp]
lemma feedbackCondObsAction_bandit (n : ℕ) :
    (Environment.bandit ν).feedbackCondObsAction n = ν.prodMkLeft Unit :=
  feedbackCondObsAction_oblivious n

end Bandit

namespace IsAlgEnvSeq

section General

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm 𝓞 𝓐 𝓨}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

/-- The observation at time `n` has law `μ n`. -/
lemma hasLaw_obs_oblivious {μ : ℕ → Measure 𝓞} [∀ n, IsProbabilityMeasure (μ n)]
    {ν : ℕ → Kernel (𝓞 × 𝓐) 𝓨} [∀ n, IsMarkovKernel (ν n)]
    (h : IsAlgEnvSeq O A Y alg (Environment.oblivious μ ν) P) (n : ℕ) :
    HasLaw (O n) (μ n) P := by
  have h' := h.hasCondDistrib_obs n
  rw [obs_oblivious] at h'
  exact h'.hasLaw_of_const

/-- The conditional distribution of the feedback at time `n` given the observation and the action
at time `n` is `ν n`. -/
lemma hasCondDistrib_feedback_oblivious {μ : ℕ → Measure 𝓞} [∀ n, IsProbabilityMeasure (μ n)]
    {ν : ℕ → Kernel (𝓞 × 𝓐) 𝓨} [∀ n, IsMarkovKernel (ν n)]
    (h : IsAlgEnvSeq O A Y alg (Environment.oblivious μ ν) P) (n : ℕ) :
    HasCondDistrib (Y n) (fun ω ↦ (O n ω, A n ω)) (ν n) P := by
  have h' := h.hasCondDistrib_feedback n
  rw [feedback_oblivious] at h'
  exact h'.comp_right

/-- The observation at time `n` has law `μ`. -/
lemma hasLaw_obs_stationary {μ : Measure 𝓞} [IsProbabilityMeasure μ]
    {ν : Kernel (𝓞 × 𝓐) 𝓨} [IsMarkovKernel ν]
    (h : IsAlgEnvSeq O A Y alg (Environment.stationary μ ν) P) (n : ℕ) :
    HasLaw (O n) μ P :=
  hasLaw_obs_oblivious h n

/-- The conditional distribution of the feedback at time `n` given the observation and the action
at time `n` is `ν`. -/
lemma hasCondDistrib_feedback_stationary {μ : Measure 𝓞} [IsProbabilityMeasure μ]
    {ν : Kernel (𝓞 × 𝓐) 𝓨} [IsMarkovKernel ν]
    (h : IsAlgEnvSeq O A Y alg (Environment.stationary μ ν) P) (n : ℕ) :
    HasCondDistrib (Y n) (fun ω ↦ (O n ω, A n ω)) ν P :=
  hasCondDistrib_feedback_oblivious h n

end General

section Bandit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {alg : Algorithm Unit 𝓐 𝓨} {ν : Kernel 𝓐 𝓨} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

/-- The conditional distribution of the feedback at time `n` given the action at time `n`
is `ν n`. -/
lemma hasCondDistrib_feedback_banditSeq {ν : ℕ → Kernel 𝓐 𝓨} [∀ n, IsMarkovKernel (ν n)]
    (h : IsAlgEnvSeq O A Y alg (Environment.banditSeq ν) P) (n : ℕ) :
    HasCondDistrib (Y n) (A n) (ν n) P := by
  have h' : HasCondDistrib (Y n) (fun ω ↦ (O n ω, A n ω)) ((ν n).prodMkLeft Unit) P :=
    hasCondDistrib_feedback_oblivious h n
  exact h'.comp_right

/-- The conditional distribution of the feedback at time `n` given the action at time `n` is `ν`. -/
lemma hasCondDistrib_feedback_bandit
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (n : ℕ) :
    HasCondDistrib (Y n) (A n) ν P :=
  hasCondDistrib_feedback_banditSeq h n

/-- The conditional distribution of the feedback at time `n` given the action at time `n` is `ν`. -/
lemma condDistrib_feedback_bandit [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (n : ℕ) :
    condDistrib (Y n) (A n) P =ᵐ[P.map (A n)] ν :=
  (hasCondDistrib_feedback_bandit h n).condDistrib_eq

/-- Conditionally on an event determined by the history before time `n` and the action at time
`n`, on which that action is equal to `b`, the feedback at time `n` has law `ν b`. -/
lemma hasLaw_feedback_cond_bandit (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (n : ℕ)
    {s : Set ((Hist Unit 𝓐 𝓨 n × Unit) × 𝓐)} (hs : MeasurableSet s) {b : 𝓐}
    (hsb : ∀ u ∈ s, u.2 = b)
    (hP : P ((fun ω ↦ ((history O A Y n ω, O n ω), A n ω)) ⁻¹' s) ≠ 0) :
    HasLaw (Y n) (ν b) P[|(fun ω ↦ ((history O A Y n ω, O n ω), A n ω)) ⁻¹' s] := by
  simpa using Environment.IsOblivious.hasLaw_feedback_cond h n hs (b := ((), b))
    (fun u hu ↦ by simp [hsb u hu]) hP

/-- Conditionally on an event determined by the history before time `n` and the action at time
`n`, on which that action is constant, the feedback at time `n` is independent of the
history before time `n` and of the action at time `n`. -/
lemma indepFun_history_action_feedback_cond_bandit
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (n : ℕ)
    {s : Set ((Hist Unit 𝓐 𝓨 n × Unit) × 𝓐)} (hs : MeasurableSet s) {b : 𝓐}
    (hsb : ∀ u ∈ s, u.2 = b) :
    (fun ω ↦ ((history O A Y n ω, O n ω), A n ω))
      ⟂ᵢ[P[|(fun ω ↦ ((history O A Y n ω, O n ω), A n ω)) ⁻¹' s]] Y n :=
  Environment.IsOblivious.indepFun_history_action_feedback_cond h n hs (b := ((), b))
    fun u hu ↦ by simp [hsb u hu]

/-- The feedback at time `n` is conditionally independent of the history before time `n`
given the action at time `n`. -/
lemma condIndepFun_feedback_history_action_bandit [StandardBorelSpace Ω]
    [StandardBorelSpace 𝓐] [Nonempty 𝓐] [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (n : ℕ) :
    Y n ⟂ᵢ[A n, h.measurable_action _ ; P] (fun ω ↦ (history O A Y n ω, O n ω)) := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  refine condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft (η := ν)
    (by fun_prop) (by fun_prop) (by fun_prop) ?_
  refine HasCondDistrib.condDistrib_eq ?_
  have h' := h.hasCondDistrib_feedback n
  rwa [feedback_bandit] at h'

lemma condIndepFun_feedback_history_action_action_bandit [StandardBorelSpace Ω]
    [StandardBorelSpace 𝓐] [Nonempty 𝓐] [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (n : ℕ) :
    Y n ⟂ᵢ[A n, h.measurable_action n; P]
      (fun ω ↦ ((history O A Y n ω, O n ω), A n ω)) := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  exact (condIndepFun_feedback_history_action_bandit h n).prod_right (by fun_prop) (by fun_prop)
    (by fun_prop)

end Bandit

end IsAlgEnvSeq

end Learning
