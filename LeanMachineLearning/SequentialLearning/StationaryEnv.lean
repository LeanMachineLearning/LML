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

An oblivious environment is an environment in which the distribution of the next feedback depends
only on the last action (and not on the past history nor on the current observation).
If the kernel that gives the distribution of the next feedback given the last action is the same at
every time step, then we say that the environment is stationary.

## Main definitions

We define a `Prop`-valued typeclass `IsObliviousEnv` to express that an environment is oblivious,
and we define two constructors for oblivious environments. Those constructors build environments
without observations, that is with observation type `Unit`.

Typeclass and related definitions:
* `IsObliviousEnv env`: the environment `env` is oblivious.
* `feedbackCondAction env n`: the kernel representing the conditional distribution of the feedback
  given the action at time `n` in an oblivious environment `env`.

Constructors for oblivious environments:
* `obliviousEnv ν`: an oblivious environment without observations, in which the distribution of the
  next feedback depends only on the last action, but in a possibly time-dependent manner, and is
  given by a sequence of Markov kernels `ν : ℕ → Kernel 𝓐 𝓨`.
* `stationaryEnv ν`: a stationary environment without observations, in which the distribution of
  the next feedback depends only on the last action (and not on the past history), and is given by
  a Markov kernel `ν : Kernel 𝓐 𝓨`.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}

/-- An environment is oblivious if the distribution of the next feedback depends only on
the last action and not on the past history nor on the current observation. -/
class IsObliviousEnv (env : Environment 𝓞 𝓐 𝓨) : Prop where
  exists_eq_prodMkLeft : ∃ ν : ℕ → Kernel 𝓐 𝓨, (∀ n, IsMarkovKernel (ν n)) ∧
    (∀ n, env.feedback n = (ν n).prodMkLeft _)

/-- The kernel representing the conditional distribution of the feedback given the action
at time `n` in an oblivious environment. -/
noncomputable
def feedbackCondAction (env : Environment 𝓞 𝓐 𝓨) [h_obl : IsObliviousEnv env] (n : ℕ) :
    Kernel 𝓐 𝓨 :=
  h_obl.exists_eq_prodMkLeft.choose n

instance (env : Environment 𝓞 𝓐 𝓨) [IsObliviousEnv env] (n : ℕ) :
    IsMarkovKernel (feedbackCondAction env n) :=
  IsObliviousEnv.exists_eq_prodMkLeft.choose_spec.1 n

lemma feedback_eq_feedbackCondAction (env : Environment 𝓞 𝓐 𝓨) [IsObliviousEnv env] (n : ℕ) :
    env.feedback n = (feedbackCondAction env n).prodMkLeft _ :=
  IsObliviousEnv.exists_eq_prodMkLeft.choose_spec.2 n

lemma ν0_eq_feedbackCondAction (env : Environment 𝓞 𝓐 𝓨) [IsObliviousEnv env] :
    env.ν0 = (feedbackCondAction env 0).prodMkLeft 𝓞 := by
  ext p : 1
  rw [Environment.ν0_def, Kernel.comap_apply, feedback_eq_feedbackCondAction,
    Kernel.prodMkLeft_apply, Kernel.prodMkLeft_apply]

namespace IsObliviousEnv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨} {P : Measure Ω} [IsFiniteMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {n N : ℕ}
  {ν : ℕ → Kernel 𝓐 𝓨} [∀ n, IsMarkovKernel (ν n)]

lemma hasCondDistrib_feedback_history_action [IsObliviousEnv env]
    (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    HasCondDistrib (Y n) (fun ω ↦ ((history O A Y n ω, O n ω), A n ω))
      ((feedbackCondAction env n).prodMkLeft _) P := by
  rw [← feedback_eq_feedbackCondAction]
  exact h.hasCondDistrib_feedback n

lemma hasCondDistrib_feedback [IsObliviousEnv env] (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    HasCondDistrib (Y n) (A n) (feedbackCondAction env n) P :=
  (hasCondDistrib_feedback_history_action h n).comp_right

variable [StandardBorelSpace 𝓞] [Nonempty 𝓞] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
  [StandardBorelSpace 𝓨] [Nonempty 𝓨]

/-- The feedback at time `n` is conditionally independent of the history before time `n` and of
the observation at time `n`, given the action at time `n`. -/
lemma condIndepFun_feedback_history_action [StandardBorelSpace Ω]
        [IsObliviousEnv env] (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    Y n ⟂ᵢ[A n, h.measurable_action _ ; P] (fun ω ↦ (history O A Y n ω, O n ω)) := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  refine condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    (η := feedbackCondAction env n)
    (by fun_prop) (by fun_prop) (by fun_prop) ?_
  refine HasCondDistrib.condDistrib_eq ?_
  rw [← feedback_eq_feedbackCondAction]
  exact h.hasCondDistrib_feedback n

lemma condIndepFun_feedback_history_action_action [StandardBorelSpace Ω]
    [IsObliviousEnv env] (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    Y n ⟂ᵢ[A n, h.measurable_action n; P] (fun ω ↦ ((history O A Y n ω, O n ω), A n ω)) := by
  have h_indep : Y n ⟂ᵢ[A n, h.measurable_action n; P]
      (fun ω ↦ (history O A Y n ω, O n ω)) := condIndepFun_feedback_history_action h n
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  exact h_indep.prod_right (by fun_prop) (by fun_prop) (by fun_prop)

end IsObliviousEnv

/-- An oblivious environment without observations, in which the distribution of the next feedback
depends only on the last action, but in a possibly time-dependent manner. -/
@[simps]
noncomputable
def obliviousEnv (ν : ℕ → Kernel 𝓐 𝓨) [∀ n, IsMarkovKernel (ν n)] : Environment Unit 𝓐 𝓨 where
  obs _ := Kernel.const _ (Measure.dirac ())
  feedback n := (ν n).prodMkLeft _

lemma feedback_obliviousEnv (ν : ℕ → Kernel 𝓐 𝓨) [∀ n, IsMarkovKernel (ν n)] (n : ℕ) :
    (obliviousEnv ν).feedback n = (ν n).prodMkLeft _ := rfl

@[simp]
lemma obs0_obliviousEnv (ν : ℕ → Kernel 𝓐 𝓨) [∀ n, IsMarkovKernel (ν n)] :
    (obliviousEnv ν).obs0 = Measure.dirac () := rfl

@[simp]
lemma ν0_obliviousEnv (ν : ℕ → Kernel 𝓐 𝓨) [∀ n, IsMarkovKernel (ν n)] :
    (obliviousEnv ν).ν0 = (ν 0).prodMkLeft Unit := by
  ext p : 1
  rw [Environment.ν0_def, Kernel.comap_apply, feedback_obliviousEnv, Kernel.prodMkLeft_apply,
    Kernel.prodMkLeft_apply]

instance (ν : ℕ → Kernel 𝓐 𝓨) [∀ n, IsMarkovKernel (ν n)] :
    IsObliviousEnv (obliviousEnv ν) where
  exists_eq_prodMkLeft := ⟨ν, inferInstance, fun _ ↦ rfl⟩

@[simp]
lemma feedbackCondAction_obliviousEnv (ν : ℕ → Kernel 𝓐 𝓨) [hν : ∀ n, IsMarkovKernel (ν n)]
    (n : ℕ) :
    feedbackCondAction (obliviousEnv ν) n = ν n := by
  rcases isEmpty_or_nonempty 𝓐 with h𝓐 | h𝓐
  · ext a : 1
    exact h𝓐.elim a
  rcases isEmpty_or_nonempty 𝓨 with hR | hR
  · refine absurd (hν 0) ?_
    simp only [Subsingleton.eq_zero ν, Pi.zero_apply]
    exact Kernel.not_isMarkovKernel_zero
  have : Nonempty (Hist Unit 𝓐 𝓨 n × Unit) := ⟨(fun _ ↦ ((), h𝓐.some, hR.some), ())⟩
  have h_eq := feedback_eq_feedbackCondAction (obliviousEnv ν) n
  rw [feedback_obliviousEnv, Kernel.prodMkLeft_inj] at h_eq
  exact h_eq.symm

/-- A stationary environment without observations, in which the distribution of the next feedback
depends only on the last action. -/
noncomputable
def stationaryEnv (ν : Kernel 𝓐 𝓨) [IsMarkovKernel ν] : Environment Unit 𝓐 𝓨 :=
  obliviousEnv fun _ ↦ ν

@[simp]
lemma obs_stationaryEnv (ν : Kernel 𝓐 𝓨) [IsMarkovKernel ν] (n : ℕ) :
    (stationaryEnv ν).obs n = Kernel.const _ (Measure.dirac ()) := rfl

@[simp]
lemma feedback_stationaryEnv (ν : Kernel 𝓐 𝓨) [IsMarkovKernel ν] (n : ℕ) :
    (stationaryEnv ν).feedback n = ν.prodMkLeft _ := rfl

@[simp]
lemma obs0_stationaryEnv (ν : Kernel 𝓐 𝓨) [IsMarkovKernel ν] :
    (stationaryEnv ν).obs0 = Measure.dirac () := rfl

@[simp]
lemma ν0_stationaryEnv (ν : Kernel 𝓐 𝓨) [IsMarkovKernel ν] :
    (stationaryEnv ν).ν0 = ν.prodMkLeft Unit :=
  ν0_obliviousEnv _

instance (ν : Kernel 𝓐 𝓨) [IsMarkovKernel ν] : IsObliviousEnv (stationaryEnv ν) where
  exists_eq_prodMkLeft := ⟨fun _ ↦ ν, inferInstance, fun _ ↦ rfl⟩

@[simp]
lemma feedbackCondAction_stationaryEnv (ν : Kernel 𝓐 𝓨) [hν : IsMarkovKernel ν] (n : ℕ) :
    feedbackCondAction (stationaryEnv ν) n = ν := feedbackCondAction_obliviousEnv _ _

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {alg : Algorithm Unit 𝓐 𝓨} {ν : Kernel 𝓐 𝓨} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

namespace IsAlgEnvSeq

/-- The conditional distribution of the feedback at time `n` given the action at time `n`
is `ν n`. -/
lemma hasCondDistrib_feedback_obliviousEnv {ν : ℕ → Kernel 𝓐 𝓨} [∀ n, IsMarkovKernel (ν n)]
    (h : IsAlgEnvSeq O A Y alg (obliviousEnv ν) P) (n : ℕ) :
    HasCondDistrib (Y n) (A n) (ν n) P := by
  simpa using IsObliviousEnv.hasCondDistrib_feedback h n

/-- The conditional distribution of the feedback at time `n` given the action at time `n` is `ν`. -/
lemma hasCondDistrib_feedback_stationaryEnv
    (h : IsAlgEnvSeq O A Y alg (stationaryEnv ν) P) (n : ℕ) :
    HasCondDistrib (Y n) (A n) ν P :=
  hasCondDistrib_feedback_obliviousEnv h n

/-- The conditional distribution of the feedback at time `n` given the action at time `n` is `ν`. -/
lemma condDistrib_feedback_stationaryEnv [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (h : IsAlgEnvSeq O A Y alg (stationaryEnv ν) P) (n : ℕ) :
    condDistrib (Y n) (A n) P =ᵐ[P.map (A n)] ν :=
  (hasCondDistrib_feedback_stationaryEnv h n).condDistrib_eq

/-- The feedback at time `n` is conditionally independent of the history before time `n`
given the action at time `n`. -/
lemma condIndepFun_feedback_history_action [StandardBorelSpace Ω]
    [StandardBorelSpace 𝓐] [Nonempty 𝓐] [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (h : IsAlgEnvSeq O A Y alg (stationaryEnv ν) P) (n : ℕ) :
    Y n ⟂ᵢ[A n, h.measurable_action _ ; P] (fun ω ↦ (history O A Y n ω, O n ω)) :=
  IsObliviousEnv.condIndepFun_feedback_history_action h n

lemma condIndepFun_feedback_history_action_action [StandardBorelSpace Ω]
    [StandardBorelSpace 𝓐] [Nonempty 𝓐] [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (h : IsAlgEnvSeq O A Y alg (stationaryEnv ν) P) (n : ℕ) :
    Y n ⟂ᵢ[A n, h.measurable_action n; P]
      (fun ω ↦ ((history O A Y n ω, O n ω), A n ω)) :=
  IsObliviousEnv.condIndepFun_feedback_history_action_action h n

end IsAlgEnvSeq

end Learning
