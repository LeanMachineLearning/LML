/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

/-!
# Announced variables

A hidden variable of one of the two players (memory or sampled index of the algorithm, parameter of
the environment) is modelled by making it part of that player's move, while the other player is
transported so as to ignore it:

* the algorithm announces a variable of type `𝓩`: it is an `Algorithm 𝓞 (𝓩 × 𝓐) 𝓨` that runs
  against `env.comapAction Prod.snd`, for an `env : Environment 𝓞 𝓐 𝓨`;
* the environment announces a variable of type `𝓔`: it is an `Environment (𝓔 × 𝓞) 𝓐 𝓨` that runs
  against `alg.comapObs Prod.snd`, for an `alg : Algorithm 𝓞 𝓐 𝓨`.

In both cases the announced variable is an honest random variable of the run, and the player that
ignores it satisfies the conditional distribution properties of a run of the un-announced
interaction: this is the content of `IsAlgEnvSeq.hasCondDistrib_action_comapObs` (the algorithm
does not use the announced variable) and of `IsAlgEnvSeq.hasCondDistrib_obs_comapAction` and
`IsAlgEnvSeq.hasCondDistrib_feedback_comapAction` (the environment does not use it).
The law of the observable trajectory is the image of the law of the full trajectory under the map
that forgets the announced variable.

## Main definitions

* `Round.map fo fa fy`, `Hist.map fo fa fy`, `Traj.map fo fa fy`: round-wise transport of a round,
  a history and a trajectory along maps of the observation, the action and the feedback, with the
  special cases `mapObs`, `mapAction` and `mapFeedback` that transport a single component.
* `Algorithm.comapObs alg f`: the algorithm that sees `f o` when the observation is `o`, both in
  the current round and in the past rounds.
* `Algorithm.comapFeedback alg g`: the algorithm that sees `g y` when the feedback of a past round
  is `y`.
* `Environment.comapAction env f`: the environment that reads `f a` when the algorithm plays `a`,
  both in the current round and in the past rounds.
* `Algorithm.IgnoresAnnounced algZ alg`: the announcing algorithm `algZ` does not read the variables
  it announced in the past rounds, and the law of the action it plays is `alg.policy n`.

## Main statements

* `IsAlgEnvSeq.hasCondDistrib_action_comapObs`, `IsAlgEnvSeq.hasCondDistrib_action_comapFeedback`:
  in a run of `alg.comapObs f` (resp. `alg.comapFeedback g`) against any environment, the
  conditional distribution of the action given the transported history and the transported
  observation is `alg.policy n`.
* `IsAlgEnvSeq.hasCondDistrib_obs_comapAction`, `IsAlgEnvSeq.hasCondDistrib_feedback_comapAction`:
  in a run against `env.comapAction f`, the observations and feedbacks have the conditional
  distributions of a run of `env` on the transported actions.
* `IsAlgEnvSeq.map_trajectory_comapObs`, `IsAlgEnvSeq.map_trajectory_comapFeedback`,
  `IsAlgEnvSeq.map_trajectory_comapAction`: the law of the trajectory that a player sees is the
  image of `trajMeasure` under the forgetful map.
* `IsAlgEnvSeq.hasCondDistrib_announced`: in a run of an announcing algorithm, the announced
  variable of round `n` has the first marginal of the policy for conditional distribution. It is an
  honest random variable of the run, not a variable integrated out inside the policy kernel.
* `IsAlgEnvSeq.isAlgEnvSeq_of_ignoresAnnounced`: **projection of a run**. If the announcing
  algorithm does not read its own past announcements, the observable part of a run of it against
  `env.comapAction Prod.snd` is a run of the behavioral algorithm against `env`. This is the case of
  the projection theorem in which the announced variable is redrawn from the observable history at
  every round; it needs no disintegration.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓞' 𝓐 𝓐' 𝓨 𝓨' Ω : Type*}
  {m𝓞 : MeasurableSpace 𝓞} {m𝓞' : MeasurableSpace 𝓞'}
  {m𝓐 : MeasurableSpace 𝓐} {m𝓐' : MeasurableSpace 𝓐'}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓨' : MeasurableSpace 𝓨'}
  {mΩ : MeasurableSpace Ω}
  {fo : 𝓞 → 𝓞'} {fa : 𝓐 → 𝓐'} {fy : 𝓨 → 𝓨'}

section Map

/-- Transport a round along maps of the observation, the action and the feedback. -/
def Round.map (fo : 𝓞 → 𝓞') (fa : 𝓐 → 𝓐') (fy : 𝓨 → 𝓨') (r : Round 𝓞 𝓐 𝓨) : Round 𝓞' 𝓐' 𝓨' :=
  (fo r.obs, fa r.action, fy r.feedback)

/-- Transport a history round-wise. -/
def Hist.map (fo : 𝓞 → 𝓞') (fa : 𝓐 → 𝓐') (fy : 𝓨 → 𝓨') {n : ℕ} (h : Hist 𝓞 𝓐 𝓨 n) :
    Hist 𝓞' 𝓐' 𝓨' n :=
  fun i ↦ Round.map fo fa fy (h i)

/-- Transport a trajectory round-wise. -/
def Traj.map (fo : 𝓞 → 𝓞') (fa : 𝓐 → 𝓐') (fy : 𝓨 → 𝓨') (τ : ℕ → Round 𝓞 𝓐 𝓨) :
    ℕ → Round 𝓞' 𝓐' 𝓨' :=
  fun n ↦ Round.map fo fa fy (τ n)

@[simp] lemma Round.obs_map (r : Round 𝓞 𝓐 𝓨) : (Round.map fo fa fy r).obs = fo r.obs := rfl
@[simp] lemma Round.action_map (r : Round 𝓞 𝓐 𝓨) :
    (Round.map fo fa fy r).action = fa r.action := rfl
@[simp] lemma Round.feedback_map (r : Round 𝓞 𝓐 𝓨) :
    (Round.map fo fa fy r).feedback = fy r.feedback := rfl

@[simp] lemma Hist.map_apply {n : ℕ} (h : Hist 𝓞 𝓐 𝓨 n) (i : Fin n) :
    Hist.map fo fa fy h i = Round.map fo fa fy (h i) := rfl

@[simp] lemma Traj.map_apply (τ : ℕ → Round 𝓞 𝓐 𝓨) (n : ℕ) :
    Traj.map fo fa fy τ n = Round.map fo fa fy (τ n) := rfl

@[fun_prop]
lemma Round.measurable_map (hfo : Measurable fo) (hfa : Measurable fa) (hfy : Measurable fy) :
    Measurable (Round.map fo fa fy) := by
  unfold Round.map
  fun_prop

@[fun_prop]
lemma Hist.measurable_map (hfo : Measurable fo) (hfa : Measurable fa) (hfy : Measurable fy)
    (n : ℕ) :
    Measurable (Hist.map fo fa fy (n := n)) := by
  unfold Hist.map
  fun_prop

@[fun_prop]
lemma Traj.measurable_map (hfo : Measurable fo) (hfa : Measurable fa) (hfy : Measurable fy) :
    Measurable (Traj.map fo fa fy) := by
  unfold Traj.map
  fun_prop

/-- Transport the observations of a round. -/
abbrev Round.mapObs (f : 𝓞 → 𝓞') (r : Round 𝓞 𝓐 𝓨) : Round 𝓞' 𝓐 𝓨 := Round.map f id id r

/-- Transport the observations of a history. -/
abbrev Hist.mapObs (f : 𝓞 → 𝓞') {n : ℕ} (h : Hist 𝓞 𝓐 𝓨 n) : Hist 𝓞' 𝓐 𝓨 n :=
  Hist.map f id id h

/-- Transport the observations of a trajectory. -/
abbrev Traj.mapObs (f : 𝓞 → 𝓞') (τ : ℕ → Round 𝓞 𝓐 𝓨) : ℕ → Round 𝓞' 𝓐 𝓨 := Traj.map f id id τ

/-- Transport the actions of a round. -/
abbrev Round.mapAction (f : 𝓐 → 𝓐') (r : Round 𝓞 𝓐 𝓨) : Round 𝓞 𝓐' 𝓨 := Round.map id f id r

/-- Transport the actions of a history. -/
abbrev Hist.mapAction (f : 𝓐 → 𝓐') {n : ℕ} (h : Hist 𝓞 𝓐 𝓨 n) : Hist 𝓞 𝓐' 𝓨 n :=
  Hist.map id f id h

/-- Transport the actions of a trajectory. -/
abbrev Traj.mapAction (f : 𝓐 → 𝓐') (τ : ℕ → Round 𝓞 𝓐 𝓨) : ℕ → Round 𝓞 𝓐' 𝓨 :=
  Traj.map id f id τ

/-- Transport the feedback of a round. -/
abbrev Round.mapFeedback (f : 𝓨 → 𝓨') (r : Round 𝓞 𝓐 𝓨) : Round 𝓞 𝓐 𝓨' := Round.map id id f r

/-- Transport the feedback of a history. -/
abbrev Hist.mapFeedback (f : 𝓨 → 𝓨') {n : ℕ} (h : Hist 𝓞 𝓐 𝓨 n) : Hist 𝓞 𝓐 𝓨' n :=
  Hist.map id id f h

/-- Transport the feedback of a trajectory. -/
abbrev Traj.mapFeedback (f : 𝓨 → 𝓨') (τ : ℕ → Round 𝓞 𝓐 𝓨) : ℕ → Round 𝓞 𝓐 𝓨' :=
  Traj.map id id f τ

variable {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

lemma history_map (n : ℕ) :
    history (fun n ω ↦ fo (O n ω)) (fun n ω ↦ fa (A n ω)) (fun n ω ↦ fy (Y n ω)) n
      = Hist.map fo fa fy ∘ history O A Y n := rfl

lemma trajectory_map :
    trajectory (fun n ω ↦ fo (O n ω)) (fun n ω ↦ fa (A n ω)) (fun n ω ↦ fy (Y n ω))
      = Traj.map fo fa fy ∘ trajectory O A Y := rfl

end Map

section Comap

/-- The algorithm that sees `f o` when the observation is `o`, both in the current round and in the
past rounds. -/
def Algorithm.comapObs (alg : Algorithm 𝓞 𝓐 𝓨) (f : 𝓞' → 𝓞)
    (hf : Measurable f := by fun_prop) : Algorithm 𝓞' 𝓐 𝓨 where
  policy n := (alg.policy n).comap (fun p ↦ (Hist.mapObs f p.1, f p.2)) (by fun_prop)

@[simp]
lemma Algorithm.policy_comapObs (alg : Algorithm 𝓞 𝓐 𝓨) (f : 𝓞' → 𝓞) (hf : Measurable f) (n : ℕ) :
    (alg.comapObs f hf).policy n
      = (alg.policy n).comap (fun p ↦ (Hist.mapObs f p.1, f p.2)) (by fun_prop) := rfl

@[simp]
lemma Algorithm.p0_comapObs (alg : Algorithm 𝓞 𝓐 𝓨) (f : 𝓞' → 𝓞) (hf : Measurable f) :
    (alg.comapObs f hf).p0 = alg.p0.comap f hf := by
  ext o : 1
  rw [p0_apply, policy_comapObs, Kernel.comap_apply, alg.policy_zero, Kernel.comap_apply]

/-- The algorithm that sees `g y` when the feedback of a past round is `y`. Together with
`Algorithm.comapObs`, this describes an algorithm that only sees a summary of each past round:
bandit feedback extracted from a loss vector, or an algorithm that ignores a variable that the
environment announces in the feedback. -/
def Algorithm.comapFeedback (alg : Algorithm 𝓞 𝓐 𝓨) (g : 𝓨' → 𝓨)
    (hg : Measurable g := by fun_prop) : Algorithm 𝓞 𝓐 𝓨' where
  policy n := (alg.policy n).comap (fun p ↦ (Hist.mapFeedback g p.1, p.2)) (by fun_prop)

@[simp]
lemma Algorithm.policy_comapFeedback (alg : Algorithm 𝓞 𝓐 𝓨) (g : 𝓨' → 𝓨) (hg : Measurable g)
    (n : ℕ) :
    (alg.comapFeedback g hg).policy n
      = (alg.policy n).comap (fun p ↦ (Hist.mapFeedback g p.1, p.2)) (by fun_prop) := rfl

@[simp]
lemma Algorithm.p0_comapFeedback (alg : Algorithm 𝓞 𝓐 𝓨) (g : 𝓨' → 𝓨) (hg : Measurable g) :
    (alg.comapFeedback g hg).p0 = alg.p0 := by
  ext o : 1
  rw [p0_apply, policy_comapFeedback, Kernel.comap_apply, alg.policy_zero, p0_apply]

/-- The environment that reads `f a` when the algorithm plays `a`, both in the current round and in
the past rounds. -/
def Environment.comapAction (env : Environment 𝓞 𝓐 𝓨) (f : 𝓐' → 𝓐)
    (hf : Measurable f := by fun_prop) : Environment 𝓞 𝓐' 𝓨 where
  obs n := (env.obs n).comap (Hist.mapAction f) (by fun_prop)
  feedback n := (env.feedback n).comap
    (fun p ↦ ((Hist.mapAction f p.1.1, p.1.2), f p.2)) (by fun_prop)

@[simp]
lemma Environment.obs_comapAction (env : Environment 𝓞 𝓐 𝓨) (f : 𝓐' → 𝓐) (hf : Measurable f)
    (n : ℕ) :
    (env.comapAction f hf).obs n = (env.obs n).comap (Hist.mapAction f) (by fun_prop) := rfl

@[simp]
lemma Environment.feedback_comapAction (env : Environment 𝓞 𝓐 𝓨) (f : 𝓐' → 𝓐) (hf : Measurable f)
    (n : ℕ) :
    (env.comapAction f hf).feedback n = (env.feedback n).comap
      (fun p ↦ ((Hist.mapAction f p.1.1, p.1.2), f p.2)) (by fun_prop) := rfl

@[simp]
lemma Environment.obs0_comapAction (env : Environment 𝓞 𝓐 𝓨) (f : 𝓐' → 𝓐) (hf : Measurable f) :
    (env.comapAction f hf).obs0 = env.obs0 := by
  rw [Environment.obs0_def, obs_comapAction, Kernel.comap_apply, env.obs_zero]

@[simp]
lemma Environment.ν0_comapAction (env : Environment 𝓞 𝓐 𝓨) (f : 𝓐' → 𝓐) (hf : Measurable f) :
    (env.comapAction f hf).ν0 = env.ν0.comap (fun p ↦ (p.1, f p.2)) (by fun_prop) := by
  ext p : 1
  rw [Environment.ν0_apply, feedback_comapAction, Kernel.comap_apply, env.feedback_zero,
    Kernel.comap_apply]

/-- An announcing algorithm `algZ : Algorithm 𝓞 (𝓩 × 𝓐) 𝓨` *ignores its own announcements*, with
behavioral algorithm `alg`, if the law of the action it plays given the past rounds and the current
observation does not depend on the variables announced in the past rounds, and is `alg.policy n`.

Announcing algorithms that redraw their announced variable from the observable history at every
round satisfy this; algorithms that reuse a variable drawn once (a mixture component, a random
permutation) do not, and their projection needs a disintegration argument. -/
def Algorithm.IgnoresAnnounced {𝓩 : Type*} [MeasurableSpace 𝓩]
    (algZ : Algorithm 𝓞 (𝓩 × 𝓐) 𝓨) (alg : Algorithm 𝓞 𝓐 𝓨) : Prop :=
  ∀ n, (algZ.policy n).snd
    = (alg.policy n).comap (fun p ↦ (Hist.mapAction Prod.snd p.1, p.2)) (by fun_prop)

lemma Algorithm.IgnoresAnnounced.comapObs {𝓩 : Type*} [MeasurableSpace 𝓩]
    {algZ : Algorithm 𝓞 (𝓩 × 𝓐) 𝓨} {alg : Algorithm 𝓞 𝓐 𝓨} (h : algZ.IgnoresAnnounced alg)
    (f : 𝓞' → 𝓞) (hf : Measurable f) :
    (algZ.comapObs f hf).IgnoresAnnounced (alg.comapObs f hf) := by
  intro n
  have h_snd : ((algZ.comapObs f hf).policy n).snd
      = ((algZ.policy n).snd).comap (fun p ↦ (Hist.mapObs f p.1, f p.2)) (by fun_prop) := rfl
  rw [h_snd, h n]
  rfl

end Comap

section Runs

variable {alg : Algorithm 𝓞 𝓐 𝓨} {P : Measure Ω} [IsFiniteMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

namespace IsAlgEnvSeq

section ComapObs

variable {env : Environment 𝓞' 𝓐 𝓨} {f : 𝓞' → 𝓞} {hf : Measurable f} {O : ℕ → Ω → 𝓞'}

/-- The algorithm does not use the part of the observation that it ignores: the conditional
distribution of its action given the transported history and observation is its own policy. -/
lemma hasCondDistrib_action_comapObs (h : IsAlgEnvSeq O A Y (alg.comapObs f hf) env P) (n : ℕ) :
    HasCondDistrib (A n)
      (fun ω ↦ (history (fun n ω ↦ f (O n ω)) A Y n ω, f (O n ω))) (alg.policy n) P :=
  HasCondDistrib.comp_right (f := fun p : Hist 𝓞' 𝓐 𝓨 n × 𝓞' ↦ (Hist.mapObs f p.1, f p.2))
    (hf := by fun_prop) (h.hasCondDistrib_action n)

/-- The law of the trajectory that the algorithm sees is the image of the law of the full
trajectory under the map that forgets the part of the observations that the algorithm ignores. -/
lemma map_trajectory_comapObs [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y (alg.comapObs f hf) env P) :
    P.map (trajectory (fun n ω ↦ f (O n ω)) A Y)
      = (trajMeasure (alg.comapObs f hf) env).map (Traj.mapObs f) := by
  calc P.map (trajectory (fun n ω ↦ f (O n ω)) A Y)
  _ = P.map (Traj.mapObs f ∘ trajectory O A Y) := rfl
  _ = (P.map (trajectory O A Y)).map (Traj.mapObs f) :=
      (Measure.map_map (by fun_prop) h.measurable_trajectory).symm
  _ = (trajMeasure (alg.comapObs f hf) env).map (Traj.mapObs f) := by rw [h.map_trajectory]

end ComapObs

section ComapFeedback

variable {env : Environment 𝓞 𝓐 𝓨'} {g : 𝓨' → 𝓨} {hg : Measurable g} {O : ℕ → Ω → 𝓞}
  {Y' : ℕ → Ω → 𝓨'}

/-- The algorithm does not use the part of the past feedbacks that it ignores: the conditional
distribution of its action given the transported history and the observation is its own policy. -/
lemma hasCondDistrib_action_comapFeedback
    (h : IsAlgEnvSeq O A Y' (alg.comapFeedback g hg) env P) (n : ℕ) :
    HasCondDistrib (A n)
      (fun ω ↦ (history O A (fun n ω ↦ g (Y' n ω)) n ω, O n ω)) (alg.policy n) P :=
  HasCondDistrib.comp_right (f := fun p : Hist 𝓞 𝓐 𝓨' n × 𝓞 ↦ (Hist.mapFeedback g p.1, p.2))
    (hf := by fun_prop) (h.hasCondDistrib_action n)

/-- The law of the trajectory that the algorithm sees is the image of the law of the full
trajectory under the map that forgets the part of the feedbacks that the algorithm ignores. -/
lemma map_trajectory_comapFeedback [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y' (alg.comapFeedback g hg) env P) :
    P.map (trajectory O A (fun n ω ↦ g (Y' n ω)))
      = (trajMeasure (alg.comapFeedback g hg) env).map (Traj.mapFeedback g) := by
  calc P.map (trajectory O A (fun n ω ↦ g (Y' n ω)))
  _ = P.map (Traj.mapFeedback g ∘ trajectory O A Y') := rfl
  _ = (P.map (trajectory O A Y')).map (Traj.mapFeedback g) :=
      (Measure.map_map (by fun_prop) h.measurable_trajectory).symm
  _ = (trajMeasure (alg.comapFeedback g hg) env).map (Traj.mapFeedback g) := by
      rw [h.map_trajectory]

end ComapFeedback

section ComapAction

variable {env : Environment 𝓞 𝓐 𝓨} {f : 𝓐' → 𝓐} {hf : Measurable f} {O : ℕ → Ω → 𝓞}
  {A' : ℕ → Ω → 𝓐'}

/-- The environment does not use the part of the action that it ignores: the conditional
distribution of the observation given the transported history is its own observation kernel. -/
lemma hasCondDistrib_obs_comapAction {alg : Algorithm 𝓞 𝓐' 𝓨}
    (h : IsAlgEnvSeq O A' Y alg (env.comapAction f hf) P) (n : ℕ) :
    HasCondDistrib (O n) (history O (fun n ω ↦ f (A' n ω)) Y n) (env.obs n) P :=
  HasCondDistrib.comp_right (f := Hist.mapAction (𝓞 := 𝓞) (𝓨 := 𝓨) f (n := n))
    (hf := by fun_prop) (h.hasCondDistrib_obs n)

/-- The environment does not use the part of the action that it ignores: the conditional
distribution of the feedback given the transported history, the observation and the transported
action is its own feedback kernel. -/
lemma hasCondDistrib_feedback_comapAction {alg : Algorithm 𝓞 𝓐' 𝓨}
    (h : IsAlgEnvSeq O A' Y alg (env.comapAction f hf) P) (n : ℕ) :
    HasCondDistrib (Y n)
      (fun ω ↦ ((history O (fun n ω ↦ f (A' n ω)) Y n ω, O n ω), f (A' n ω))) (env.feedback n) P :=
  HasCondDistrib.comp_right
    (f := fun p : (Hist 𝓞 𝓐' 𝓨 n × 𝓞) × 𝓐' ↦ ((Hist.mapAction f p.1.1, p.1.2), f p.2))
    (hf := by fun_prop) (h.hasCondDistrib_feedback n)

/-- The law of the trajectory that the environment sees is the image of the law of the full
trajectory under the map that forgets the part of the actions that the environment ignores. -/
lemma map_trajectory_comapAction [IsProbabilityMeasure P] {alg : Algorithm 𝓞 𝓐' 𝓨}
    (h : IsAlgEnvSeq O A' Y alg (env.comapAction f hf) P) :
    P.map (trajectory O (fun n ω ↦ f (A' n ω)) Y)
      = (trajMeasure alg (env.comapAction f hf)).map (Traj.mapAction f) := by
  calc P.map (trajectory O (fun n ω ↦ f (A' n ω)) Y)
  _ = P.map (Traj.mapAction f ∘ trajectory O A' Y) := rfl
  _ = (P.map (trajectory O A' Y)).map (Traj.mapAction f) :=
      (Measure.map_map (by fun_prop) h.measurable_trajectory).symm
  _ = (trajMeasure alg (env.comapAction f hf)).map (Traj.mapAction f) := by rw [h.map_trajectory]

end ComapAction

section Announcing

variable {𝓩 : Type*} {m𝓩 : MeasurableSpace 𝓩} {env : Environment 𝓞 𝓐 𝓨}
  {algZ : Algorithm 𝓞 (𝓩 × 𝓐) 𝓨} {O : ℕ → Ω → 𝓞} {B : ℕ → Ω → 𝓩 × 𝓐}

/-- The announced variable of round `n`, given the past rounds and the current observation, has the
first marginal of the policy for conditional distribution. It is an honest random variable of the
run, not a variable integrated out inside the policy kernel. -/
lemma hasCondDistrib_announced {env' : Environment 𝓞 (𝓩 × 𝓐) 𝓨}
    (h : IsAlgEnvSeq O B Y algZ env' P) (n : ℕ) :
    HasCondDistrib (fun ω ↦ (B n ω).1) (fun ω ↦ (history O B Y n ω, O n ω))
      (algZ.policy n).fst P :=
  (h.hasCondDistrib_action n).fst

/-- **Projection of a run of an announcing algorithm.** If `algZ` announces a variable in `𝓩` and
does not read its own past announcements, then the observable part of a run of `algZ` against
`env.comapAction Prod.snd` is a run of the behavioral algorithm `alg` against `env`. The announced
variables are honest random variables of that run.

This is the special case of the projection theorem in which the announced variable is redrawn from
the observable history at every round; it needs no disintegration. -/
lemma isAlgEnvSeq_of_ignoresAnnounced {alg : Algorithm 𝓞 𝓐 𝓨}
    (h : IsAlgEnvSeq O B Y algZ (env.comapAction Prod.snd) P)
    (h_alg : algZ.IgnoresAnnounced alg) :
    IsAlgEnvSeq O (fun n ω ↦ (B n ω).2) Y alg env P where
  measurable_obs := h.measurable_obs
  measurable_action n := (h.measurable_action n).snd
  measurable_feedback := h.measurable_feedback
  hasCondDistrib_obs n := h.hasCondDistrib_obs_comapAction n
  hasCondDistrib_feedback n := h.hasCondDistrib_feedback_comapAction n
  hasCondDistrib_action n := by
    have h1 := (h.hasCondDistrib_action n).snd
    rw [h_alg n] at h1
    exact HasCondDistrib.comp_right
      (f := fun p : Hist 𝓞 (𝓩 × 𝓐) 𝓨 n × 𝓞 ↦ (Hist.mapAction Prod.snd p.1, p.2))
      (hf := by fun_prop) (Z := fun ω ↦ (history O B Y n ω, O n ω)) h1

end Announcing

end IsAlgEnvSeq

end Runs

end Learning
