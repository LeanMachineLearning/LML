/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Comap

/-!
# Announced variables

TODO

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

* `Algorithm.IgnoresAnnounced algZ alg`: the announcing algorithm `algZ` does not read the variables
  it announced in the past rounds, and the law of the action it plays is `alg.policy n`.

## Main statements

* `IsAlgEnvSeq.map_trajectory_comapObs`, `IsAlgEnvSeq.map_trajectory_comapFeedback`,
  `IsAlgEnvSeq.map_trajectory_comapAction`: the law of the trajectory that a player sees is the
  image of `trajMeasure` under the forgetful map.
* `IsAlgEnvSeq.hasCondDistrib_announced`: in a run of an announcing algorithm, the announced
  variable of round `n` has the first marginal of the policy for conditional distribution. It is an
  honest random variable of the run, not a variable integrated out inside the policy kernel.
* `IsAlgEnvSeq.isAlgEnvSeq_of_ignoresAnnounced`: **projection of a run**. If the announcing
  algorithm does not read its own past announcements, the observable part of a run of it against
  `env.comapAction Prod.snd` is a run of the behavioral algorithm against `env`.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓞' 𝓐 𝓨 Ω : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓞' : MeasurableSpace 𝓞'}
  {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨} {mΩ : MeasurableSpace Ω}

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

namespace IsAlgEnvSeq

variable {𝓩 : Type*} {m𝓩 : MeasurableSpace 𝓩} {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}
  {algZ : Algorithm 𝓞 (𝓩 × 𝓐) 𝓨} {P : Measure Ω} [IsFiniteMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {B : ℕ → Ω → 𝓩 × 𝓐}

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

end IsAlgEnvSeq

end Learning
