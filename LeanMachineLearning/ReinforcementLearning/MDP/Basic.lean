/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Algorithm
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Markov decision processes and their environments

A Markov decision process (MDP) with state space `𝓢`, action space `𝓐` and reward space `𝓡` is
given by a transition kernel `P : Kernel (𝓢 × 𝓐) 𝓢` and a reward kernel `R : Kernel (𝓢 × 𝓐) 𝓡`,
both Markov. It defines an environment of LML's interaction protocol: the observation of each
round is the current state and the feedback is the reward. From an initial law `μ₀` of the
first state,
* the first state has law `μ₀`;
* the state of round `n + 1` has law `P (s, a)`, where `s` and `a` are the state and action of
  round `n`;
* the reward of round `n` has law `R (s, a)`, where `s` and `a` are the state and action of
  round `n`.

Every algorithm of the interaction protocol, run in this environment, is a history-dependent
policy of the MDP, and the laws of its runs are those of the MDP controlled by that policy.

## Main definitions

* `Learning.MDP 𝓢 𝓐 𝓡`: a Markov decision process.
* `Learning.MDP.env M μ₀`: the environment of `M` started from the initial law `μ₀`.
* `Learning.MDP.meanReward R p`: the mean reward `∫ y, y ∂(R p)` of the state-action pair `p`.

## Main statements

* `Learning.MDP.measurable_env`: the environment depends measurably on the initial law.

For every algorithm-environment sequence `IsAlgEnvSeq O A Y alg (M.env μ) P`:
* `Learning.MDP.hasLaw_obs_zero`: the first state `O 0` has law `μ`, for a probability measure
  `μ`;
* `Learning.MDP.hasCondDistrib_obs_add_one_history`, `Learning.MDP.hasCondDistrib_obs_add_one`:
  the state `O (n + 1)` has conditional law `M.P (O n, A n)` given the history up to round `n`,
  hence given the state-action pair `(O n, A n)` only;
* `Learning.MDP.hasLaw_obs_add_one`: the state `O (n + 1)` has law `M.P ∘ₘ L`, where `L` is the
  law of the state-action pair `(O n, A n)`;
* `Learning.MDP.hasCondDistrib_feedback_history`, `Learning.MDP.hasCondDistrib_feedback`: the
  reward `Y n` has conditional law `M.R (O n, A n)` given the history before round `n`, `O n` and
  `A n`, hence given `(O n, A n)` only;
* `Learning.MDP.ae_feedback_mem`: if the rewards of `M.R` lie almost surely in a measurable set,
  so does `Y n`;
* `Learning.MDP.integral_feedback`: the expectation of an integrable reward `Y n` is the integral
  of the mean reward against the law of `(O n, A n)`.

## Implementation notes

The environment `M.env μ₀` is defined for every measure `μ₀`, so that it depends measurably on
`μ₀` (`Learning.MDP.measurable_env`): when `μ₀` is not a probability measure, the first state is
drawn from the Dirac mass at an arbitrary state, which needs `Nonempty 𝓢`.

The mean reward takes the reward kernel rather than the MDP, so that it also applies to other
reward kernels on the same state-action pairs.

## References

* M. L. Puterman, *Markov Decision Processes: Discrete Stochastic Dynamic Programming*, Wiley,
  1994, Chapter 2.
* D. P. Bertsekas and S. E. Shreve, *Stochastic Optimal Control: The Discrete-Time Case*,
  Academic Press, 1978 (MDPs on Borel state and action spaces).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

/-- A Markov decision process with state space `𝓢`, action space `𝓐` and reward space `𝓡`,
described by a transition kernel `P : Kernel (𝓢 × 𝓐) 𝓢` and a reward kernel
`R : Kernel (𝓢 × 𝓐) 𝓡`, both Markov. See `MDP.env` for its environment. -/
@[ext]
structure MDP (𝓢 𝓐 𝓡 : Type*) [MeasurableSpace 𝓢] [MeasurableSpace 𝓐] [MeasurableSpace 𝓡] where
  /-- The transition kernel: the law of the next state given the current state and action. -/
  P : Kernel (𝓢 × 𝓐) 𝓢
  /-- The transition kernel is a Markov kernel. -/
  [hP : IsMarkovKernel P]
  /-- The reward kernel: the law of the reward given the current state and action. -/
  R : Kernel (𝓢 × 𝓐) 𝓡
  /-- The reward kernel is a Markov kernel. -/
  [hR : IsMarkovKernel R]

namespace MDP

variable {𝓢 𝓐 𝓡 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓡 : MeasurableSpace 𝓡}

instance (M : MDP 𝓢 𝓐 𝓡) : IsMarkovKernel M.P := M.hP
instance (M : MDP 𝓢 𝓐 𝓡) : IsMarkovKernel M.R := M.hR

/-! ### Mean rewards -/

section MeanReward

variable [NormedAddCommGroup 𝓡] [NormedSpace ℝ 𝓡]

/-- The mean reward `r (s, a) = 𝔼[R (s, a)]` of a state-action pair, for a reward kernel `R`. -/
noncomputable def meanReward (R : Kernel (𝓢 × 𝓐) 𝓡) (p : 𝓢 × 𝓐) : 𝓡 := (R p)[id]

lemma meanReward_def (R : Kernel (𝓢 × 𝓐) 𝓡) (p : 𝓢 × 𝓐) :
    meanReward R p = ∫ y, y ∂(R p) :=
  (rfl)

/-- The mean reward is a measurable function of the state-action pair. -/
@[fun_prop]
lemma measurable_meanReward [SecondCountableTopology 𝓡] [BorelSpace 𝓡]
    (R : Kernel (𝓢 × 𝓐) 𝓡) : Measurable (meanReward R) :=
  (stronglyMeasurable_id.integral_kernel (κ := R)).measurable

/-- Rewards bounded by `C` have a mean bounded by `C`. -/
lemma norm_meanReward_le (R : Kernel (𝓢 × 𝓐) 𝓡) {p : 𝓢 × 𝓐} [IsProbabilityMeasure (R p)] {C : ℝ}
    (hR : ∀ᵐ y ∂(R p), ‖y‖ ≤ C) : ‖meanReward R p‖ ≤ C := by
  simpa [meanReward_def] using norm_integral_le_of_norm_le_const hR

end MeanReward

/-! ### The environment of an MDP -/

open Classical in
/-- The environment of the MDP `M` started from the initial law `μ₀`: the observation of a round
is the current state and its feedback is the reward.
* The state of round `0` has law `μ₀`, or the Dirac mass at an arbitrary state if `μ₀` is not a
  probability measure.
* The state of round `n + 1` has law `M.P (s, a)`, where `s` and `a` are the state and action of
  round `n`.
* The reward of round `n` has law `M.R (s, a)`, where `s` and `a` are the state and action of
  round `n`. -/
protected noncomputable def env [Nonempty 𝓢] (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) :
    Environment 𝓢 𝓐 𝓡 where
  obs
  | 0 => Kernel.const _
    (if IsProbabilityMeasure μ₀ then μ₀ else Measure.dirac (Classical.arbitrary 𝓢))
  | n + 1 => M.P.comap (fun h ↦ ((h (Fin.last n)).obs, (h (Fin.last n)).action)) (by fun_prop)
  feedback := fun _ ↦ M.R.comap (fun p ↦ (p.1.2, p.2)) (by fun_prop)
  isMarkovKernel_obs n := by
    cases n
    · split_ifs <;> infer_instance
    · infer_instance

variable [Nonempty 𝓢] {M : MDP 𝓢 𝓐 𝓡} {μ₀ : Measure 𝓢}

open Classical in
/-- The observation kernel of round `0` of the environment of `M` is the constant kernel `μ₀`, or
the Dirac mass at an arbitrary state if `μ₀` is not a probability measure. -/
lemma obs_env_zero (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) :
    (M.env μ₀).obs 0 = Kernel.const _
      (if IsProbabilityMeasure μ₀ then μ₀ else Measure.dirac (Classical.arbitrary 𝓢)) :=
  (rfl)

/-- The first state of the environment of `M` has law `μ₀` when `μ₀` is a probability measure. -/
@[simp]
lemma obsZero_env (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) [hμ₀ : IsProbabilityMeasure μ₀] :
    (M.env μ₀).obsZero = μ₀ := by
  simp [Environment.obsZero_def, obs_env_zero, hμ₀]

/-- If `μ₀` is not a probability measure, the first state of the environment of `M` is an
arbitrary fixed state. -/
lemma obsZero_env_of_not_isProbabilityMeasure (M : MDP 𝓢 𝓐 𝓡) (h : ¬IsProbabilityMeasure μ₀) :
    (M.env μ₀).obsZero = Measure.dirac (Classical.arbitrary 𝓢) := by
  simp [Environment.obsZero_def, obs_env_zero, h]

/-- The observation kernel of round `n + 1` of the environment of `M` is the transition kernel,
applied to the state and action of round `n`. -/
lemma obs_env_add_one (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) (n : ℕ) :
    (M.env μ₀).obs (n + 1) = M.P.comap
      (fun h : Hist 𝓢 𝓐 𝓡 (n + 1) ↦ ((h (Fin.last n)).obs, (h (Fin.last n)).action))
      (by fun_prop) :=
  (rfl)

@[simp]
lemma obs_env_add_one_apply (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) (n : ℕ) (h : Hist 𝓢 𝓐 𝓡 (n + 1)) :
    (M.env μ₀).obs (n + 1) h = M.P ((h (Fin.last n)).obs, (h (Fin.last n)).action) := by
  rw [obs_env_add_one, Kernel.comap_apply]

/-- The feedback kernel of every round of the environment of `M` is the reward kernel, applied to
the current state and action. -/
lemma feedback_env (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) (n : ℕ) :
    (M.env μ₀).feedback n =
      M.R.comap (fun p : (Hist 𝓢 𝓐 𝓡 n × 𝓢) × 𝓐 ↦ (p.1.2, p.2)) (by fun_prop) :=
  (rfl)

@[simp]
lemma feedback_env_apply (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) (n : ℕ)
    (p : (Hist 𝓢 𝓐 𝓡 n × 𝓢) × 𝓐) :
    (M.env μ₀).feedback n p = M.R (p.1.2, p.2) := by
  rw [feedback_env, Kernel.comap_apply]

/-- The environment of an MDP depends measurably on the initial law. -/
lemma measurable_env (M : MDP 𝓢 𝓐 𝓡) : Measurable M.env := by
  rw [measurable_environment_iff]
  refine fun n ↦ ⟨?_, by simp_rw [feedback_env]; fun_prop⟩
  cases n with
  | zero =>
    simp_rw [obs_env_zero]
    exact Kernel.measurable_const.comp <| Measurable.ite
      ProbabilityMeasure.measurableSet_isProbabilityMeasure (by fun_prop) (by fun_prop)
  | succ n => simp_rw [obs_env_add_one]; fun_prop

/-! ### Runs in the environment of an MDP -/

section Runs

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {O : ℕ → Ω → 𝓢} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓡} {alg : Algorithm 𝓢 𝓐 𝓡} {μ : Measure 𝓢}

/-- In a run in the environment of an MDP started from the probability measure `μ`, the first
state has law `μ`. -/
lemma hasLaw_obs_zero [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y alg (M.env μ) P) :
    HasLaw (O 0) μ P := by
  simpa using h.hasLaw_obs_zero

/-- In a run in the environment of an MDP, the state of round `n + 1` has conditional law
`M.P (s, a)` given the history of the rounds up to `n`, where `s` and `a` are the state and
action of round `n`. -/
lemma hasCondDistrib_obs_add_one_history (h : IsAlgEnvSeq O A Y alg (M.env μ) P) (n : ℕ) :
    HasCondDistrib (O (n + 1)) (history O A Y (n + 1))
      (M.P.comap (fun h ↦ ((h (Fin.last n)).obs, (h (Fin.last n)).action)) (by fun_prop) :
        Kernel (Hist 𝓢 𝓐 𝓡 (n + 1)) 𝓢) P := by
  rw [← obs_env_add_one M μ]
  exact h.hasCondDistrib_obs (n + 1)

/-- Markov property of the states: in a run in the environment of an MDP, the state of
round `n + 1` has conditional law `M.P` given the state and action of round `n`. -/
lemma hasCondDistrib_obs_add_one [SFinite P] (h : IsAlgEnvSeq O A Y alg (M.env μ) P) (n : ℕ) :
    HasCondDistrib (O (n + 1)) (fun ω ↦ (O n ω, A n ω)) M.P P :=
  (hasCondDistrib_obs_add_one_history h n).comp_right

/-- In a run in the environment of an MDP, the law of the state of round `n + 1` is the law of
the state-action pair of round `n` composed with the transition kernel `M.P`. -/
lemma hasLaw_obs_add_one [SFinite P] (h : IsAlgEnvSeq O A Y alg (M.env μ) P) (n : ℕ) :
    HasLaw (O (n + 1)) (M.P ∘ₘ P.map (fun ω ↦ (O n ω, A n ω))) P :=
  (hasCondDistrib_obs_add_one h n).hasLaw_comp

/-- In a run in the environment of an MDP, the reward of round `n` has conditional law
`M.R (s, a)` given the history before round `n`, the state `s` and the action `a` of
round `n`. -/
lemma hasCondDistrib_feedback_history (h : IsAlgEnvSeq O A Y alg (M.env μ) P) (n : ℕ) :
    HasCondDistrib (Y n) (fun ω ↦ ((history O A Y n ω, O n ω), A n ω))
      (M.R.comap (fun p ↦ (p.1.2, p.2)) (by fun_prop) : Kernel ((Hist 𝓢 𝓐 𝓡 n × 𝓢) × 𝓐) 𝓡)
      P := by
  rw [← feedback_env M μ n]
  exact h.hasCondDistrib_feedback n

/-- In a run in the environment of an MDP, the reward of round `n` has conditional law `M.R`
given the state and action of round `n`. -/
lemma hasCondDistrib_feedback [SFinite P] (h : IsAlgEnvSeq O A Y alg (M.env μ) P) (n : ℕ) :
    HasCondDistrib (Y n) (fun ω ↦ (O n ω, A n ω)) M.R P :=
  (hasCondDistrib_feedback_history h n).comp_right

/-- Along a run in an MDP whose rewards lie almost surely in a measurable set `s`, the reward of
every round lies in `s` almost surely. For rewards bounded by `C`, take `s = {y | |y| ≤ C}`. -/
lemma ae_feedback_mem [SFinite P] (h : IsAlgEnvSeq O A Y alg (M.env μ) P) {s : Set 𝓡}
    (hs : MeasurableSet s) (hR : ∀ p, ∀ᵐ y ∂(M.R p), y ∈ s) (n : ℕ) :
    ∀ᵐ ω ∂P, Y n ω ∈ s := by
  have h_law := hasCondDistrib_feedback h n
  have h_ae : ∀ᵐ q ∂(P.map (fun ω ↦ (O n ω, A n ω)) ⊗ₘ M.R), q.2 ∈ s :=
    Measure.ae_compProd_of_ae_ae (measurable_snd hs) (.of_forall hR)
  rw [← h_law.map_eq] at h_ae
  exact ae_of_ae_map h_law.aemeasurable h_ae

/-- Along a run in an MDP, if the reward of round `n` is integrable, its expectation is the
integral of the mean reward against the law of the state-action pair of round `n`. -/
lemma integral_feedback [NormedAddCommGroup 𝓡] [NormedSpace ℝ 𝓡] [SecondCountableTopology 𝓡]
    [BorelSpace 𝓡] [SFinite P] (h : IsAlgEnvSeq O A Y alg (M.env μ) P) {n : ℕ}
    (hY : Integrable (Y n) P) :
    ∫ ω, Y n ω ∂P = ∫ p, meanReward M.R p ∂(P.map fun ω ↦ (O n ω, A n ω)) := by
  have h_law := hasCondDistrib_feedback h n
  have h_int : Integrable (fun q : (𝓢 × 𝓐) × 𝓡 ↦ q.2)
      (P.map (fun ω ↦ (O n ω, A n ω)) ⊗ₘ M.R) := by
    rwa [← h_law.map_eq,
      integrable_map_measure measurable_snd.aestronglyMeasurable h_law.aemeasurable]
  have h_eq := h_law.integral_comp (f := Prod.snd) measurable_snd.aestronglyMeasurable
  simp only [Function.comp_def] at h_eq
  rw [h_eq, Measure.integral_compProd h_int]
  simp_rw [meanReward_def]

end Runs

end MDP

end Learning
