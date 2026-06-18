/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber
-/
module

public import LeanMachineLearning.Online.Bandit.BayesRegret
public import LeanMachineLearning.SequentialLearning.AlgorithmDensityBayes
public import LeanMachineLearning.SequentialLearning.Algorithms.Uniform

/-!
# Thompson Sampling

This file defines the Thompson sampling algorithm. This algorithm samples an action according to its
probability of being optimal under the posterior over environments given the history so far.

## Main definitions

* `tsAlgorithm hK Q κ`: a Thompson sampling algorithm with actions in `Fin K` given `hK : 0 < K`,
  a prior distribution over parameters `Q : Measure 𝓔`, and a Markov kernel
  `κ : Kernel (𝓔 × Fin K) ℝ`. This kernel defines how a parameter `e : 𝓔` gives rise to
  a stationary environment: `stationaryEnv (κ.sectR e) : Environment (Fin K) ℝ`.

## Main results

* `hasCondDistrib_action` : if Thompson sampling has the correct prior over environments, then
  the conditional distribution of the next action given the history so far is equal to the
  conditional distribution of the best action given the history so far.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning
open IsBayesAlgEnvSeq (bestAction)

namespace Bandits

section Algorithm

variable {K : ℕ}
variable {𝓔 : Type*} [MeasurableSpace 𝓔] [StandardBorelSpace 𝓔] [Nonempty 𝓔]

/-- The Thompson sampling policy samples an action according to its probability of being optimal
under the posterior over environments given the history so far.
The posterior under a uniform algorithm is used to avoid a circular definition. -/
noncomputable
def TS.policy (hK : 0 < K) (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × Fin K) ℝ)
    [IsMarkovKernel κ] (n : ℕ) : Kernel (Iic n → (Fin K) × ℝ) (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  (IT.bayesTrajMeasurePosterior Q κ uniformAlgorithm n).map (bestAction κ id)

instance {hK : 0 < K} {Q : Measure 𝓔} [IsProbabilityMeasure Q] {κ : Kernel (𝓔 × Fin K) ℝ}
    [IsMarkovKernel κ] {n : ℕ} : IsMarkovKernel (TS.policy hK Q κ n) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The initial action is sampled according to its probability of being optimal under the prior over
environments. -/
noncomputable
def TS.initialPolicy (hK : 0 < K) (Q : Measure 𝓔) (κ : Kernel (𝓔 × Fin K) ℝ) : Measure (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  Q.map (bestAction κ id)

instance {hK : 0 < K} {Q : Measure 𝓔} [IsProbabilityMeasure Q] {κ : Kernel (𝓔 × Fin K) ℝ} :
    IsProbabilityMeasure (TS.initialPolicy hK Q κ) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- The Thompson sampling algorithm with actions in `Fin K`, where `Q : Measure 𝓔` is a prior
  distribution over parameters, and `κ : Kernel (𝓔 × Fin K) ℝ` is a Markov kernel that defines the
  stationary environment `stationaryEnv (κ.sectR e)` that corresponds to a parameter `e : 𝓔`.

  At every time `n`, the Thompson sampling policy uses the posterior over the parameters given the
  history up to time `n` to derive the probability of each action being optimal. The action for time
  `n` is sampled according to these probabilities. -/
noncomputable
def tsAlgorithm (hK : 0 < K) (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × Fin K) ℝ)
    [IsMarkovKernel κ] : Algorithm (Fin K) ℝ where
  policy := TS.policy hK Q κ
  p0 := TS.initialPolicy hK Q κ

end Algorithm

variable {K : ℕ} [Nonempty (Fin K)]
variable {Ω : Type*} [MeasurableSpace Ω]
variable {𝓔 : Type*} [MeasurableSpace 𝓔] [StandardBorelSpace 𝓔] [Nonempty 𝓔]
variable {E : Ω → 𝓔} {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
variable {Q : Measure 𝓔} [IsProbabilityMeasure Q] {κ : Kernel (𝓔 × Fin K) ℝ} [IsMarkovKernel κ]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- If Thompson sampling has the correct prior over environments, then the conditional distribution
of the next action given the history so far is equal to the conditional distribution of the best
action given the history so far. -/
lemma TS.hasCondDistrib_action (hK : 0 < K) (h : IsBayesAlgEnvSeq Q κ (tsAlgorithm hK Q κ) E A R P)
    (n : ℕ) : HasCondDistrib (A (n + 1)) (history A R n)
      (condDistrib (bestAction κ E) (history A R n) P) P where
  aemeasurable_fst := (h.measurable_action (n + 1)).aemeasurable
  aemeasurable_snd :=
    (measurable_history h.measurable_action h.measurable_feedback n).aemeasurable
  condDistrib_eq := by
    have hm : Measurable (bestAction κ id) := by fun_prop
    calc
      _ =ᵐ[P.map (history A R n)]
          (IT.bayesTrajMeasurePosterior Q κ uniformAlgorithm n).map (bestAction κ id) :=
          (h.hasCondDistrib_action' n).condDistrib_eq
      _ =ᵐ[P.map (history A R n)]
          (condDistrib E (history A R n) P).map (bestAction κ id) := by
          filter_upwards [(h.hasCondDistrib_env_history
            (IT.isBayesAlgEnvSeq_bayesTrajMeasure Q κ uniformAlgorithm)
            absolutelyContinuous_uniformAlgorithm n).condDistrib_eq] with _ hc
          simp_rw [Kernel.map_apply _ hm, IT.bayesTrajMeasurePosterior, hc]
      _ =ᵐ[P.map (history A R n)]
          condDistrib (bestAction κ E) (history A R n) P :=
          (condDistrib_comp (history A R n) h.measurable_param.aemeasurable hm).symm

end Bandits
