/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber
-/
module

public import LeanMachineLearning.SequentialLearning.AlgorithmDensity
public import LeanMachineLearning.SequentialLearning.BayesStationaryEnv

/-!
# Algorithm density under Bayesian stationary environments

This file provides results about `Algorithm.density` for the Bayesian stationary environment
setting.

## Main results

Let `h : IsBayesAlgEnvSeq Q κ alg E A Y P`, `h₀ : IsBayesAlgEnvSeq Q κ alg₀ E₀ A₀ Y₀ P₀`, and
`hc : alg ≪ₐ alg₀`.

* `hasLaw_hist_withDensity h h₀ hc n`: the law of the history at time `n` under `P` is the law of
  the history at time `n` under `P₀` with density `alg.density alg₀ n`. Intuitively, the law of the
  history under `alg` can be obtained from the law of the history under `alg₀` when they are
  interacting with underlying stationary environments drawn from the same distribution.
* `hasCondDistrib_env_hist h h₀ hc n`: the conditional distribution of `E` given the history at time
  `n` under `P` is almost everywhere equal to the conditional distribution of `E₀` given the history
  at time `n` under `P₀`. Intuitively, the posterior is independent of the algorithm used to observe
  the history.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace Learning

open scoped Algorithm

namespace IsBayesAlgEnvSeq

variable {𝓐 𝓨 : Type*} [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]
variable {𝓔 : Type*} [MeasurableSpace 𝓔]
variable [StandardBorelSpace 𝓐] [Nonempty 𝓐] [StandardBorelSpace 𝓨] [Nonempty 𝓨]
variable {Q : Measure 𝓔}
variable {κ : Kernel (𝓔 × 𝓐) 𝓨} [IsMarkovKernel κ]

variable {Ω : Type*} [MeasurableSpace Ω]
variable {E : Ω → 𝓔} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
variable {alg : Algorithm 𝓐 𝓨}
variable {P : Measure Ω} [IsProbabilityMeasure P]

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]
variable {E₀ : Ω₀ → 𝓔} {A₀ : ℕ → Ω₀ → 𝓐} {Y₀ : ℕ → Ω₀ → 𝓨}
variable {alg₀ : Algorithm 𝓐 𝓨}
variable {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]

lemma condDistrib_hist_eq_condDistrib_hist_withDensity (h : IsBayesAlgEnvSeq Q κ alg E A Y P)
    (h₀ : IsBayesAlgEnvSeq Q κ alg₀ E₀ A₀ Y₀ P₀) (hc : alg ≪ₐ alg₀) (n : ℕ) :
    condDistrib (IsAlgEnvSeq.hist A Y n) E P =ᵐ[Q]
      ((condDistrib (IsAlgEnvSeq.hist A₀ Y₀ n) E₀ P₀).withDensity
        (fun _ ↦ alg.density alg₀ n)) := by
    filter_upwards [h.ae_IsAlgEnvSeq, h₀.ae_IsAlgEnvSeq, h.hasLaw_IT_hist n, h₀.hasLaw_IT_hist n]
      with _ hae hae₀ he he₀
    rw [Kernel.withDensity_apply _ (by fun_prop), ← he.map_eq, ← he₀.map_eq]
    exact (hae.hasLaw_hist_withDensity hae₀ hc n).map_eq

lemma hasLaw_hist_withDensity (h : IsBayesAlgEnvSeq Q κ alg E A Y P)
    (h₀ : IsBayesAlgEnvSeq Q κ alg₀ E₀ A₀ Y₀ P₀) (hc : alg ≪ₐ alg₀) (n : ℕ) :
    HasLaw (IsAlgEnvSeq.hist A Y n)
      ((P₀.map (IsAlgEnvSeq.hist A₀ Y₀ n)).withDensity (alg.density alg₀ n)) P where
  aemeasurable :=
    (IsAlgEnvSeq.measurable_hist h.measurable_action h.measurable_feedback n).aemeasurable
  map_eq := by
    have hA := h.measurable_action
    have hY := h.measurable_feedback
    have hA₀ := h₀.measurable_action
    have hY₀ := h₀.measurable_feedback
    have hE := h.measurable_param
    have hE₀ := h₀.measurable_param
    rw [← condDistrib_comp_map hE.aemeasurable (by fun_prop), h.hasLaw_env.map_eq,
          Measure.bind_congr_right (h.condDistrib_hist_eq_condDistrib_hist_withDensity h₀ hc n),
          Kernel.comp_withDensity_eq_withDensity_comp (by fun_prop),
          ← h₀.hasLaw_env.map_eq, condDistrib_comp_map hE₀.aemeasurable (by fun_prop)]

variable [StandardBorelSpace 𝓔] [Nonempty 𝓔]
variable [IsProbabilityMeasure Q]

lemma hasCondDistrib_env_hist (h : IsBayesAlgEnvSeq Q κ alg E A Y P)
    (h₀ : IsBayesAlgEnvSeq Q κ alg₀ E₀ A₀ Y₀ P₀) (hc : alg ≪ₐ alg₀) (n : ℕ) :
    HasCondDistrib E (IsAlgEnvSeq.hist A Y n)
      (condDistrib E₀ (IsAlgEnvSeq.hist A₀ Y₀ n) P₀) P where
  aemeasurable_fst := h.measurable_param.aemeasurable
  aemeasurable_snd :=
    (IsAlgEnvSeq.measurable_hist h.measurable_action h.measurable_feedback n).aemeasurable
  condDistrib_eq := by
    have hA := h.measurable_action
    have hY := h.measurable_feedback
    have hA₀ := h₀.measurable_action
    have hY₀ := h₀.measurable_feedback
    have hE := h.measurable_param
    have hE₀ := h₀.measurable_param
    rw [condDistrib_ae_eq_iff_measure_eq_compProd _ h.measurable_param.aemeasurable,
      ← map_swap_compProd_map_condDistrib (by fun_prop), h.hasLaw_env.map_eq,
      Measure.compProd_eq_compProd_withDensity_comp_snd (by fun_prop)
        (h.condDistrib_hist_eq_condDistrib_hist_withDensity h₀ hc n),
      map_swap_withDensity_comp_snd (by fun_prop),
      ← h₀.hasLaw_env.map_eq, map_swap_compProd_map_condDistrib (by fun_prop),
      ← compProd_map_condDistrib (by fun_prop),
      ← Measure.compProd_withDensity_left (by fun_prop),
      ← (hasLaw_hist_withDensity h h₀ hc n).map_eq]

end IsBayesAlgEnvSeq

end Learning
