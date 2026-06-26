/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Kernel.Composition.MeasureCompProd
public import LeanMachineLearning.ForMathlib.Probability.WithDensity
public import LeanMachineLearning.SequentialLearning.Algorithm

/-!
# Algorithm density

We define a density function that allows obtaining the law of the history under one algorithm from
the law of the history under another algorithm when they are interacting with the same
environment. This also requires one algorithm to be absolutely continuous with respect to another, a
concept that we also introduce here.

## Main definitions

* `AbsolutelyContinuous alg alg₀`: `alg` is absolutely continuous with respect to `alg₀` (also
  denoted `alg ≪ₐ alg₀`) when, in every situation, a set of actions with probability zero under
  `alg₀` also has probability zero under `alg`. Intuitively, `alg` never acts in a way that `alg₀`
  would never act.
* `density alg alg₀ n`: a density function that allows obtaining the law of the history at time `n`
  under `alg` from the law of the history at time `n` under `alg₀` when they are interacting with
  the same environment and `alg ≪ₐ alg₀`.

## Main results

* `absolutelyContinuous_map_hist`: the law of the history at time `n` under `alg` is absolutely
  continuous with respect to the law of the history at time `n` under `alg₀` when they
  are interacting with the same environment and `alg ≪ₐ alg₀`.
* `hasLaw_history_withDensity`: the law of the history at time `n` under `alg` is the law of the
  history at time `n` under `alg₀` with density `alg.density alg₀ n` when they are interacting
  with the same environment and `alg ≪ₐ alg₀`.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

open scoped ENNReal

namespace Learning

variable {𝓐 𝓨 : Type*} [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]

namespace Algorithm

/-- For every time and history, the distribution over actions according to `alg` is absolutely
continuous with respect to the distribution over actions according to `alg₀`. -/
structure AbsolutelyContinuous (alg alg₀ : Algorithm 𝓐 𝓨) : Prop where
  p0 : alg.p0 ≪ alg₀.p0
  policy n h : alg.policy n h ≪ alg₀.policy n h

@[inherit_doc AbsolutelyContinuous]
scoped notation:50 alg " ≪ₐ " alg₀ => AbsolutelyContinuous alg alg₀

/-- If the algorithm `alg` is absolutely continuous with respect to the algorithm `alg₀` and they
are both interacting with the same environment, then the law of the history at time `n` under `alg`
is the law of the history at time `n` under `alg₀` with density `alg.density alg₀ n`. -/
noncomputable
def density [MeasurableSpace.CountablyGenerated 𝓐] (alg alg₀ : Algorithm 𝓐 𝓨) :
    (n : ℕ) → (Iic n → 𝓐 × 𝓨) → ℝ≥0∞
  | 0, h => (alg.p0.rnDeriv alg₀.p0 (h ⟨0, by simp⟩).1)
  | n + 1, h =>
    let p := MeasurableEquiv.IicSuccProd (fun _ ↦ 𝓐 × 𝓨) n h
    alg.density alg₀ n p.1 * (alg.policy n).rnDeriv (alg₀.policy n) p.1 p.2.1

@[fun_prop]
lemma measurable_density [MeasurableSpace.CountablyGenerated 𝓐] (alg alg₀ : Algorithm 𝓐 𝓨) (n : ℕ) :
    Measurable (alg.density alg₀ n) := by
  induction n with
  | zero => simp_rw [density]; fun_prop
  | succ n ih => simp_rw [density]; fun_prop

end Algorithm

open scoped Algorithm

namespace IsAlgEnvSeq

variable {Ω : Type*} [MeasurableSpace Ω]
variable {alg : Algorithm 𝓐 𝓨} {env : Environment 𝓐 𝓨}
variable {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
variable {P : Measure Ω} [IsFiniteMeasure P]

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]
variable {alg₀ : Algorithm 𝓐 𝓨}
variable {A₀ : ℕ → Ω₀ → 𝓐} {Y₀ : ℕ → Ω₀ → 𝓨}
variable {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]

lemma absolutelyContinuous_map_history (h : IsAlgEnvSeq A Y alg env P)
    (h₀ : IsAlgEnvSeq A₀ Y₀ alg₀ env P₀) (hc : alg ≪ₐ alg₀) (n : ℕ) :
    P.map (history A Y n) ≪ P₀.map (history A₀ Y₀ n) := by
  induction n with
  | zero =>
    rw [h.hasLaw_history_zero.map_eq, h₀.hasLaw_history_zero.map_eq]
    apply Measure.AbsolutelyContinuous.map _ (by fun_prop)
    rw [h.hasLaw_step_zero.map_eq, h₀.hasLaw_step_zero.map_eq]
    exact Measure.AbsolutelyContinuous.compProd_left hc.p0 _
  | succ n ih =>
    simp_rw [history_succ]
    rw [← Measure.map_map (by fun_prop), ← Measure.map_map (by fun_prop)]
    rotate_left
    · exact (h₀.measurable_history n).prodMk (h₀.measurable_step (n + 1))
    · exact (h.measurable_history n).prodMk (h.measurable_step (n + 1))
    apply Measure.AbsolutelyContinuous.map _ (by fun_prop)
    rw [(h.hasCondDistrib_step n).map_eq, (h₀.hasCondDistrib_step n).map_eq]
    apply Measure.AbsolutelyContinuous.compProd ih
    filter_upwards with h' using Measure.AbsolutelyContinuous.compProd_left_apply (hc.policy n h') _

variable [MeasurableSpace.CountablyGenerated 𝓐]

lemma hasLaw_history_withDensity (h : IsAlgEnvSeq A Y alg env P)
    (h₀ : IsAlgEnvSeq A₀ Y₀ alg₀ env P₀) (hc : alg ≪ₐ alg₀) (n : ℕ) : HasLaw (history A Y n)
      ((P₀.map (history A₀ Y₀ n)).withDensity (alg.density alg₀ n)) P where
  aemeasurable := (h.measurable_history n).aemeasurable
  map_eq := by
    induction n with
    | zero =>
      rw [h.hasLaw_history_zero.map_eq, h₀.hasLaw_history_zero.map_eq, h.hasLaw_step_zero.map_eq,
        h₀.hasLaw_step_zero.map_eq]
      rw [← Measure.withDensity_rnDeriv_eq _ _ hc.p0,
        Measure.compProd_withDensity_left (by fun_prop)]
      exact map_equiv_withDensity (by fun_prop)
    | succ n ih =>
      let ρ h' (ar : 𝓐 × 𝓨) := Kernel.rnDeriv (alg.policy n) (alg₀.policy n) h' ar.1
      have hs : stepKernel alg env n = (stepKernel alg₀ env n).withDensity ρ := by
        rw [stepKernel, ← Kernel.withDensity_rnDeriv_eq' (hc.policy n)]
        exact Kernel.compProd_withDensity_left (Kernel.measurable_rnDeriv _ _)
      have : IsMarkovKernel ((stepKernel alg₀ env n).withDensity ρ) := by
        rw [← hs]
        infer_instance
      simp_rw [history_succ]
      rw [← Measure.map_map (by fun_prop), ← Measure.map_map (by fun_prop)]
      rotate_left
      · exact (h₀.measurable_history n).prodMk (h₀.measurable_step (n + 1))
      · exact (h.measurable_history n).prodMk (h.measurable_step (n + 1))
      rw [(h.hasCondDistrib_step n).map_eq, (h₀.hasCondDistrib_step n).map_eq, ih, hs,
        Measure.compProd_withDensity_withDensity (by fun_prop) (by fun_prop)]
      exact map_equiv_withDensity (by fun_prop)

end IsAlgEnvSeq

end Learning
