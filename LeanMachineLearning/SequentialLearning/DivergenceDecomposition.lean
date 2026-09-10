/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.ChainRule
public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.CompProd
public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.MapSequence
public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.Restrict
public import LeanMachineLearning.SequentialLearning.StationaryEnv

/-!
# The divergence decomposition

Let `alg`, `alg'` be algorithms, `env`, `env'` be environments, and consider two
algorithm-environment sequences `(O, A, Y)` and `(O', A', Y')` of `alg` against `env` and of `alg'`
against `env'`, on arbitrary probability spaces `(Ω, P)` and `(Ω', P')`. The Kullback-Leibler
divergence between the laws of the histories of the first `M` rounds is the sum, over the rounds
`t < M`, of the conditional divergences of the step at round `t` given the first `t` rounds.
Note that both arguments of the conditional term use the law of the *first* history,
so that term measures only how the two step kernels differ.
The same identity holds for the whole trajectory `trajectory O A Y : Ω → (ℕ → Round 𝓞 𝓐 𝓨)`, with
a series in place of the finite sum.

For a single algorithm run against two stationary environments with reward kernels `κ` and
`κ'`, the two step kernels share the observation kernel and the policy and differ only in the
reward kernel, so the conditional divergence of a step is the conditional divergence of the reward
given the played action.
This is the *divergence decomposition* of bandit lower bounds.

## Main statements

* `IsAlgEnvSeq.klDiv_map_history_stepKernel`, `IsAlgEnvSeq.klDiv_map_trajectory_stepKernel`:
  the chain rule for the law of the history of the first `M` rounds and for the law of the
  trajectory.
* `IsAlgEnvSeq.klDiv_map_history_compProd`, `IsAlgEnvSeq.klDiv_map_history`: the divergence
  decomposition for two stationary environments, in composition-product and in integral form.
* `IsAlgEnvSeq.klDiv_map_trajectory_compProd`, `IsAlgEnvSeq.klDiv_map_trajectory`: the same two
  forms for the trajectory.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal RealInnerProductSpace ENat

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {O' : ℕ → Ω' → 𝓞} {A' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}
  {alg alg' : Algorithm 𝓞 𝓐 𝓨} {env env' : Environment 𝓞 𝓐 𝓨}

section

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {μ : Measure α} [IsFiniteMeasure μ]

/-- The divergence of one step of a policy/reward decomposition, in composition-product form:
the policy `π` is shared and the reward kernels `κ`, `η` (which ignore the history) differ, so
the divergence is the conditional divergence of the reward kernels given the played action,
whose law is `π ∘ₘ μ`. -/
lemma klDiv_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd (μ : Measure α)
    [IsFiniteMeasure μ] (π : Kernel α β) [IsMarkovKernel π] (κ η : Kernel β γ) [IsFiniteKernel κ]
    [IsFiniteKernel η] :
    klDiv (μ ⊗ₘ (π ⊗ₖ κ.prodMkLeft α)) (μ ⊗ₘ (π ⊗ₖ η.prodMkLeft α)) =
      klDiv ((π ∘ₘ μ) ⊗ₘ κ) ((π ∘ₘ μ) ⊗ₘ η) := by
  rw [← klDiv_map_measurableEquiv _ _ MeasurableEquiv.prodAssoc.symm, Measure.compProd_assoc,
    Measure.compProd_assoc, ← Measure.snd_compProd, Measure.snd]
  exact klDiv_compProd_comap _ _ _ measurable_snd

/-- The divergence of one step of an observation/policy/reward decomposition, in
composition-product form: the observation kernel `o` and the policy `π` are shared and the reward
kernels `κ`, `η` (which ignore the history and the observation) differ, so the divergence is the
conditional divergence of the reward kernels given the played action, whose law is
`π ∘ₘ (μ ⊗ₘ o)`. -/
lemma klDiv_compProd_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd (μ : Measure α)
    [IsFiniteMeasure μ] (o : Kernel α β) [IsMarkovKernel o] (π : Kernel (α × β) γ)
    [IsMarkovKernel π] (κ η : Kernel γ δ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (μ ⊗ₘ (o ⊗ₖ (π ⊗ₖ κ.prodMkLeft (α × β))))
        (μ ⊗ₘ (o ⊗ₖ (π ⊗ₖ η.prodMkLeft (α × β)))) =
      klDiv ((π ∘ₘ (μ ⊗ₘ o)) ⊗ₘ κ) ((π ∘ₘ (μ ⊗ₘ o)) ⊗ₘ η) := by
  rw [← klDiv_map_measurableEquiv _ _ MeasurableEquiv.prodAssoc.symm, Measure.compProd_assoc,
    Measure.compProd_assoc]
  exact klDiv_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd _ _ _ _

end

/-- **Chain rule for histories.** For two algorithms `alg`, `alg'` run against two environments
`env`, `env'`, the divergence between the laws of the histories of the first `M` rounds is
the sum over the rounds `t < M` of the conditional divergences of the step at round `t` given
the first `t` rounds. -/
lemma IsAlgEnvSeq.klDiv_map_history_stepKernel (h : IsAlgEnvSeq O A Y alg env P)
    (h' : IsAlgEnvSeq O' A' Y' alg' env' P') (M : ℕ) :
    klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M)) =
      ∑ t ∈ range M,
        klDiv (P.map (history O A Y t) ⊗ₘ stepKernel alg env t)
          (P.map (history O A Y t) ⊗ₘ stepKernel alg' env' t) := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  have hO' := h'.measurable_obs
  have hA' := h'.measurable_action
  have hY' := h'.measurable_feedback
  induction M with
  | zero => simp
  | succ M ih =>
    rw [history_succ, history_succ, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_map (by fun_prop) (by fun_prop), klDiv_map_measurableEquiv,
      (h.hasCondDistrib_step M).map_eq, (h'.hasCondDistrib_step M).map_eq,
      klDiv_compProd_eq_add, ih, sum_range_succ]

/-- The divergence between the laws of two trajectories is the supremum over `n` of the divergences
between the laws of the histories up to time `n`. -/
lemma klDiv_map_trajectory_eq_iSup (hO : ∀ n, Measurable (O n)) (hA : ∀ n, Measurable (A n))
    (hY : ∀ n, Measurable (Y n)) (hO' : ∀ n, Measurable (O' n)) (hA' : ∀ n, Measurable (A' n))
    (hY' : ∀ n, Measurable (Y' n)) :
    klDiv (P.map (trajectory O A Y)) (P'.map (trajectory O' A' Y')) =
      ⨆ n, klDiv (P.map (history O A Y n)) (P'.map (history O' A' Y' n)) := by
  have hg : ∀ n, Measurable fun f : ℕ → Round 𝓞 𝓐 𝓨 ↦ fun i : Fin n ↦ f i.1 := fun n ↦
    measurable_pi_lambda _ fun i ↦ measurable_pi_apply i.1
  rw [klDiv_eq_iSup_map hg ?_ MeasurableSpace.iSup_comap_restrictFin]
  · refine iSup_congr fun n ↦ ?_
    rw [Measure.map_map (hg n) (measurable_trajectory hO hA hY),
      Measure.map_map (hg n) (measurable_trajectory hO' hA' hY')]
    rfl
  · intro n m hnm
    have : (fun f : ℕ → Round 𝓞 𝓐 𝓨 ↦ fun i : Fin n ↦ f i.1) =
        (fun h : Fin m → Round 𝓞 𝓐 𝓨 ↦ fun i : Fin n ↦ h (Fin.castLE hnm i)) ∘
          fun f : ℕ → Round 𝓞 𝓐 𝓨 ↦ fun i : Fin m ↦ f i.1 := rfl
    beta_reduce
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_lambda _ fun i ↦
      measurable_pi_apply (Fin.castLE hnm i)).comap_le

/-- **Chain rule for trajectories.** For two algorithms `alg` and `alg'` run against
two environments `env` and `env'`, the divergence between the laws of the trajectories is
the series over the rounds `t` of the conditional divergences of the step at round `t` given
the first `t` rounds. -/
lemma IsAlgEnvSeq.klDiv_map_trajectory_stepKernel (h : IsAlgEnvSeq O A Y alg env P)
    (h' : IsAlgEnvSeq O' A' Y' alg' env' P') :
    klDiv (P.map (trajectory O A Y)) (P'.map (trajectory O' A' Y')) =
      ∑' t : ℕ, klDiv (P.map (history O A Y t) ⊗ₘ stepKernel alg env t)
        (P.map (history O A Y t) ⊗ₘ stepKernel alg' env' t) := by
  rw [klDiv_map_trajectory_eq_iSup h.measurable_obs h.measurable_action h.measurable_feedback
    h'.measurable_obs h'.measurable_action h'.measurable_feedback, ENNReal.tsum_eq_iSup_nat]
  exact iSup_congr fun n ↦ h.klDiv_map_history_stepKernel h' n

section StationaryEnv

variable {O : ℕ → Ω → Unit} {O' : ℕ → Ω' → Unit} {alg : Algorithm Unit 𝓐 𝓨}
  {κ κ' : Kernel 𝓐 𝓨} [IsMarkovKernel κ] [IsMarkovKernel κ']

/-- Chain rule for histories of a single algorithm versus two stationary environments. -/
lemma IsAlgEnvSeq.klDiv_map_history_compProd (h : IsAlgEnvSeq O A Y alg (stationaryEnv κ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (stationaryEnv κ') P') (M : ℕ) :
    klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M)) =
      ∑ t ∈ range M, klDiv (P.map (A t) ⊗ₘ κ) (P.map (A t) ⊗ₘ κ') := by
  rw [h.klDiv_map_history_stepKernel h']
  refine sum_congr rfl fun t _ ↦ ?_
  have h_obs := (h.hasCondDistrib_obs t).map_eq
  rw [obs_stationaryEnv] at h_obs
  rw [stepKernel_stationaryEnv, stepKernel_stationaryEnv,
    klDiv_compProd_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd, ← h_obs,
    ← (h.hasCondDistrib_action t).hasLaw_comp.map_eq]

/-- Chain rule for histories of a single algorithm versus two stationary environments. -/
lemma IsAlgEnvSeq.klDiv_map_history [MeasurableSpace.CountablyGenerated 𝓨]
    (h : IsAlgEnvSeq O A Y alg (stationaryEnv κ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (stationaryEnv κ') P') (M : ℕ) :
    klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M)) =
      ∑ t ∈ range M, ∫⁻ ω, klDiv (κ (A t ω)) (κ' (A t ω)) ∂P := by
  rw [h.klDiv_map_history_compProd h']
  refine sum_congr rfl fun t _ ↦ ?_
  rw [klDiv_compProd_right_eq_lintegral,
    lintegral_map (measurable_klDiv_kernel κ κ') (h.measurable_action t)]

/-- Chain rule for trajectories of a single algorithm versus two stationary environments. -/
lemma IsAlgEnvSeq.klDiv_map_trajectory_compProd (h : IsAlgEnvSeq O A Y alg (stationaryEnv κ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (stationaryEnv κ') P') :
    klDiv (P.map (trajectory O A Y)) (P'.map (trajectory O' A' Y')) =
      ∑' t : ℕ, klDiv (P.map (A t) ⊗ₘ κ) (P.map (A t) ⊗ₘ κ') := by
  rw [klDiv_map_trajectory_eq_iSup h.measurable_obs h.measurable_action h.measurable_feedback
    h'.measurable_obs h'.measurable_action h'.measurable_feedback, ENNReal.tsum_eq_iSup_nat]
  exact iSup_congr fun n ↦ h.klDiv_map_history_compProd h' n

/-- Chain rule for trajectories of a single algorithm versus two stationary environments. -/
lemma IsAlgEnvSeq.klDiv_map_trajectory [MeasurableSpace.CountablyGenerated 𝓨]
    (h : IsAlgEnvSeq O A Y alg (stationaryEnv κ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (stationaryEnv κ') P') :
    klDiv (P.map (trajectory O A Y)) (P'.map (trajectory O' A' Y')) =
      ∑' t : ℕ, ∫⁻ ω, klDiv (κ (A t ω)) (κ' (A t ω)) ∂P := by
  rw [h.klDiv_map_trajectory_compProd h']
  refine tsum_congr fun t ↦ ?_
  rw [klDiv_compProd_right_eq_lintegral,
    lintegral_map (measurable_klDiv_kernel κ κ') (h.measurable_action t)]

end StationaryEnv

end Learning
