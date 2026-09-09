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

Let `alg` be an algorithm and `env, env'` two environments, and consider two algorithm-environment
sequences of `alg` against these environments, on arbitrary probability spaces. The
Kullback–Leibler divergence between the laws of the histories of the first `M` rounds is the sum,
over the rounds `t < M`, of the conditional divergences of the step at round `t` given the first
`t` rounds (`IsAlgEnvSeq.klDiv_map_history_stepKernel`, a chain rule): the policy kernels
are shared and only the feedback kernels differ. More generally, for a stopping rule `S` with
stopping time `τ = stoppingTime X Y S` (the number of rounds played), the divergence between the
laws of the histories stopped at `min τ M` is the sum over `t < M` of the conditional divergences
of the step at round `t`, on the event `{t < τ}`
(`IsAlgEnvSeq.klDiv_map_stoppedHist_min_stepKernel`), and when `τ` is almost surely finite
under both laws, the divergence between the laws of the stopped histories is the series of these
terms (`IsAlgEnvSeq.klDiv_map_stoppedHist_stepKernel`).

For two stationary environments with reward kernels `κ, κ'`, the conditional divergence of a
step is the conditional divergence of the reward given the played action. This is the
*divergence decomposition* of bandit lower bounds, in composition-product form
`klDiv (P.map (history X Y M)) (P'.map (history X' Y' M))
  = ∑ t < M, klDiv (P.map (X t) ⊗ₘ κ) (P.map (X t) ⊗ₘ κ')`
(`IsAlgEnvSeq.klDiv_map_history_compProd`, on arbitrary measurable spaces) and in integral form
`= ∑ t < M, ∫⁻ ω, klDiv (κ (X t ω)) (κ' (X t ω)) ∂P`
(`IsAlgEnvSeq.klDiv_map_history`, when `𝓨` is countably generated), together with the versions
for the history stopped at a bounded stopping time (`klDiv_map_stoppedHist_min_compProd`,
`klDiv_map_stoppedHist_min`) and for the history stopped at an almost surely finite stopping
time:
`klDiv (P.map (stoppedHist X Y τ)) (P'.map (stoppedHist X' Y' τ'))
  = ∫⁻ ω, ∑ t < τ ω, klDiv (κ (X t ω)) (κ' (X t ω)) ∂P`
(`IsAlgEnvSeq.klDiv_map_stoppedHist_compProd`, `IsAlgEnvSeq.klDiv_map_stoppedHist`), and
for the whole trajectory `trajectory X Y : Ω → (ℕ → 𝓐 × 𝓨)`:
`klDiv (P.map (trajectory X Y)) (P'.map (trajectory X' Y'))
  = ∑' t, klDiv (P.map (X t) ⊗ₘ κ) (P.map (X t) ⊗ₘ κ')`
(`IsAlgEnvSeq.klDiv_map_trajectory_compProd`, `IsAlgEnvSeq.klDiv_map_trajectory`).

The bounded stopping-time version is proved by induction on `M`: the law of the history stopped
at `min τ (M + 1)` splits according to whether `τ ≤ M` (`map_stoppedHist_min_succ_eq_add`), the
divergence is additive over disjoint supports (`klDiv_add_add_of_measure_eq_zero`) and the chain
rule `klDiv_compProd_eq_add` handles the step at round `M`. The finite-horizon version is the
case `S = ∅`. The almost surely finite version follows by monotone convergence
(`klDiv_eq_iSup_restrict`) and the data-processing inequality, since the history stopped at
`min τ M` is the truncation of the stopped history. The integral forms follow from the
composition-product forms by LML's integrated chain rule `klDiv_compProd_right_eq_lintegral`.
The infinite trajectory version follows from the finite-horizon one since the divergence is the
supremum of the divergences of the finite-dimensional marginals (`klDiv_eq_iSup_map`).

For the linear Gaussian environments `linearGaussianEnv 𝒳 θ`, `linearGaussianEnv 𝒳 θ'` the one-step
divergence is `⟪x, θ - θ'⟫ ^ 2 / 2`, which gives
`klDiv (P.map (history X Y n)) (P'.map (history X' Y' n))
  = ofReal (∑ t < n, ∫ ω, ⟪X t ω, θ - θ'⟫ ^ 2 / 2 ∂P)`
(`LinearBandit.klDiv_map_history`) and the bound `n R ^ 2 ‖θ - θ'‖ ^ 2 / 2` when `𝒳`
is contained in the ball of radius `R` (`LinearBandit.klDiv_map_history_le`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal RealInnerProductSpace ENat

namespace Learning

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {X' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}
  {alg alg' : Algorithm 𝓐 𝓨} {env env' : Environment 𝓐 𝓨}
  {κ κ' : Kernel 𝓐 𝓨} [IsMarkovKernel κ] [IsMarkovKernel κ']

section

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} [IsFiniteMeasure μ]

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

end

/-! ### Histories of a fixed number of rounds -/

/-- **Chain rule for histories.** For an algorithm `alg` run against two environments `env`,
`env'`, the divergence between the laws of the histories of the first `M` rounds is the sum over
the rounds `t < M` of the conditional divergences of the step at round `t` given the first `t`
rounds (composition-product form). -/
lemma IsAlgEnvSeq.klDiv_map_history_stepKernel (h : IsAlgEnvSeq X Y alg env P)
    (h' : IsAlgEnvSeq X' Y' alg' env' P') (M : ℕ) :
    klDiv (P.map (history X Y M)) (P'.map (history X' Y' M)) =
      ∑ t ∈ range M,
        klDiv (P.map (history X Y t) ⊗ₘ stepKernel alg env t)
          (P.map (history X Y t) ⊗ₘ stepKernel alg' env' t) := by
  have hX := h.measurable_action
  have hY := h.measurable_feedback
  have hX' := h'.measurable_action
  have hY' := h'.measurable_feedback
  induction M with
  | zero => simp
  | succ M ih =>
    rw [history_succ, history_succ, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_map (by fun_prop) (by fun_prop), klDiv_map_measurableEquiv,
      (h.hasCondDistrib_step M).map_eq, (h'.hasCondDistrib_step M).map_eq,
      klDiv_compProd_eq_add, ih, sum_range_succ]

/-- **Divergence decomposition**, composition-product form, for the history of the first `M`
rounds: for an algorithm `alg` run against two stationary environments with reward kernels `κ`
and `κ'`, the divergence between the laws of the histories of the first `M` rounds is the sum over
the rounds `t < M` of the conditional divergences of the reward kernels given the played
action. -/
lemma IsAlgEnvSeq.klDiv_map_history_compProd (h : IsAlgEnvSeq X Y alg (stationaryEnv κ) P)
    (h' : IsAlgEnvSeq X' Y' alg (stationaryEnv κ') P') (M : ℕ) :
    klDiv (P.map (history X Y M)) (P'.map (history X' Y' M)) =
      ∑ t ∈ range M, klDiv (P.map (X t) ⊗ₘ κ) (P.map (X t) ⊗ₘ κ') := by
  rw [h.klDiv_map_history_stepKernel h']
  refine sum_congr rfl fun t _ ↦ ?_
  rw [stepKernel_stationaryEnv, stepKernel_stationaryEnv,
    klDiv_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd,
    ← (h.hasCondDistrib_action t).hasLaw_comp.map_eq]

/-- **Divergence decomposition**, integral form, for the history of the first `M` rounds: the
divergence between the laws of the histories of the first `M` rounds is the expected sum, along
the first trajectory, of the divergences of the reward kernels at the played actions. -/
lemma IsAlgEnvSeq.klDiv_map_history [MeasurableSpace.CountablyGenerated 𝓨]
    (h : IsAlgEnvSeq X Y alg (stationaryEnv κ) P)
    (h' : IsAlgEnvSeq X' Y' alg (stationaryEnv κ') P') (M : ℕ) :
    klDiv (P.map (history X Y M)) (P'.map (history X' Y' M)) =
      ∑ t ∈ range M, ∫⁻ ω, klDiv (κ (X t ω)) (κ' (X t ω)) ∂P := by
  rw [h.klDiv_map_history_compProd h']
  refine sum_congr rfl fun t _ ↦ ?_
  rw [klDiv_compProd_right_eq_lintegral,
    lintegral_map (measurable_klDiv_kernel κ κ') (h.measurable_action t)]

/-! ### Infinite trajectories -/

/-- The divergence between the laws of two trajectories is the supremum of the divergences
between the laws of the histories up to time `n`. -/
lemma klDiv_map_trajectory_eq_iSup (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hX' : ∀ n, Measurable (X' n)) (hY' : ∀ n, Measurable (Y' n)) :
    klDiv (P.map (trajectory X Y)) (P'.map (trajectory X' Y')) =
      ⨆ n, klDiv (P.map (history X Y n)) (P'.map (history X' Y' n)) := by
  have hg : ∀ n, Measurable fun f : ℕ → 𝓐 × 𝓨 ↦ fun i : Fin n ↦ f i.1 := fun n ↦
    measurable_pi_lambda _ fun i ↦ measurable_pi_apply i.1
  rw [klDiv_eq_iSup_map hg ?_ MeasurableSpace.iSup_comap_restrictFin]
  · refine iSup_congr fun n ↦ ?_
    rw [Measure.map_map (hg n) (measurable_trajectory hX hY),
      Measure.map_map (hg n) (measurable_trajectory hX' hY')]
    rfl
  · intro n m hnm
    have : (fun f : ℕ → 𝓐 × 𝓨 ↦ fun i : Fin n ↦ f i.1) =
        (fun h : Fin m → 𝓐 × 𝓨 ↦ fun i : Fin n ↦ h (Fin.castLE hnm i)) ∘
          fun f : ℕ → 𝓐 × 𝓨 ↦ fun i : Fin m ↦ f i.1 := rfl
    beta_reduce
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_lambda _ fun i ↦
      measurable_pi_apply (Fin.castLE hnm i)).comap_le

/-- **Chain rule for trajectories.** For an algorithm `alg` run against two environments `env`,
`env'`, the divergence between the laws of the trajectories is the series over the rounds `t` of
the conditional divergences of the step at round `t` given the first `t` rounds
(composition-product form). -/
lemma IsAlgEnvSeq.klDiv_map_trajectory_stepKernel (h : IsAlgEnvSeq X Y alg env P)
    (h' : IsAlgEnvSeq X' Y' alg' env' P') :
    klDiv (P.map (trajectory X Y)) (P'.map (trajectory X' Y')) =
      ∑' t : ℕ, klDiv (P.map (history X Y t) ⊗ₘ stepKernel alg env t)
        (P.map (history X Y t) ⊗ₘ stepKernel alg' env' t) := by
  have hX := h.measurable_action
  have hY := h.measurable_feedback
  have hX' := h'.measurable_action
  have hY' := h'.measurable_feedback
  rw [klDiv_map_trajectory_eq_iSup hX hY hX' hY', ENNReal.tsum_eq_iSup_nat]
  exact iSup_congr fun n ↦ h.klDiv_map_history_stepKernel h' n

/-- **Divergence decomposition for trajectories**, composition-product form: for an algorithm
`alg` run against two stationary environments with reward kernels `κ` and `κ'`, the divergence
between the laws of the trajectories is the series over the rounds `t` of the conditional
divergences of the reward kernels given the played action. -/
lemma IsAlgEnvSeq.klDiv_map_trajectory_compProd (h : IsAlgEnvSeq X Y alg (stationaryEnv κ) P)
    (h' : IsAlgEnvSeq X' Y' alg (stationaryEnv κ') P') :
    klDiv (P.map (trajectory X Y)) (P'.map (trajectory X' Y')) =
      ∑' t : ℕ, klDiv (P.map (X t) ⊗ₘ κ) (P.map (X t) ⊗ₘ κ') := by
  rw [klDiv_map_trajectory_eq_iSup h.measurable_action h.measurable_feedback
    h'.measurable_action h'.measurable_feedback, ENNReal.tsum_eq_iSup_nat]
  exact iSup_congr fun n ↦ h.klDiv_map_history_compProd h' n

/-- **Divergence decomposition for trajectories**, integral form: the divergence between the
laws of the trajectories is the series over the rounds `t` of the expected divergences of the
reward kernels at the played actions. -/
lemma IsAlgEnvSeq.klDiv_map_trajectory [MeasurableSpace.CountablyGenerated 𝓨]
    (h : IsAlgEnvSeq X Y alg (stationaryEnv κ) P)
    (h' : IsAlgEnvSeq X' Y' alg (stationaryEnv κ') P') :
    klDiv (P.map (trajectory X Y)) (P'.map (trajectory X' Y')) =
      ∑' t : ℕ, ∫⁻ ω, klDiv (κ (X t ω)) (κ' (X t ω)) ∂P := by
  rw [h.klDiv_map_trajectory_compProd h']
  refine tsum_congr fun t ↦ ?_
  rw [klDiv_compProd_right_eq_lintegral,
    lintegral_map (measurable_klDiv_kernel κ κ') (h.measurable_action t)]

end Learning
