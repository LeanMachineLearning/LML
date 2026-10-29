/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import LeanMachineLearning.ForMathlib.Analysis.Convex.Integral
public import LeanMachineLearning.ForMathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The means of the feedback distribution

## Main definitions

* `Environment.feedbackKernel env O A Y n ω`: the law of the feedback at time `n`, as a kernel
  from the action chosen at time `n`, given the history and the observation of the run at `ω`.
* `Environment.means env O A Y k n ω`: the mean of that law at action `k`.

## Main statements

* `IsAlgEnvSeq.condExp_feedback`: the conditional expectation of the feedback at time `n` given the
  history, the observation and the action at time `n` is the mean of the feedback at the chosen
  action.
* `IsAlgEnvSeq.integrable_means_action`, `IsAlgEnvSeq.memLp_means_action`: integrability of the
  mean at the chosen action.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset

open scoped ENNReal

namespace Learning

variable {Ω 𝓞 𝓐 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓞 : MeasurableSpace 𝓞}
  {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  [NormedAddCommGroup 𝓨] [NormedSpace ℝ 𝓨]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {P : Measure Ω}
  {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}

/-- The law of the feedback at time `n`, as a kernel from the action chosen at time `n`, given the
history and the observation of the run at `ω`: the feedback kernel `env.feedback n` applied to the
history and the observation at time `n`. -/
noncomputable def Environment.feedbackKernel (env : Environment 𝓞 𝓐 𝓨) (O : ℕ → Ω → 𝓞)
    (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (n : ℕ) (ω : Ω) : Kernel 𝓐 𝓨 :=
  (env.feedback n).sectR (history O A Y n ω, O n ω)

/-- The means of the feedback distribution as a function of the action chosen at time `n`. -/
noncomputable def Environment.means (env : Environment 𝓞 𝓐 𝓨) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → 𝓐)
    (Y : ℕ → Ω → 𝓨) (k : 𝓐) (n : ℕ) (ω : Ω) : 𝓨 :=
  (env.feedbackKernel O A Y n ω k)[id]

@[simp]
lemma Environment.means_zero (env : Environment 𝓞 𝓐 𝓨) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → 𝓐)
    (Y : ℕ → Ω → 𝓨) (k : 𝓐) (ω : Ω) :
    env.means O A Y k 0 ω = (env.feedbackZero (O 0 ω, k))[id] := by
  simp [Environment.means, Environment.feedbackKernel, Environment.feedback_zero]

@[simp]
lemma Environment.means_of_isOblivious [env.IsOblivious] (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → 𝓐)
    (Y : ℕ → Ω → 𝓨) (k : 𝓐) (n : ℕ) (ω : Ω) :
    env.means O A Y k n ω = (env.feedbackCondObsAction n (O n ω, k))[id] := by
  simp [Environment.means, Environment.feedbackKernel, env.feedback_eq_comap_feedbackCondObsAction,
    Kernel.comap_apply]

lemma Environment.means_of_isStationary [env.IsStationary] (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → 𝓐)
    (Y : ℕ → Ω → 𝓨) (k : 𝓐) (n : ℕ) (ω : Ω) :
    env.means O A Y k n ω = (env.feedbackZero (O n ω, k))[id] := by
  rw [means_of_isOblivious, env.feedbackCondObsAction_eq_feedbackZero]

lemma means_oblivious (μ : ℕ → Measure 𝓞) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : ℕ → Kernel (𝓞 × 𝓐) 𝓨) [∀ n, IsMarkovKernel (ν n)] (k : 𝓐) (n : ℕ) (ω : Ω) :
    (Environment.oblivious μ ν).means O A Y k n ω = (ν n (O n ω, k))[id] := by simp

lemma means_stationary (μ : Measure 𝓞) [IsProbabilityMeasure μ] (ν : Kernel (𝓞 × 𝓐) 𝓨)
    [IsMarkovKernel ν] (k : 𝓐) (n : ℕ) (ω : Ω) :
    (Environment.stationary μ ν).means O A Y k n ω = (ν (O n ω, k))[id] := by simp

lemma means_banditSeq (ν : ℕ → Kernel 𝓐 𝓨) [∀ n, IsMarkovKernel (ν n)]
    {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} (k : 𝓐) (n : ℕ) (ω : Ω) :
    (Environment.banditSeq ν).means O A Y k n ω = (ν n k)[id] := by simp

lemma means_bandit (ν : Kernel 𝓐 𝓨) [IsMarkovKernel ν]
    {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} (k : 𝓐) (n : ℕ) (ω : Ω) :
    (Environment.bandit ν).means O A Y k n ω = (ν k)[id] := by simp

@[fun_prop]
lemma IsAlgEnvSeq.stronglyMeasurable_means [SecondCountableTopology 𝓨] [OpensMeasurableSpace 𝓨]
    (h : IsAlgEnvSeq O A Y alg env P) (k : 𝓐) (n : ℕ) :
    StronglyMeasurable (env.means O A Y k n) := by
  unfold Environment.means
  have hO := h.measurable_obs
  have h_eq ω : env.feedbackKernel O A Y n ω k =
      (env.feedback n ∘ₖ Kernel.deterministic (fun ω ↦ ((history O A Y n ω, O n ω), k))
        (((h.measurable_history n).prodMk (h.measurable_obs n)).prodMk (by fun_prop))) ω := by
    simp [Environment.feedbackKernel, Kernel.comp_deterministic_eq_comap]
  simp_rw [h_eq]
  fun_prop

@[fun_prop]
lemma IsAlgEnvSeq.measurable_means [SecondCountableTopology 𝓨] [BorelSpace 𝓨]
    (h : IsAlgEnvSeq O A Y alg env P) (k : 𝓐) (n : ℕ) :
    Measurable (env.means O A Y k n) :=
  (h.stronglyMeasurable_means k n).measurable

lemma IsAlgEnvSeq.adapted_means_filtrationAction [SecondCountableTopology 𝓨] [BorelSpace 𝓨]
    (h : IsAlgEnvSeq O A Y alg env P) :
    Adapted h.filtrationAction (fun n ω ↦ env.means O A Y (A n ω) n ω) := by
  intro n
  simp only [Environment.means, Environment.feedbackKernel, Kernel.sectR_apply, id_eq]
  rw [IsAlgEnvSeq.filtrationAction_eq_comap]
  exact measurable_comp_comap (fun ω ↦ ((history O A Y n ω, O n ω), A n ω))
    (stronglyMeasurable_id.integral_kernel (κ := env.feedback n)).measurable

lemma IsAlgEnvSeq.stronglyAdapted_means_filtrationAction [SecondCountableTopology 𝓨] [BorelSpace 𝓨]
    (h : IsAlgEnvSeq O A Y alg env P) :
    StronglyAdapted h.filtrationAction (fun n ω ↦ env.means O A Y (A n ω) n ω) :=
  (h.adapted_means_filtrationAction).stronglyAdapted

lemma IsAlgEnvSeq.adapted_means [SecondCountableTopology 𝓨] [BorelSpace 𝓨]
    (h : IsAlgEnvSeq O A Y alg env P) :
    Adapted h.filtration (fun n ω ↦ env.means O A Y (A n ω) n ω) :=
  fun n ↦ (h.adapted_means_filtrationAction n).mono (h.filtrationAction_le_filtration n) le_rfl

omit [NormedSpace ℝ 𝓨] in
lemma IsAlgEnvSeq.condExp_feedback_comp [IsFiniteMeasure P] {𝓩 : Type*} [NormedAddCommGroup 𝓩]
    [NormedSpace ℝ 𝓩] [CompleteSpace 𝓩] [StandardBorelSpace 𝓨]
    (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ)
    {g : 𝓨 → 𝓩} (hg : StronglyMeasurable g) (hint : Integrable (fun ω ↦ g (Y n ω)) P) :
    P[fun ω ↦ g (Y n ω) | h.filtrationAction n] =ᵐ[P]
      fun ω ↦ (env.feedback n ((history O A Y n ω, O n ω), A n ω))[g] := by
  have hX : Measurable (fun ω ↦ ((history O A Y n ω, O n ω), A n ω)) :=
    ((h.measurable_history n).prodMk (h.measurable_obs n)).prodMk (h.measurable_action n)
  rw [h.filtrationAction_eq_comap n]
  exact (h.hasCondDistrib_feedback n).condExp_comp_ae_eq hX hg hint

lemma IsAlgEnvSeq.condExp_feedback [IsFiniteMeasure P] [BorelSpace 𝓨] [SecondCountableTopology 𝓨]
    [CompleteSpace 𝓨]
    (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ)
    (hint : Integrable (Y n) P) :
    P[Y n | h.filtrationAction n] =ᵐ[P] fun ω ↦ env.means O A Y (A n ω) n ω :=
  condExp_feedback_comp h n stronglyMeasurable_id hint

lemma IsAlgEnvSeq.memLp_means_action [SFinite P] [SecondCountableTopology 𝓨] [BorelSpace 𝓨]
    (h : IsAlgEnvSeq O A Y alg env P) {n : ℕ} {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ∞)
    (hint : MemLp (Y n) p P) :
    MemLp (fun ω ↦ env.means O A Y (A n ω) n ω) p P := by
  have hp0 : p ≠ 0 := by positivity
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have h_hist := h.measurable_history
  have hint' : MemLp id p (P.map (Y n)) := by
    rwa [memLp_map_measure_iff (by fun_prop) (h.measurable_feedback _).aemeasurable]
  unfold Environment.means Environment.feedbackKernel
  simp only [id_eq]
  rw [(h.hasLaw_feedback_comp n).map_eq, Measure.memLp_comp_iff hp0 hp_top (by fun_prop)] at hint'
  have hint'' := hint'.2.comp_aemeasurable (by fun_prop)
  have h_eq ω : (env.feedback n) ((history O A Y n ω, O n ω), A n ω) =
      (env.feedback n ∘ₖ
        Kernel.deterministic (fun ω ↦ ((history O A Y n ω, O n ω), A n ω)) (by fun_prop)) ω := by
    simp [Kernel.comp_deterministic_eq_comap]
  rw [← integrable_norm_rpow_iff _ hp0 hp_top]
  swap
  · refine StronglyMeasurable.aestronglyMeasurable ?_
    simp_rw [Kernel.sectR_apply, h_eq]
    exact StronglyMeasurable.integral_kernel (by fun_prop)
  simp only [id_eq] at hint''
  refine Integrable.mono' hint'' ?_ ?_
  · refine ((AEMeasurable.norm ?_).pow_const _).aestronglyMeasurable
    refine (StronglyMeasurable.measurable ?_).aemeasurable
    simp_rw [Kernel.sectR_apply, h_eq]
    exact StronglyMeasurable.integral_kernel (by fun_prop)
  · simp only [Real.norm_eq_abs, Function.comp_apply, Kernel.sectR_apply]
    filter_upwards [ae_of_ae_map (((h_hist n).prodMk (hO n)).prodMk (hA n)).aemeasurable hint'.1]
      with ω hω
    rw [abs_of_nonneg (by positivity)]
    exact norm_integral_rpow_le_integral_norm_rpow hp1 hp_top hω

lemma IsAlgEnvSeq.integrable_means_action [SFinite P] [SecondCountableTopology 𝓨]
    [OpensMeasurableSpace 𝓨]
    (h : IsAlgEnvSeq O A Y alg env P) {n : ℕ} (hint : Integrable (Y n) P) :
    Integrable (fun ω ↦ env.means O A Y (A n ω) n ω) P := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have h_hist := h.measurable_history
  have hint' : Integrable id (P.map (Y n)) := by
    rwa [integrable_map_measure (by fun_prop) (h.measurable_feedback _).aemeasurable]
  unfold Environment.means Environment.feedbackKernel
  simp only [id_eq]
  rw [(h.hasLaw_feedback_comp n).map_eq, Measure.integrable_comp_iff (by fun_prop)] at hint'
  have hint'' := hint'.2.comp_aemeasurable (by fun_prop)
  simp only [id_eq] at hint''
  refine Integrable.mono' hint'' ?_ ?_
  · refine StronglyMeasurable.aestronglyMeasurable ?_
    have h_eq ω : (env.feedback n) ((history O A Y n ω, O n ω), A n ω) =
        (env.feedback n ∘ₖ
          Kernel.deterministic (fun ω ↦ ((history O A Y n ω, O n ω), A n ω)) (by fun_prop)) ω := by
      simp [Kernel.comp_deterministic_eq_comap]
    simp_rw [Kernel.sectR_apply, h_eq]
    exact StronglyMeasurable.integral_kernel (by fun_prop)
  · simp only [Function.comp_apply]
    filter_upwards with ω using norm_integral_le_integral_norm _

end Learning
