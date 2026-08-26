/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import LeanMachineLearning.ForMathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The means of the feedback distribution

## Main definitions

* `Environment.means`

## Main results

*
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω β 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β}
  {m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace 𝓨] [Nonempty 𝓨]
  {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → β} {Y : Ω → 𝓨}
  {κ : Kernel β 𝓨} [IsFiniteKernel κ]

lemma HasCondDistrib.condExp_comp_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (h : HasCondDistrib Y X κ P) (hX : Measurable X)
    {g : 𝓨 → F} (hg : StronglyMeasurable g) (hint : Integrable (fun ω ↦ g (Y ω)) P) :
    P[fun ω ↦ g (Y ω) | mβ.comap X] =ᵐ[P] fun ω ↦ ∫ y, g y ∂(κ (X ω)) := by
  refine (condExp_ae_eq_integral_condDistrib hX h.aemeasurable_snd hg hint).trans ?_
  filter_upwards [ae_of_ae_map hX.aemeasurable h.condDistrib_eq] with ω hω
  rw [hω]

end ProbabilityTheory

namespace Learning

variable {Ω 𝓐 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  [NormedAddCommGroup 𝓨] [NormedSpace ℝ 𝓨]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {P : Measure Ω} [IsFiniteMeasure P]
  {alg : Algorithm 𝓐 𝓨} {env : Environment 𝓐 𝓨}

/-- The kernel that gives the measure of the feedback distribution as a function of the action
chosen at time `n`. -/
noncomputable def Environment.measure (env : Environment 𝓐 𝓨) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (n : ℕ) (ω : Ω) : Kernel 𝓐 𝓨 :=
  (env.feedback n).sectR (history A Y n ω)

/-- The means of the feedback distribution as a function of the action chosen at time `n`. -/
noncomputable def Environment.means (env : Environment 𝓐 𝓨) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (k : 𝓐) (n : ℕ) (ω : Ω) : 𝓨 :=
  (env.measure A Y n ω k)[id]

@[simp]
lemma means_zero (env : Environment 𝓐 𝓨) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (k : 𝓐) (ω : Ω) :
    env.means A Y k 0 ω = (env.ν0 k)[id] := by
  simp [Environment.means, Environment.measure, Environment.feedback_zero]

@[simp]
lemma means_of_isObliviousEnv [IsObliviousEnv env] (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (k : 𝓐) (n : ℕ) (ω : Ω) :
    env.means A Y k n ω = (feedbackCondAction env n k)[id] := by
  simp [Environment.means, Environment.measure, feedback_eq_feedbackCondAction]

lemma means_obliviousEnv (ν : ℕ → Kernel 𝓐 𝓨) [∀ n, IsMarkovKernel (ν n)]
    (k : 𝓐) (n : ℕ) (ω : Ω) :
    (obliviousEnv ν).means A Y k n ω = (ν n k)[id] := by simp

lemma means_stationaryEnv (ν : Kernel 𝓐 𝓨) [IsMarkovKernel ν] (k : 𝓐) (n : ℕ) (ω : Ω) :
    (stationaryEnv ν).means A Y k n ω = (ν k)[id] := by simp

@[fun_prop]
lemma IsAlgEnvSeq.stronglyMeasurable_means [SecondCountableTopology 𝓨] [OpensMeasurableSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) (k : 𝓐) (n : ℕ) :
    StronglyMeasurable (env.means A Y k n) := by
  unfold Environment.means
  have h_eq ω : env.measure A Y n ω k =
      (env.feedback n ∘ₖ Kernel.deterministic (fun ω ↦ (history A Y n ω, k))
        ((h.measurable_history n).prodMk (by fun_prop))) ω := by
    simp [Environment.measure, Kernel.comp_deterministic_eq_comap]
  simp_rw [h_eq]
  fun_prop

@[fun_prop]
lemma IsAlgEnvSeq.measurable_means [SecondCountableTopology 𝓨] [BorelSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) (k : 𝓐) (n : ℕ) :
    Measurable (env.means A Y k n) :=
  (h.stronglyMeasurable_means k n).measurable

lemma IsAlgEnvSeq.adapted_means_filtrationAction [SecondCountableTopology 𝓨] [BorelSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) :
    Adapted h.filtrationAction (fun n ω ↦ env.means A Y (A n ω) n ω) := by
  intro n
  simp only [Environment.means, Environment.measure, Kernel.sectR_apply, id_eq]
  change Measurable[h.filtrationAction n]
    ((fun ω ↦ ∫ x, x ∂(env.feedback n ω)) ∘ (fun ω ↦ (history A Y n ω, A n ω)))
  rw [IsAlgEnvSeq.filtrationAction_eq_comap]
  exact measurable_comp_comap _ stronglyMeasurable_id.integral_kernel.measurable

lemma IsAlgEnvSeq.stronglyAdapted_means_filtrationAction [SecondCountableTopology 𝓨] [BorelSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) :
    StronglyAdapted h.filtrationAction (fun n ω ↦ env.means A Y (A n ω) n ω) :=
  (h.adapted_means_filtrationAction).stronglyAdapted

lemma IsAlgEnvSeq.adapted_means [SecondCountableTopology 𝓨] [BorelSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) :
    Adapted h.filtration (fun n ω ↦ env.means A Y (A n ω) n ω) :=
  fun n ↦ (h.adapted_means_filtrationAction n).mono (h.filtrationAction_le_filtration n) le_rfl

omit [NormedSpace ℝ 𝓨] in
lemma IsAlgEnvSeq.condExp_feedback_comp {𝓩 : Type*} [NormedAddCommGroup 𝓩] [NormedSpace ℝ 𝓩]
    [CompleteSpace 𝓩] [StandardBorelSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) (n : ℕ)
    {g : 𝓨 → 𝓩} (hg : StronglyMeasurable g) (hint : Integrable (fun ω ↦ g (Y n ω)) P) :
    P[fun ω ↦ g (Y n ω) | h.filtrationAction n] =ᵐ[P]
      fun ω ↦ (env.feedback n (history A Y n ω, A n ω))[g] := by
  have hX : Measurable (fun ω ↦ (history A Y n ω, A n ω)) :=
    (h.measurable_history n).prodMk (h.measurable_action n)
  rw [h.filtrationAction_eq_comap n]
  exact (h.hasCondDistrib_feedback n).condExp_comp_eq hX hg hint

lemma IsAlgEnvSeq.condExp_feedback [BorelSpace 𝓨] [SecondCountableTopology 𝓨] [CompleteSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) (n : ℕ)
    (hint : Integrable (Y n) P) :
    P[Y n | h.filtrationAction n] =ᵐ[P] fun ω ↦ env.means A Y (A n ω) n ω :=
  condExp_feedback_comp h n stronglyMeasurable_id hint

lemma IsAlgEnvSeq.memLp_means_action [SecondCountableTopology 𝓨] [BorelSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) {n : ℕ} {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ∞)
    (hint : MemLp (Y n) p P) :
    MemLp (fun ω ↦ env.means A Y (A n ω) n ω) p P := by
  have hp0 : p ≠ 0 := by positivity
  have hA := h.measurable_action
  have h_hist := h.measurable_history
  have hint' : MemLp id p (P.map (Y n)) := by
    rwa [memLp_map_measure_iff (by fun_prop) (h.measurable_feedback _).aemeasurable]
  unfold Environment.means Environment.measure
  simp only [id_eq]
  rw [(h.hasLaw_feedback_comp n).map_eq, Measure.memLp_comp_iff hp0 hp_top (by fun_prop)] at hint'
  have hint'' := hint'.2.comp_aemeasurable (by fun_prop)
  have h_eq ω : (env.feedback n) (history A Y n ω, A n ω) =
      (env.feedback n ∘ₖ
        Kernel.deterministic (fun ω ↦ (history A Y n ω, A n ω)) (by fun_prop)) ω := by
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
    filter_upwards [ae_of_ae_map ((h_hist n).prodMk (hA n)).aemeasurable hint'.1] with ω hω
    rw [abs_of_nonneg (by positivity)]
    exact norm_integral_rpow_le_integral_norm_rpow hp1 hp_top hω

lemma IsAlgEnvSeq.integrable_means_action [SecondCountableTopology 𝓨] [OpensMeasurableSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) {n : ℕ} (hint : Integrable (Y n) P) :
    Integrable (fun ω ↦ env.means A Y (A n ω) n ω) P := by
  have hA := h.measurable_action
  have h_hist := h.measurable_history
  have hint' : Integrable id (P.map (Y n)) := by
    rwa [integrable_map_measure (by fun_prop) (h.measurable_feedback _).aemeasurable]
  unfold Environment.means Environment.measure
  simp only [id_eq]
  rw [(h.hasLaw_feedback_comp n).map_eq, Measure.integrable_comp_iff (by fun_prop)] at hint'
  have hint'' := hint'.2.comp_aemeasurable (by fun_prop)
  simp only [id_eq] at hint''
  refine Integrable.mono' hint'' ?_ ?_
  · refine StronglyMeasurable.aestronglyMeasurable ?_
    have h_eq ω : (env.feedback n) (history A Y n ω, A n ω) =
        (env.feedback n ∘ₖ
          Kernel.deterministic (fun ω ↦ (history A Y n ω, A n ω)) (by fun_prop)) ω := by
      simp [Kernel.comp_deterministic_eq_comap]
    simp_rw [Kernel.sectR_apply, h_eq]
    exact StronglyMeasurable.integral_kernel (by fun_prop)
  · simp only [Function.comp_apply]
    filter_upwards with ω using norm_integral_le_integral_norm _

end Learning
