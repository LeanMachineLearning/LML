/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import Mathlib.Analysis.Convex.Integral

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
  if n = 0 then env.ν0 else (env.feedback (n - 1)).sectR (history A Y (n - 1) ω)

/-- The means of the feedback distribution as a function of the action chosen at time `n`. -/
noncomputable def Environment.means (env : Environment 𝓐 𝓨) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (k : 𝓐) (n : ℕ) (ω : Ω) : 𝓨 :=
  (env.measure A Y n ω k)[id]

@[simp]
lemma means_zero (env : Environment 𝓐 𝓨) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (k : 𝓐) (ω : Ω) :
    env.means A Y k 0 ω = (env.ν0 k)[id] := by simp [Environment.means, Environment.measure]

@[simp]
lemma means_of_isObliviousEnv [IsObliviousEnv env] (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (k : 𝓐) (n : ℕ) (ω : Ω) :
    env.means A Y k n ω = (feedbackCondAction env n k)[id] := by
  simp only [Environment.means, Environment.measure, ν0_eq_feedbackCondAction, id_eq,
    feedback_eq_feedbackCondAction]
  split_ifs with hn
  · simp [hn]
  · simp [Nat.sub_add_cancel (by grind : 1 ≤ n)]

lemma means_obliviousEnv (ν : ℕ → Kernel 𝓐 𝓨) [∀ n, IsMarkovKernel (ν n)]
    (k : 𝓐) (n : ℕ) (ω : Ω) :
    (obliviousEnv ν).means A Y k n ω = (ν n k)[id] := by simp

lemma means_stationaryEnv (ν : Kernel 𝓐 𝓨) [IsMarkovKernel ν] (k : 𝓐) (n : ℕ) (ω : Ω) :
    (stationaryEnv ν).means A Y k n ω = (ν k)[id] := by simp

@[fun_prop]
lemma stronglyMeasurable_means [SecondCountableTopology 𝓨] [OpensMeasurableSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) (k : 𝓐) (n : ℕ) :
    StronglyMeasurable (env.means A Y k n) := by
  unfold Environment.means
  have h_eq ω : env.measure A Y n ω k =
      (if n = 0 then env.ν0 ∘ₖ (Kernel.deterministic (fun _ ↦ k) (by fun_prop))
        else (env.feedback (n - 1)) ∘ₖ (Kernel.deterministic (fun ω ↦ (history A Y (n - 1) ω, k))
          ((h.measurable_history (n - 1)).prodMk (by fun_prop)))) ω := by
    split_ifs with hn <;> simp [hn, Environment.measure, Kernel.comp_deterministic_eq_comap]
  simp_rw [h_eq]
  fun_prop

@[fun_prop]
lemma measurable_means [SecondCountableTopology 𝓨] [BorelSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) (k : 𝓐) (n : ℕ) :
    Measurable (env.means A Y k n) :=
  (stronglyMeasurable_means h k n).measurable

lemma IsAlgEnvSeq.adapted_means_filtrationAction [SecondCountableTopology 𝓨] [BorelSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) :
    Adapted h.filtrationAction (fun n ω ↦ env.means A Y (A n ω) n ω) := by
  intro n
  cases n with
  | zero => exact measurable_comp_comap _ stronglyMeasurable_id.integral_kernel.measurable
  | succ n =>
    simp only [Environment.means, Environment.measure, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      ↓reduceIte, Nat.add_one_sub_one, Kernel.sectR_apply, id_eq]
    change Measurable[h.filtrationAction (n + 1)]
      ((fun ω ↦ ∫ x, x ∂(env.feedback n ω)) ∘ (fun ω ↦ (history A Y n ω, A (n + 1) ω)))
    rw [IsAlgEnvSeq.filtrationAction_eq_comap _ _ (by grind)]
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
lemma IsAlgEnvSeq.condExp_feedback_zero_comp {𝓩 : Type*} [NormedAddCommGroup 𝓩] [NormedSpace ℝ 𝓩]
    [CompleteSpace 𝓩] [StandardBorelSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P)
    {g : 𝓨 → 𝓩} (hg : StronglyMeasurable g) (hint : Integrable (fun ω ↦ g (Y 0 ω)) P) :
    P[fun ω ↦ g (Y 0 ω) | h.filtrationAction 0] =ᵐ[P] fun ω ↦ (env.ν0 (A 0 ω))[g] := by
  have hX : Measurable (fun ω ↦ (history A Y 0 ω, A 0 ω)) :=
    (h.measurable_history 0).prodMk (h.measurable_action 0)
  rw [h.filtrationAction_zero_eq_comap]
  exact h.hasCondDistrib_feedback_zero.condExp_comp_eq (h.measurable_action 0) hg hint

omit [NormedSpace ℝ 𝓨] in
lemma IsAlgEnvSeq.condExp_feedback_comp {𝓩 : Type*} [NormedAddCommGroup 𝓩] [NormedSpace ℝ 𝓩]
    [CompleteSpace 𝓩] [StandardBorelSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) (n : ℕ)
    {g : 𝓨 → 𝓩} (hg : StronglyMeasurable g) (hint : Integrable (fun ω ↦ g (Y (n + 1) ω)) P) :
    P[fun ω ↦ g (Y (n + 1) ω) | h.filtrationAction (n + 1)] =ᵐ[P]
      fun ω ↦ (env.feedback n (history A Y n ω, A (n + 1) ω))[g] := by
  have hX : Measurable (fun ω ↦ (history A Y n ω, A (n + 1) ω)) :=
    (h.measurable_history n).prodMk (h.measurable_action (n + 1))
  rw [h.filtrationAction_eq_comap (n + 1) (by simp)]
  exact (h.hasCondDistrib_feedback n).condExp_comp_eq hX hg hint

lemma IsAlgEnvSeq.condExp_feedback [BorelSpace 𝓨] [SecondCountableTopology 𝓨] [CompleteSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) (n : ℕ)
    (hint : Integrable (Y n) P) :
    P[Y n | h.filtrationAction n] =ᵐ[P] fun ω ↦ env.means A Y (A n ω) n ω := by
  cases n with
  | zero => exact condExp_feedback_zero_comp h stronglyMeasurable_id hint
  | succ n => exact condExp_feedback_comp h n stronglyMeasurable_id hint

protected lemma _root_.MeasureTheory.Measure.memLp_comp_iff
    {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [NormedAddCommGroup E]
    {κ : Kernel α β} {μ : Measure α} {f : β → E} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f (κ ∘ₘ μ)) :
    MemLp f p (κ ∘ₘ μ)
      ↔ (∀ᵐ x ∂μ, MemLp f p (κ x)) ∧ Integrable (fun x ↦ ∫ y, ‖f y‖ ^ p.toReal ∂κ x) μ := by
    rw [← integrable_norm_rpow_iff (by fun_prop) hp0 hp_top, Measure.integrable_comp_iff]
    swap; · exact (hf.norm.aemeasurable.pow_const p.toReal).aestronglyMeasurable
    -- todo extract
    unfold AEStronglyMeasurable at hf
    obtain ⟨g, hg, hfg⟩ := hf
    obtain hfg' := Measure.ae_ae_of_ae_comp hfg
    have hf' : ∀ᵐ ω ∂μ, AEStronglyMeasurable f (κ ω) := by
      filter_upwards [hfg'] with ω hω using ⟨g, hg, hω⟩
    --
    congr! 1
    · suffices ∀ᵐ x ∂μ, Integrable (fun x ↦ ‖f x‖ ^ p.toReal) (κ x) ↔ MemLp f p (κ x) by
        refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
          <;> filter_upwards [h, this] with x hx h_iff
        · rwa [h_iff] at hx
        · rwa [← h_iff] at hx
      filter_upwards [hf'] with ω hω
      rw [integrable_norm_rpow_iff hω hp0 hp_top]
    · congr! 4 with y
      simp only [Real.norm_eq_abs, abs_eq_self]
      positivity

/-- **Jensen's inequality** for the convex function `x ↦ ‖x‖ ^ p`, `1 ≤ p`. -/
lemma _root_.MeasureTheory.norm_integral_rpow_le_integral_norm_rpow
    {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → E} {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp_top : p ≠ ∞) (hf : MemLp f p μ) :
    ‖∫ x, f x ∂μ‖ ^ p.toReal ≤ ∫ x, ‖f x‖ ^ p.toReal ∂μ := by
  have hp0 : p ≠ 0 := by positivity
  have hp1' : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp1
  calc ‖∫ x, f x ∂μ‖ ^ p.toReal
  _ ≤ (∫ x, ‖f x‖ ∂μ) ^ p.toReal := by
    gcongr
    exact norm_integral_le_integral_norm _
  _ ≤ ∫ x, ‖f x‖ ^ p.toReal ∂μ :=
    ConvexOn.map_integral_le (convexOn_rpow hp1')
      (Real.continuous_rpow_const (by positivity)).continuousOn isClosed_Ici
      (ae_of_all _ fun x ↦ norm_nonneg _) (hf.integrable hp1).norm
      ((integrable_norm_rpow_iff hf.1 hp0 hp_top).mpr hf)

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
  cases n with
  | zero =>
    simp only [↓reduceIte, id_eq]
    rw [h.hasLaw_feedback_zero_comp.map_eq, Measure.memLp_comp_iff hp0 hp_top (by fun_prop)]
      at hint'
    have hint'' := hint'.2.comp_aemeasurable (by fun_prop)
    have h_eq ω : env.ν0 (A 0 ω) = (env.ν0 ∘ₖ Kernel.deterministic (A 0) (by fun_prop)) ω := by
      simp [Kernel.comp_deterministic_eq_comap]
    rw [← integrable_norm_rpow_iff _ hp0 hp_top]
    swap
    · refine StronglyMeasurable.aestronglyMeasurable ?_
      simp_rw [h_eq]
      exact StronglyMeasurable.integral_kernel (by fun_prop)
    simp only [id_eq] at hint''
    refine Integrable.mono' hint'' ?_ ?_
    · refine ((AEMeasurable.norm ?_).pow_const _).aestronglyMeasurable
      refine (StronglyMeasurable.measurable ?_).aemeasurable
      simp_rw [h_eq]
      exact StronglyMeasurable.integral_kernel (by fun_prop)
    · simp only [Real.norm_eq_abs, Function.comp_apply]
      filter_upwards [ae_of_ae_map (hA 0).aemeasurable hint'.1] with ω hω
      rw [abs_of_nonneg (by positivity)]
      exact norm_integral_rpow_le_integral_norm_rpow hp1 hp_top hω
  | succ n =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_one_sub_one, id_eq]
    rw [(h.hasLaw_feedback_comp n).map_eq, Measure.memLp_comp_iff hp0 hp_top (by fun_prop)] at hint'
    have hint'' := hint'.2.comp_aemeasurable (by fun_prop)
    have h_eq ω : (env.feedback n) (history A Y n ω, A (n + 1) ω) =
        (env.feedback n ∘ₖ
          Kernel.deterministic (fun ω ↦ (history A Y n ω, A (n + 1) ω)) (by fun_prop)) ω := by
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
      filter_upwards [ae_of_ae_map ((h_hist n).prodMk (hA (n + 1))).aemeasurable hint'.1]
        with ω hω
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
  cases n with
  | zero =>
    simp only [↓reduceIte, id_eq]
    rw [h.hasLaw_feedback_zero_comp.map_eq, Measure.integrable_comp_iff (by fun_prop)] at hint'
    have hint'' := hint'.2.comp_aemeasurable (by fun_prop)
    simp only [id_eq] at hint''
    refine Integrable.mono' hint'' ?_ ?_
    · refine StronglyMeasurable.aestronglyMeasurable ?_
      have h_eq ω : env.ν0 (A 0 ω) =
          (env.ν0 ∘ₖ Kernel.deterministic (A 0) (by fun_prop)) ω := by
        simp [Kernel.comp_deterministic_eq_comap]
      simp_rw [h_eq]
      exact StronglyMeasurable.integral_kernel (by fun_prop)
    · simp only [Function.comp_apply]
      filter_upwards with ω using norm_integral_le_integral_norm _
  | succ n =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_one_sub_one, id_eq]
    rw [(h.hasLaw_feedback_comp n).map_eq, Measure.integrable_comp_iff (by fun_prop)] at hint'
    have hint'' := hint'.2.comp_aemeasurable (by fun_prop)
    simp only [id_eq] at hint''
    refine Integrable.mono' hint'' ?_ ?_
    · refine StronglyMeasurable.aestronglyMeasurable ?_
      have h_eq ω : (env.feedback n) (history A Y n ω, A (n + 1) ω) =
          (env.feedback n ∘ₖ
            Kernel.deterministic (fun ω ↦ (history A Y n ω, A (n + 1) ω)) (by fun_prop)) ω := by
        simp [Kernel.comp_deterministic_eq_comap]
      simp_rw [Kernel.sectR_apply, h_eq]
      exact StronglyMeasurable.integral_kernel (by fun_prop)
    · simp only [Function.comp_apply]
      filter_upwards with ω using norm_integral_le_integral_norm _

end Learning
