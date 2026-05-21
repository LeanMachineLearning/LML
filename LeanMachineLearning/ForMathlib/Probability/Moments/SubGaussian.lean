/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

open MeasureTheory Real
open scoped ENNReal NNReal

namespace ProbabilityTheory

namespace HasCondSubgaussianMGF

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}

lemma ae_trim_condExp_exp_sub_le_one (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) :
    ∀ᵐ ω' ∂(μ.trim hm), (μ[fun ω ↦ exp (t * X ω - c * t ^ 2 / 2)|m]) ω' ≤ 1 := by
  have h_le : ∀ᵐ ω' ∂(μ.trim hm), μ[fun ω ↦ exp (t * X ω)|m] ω' ≤ exp (c * t ^ 2 / 2) :=
    h.ae_trim_condExp_le t
  have h_eq : μ[fun ω ↦ exp (t * X ω) / exp (c * t ^ 2 / 2)|m] =ᵐ[μ.trim hm]
      fun ω ↦ μ[fun ω ↦ exp (t * X ω)|m] ω / exp (c * t ^ 2 / 2) := by
    refine ae_eq_trim_of_measurable _ ?_ ?_ ?_
    · exact stronglyMeasurable_condExp.measurable
    · refine Measurable.div_const ?_ _
      exact stronglyMeasurable_condExp.measurable
    simp_rw [div_eq_inv_mul]
    refine condExp_mul_of_stronglyMeasurable_left ?_ ?_ ?_
    · fun_prop
    · refine Integrable.const_mul ?_ _
      exact h.integrable_exp_mul _
    · exact h.integrable_exp_mul _
  filter_upwards [h_le, h_eq] with ω hω_le hω_eq
  simp_rw [exp_sub, hω_eq]
  rwa [div_le_one (by positivity)]

lemma ae_condExp_exp_sub_le_one (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) :
    ∀ᵐ ω' ∂μ, (μ[fun ω ↦ exp (t * X ω - c * t ^ 2 / 2)|m]) ω' ≤ 1 :=
  ae_of_ae_trim hm (h.ae_trim_condExp_exp_sub_le_one t)

lemma memLp_exp_mul_sub (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) (p : ℝ≥0) :
    MemLp (fun ω ↦ exp (t * X ω - c * t ^ 2 / 2)) p μ := by
  have h_lp := h.memLp_exp_mul t p
  simp_rw [sub_eq_add_neg, exp_add]
  exact h_lp.mul_const _

lemma integrable_exp_mul_sub (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * X ω - c * t ^ 2 / 2)) μ := by
  have h_int := h.integrable_exp_mul t
  simp_rw [exp_sub]
  exact h_int.div_const _

end HasCondSubgaussianMGF

namespace HasSubgaussianMGF

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y : Ω → ℝ} {c cX cY : ℝ≥0}

/-- Chernoff bound on the left tail of a sub-Gaussian random variable. -/
lemma measure_le_le (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | X ω ≤ -ε} ≤ exp (-ε ^ 2 / (2 * c)) := by
  simp_rw [le_neg (b := ε), ← Pi.neg_apply]
  exact h.neg.measure_ge_le hε

/-- **Hoeffding inequality** for sub-Gaussian random variables. -/
lemma measure_sum_le_le_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {c : ι → ℝ≥0}
    {s : Finset ι} (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ -ε} ≤ exp (-ε ^ 2 / (2 * ∑ i ∈ s, c i)) := by
  simp_rw [le_neg (b := ε), ← Finset.sum_neg_distrib, ← Pi.neg_apply (f := X _),
    ← Pi.neg_apply (f := X)]
  refine measure_sum_ge_le_of_iIndepFun (X := -X) (μ := μ) ?_ ?_ hε
  · exact h_indep.comp _ (fun _ ↦ measurable_neg)
  · exact fun i hi ↦ (h_subG i hi).neg

/-- **Hoeffding inequality** for sub-Gaussian random variables. -/
lemma measure_sum_range_le_le_of_iIndepFun {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ℝ≥0}
    {n : ℕ} (h_subG : ∀ i < n, HasSubgaussianMGF (X i) c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∑ i ∈ Finset.range n, X i ω ≤ -ε} ≤ exp (-ε ^ 2 / (2 * n * c)) := by
  simp_rw [le_neg (b := ε), ← Finset.sum_neg_distrib, ← Pi.neg_apply (f := X _),
    ← Pi.neg_apply (f := X)]
  refine measure_sum_range_ge_le_of_iIndepFun (X := -X) (μ := μ) ?_ ?_ hε
  · exact h_indep.comp _ (fun _ ↦ measurable_neg)
  · exact fun i hi ↦ (h_subG i hi).neg

section Sum

variable {ι ι' : Type*} {X : ι → Ω → ℝ} {cX : ι → ℝ≥0} {s : Finset ι}
  {Y : ι' → Ω → ℝ} {cY : ι' → ℝ≥0} {t : Finset ι'}

lemma measure_sum_le_sum_le [IsFiniteMeasure μ]
    (hX_indep : iIndepFun X μ) (hY_indep : iIndepFun Y μ)
    (hX_subG : ∀ i ∈ s, HasSubgaussianMGF (fun ω ↦ X i ω - μ[X i]) (cX i) μ)
    (hY_subG : ∀ j ∈ t, HasSubgaussianMGF (fun ω ↦ Y j ω - μ[Y j]) (cY j) μ)
    (h_indep_sum : IndepFun (fun ω ↦ ∑ i ∈ s, X i ω) (fun ω ↦ ∑ j ∈ t, Y j ω) μ)
    (h_le : ∑ j ∈ t, μ[Y j] ≤ ∑ i ∈ s, μ[X i]) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ ∑ j ∈ t, Y j ω}
      ≤ exp (- (∑ j ∈ t, μ[Y j] - ∑ i ∈ s, μ[X i]) ^ 2
        / (2 * (∑ i ∈ s, cX i + ∑ j ∈ t, cY j))) := by
  have hX_int i (his : i ∈ s) : Integrable (X i) μ := by
    have h_int := (hX_subG i his).integrable
    simp_rw [sub_eq_add_neg, integrable_add_const_iff] at h_int
    exact h_int
  have hY_int j (his : j ∈ t) : Integrable (Y j) μ := by
    have h_int := (hY_subG j his).integrable
    simp_rw [sub_eq_add_neg, integrable_add_const_iff] at h_int
    exact h_int
  refine (measureReal_le_le_exp
    (cX := ∑ i ∈ s, cX i) (cY := ∑ j ∈ t, cY j) ?_ ?_ h_indep_sum ?_).trans_eq ?_
  · suffices HasSubgaussianMGF (fun ω ↦ ∑ i ∈ s, (X i ω - μ[X i])) (∑ i ∈ s, cX i) μ by
      convert this
      rw [integral_finset_sum _ hX_int, Finset.sum_sub_distrib]
    refine sum_of_iIndepFun ?_ hX_subG
    exact hX_indep.comp (g := fun i x ↦ x - μ[X i]) (by fun_prop)
  · suffices HasSubgaussianMGF (fun ω ↦ ∑ j ∈ t, (Y j ω - μ[Y j])) (∑ j ∈ t, cY j) μ by
      convert this
      rw [integral_finset_sum _ hY_int, Finset.sum_sub_distrib]
    refine sum_of_iIndepFun ?_ hY_subG
    exact hY_indep.comp (g := fun i x ↦ x - μ[Y i]) (by fun_prop)
  · rwa [integral_finset_sum _ hX_int, integral_finset_sum _ hY_int]
  · congr
    · rw [integral_finset_sum _ hY_int]
    · rw [integral_finset_sum _ hX_int]

lemma measure_sum_le_sum_le' [IsFiniteMeasure μ]
    (hX_indep : iIndepFun X μ) (hY_indep : iIndepFun Y μ)
    (hX_subG : ∀ i ∈ s, HasSubgaussianMGF (fun ω ↦ X i ω - μ[X i]) (cX i) μ)
    (hY_subG : ∀ j ∈ t, HasSubgaussianMGF (fun ω ↦ Y j ω - μ[Y j]) (cY j) μ)
    (h_indep_sum : IndepFun (fun ω ↦ (X · ω)) (fun ω ↦ (Y · ω)) μ)
    (h_le : ∑ j ∈ t, μ[Y j] ≤ ∑ i ∈ s, μ[X i]) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ ∑ j ∈ t, Y j ω}
      ≤ Real.exp (- (∑ j ∈ t, μ[Y j] - ∑ i ∈ s, μ[X i]) ^ 2
        / (2 * (∑ i ∈ s, cX i + ∑ j ∈ t, cY j))) := by
  refine measure_sum_le_sum_le hX_indep hY_indep hX_subG hY_subG ?_ h_le
  exact h_indep_sum.comp (φ := fun p ↦ ∑ i ∈ s, p i) (ψ := fun p ↦ ∑ j ∈ t, p j)
    (by fun_prop) (by fun_prop)

end Sum

end HasSubgaussianMGF

end ProbabilityTheory
