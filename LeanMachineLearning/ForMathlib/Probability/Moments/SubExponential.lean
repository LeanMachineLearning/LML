/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Moments.MGFAnalytic

import Mathlib.Analysis.Convex.Integral

/-!
# Sub-exponential random variables

A real random variable `X` has a sub-exponential moment generating function (mgf) with parameters
`(V, b)` if for every `t` with `b * |t| ≤ 1`, `exp (t * X)` is integrable and
`mgf X μ t ≤ exp (V * t ^ 2 / 2)`. The range of `t` is written as `b * |t| ≤ 1` (rather than
`|t| ≤ 1 / b`) so that `b = 0` imposes no restriction on `t`: the case `b = 0` is exactly
`HasSubgaussianMGF` (see `Mathlib/Probability/Moments/SubGaussian.lean`, whose structure
this file follows).

As for sub-Gaussian variables, the notion is first defined with respect to a kernel and a
measure (`Kernel.HasSubexponentialMGF`), then specialized to conditionally sub-exponential
variables (`HasCondSubexponentialMGF`, the kernel being the conditional expectation kernel of a
sub-σ-algebra) and to sub-exponential variables with respect to a measure
(`HasSubexponentialMGF`, a constant kernel).

## Main definitions

* `Kernel.HasSubexponentialMGF X V b κ ν`: for every `t` with `b * |t| ≤ 1`, `exp (t * X)` is
  integrable with respect to `κ ∘ₘ ν` and, for `ν`-almost every `ω'`,
  `mgf X (κ ω') t ≤ exp (V * t ^ 2 / 2)`.
* `HasCondSubexponentialMGF m hm X V b μ`: `Kernel.HasSubexponentialMGF` with respect to the
  conditional expectation kernel `condExpKernel μ m` and the measure `μ.trim hm`.
* `HasSubexponentialMGF X V b μ`: for every `t` with `b * |t| ≤ 1`, `exp (t * X)` is
  `μ`-integrable and `mgf X μ t ≤ exp (V * t ^ 2 / 2)`. This is equivalent to
  `Kernel.HasSubexponentialMGF` with a constant kernel (`hasSubexponentialMGF_iff_kernel`).

## Main results

* `HasSubexponentialMGF.integral_eq_zero`: a sub-exponential variable is integrable and centered.
* `HasSubexponentialMGF.const_mul`, `neg`, `mono`, `add`, `add_of_indepFun`, `sum_of_iIndepFun`:
  stability under scaling, sums, and independent sums.
* `HasSubexponentialMGF.measure_ge_le`, `measure_le_le`, `measure_abs_ge_le`: Bernstein-type
  tail bounds `exp (-min (t ^ 2 / (2 * V)) (t / (2 * b)))`.
* `HasSubexponentialMGF.measure_sum_ge_le_of_iIndepFun`, `measure_abs_average_ge_le`:
  Bernstein's inequality for sums and averages of independent sub-exponential variables.
* `hasSubexponentialMGF_of_abs_le_of_integral_eq_zero`: a centered variable bounded by `M` with
  second moment at most `v` has parameters `(3 * v / 2, M)`.
* `HasSubexponentialMGF.sum_of_hasCondSubexponentialMGF` and
  `measure_sum_ge_le_of_hasCondSubexponentialMGF`: a sum of conditionally sub-exponential
  martingale differences is sub-exponential, and the corresponding Azuma–Bernstein inequality.

## Implementation notes

The parameters `V` and `b` are real numbers rather than `ℝ≥0`, which avoids coercions in the
arithmetic of the applications. The Bernstein-type tail bounds do not assume `0 < V` or `0 < b`:
when `V ≤ 0` or `b ≤ 0`, the right-hand side `exp (-min (t ^ 2 / (2 * V)) (t / (2 * b)))` is at
least `1` (with the convention `x / 0 = 0`) and the bound holds trivially.
As in `Kernel.HasSubgaussianMGF`, the integrability condition of the kernel version is
integrability with respect to `κ ∘ₘ ν`, not almost-everywhere integrability with respect to
`κ ω'`.
-/

@[expose] public section

open MeasureTheory Real Finset
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

section Kernel

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω → ℝ} {V b : ℝ}

/-! ### Sub-exponential with respect to a kernel and a measure -/

/-- A random variable `X` has a sub-exponential moment-generating function with parameters
`(V, b)` with respect to a kernel `κ` and a measure `ν` if for every `t` with `b * |t| ≤ 1`,
`exp (t * X)` is integrable with respect to `κ ∘ₘ ν` and, for `ν`-almost all `ω'`,
the moment-generating function of `X` with respect to `κ ω'` is bounded by `exp (V * t ^ 2 / 2)`.
For `b = 0` this is `Kernel.HasSubgaussianMGF X V κ ν`. -/
structure Kernel.HasSubexponentialMGF (X : Ω → ℝ) (V b : ℝ)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t, b * |t| ≤ 1 → Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν)
  mgf_le : ∀ᵐ ω' ∂ν, ∀ t, b * |t| ≤ 1 → mgf X (κ ω') t ≤ exp (V * t ^ 2 / 2)

namespace Kernel.HasSubexponentialMGF

section BasicProperties

lemma aestronglyMeasurable (h : HasSubexponentialMGF X V b κ ν) :
    AEStronglyMeasurable X (κ ∘ₘ ν) := by
  have h_int := h.integrable_exp_mul (|b| + 1)⁻¹ (by
    rw [abs_of_pos (by positivity), mul_inv_le_iff₀ (by positivity), one_mul]
    linarith [le_abs_self b])
  exact (aemeasurable_of_aemeasurable_exp_mul (by positivity)
    h_int.1.aemeasurable).aestronglyMeasurable

lemma ae_integrable_exp_mul (h : HasSubexponentialMGF X V b κ ν) {t : ℝ} (ht : b * |t| ≤ 1) :
    ∀ᵐ ω' ∂ν, Integrable (fun y ↦ exp (t * X y)) (κ ω') :=
  Measure.ae_integrable_of_integrable_comp (h.integrable_exp_mul t ht)

lemma ae_aestronglyMeasurable (h : HasSubexponentialMGF X V b κ ν) :
    ∀ᵐ ω' ∂ν, AEStronglyMeasurable X (κ ω') := by
  filter_upwards [h.ae_integrable_exp_mul (t := (|b| + 1)⁻¹) (by
    rw [abs_of_pos (by positivity), mul_inv_le_iff₀ (by positivity), one_mul]
    linarith [le_abs_self b])] with ω h_int
  exact (aemeasurable_of_aemeasurable_exp_mul (by positivity)
    h_int.1.aemeasurable).aestronglyMeasurable

/-- Auxiliary lemma: almost-everywhere integrability of `exp (t * X)` with respect to `κ ω'`,
simultaneously for all admissible `t`, from the integrability with respect to `κ ∘ₘ ν`. -/
lemma ae_forall_integrable_exp_mul_of_forall
    (h_int : ∀ t : ℝ, b * |t| ≤ 1 → Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν)) :
    ∀ᵐ ω' ∂ν, ∀ t, b * |t| ≤ 1 → Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
  rcases le_or_gt b 0 with hb | hb
  · have h (n : ℤ) : ∀ᵐ ω' ∂ν, Integrable (fun ω ↦ exp (n * X ω)) (κ ω') :=
      Measure.ae_integrable_of_integrable_comp (h_int n (by nlinarith [abs_nonneg (n : ℝ)]))
    rw [← ae_all_iff] at h
    filter_upwards [h] with ω' h t _
    exact integrable_exp_mul_of_le_of_le (h _) (h _) (Int.floor_le t) (Int.le_ceil t)
  · have hb1 : b * |1 / b| ≤ 1 := by rw [abs_of_pos (by positivity), mul_one_div_cancel hb.ne']
    have hb2 : b * |-(1 / b)| ≤ 1 := by rwa [abs_neg]
    filter_upwards [Measure.ae_integrable_of_integrable_comp (h_int _ hb1),
      Measure.ae_integrable_of_integrable_comp (h_int _ hb2)] with ω' h1 h2 t ht
    rw [mul_comm, ← le_div_iff₀ hb, abs_le] at ht
    exact integrable_exp_mul_of_le_of_le h2 h1 ht.1 ht.2

lemma ae_forall_integrable_exp_mul (h : HasSubexponentialMGF X V b κ ν) :
    ∀ᵐ ω' ∂ν, ∀ t, b * |t| ≤ 1 → Integrable (fun ω ↦ exp (t * X ω)) (κ ω') :=
  ae_forall_integrable_exp_mul_of_forall h.integrable_exp_mul

lemma ae_forall_memLp_exp_mul (h : HasSubexponentialMGF X V b κ ν) (p : ℝ≥0) :
    ∀ᵐ ω' ∂ν, ∀ t : ℝ, b * |(p : ℝ) * t| ≤ 1 → MemLp (fun ω ↦ exp (t * X ω)) p (κ ω') := by
  filter_upwards [h.ae_forall_integrable_exp_mul, h.ae_aestronglyMeasurable] with ω' hi hm t ht
  refine ⟨continuous_exp.comp_aestronglyMeasurable (hm.const_mul t), ?_⟩
  by_cases hp : p = 0
  · simp [hp]
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp) (by simp),
    ENNReal.coe_toReal]
  have hf := (hi (p * t) ht).lintegral_lt_top
  convert! hf using 3 with ω
  rw [enorm_eq_ofReal (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity),
    ← exp_mul, mul_comm, ← mul_assoc]
  positivity

lemma memLp_exp_mul (h : HasSubexponentialMGF X V b κ ν) {t : ℝ} (p : ℝ≥0)
    (ht : b * |(p : ℝ) * t| ≤ 1) :
    MemLp (fun ω ↦ exp (t * X ω)) p (κ ∘ₘ ν) := by
  refine ⟨continuous_exp.comp_aestronglyMeasurable (h.aestronglyMeasurable.const_mul t), ?_⟩
  by_cases hp0 : p = 0
  · simp [hp0]
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp0) (by simp)]
  simp only [ENNReal.coe_toReal]
  have h' := (h.integrable_exp_mul (p * t) ht).2
  rw [hasFiniteIntegral_def] at h'
  convert! h' using 3 with ω
  rw [enorm_eq_ofReal (by positivity), enorm_eq_ofReal (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity), ← exp_mul, mul_comm, ← mul_assoc]
  positivity

lemma cgf_le (h : HasSubexponentialMGF X V b κ ν) (hV : 0 ≤ V) :
    ∀ᵐ ω' ∂ν, ∀ t, b * |t| ≤ 1 → cgf X (κ ω') t ≤ V * t ^ 2 / 2 := by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul] with ω' h h_int t ht
  calc cgf X (κ ω') t
  _ = log (mgf X (κ ω') t) := rfl
  _ ≤ log (exp (V * t ^ 2 / 2)) := by
    by_cases h0 : κ ω' = 0
    · simpa [h0] using by positivity
    gcongr
    · exact mgf_pos' h0 (h_int t ht)
    · exact h t ht
  _ ≤ V * t ^ 2 / 2 := by rw [log_exp]

lemma isFiniteMeasure (h : HasSubexponentialMGF X V b κ ν) :
    ∀ᵐ ω' ∂ν, IsFiniteMeasure (κ ω') := by
  filter_upwards [h.ae_integrable_exp_mul (t := 0) (by simp)] with ω' h
  simpa [integrable_const_iff] using h

lemma measure_univ_le_one (h : HasSubexponentialMGF X V b κ ν) :
    ∀ᵐ ω' ∂ν, κ ω' Set.univ ≤ 1 := by
  filter_upwards [h.isFiniteMeasure, h.mgf_le] with ω' h h_mgf
  suffices (κ ω').real Set.univ ≤ 1 by
    rwa [← ENNReal.ofReal_one, ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) zero_le_one]
  simpa [mgf] using h_mgf 0 (by simp)

lemma measure_le_one (h : HasSubexponentialMGF X V b κ ν) (s : Set Ω) :
    ∀ᵐ ω' ∂ν, κ ω' s ≤ 1 := by
  filter_upwards [h.measure_univ_le_one] with ω' h using (measure_mono (Set.subset_univ _)).trans h

lemma measureReal_le_one (h : HasSubexponentialMGF X V b κ ν) (s : Set Ω) :
    ∀ᵐ ω' ∂ν, (κ ω').real s ≤ 1 := by
  filter_upwards [h.measure_le_one s] with ω' h
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rwa [ENNReal.ofReal_one]

end BasicProperties

/-- To prove that `X` is sub-exponential with respect to `κ` and `ν`, it suffices to check the
bound on the mgf for each admissible `t` separately, almost everywhere. -/
protected lemma of_ae_mgf_le
    (h_int : ∀ t : ℝ, b * |t| ≤ 1 → Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν))
    (h_mgf : ∀ t : ℝ, b * |t| ≤ 1 → ∀ᵐ ω' ∂ν, mgf X (κ ω') t ≤ exp (V * t ^ 2 / 2)) :
    Kernel.HasSubexponentialMGF X V b κ ν where
  integrable_exp_mul := h_int
  mgf_le := by
    have h_rat : ∀ᵐ ω' ∂ν, ∀ q : ℚ, b * |(q : ℝ)| ≤ 1 →
        mgf X (κ ω') q ≤ exp (V * (q : ℝ) ^ 2 / 2) := by
      rw [ae_all_iff]
      intro q
      by_cases hq : b * |(q : ℝ)| ≤ 1
      · filter_upwards [h_mgf q hq] with ω' h _ using h
      · exact ae_of_all _ fun _ h ↦ absurd h hq
    have h_end : ∀ᵐ ω' ∂ν, ∀ t, b * |t| = 1 → mgf X (κ ω') t ≤ exp (V * t ^ 2 / 2) := by
      rcases le_or_gt b 0 with hb | hb
      · refine ae_of_all _ fun _ t ht ↦ absurd ht ?_
        nlinarith [abs_nonneg t]
      · have hb1 : b * |1 / b| ≤ 1 := by
          rw [abs_of_pos (by positivity), mul_one_div_cancel hb.ne']
        have hb2 : b * |-(1 / b)| ≤ 1 := by rwa [abs_neg]
        filter_upwards [h_mgf _ hb1, h_mgf _ hb2] with ω' h1 h2 t ht
        have ht' : |t| = 1 / b := by rw [eq_div_iff hb.ne', mul_comm]; exact ht
        rcases (abs_eq (by positivity : (0 : ℝ) ≤ 1 / b)).1 ht' with rfl | rfl
        · exact h1
        · exact h2
    filter_upwards [ae_forall_integrable_exp_mul_of_forall h_int, h_rat, h_end]
      with ω' h_int h_rat h_end t ht
    rcases ht.lt_or_eq with ht | ht
    · have hU : IsOpen {s : ℝ | b * |s| < 1} := isOpen_lt (by fun_prop) continuous_const
      have hsub : {s : ℝ | b * |s| < 1} ⊆ interior (integrableExpSet X (κ ω')) :=
        hU.subset_interior_iff.2 fun s hs ↦ h_int s hs.le
      refine ContinuousWithinAt.closure_le (f := mgf X (κ ω'))
        (g := fun s ↦ exp (V * s ^ 2 / 2))
        (s := {s : ℝ | b * |s| < 1} ∩ Set.range ((↑) : ℚ → ℝ))
        (Dense.open_subset_closure_inter Rat.denseRange_cast hU ht) ?_ ?_ ?_
      · exact (continuousOn_mgf.continuousAt
          (isOpen_interior.mem_nhds (hsub ht))).continuousWithinAt
      · exact (by fun_prop : Continuous fun s : ℝ ↦ exp (V * s ^ 2 / 2)).continuousAt
          |>.continuousWithinAt
      · rintro _ ⟨hs, q, rfl⟩
        exact h_rat q hs.le
    · exact h_end t ht

@[simp]
lemma fun_zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] :
    HasSubexponentialMGF (fun _ ↦ 0) 0 b κ ν where
  integrable_exp_mul := by simp
  mgf_le := by simp

@[simp]
lemma zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] : HasSubexponentialMGF 0 0 b κ ν :=
  fun_zero

@[simp]
lemma zero_kernel : HasSubexponentialMGF X V b (0 : Kernel Ω' Ω) ν := by
  constructor
  · simp [FunLike.coe_zero]
  · simp [exp_nonneg]

@[simp]
lemma zero_measure : HasSubexponentialMGF X V b κ (0 : Measure Ω') := ⟨by simp, by simp⟩

@[to_fun]
lemma neg (h : HasSubexponentialMGF X V b κ ν) : HasSubexponentialMGF (-X) V b κ ν where
  integrable_exp_mul t ht := by simpa using h.integrable_exp_mul (-t) (by simpa using ht)
  mgf_le := by
    filter_upwards [h.mgf_le] with ω' hm t ht
    simpa [mgf] using hm (-t) (by simpa using ht)

lemma mono (h : HasSubexponentialMGF X V b κ ν) {V' b' : ℝ} (hV : V ≤ V') (hb : b ≤ b') :
    HasSubexponentialMGF X V' b' κ ν where
  integrable_exp_mul t ht :=
    h.integrable_exp_mul t ((mul_le_mul_of_nonneg_right hb (abs_nonneg t)).trans ht)
  mgf_le := by
    filter_upwards [h.mgf_le] with ω' hω t ht
    refine (hω t ((mul_le_mul_of_nonneg_right hb (abs_nonneg t)).trans ht)).trans ?_
    gcongr

lemma _root_.ProbabilityTheory.Kernel.HasSubgaussianMGF.hasSubexponentialMGF {c : ℝ≥0}
    (h : Kernel.HasSubgaussianMGF X c κ ν) (b : ℝ) :
    HasSubexponentialMGF X c b κ ν where
  integrable_exp_mul t _ := h.integrable_exp_mul t
  mgf_le := by filter_upwards [h.mgf_le] with ω' h t _ using h t

lemma hasSubgaussianMGF (h : HasSubexponentialMGF X V 0 κ ν) (hV : 0 ≤ V) :
    Kernel.HasSubgaussianMGF X ⟨V, hV⟩ κ ν where
  integrable_exp_mul t := h.integrable_exp_mul t (by simp)
  mgf_le := by filter_upwards [h.mgf_le] with ω' h t using h t (by simp)

lemma congr {Y : Ω → ℝ} (h : HasSubexponentialMGF X V b κ ν) (h' : X =ᵐ[κ ∘ₘ ν] Y) :
    HasSubexponentialMGF Y V b κ ν where
  integrable_exp_mul t ht := by
    refine (integrable_congr ?_).mpr (h.integrable_exp_mul t ht)
    filter_upwards [h'] with ω hω using by rw [hω]
  mgf_le := by
    have h'' := Measure.ae_ae_of_ae_comp h'
    filter_upwards [h.mgf_le, h''] with ω' h_mgf h' t ht
    rw [mgf_congr (Filter.EventuallyEq.symm h')]
    exact h_mgf t ht

lemma _root_.ProbabilityTheory.Kernel.hasSubexponentialMGF_congr {Y : Ω → ℝ}
    (h : X =ᵐ[κ ∘ₘ ν] Y) :
    HasSubexponentialMGF X V b κ ν ↔ HasSubexponentialMGF Y V b κ ν :=
  ⟨fun hX ↦ congr hX h, fun hY ↦ congr hY (ae_eq_symm h)⟩

lemma of_map {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {κ : Kernel Ω' Ω''}
    {Y : Ω'' → Ω} {X : Ω → ℝ} (hY : Measurable Y)
    (h : HasSubexponentialMGF X V b (κ.map Y) ν) :
    HasSubexponentialMGF (X ∘ Y) V b κ ν where
  integrable_exp_mul t ht := by
    have h1 := h.integrable_exp_mul t ht
    rwa [← Measure.map_comp _ _ hY, integrable_map_measure h1.aestronglyMeasurable (by fun_prop)]
      at h1
  mgf_le := by
    filter_upwards [h.ae_forall_integrable_exp_mul, h.mgf_le] with ω' h_int h_mgf t ht
    refine (h_mgf t ht).trans_eq' ?_
    rw [map_apply _ hY, mgf_map hY.aemeasurable]
    convert! (h_int t ht).1
    rw [map_apply _ hY]

lemma id_map_iff (hX : Measurable X) :
    HasSubexponentialMGF id V b (κ.map X) ν ↔ HasSubexponentialMGF X V b κ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun t ht ↦ ?_, ?_⟩⟩
  · change HasSubexponentialMGF (id ∘ X) V b κ ν
    exact .of_map hX h
  · rw [← Kernel.deterministic_comp_eq_map hX, ← Measure.comp_assoc,
      Measure.deterministic_comp_eq_map, integrable_map_measure (by fun_prop) hX.aemeasurable]
    exact h.integrable_exp_mul t ht
  · simpa [Kernel.map_apply _ hX, mgf_id_map hX.aemeasurable] using h.mgf_le

protected lemma const_mul (h : HasSubexponentialMGF X V b κ ν) (r : ℝ) :
    HasSubexponentialMGF (fun ω ↦ r * X ω) (r ^ 2 * V) (|r| * b) κ ν where
  integrable_exp_mul t ht := by
    simp_rw [← mul_assoc]
    exact h.integrable_exp_mul (t * r) (by rw [abs_mul]; linarith)
  mgf_le := by
    filter_upwards [h.mgf_le] with ω hω t ht
    rw [mgf_const_mul, mul_comm r t]
    refine (hω (t * r) (by rw [abs_mul]; linarith)).trans_eq ?_
    congr 1
    ring

section ChernoffBound

lemma measure_ge_le_exp_add (h : HasSubexponentialMGF X V b κ ν) (t : ℝ) :
    ∀ᵐ ω' ∂ν, ∀ s, 0 ≤ s → b * |s| ≤ 1 →
      (κ ω').real {ω | t ≤ X ω} ≤ exp (-s * t + V * s ^ 2 / 2) := by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul, h.isFiniteMeasure]
    with ω' h1 h2 _ s hs hsb
  calc (κ ω').real {ω | t ≤ X ω}
  _ ≤ exp (-s * t) * mgf X (κ ω') s := measure_ge_le_exp_mul_mgf t hs (h2 s hsb)
  _ ≤ exp (-s * t + V * s ^ 2 / 2) := by
    rw [exp_add]
    gcongr
    exact h1 s hsb

/-- Chernoff bound in the Gaussian regime `t * b ≤ V`. -/
lemma measure_ge_le_exp_neg_sq (h : HasSubexponentialMGF X V b κ ν) {t : ℝ}
    (ht : 0 ≤ t) (htb : t * b ≤ V) :
    ∀ᵐ ω' ∂ν, (κ ω').real {ω | t ≤ X ω} ≤ exp (-(t ^ 2 / (2 * V))) := by
  rcases le_or_gt V 0 with hV | hV
  · filter_upwards [h.measureReal_le_one _] with ω' h
    refine h.trans (one_le_exp ?_)
    rw [neg_nonneg]
    exact div_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hlam : b * |t / V| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), ← mul_div_assoc, div_le_one hV, mul_comm]
    exact htb
  filter_upwards [h.measure_ge_le_exp_add t] with ω' h
  refine (h (t / V) (by positivity) hlam).trans_eq ?_
  congr 1
  field_simp
  ring

/-- Chernoff bound in the exponential regime `V ≤ t * b`. -/
lemma measure_ge_le_exp_neg_div (h : HasSubexponentialMGF X V b κ ν) (hb : 0 < b) {t : ℝ}
    (htb : V ≤ t * b) :
    ∀ᵐ ω' ∂ν, (κ ω').real {ω | t ≤ X ω} ≤ exp (-(t / (2 * b))) := by
  filter_upwards [h.measure_ge_le_exp_add t] with ω' h
  refine (h (1 / b) (by positivity)
    (by rw [abs_of_pos (by positivity), mul_one_div_cancel hb.ne'])).trans ?_
  rw [exp_le_exp]
  have h1 : V / (2 * b ^ 2) ≤ t / (2 * b) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : -(1 / b) * t + V * (1 / b) ^ 2 / 2 = -(t / b) + V / (2 * b ^ 2) := by
    field_simp
  have h3 : t / (2 * b) = t / b - t / (2 * b) := by field_simp; ring
  linarith

/-- **Bernstein-type tail bound** for the upper tail of a sub-exponential random variable.
When `V ≤ 0` or `b ≤ 0`, the right-hand side is at least `1` and the bound is trivial. -/
lemma measure_ge_le (h : HasSubexponentialMGF X V b κ ν) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω' ∂ν, (κ ω').real {ω | t ≤ X ω} ≤ exp (-min (t ^ 2 / (2 * V)) (t / (2 * b))) := by
  rcases le_or_gt b 0 with hb | hb
  · filter_upwards [h.measureReal_le_one _] with ω' h
    refine h.trans (one_le_exp ?_)
    rw [neg_nonneg]
    exact (min_le_right _ _).trans (div_nonpos_of_nonneg_of_nonpos ht (by linarith))
  rcases le_or_gt (t * b) V with htb | htb
  · filter_upwards [h.measure_ge_le_exp_neg_sq ht htb] with ω' h
    exact h.trans (exp_le_exp.2 (neg_le_neg (min_le_left _ _)))
  · filter_upwards [h.measure_ge_le_exp_neg_div hb htb.le] with ω' h
    exact h.trans (exp_le_exp.2 (neg_le_neg (min_le_right _ _)))

/-- **Bernstein-type tail bound** for the lower tail of a sub-exponential random variable. -/
lemma measure_le_le (h : HasSubexponentialMGF X V b κ ν) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω' ∂ν, (κ ω').real {ω | X ω ≤ -t} ≤ exp (-min (t ^ 2 / (2 * V)) (t / (2 * b))) := by
  filter_upwards [h.neg.measure_ge_le ht] with ω' h
  simpa only [Pi.neg_apply, le_neg] using h

/-- **Bernstein-type tail bound**, two-sided. -/
lemma measure_abs_ge_le (h : HasSubexponentialMGF X V b κ ν) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω' ∂ν, (κ ω').real {ω | t ≤ |X ω|}
      ≤ 2 * exp (-min (t ^ 2 / (2 * V)) (t / (2 * b))) := by
  filter_upwards [h.measure_ge_le ht, h.measure_le_le ht, h.isFiniteMeasure]
    with ω' h1 h2 _
  calc (κ ω').real {ω | t ≤ |X ω|}
      ≤ (κ ω').real ({ω | t ≤ X ω} ∪ {ω | X ω ≤ -t}) := by
        refine measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)
        simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
        rcases le_abs.1 hω with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (le_neg.1 h1)
    _ ≤ (κ ω').real {ω | t ≤ X ω} + (κ ω').real {ω | X ω ≤ -t} := measureReal_union_le _ _
    _ ≤ exp (-min (t ^ 2 / (2 * V)) (t / (2 * b)))
        + exp (-min (t ^ 2 / (2 * V)) (t / (2 * b))) := add_le_add h1 h2
    _ = 2 * exp (-min (t ^ 2 / (2 * V)) (t / (2 * b))) := by ring

end ChernoffBound

section Add

/-- Sum of two (not necessarily independent) sub-exponential variables, by Hölder's inequality
with conjugate exponents `p` and `q`. The case `p = q = 2` is `add`. -/
lemma add_of_holderConjugate {Y : Ω → ℝ} {VX VY bX bY p q : ℝ} (hpq : p.HolderConjugate q)
    (hX : HasSubexponentialMGF X VX bX κ ν) (hY : HasSubexponentialMGF Y VY bY κ ν) :
    HasSubexponentialMGF (fun ω ↦ X ω + Y ω) (p * VX + q * VY) (max (p * bX) (q * bY)) κ ν := by
  have hp : 0 < p := hpq.pos
  have hq : 0 < q := hpq.symm.pos
  have hpX : ∀ t, max (p * bX) (q * bY) * |t| ≤ 1 → bX * |p * t| ≤ 1 := fun t ht ↦ by
    rw [abs_mul, abs_of_pos hp]
    calc bX * (p * |t|) = (p * bX) * |t| := by ring
      _ ≤ max (p * bX) (q * bY) * |t| := by gcongr; exact le_max_left _ _
      _ ≤ 1 := ht
  have hqY : ∀ t, max (p * bX) (q * bY) * |t| ≤ 1 → bY * |q * t| ≤ 1 := fun t ht ↦ by
    rw [abs_mul, abs_of_pos hq]
    calc bY * (q * |t|) = (q * bY) * |t| := by ring
      _ ≤ max (p * bX) (q * bY) * |t| := by gcongr; exact le_max_right _ _
      _ ≤ 1 := ht
  have hp' : ((p.toNNReal : ℝ≥0) : ℝ) = p := Real.coe_toNNReal p hp.le
  have hq' : ((q.toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal q hq.le
  refine ⟨fun t ht ↦ ?_, ?_⟩
  · simp_rw [mul_add, exp_add]
    have : (↑p.toNNReal : ℝ≥0∞).HolderTriple (↑q.toNNReal) 1 := hpq.ennrealOfReal
    exact MemLp.integrable_mul (hX.memLp_exp_mul p.toNNReal (by rw [hp']; exact hpX t ht))
      (hY.memLp_exp_mul q.toNNReal (by rw [hq']; exact hqY t ht))
  · filter_upwards [hX.mgf_le, hY.mgf_le, hX.ae_forall_memLp_exp_mul p.toNNReal,
      hY.ae_forall_memLp_exp_mul q.toNNReal] with ω' hmX hmY hlX hlY t ht
    calc (κ ω')[fun ω ↦ exp (t * (X ω + Y ω))]
    _ ≤ (κ ω')[fun ω ↦ exp (t * X ω) ^ p] ^ (1 / p) *
        (κ ω')[fun ω ↦ exp (t * Y ω) ^ q] ^ (1 / q) := by
      simp_rw [mul_add, exp_add]
      apply integral_mul_le_Lp_mul_Lq_of_nonneg hpq
      · exact ae_of_all _ fun _ ↦ exp_nonneg _
      · exact ae_of_all _ fun _ ↦ exp_nonneg _
      · exact hlX t (by rw [hp']; exact hpX t ht)
      · exact hlY t (by rw [hq']; exact hqY t ht)
    _ ≤ exp (VX * (t * p) ^ 2 / 2) ^ (1 / p) * exp (VY * (t * q) ^ 2 / 2) ^ (1 / q) := by
      simp_rw [← exp_mul _ p, ← exp_mul _ q, mul_right_comm t _ p, mul_right_comm t _ q]
      gcongr
      · exact hmX (t * p) (by rw [mul_comm t p]; exact hpX t ht)
      · exact hmY (t * q) (by rw [mul_comm t q]; exact hqY t ht)
    _ = exp ((p * VX + q * VY) * t ^ 2 / 2) := by
      simp_rw [← exp_mul, ← exp_add]
      congr 1
      field_simp

/-- Sum of two (not necessarily independent) sub-exponential variables, by the Cauchy–Schwarz
inequality. -/
lemma add {Y : Ω → ℝ} {VX VY bX bY : ℝ}
    (hX : HasSubexponentialMGF X VX bX κ ν) (hY : HasSubexponentialMGF Y VY bY κ ν) :
    HasSubexponentialMGF (fun ω ↦ X ω + Y ω) (2 * (VX + VY)) (2 * max bX bY) κ ν := by
  have := hX.add_of_holderConjugate Real.HolderConjugate.two_two hY
  convert this using 1
  · ring
  · rw [mul_max_of_nonneg _ _ zero_le_two]

variable {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {Y : Ω'' → ℝ} {VY : ℝ}

lemma prodMkLeft_compProd {η : Kernel Ω Ω''} (h : HasSubexponentialMGF Y VY b η (κ ∘ₘ ν)) :
    HasSubexponentialMGF Y VY b (prodMkLeft Ω' η) (ν ⊗ₘ κ) := by
  by_cases hν : SFinite ν
  swap; · simp [hν]
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  constructor
  · simpa using h.integrable_exp_mul
  · have h2 := h.mgf_le
    rw [← Measure.snd_compProd, Measure.snd] at h2
    exact ae_of_ae_map (by fun_prop) h2

variable [SFinite ν]

lemma integrable_exp_add_compProd {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η]
    (hX : HasSubexponentialMGF X V b κ ν) (hY : HasSubexponentialMGF Y VY b η (ν ⊗ₘ κ))
    {t : ℝ} (ht : b * |t| ≤ 1) :
    Integrable (fun ω ↦ exp (t * (X ω.1 + Y ω.2))) ((κ ⊗ₖ η) ∘ₘ ν) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [FunLike.coe_zero, hκ]
  rcases eq_zero_or_isMarkovKernel η with rfl | hη
  · simp [FunLike.coe_zero]
  set μ := (κ ⊗ₖ η) ∘ₘ ν with hμ
  have hfst : κ ∘ₘ ν = μ.map Prod.fst := by
    rw [hμ, Measure.map_comp _ _ measurable_fst, ← Kernel.fst_eq, Kernel.fst_compProd]
  have hsnd : η ∘ₘ (ν ⊗ₘ κ) = μ.map Prod.snd := by
    rw [hμ, Measure.comp_compProd_comm, Measure.snd]
  -- measurable representatives of `X` and `Y`
  have hXm := hX.aestronglyMeasurable
  have hYm := hY.aestronglyMeasurable
  set X' := hXm.mk X with hX'
  set Y' := hYm.mk Y with hY'
  have hX'm : Measurable X' := hXm.stronglyMeasurable_mk.measurable
  have hY'm : Measurable Y' := hYm.stronglyMeasurable_mk.measurable
  have hX'' : HasSubexponentialMGF X' V b κ ν := hX.congr hXm.ae_eq_mk
  have hY'' : HasSubexponentialMGF Y' VY b η (ν ⊗ₘ κ) := hY.congr hYm.ae_eq_mk
  have hXeq : (fun ω : Ω × Ω'' ↦ X ω.1) =ᵐ[μ] fun ω ↦ X' ω.1 := by
    have h : ∀ᵐ y ∂(μ.map Prod.fst), X y = X' y := by
      rw [← hfst]
      exact hXm.ae_eq_mk
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hYeq : (fun ω : Ω × Ω'' ↦ Y ω.2) =ᵐ[μ] fun ω ↦ Y' ω.2 := by
    have h : ∀ᵐ y ∂(μ.map Prod.snd), Y y = Y' y := by
      rw [← hsnd]
      exact hYm.ae_eq_mk
    exact ae_of_ae_map measurable_snd.aemeasurable h
  have h_eq : (fun ω : Ω × Ω'' ↦ exp (t * (X ω.1 + Y ω.2)))
      =ᵐ[μ] fun ω ↦ exp (t * X' ω.1) * exp (t * Y' ω.2) := by
    filter_upwards [hXeq, hYeq] with ω h1 h2
    rw [h1, h2, mul_add, exp_add]
  rw [integrable_congr h_eq]
  refine ⟨(by fun_prop : Measurable fun ω : Ω × Ω'' ↦ exp (t * X' ω.1) * exp (t * Y' ω.2))
    |>.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ by positivity)]
  -- the bound on the inner integral
  have h_inner : ∀ᵐ ω' ∂ν, ∀ᵐ x ∂κ ω',
      ∫⁻ y, ENNReal.ofReal (exp (t * Y' y)) ∂η (ω', x) ≤ ENNReal.ofReal (exp (VY * t ^ 2 / 2)) := by
    refine Measure.ae_ae_of_ae_compProd (p := fun p ↦ ∫⁻ y, ENNReal.ofReal (exp (t * Y' y)) ∂η p
      ≤ ENNReal.ofReal (exp (VY * t ^ 2 / 2))) ?_
    filter_upwards [hY''.mgf_le, hY''.ae_integrable_exp_mul ht] with p h_mgf h_int
    rw [← ofReal_integral_eq_lintegral_ofReal h_int (ae_of_all _ fun _ ↦ by positivity)]
    exact ENNReal.ofReal_le_ofReal (h_mgf t ht)
  have hmeas : Measurable fun ω : Ω × Ω'' ↦
      ENNReal.ofReal (exp (t * X' ω.1)) * ENNReal.ofReal (exp (t * Y' ω.2)) := by fun_prop
  calc ∫⁻ ω, ENNReal.ofReal (exp (t * X' ω.1) * exp (t * Y' ω.2)) ∂μ
  _ = ∫⁻ ω', ∫⁻ x, ∫⁻ y, ENNReal.ofReal (exp (t * X' x)) * ENNReal.ofReal (exp (t * Y' y))
      ∂η (ω', x) ∂κ ω' ∂ν := by
    simp_rw [ENNReal.ofReal_mul (exp_pos _).le]
    rw [hμ, Measure.lintegral_bind (Kernel.aemeasurable _) hmeas.aemeasurable]
    congr with ω'
    rw [Kernel.lintegral_compProd _ _ _ hmeas]
  _ ≤ ∫⁻ ω', ∫⁻ x, ENNReal.ofReal (exp (t * X' x)) * ENNReal.ofReal (exp (VY * t ^ 2 / 2))
      ∂κ ω' ∂ν := by
    refine lintegral_mono_ae ?_
    filter_upwards [h_inner] with ω' h_inner
    refine lintegral_mono_ae ?_
    filter_upwards [h_inner] with x hx
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
  _ = (∫⁻ x, ENNReal.ofReal (exp (t * X' x)) ∂(κ ∘ₘ ν))
      * ENNReal.ofReal (exp (VY * t ^ 2 / 2)) := by
    rw [Measure.lintegral_bind (Kernel.aemeasurable _) (by fun_prop),
      ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    congr with ω'
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  _ < ∞ := by
    refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top
    have := (hX''.integrable_exp_mul t ht).2
    rwa [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ by positivity)] at this

/-- For `ν : Measure Ω'`, `κ : Kernel Ω' Ω` and `η : (Ω' × Ω) Ω''`, if a random variable `X : Ω → ℝ`
has a sub-exponential mgf with respect to `κ` and `ν` and another random variable `Y : Ω'' → ℝ` has
a sub-exponential mgf with respect to `η` and `ν ⊗ₘ κ : Measure (Ω' × Ω)`, with the same
parameter `b`, then `X + Y` (random variable on the measurable space `Ω × Ω''`) has a
sub-exponential mgf with respect to `κ ⊗ₖ η : Kernel Ω' (Ω × Ω'')` and `ν`. -/
lemma add_compProd {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η]
    (hX : HasSubexponentialMGF X V b κ ν) (hY : HasSubexponentialMGF Y VY b η (ν ⊗ₘ κ)) :
    HasSubexponentialMGF (fun p ↦ X p.1 + Y p.2) (V + VY) b (κ ⊗ₖ η) ν := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  refine .of_ae_mgf_le (fun t ht ↦ integrable_exp_add_compProd hX hY ht) fun t ht ↦ ?_
  filter_upwards [hX.mgf_le, hX.ae_integrable_exp_mul ht, Measure.ae_ae_of_ae_compProd hY.mgf_le,
    Measure.ae_integrable_of_integrable_comp <| integrable_exp_add_compProd hX hY ht]
    with ω' hX_mgf hX_int hY_mgf h_int_mul
  calc mgf (fun p ↦ X p.1 + Y p.2) ((κ ⊗ₖ η) ω') t
  _ = ∫ x, exp (t * X x) * ∫ y, exp (t * Y y) ∂(η (ω', x)) ∂(κ ω') := by
    simp_rw [mgf, mul_add, exp_add] at h_int_mul ⊢
    simp_rw [integral_compProd h_int_mul, integral_const_mul]
  _ ≤ ∫ x, exp (t * X x) * exp (VY * t ^ 2 / 2) ∂(κ ω') := by
    refine integral_mono_of_nonneg ?_ (hX_int.mul_const _) ?_
    · exact ae_of_all _ fun ω ↦ mul_nonneg (by positivity)
        (integral_nonneg (fun _ ↦ by positivity))
    · filter_upwards [hY_mgf] with ω hY_mgf
      gcongr
      exact hY_mgf t ht
  _ ≤ exp ((V + VY) * t ^ 2 / 2) := by
    rw [integral_mul_const, add_mul, add_div, exp_add]
    gcongr
    exact hX_mgf t ht

/-- For `ν : Measure Ω'`, `κ : Kernel Ω' Ω` and `η : Ω Ω''`, if a random variable `X : Ω → ℝ`
has a sub-exponential mgf with respect to `κ` and `ν` and another random variable `Y : Ω'' → ℝ` has
a sub-exponential mgf with respect to `η` and `κ ∘ₘ ν : Measure Ω`, with the same parameter `b`,
then `X + Y` (random variable on the measurable space `Ω × Ω''`) has a sub-exponential mgf with
respect to `κ ⊗ₖ prodMkLeft Ω' η : Kernel Ω' (Ω × Ω'')` and `ν`. -/
lemma add_comp {η : Kernel Ω Ω''} [IsZeroOrMarkovKernel η]
    (hX : HasSubexponentialMGF X V b κ ν) (hY : HasSubexponentialMGF Y VY b η (κ ∘ₘ ν)) :
    HasSubexponentialMGF (fun p ↦ X p.1 + Y p.2) (V + VY) b (κ ⊗ₖ prodMkLeft Ω' η) ν :=
  hX.add_compProd hY.prodMkLeft_compProd

end Add

end Kernel.HasSubexponentialMGF

end Kernel

section Conditional

/-! ### Conditionally sub-exponential moment-generating function -/

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {V b : ℝ}

variable (m) (hm) in
/-- A random variable `X` has a conditionally sub-exponential moment-generating function
with parameters `(V, b)` with respect to a sigma-algebra `m` and a measure `μ` if for all `t`
with `b * |t| ≤ 1`, `exp (t * X)` is `μ`-integrable and the moment-generating function of `X`
conditioned on `m` is almost surely bounded by `exp (V * t ^ 2 / 2)`.

The actual definition uses `Kernel.HasSubexponentialMGF`: `HasCondSubexponentialMGF` is defined
as sub-exponential with respect to the conditional expectation kernel for `m` and the restriction
of `μ` to the sigma-algebra `m`. -/
def HasCondSubexponentialMGF (X : Ω → ℝ) (V b : ℝ)
    (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.HasSubexponentialMGF X V b (condExpKernel μ m) (μ.trim hm)

namespace HasCondSubexponentialMGF

lemma mgf_le (h : HasCondSubexponentialMGF m hm X V b μ) :
    ∀ᵐ ω' ∂(μ.trim hm), ∀ t, b * |t| ≤ 1 →
      mgf X (condExpKernel μ m ω') t ≤ exp (V * t ^ 2 / 2) :=
  Kernel.HasSubexponentialMGF.mgf_le h

lemma cgf_le (h : HasCondSubexponentialMGF m hm X V b μ) (hV : 0 ≤ V) :
    ∀ᵐ ω' ∂(μ.trim hm), ∀ t, b * |t| ≤ 1 → cgf X (condExpKernel μ m ω') t ≤ V * t ^ 2 / 2 :=
  Kernel.HasSubexponentialMGF.cgf_le h hV

lemma ae_trim_condExp_le (h : HasCondSubexponentialMGF m hm X V b μ) {t : ℝ}
    (ht : b * |t| ≤ 1) :
    ∀ᵐ ω' ∂(μ.trim hm), (μ[fun ω ↦ exp (t * X ω) | m]) ω' ≤ exp (V * t ^ 2 / 2) := by
  have h_eq := condExp_ae_eq_trim_integral_condExpKernel hm (h.integrable_exp_mul t ht)
  simp_rw [condExpKernel_comp_trim] at h_eq
  filter_upwards [h.mgf_le, h_eq] with ω' h_mgf h_eq
  rw [h_eq]
  exact h_mgf t ht

lemma ae_condExp_le (h : HasCondSubexponentialMGF m hm X V b μ) {t : ℝ} (ht : b * |t| ≤ 1) :
    ∀ᵐ ω' ∂μ, (μ[fun ω ↦ exp (t * X ω) | m]) ω' ≤ exp (V * t ^ 2 / 2) :=
  ae_of_ae_trim hm (h.ae_trim_condExp_le ht)

@[simp]
lemma fun_zero : HasCondSubexponentialMGF m hm (fun _ ↦ 0) 0 b μ :=
  Kernel.HasSubexponentialMGF.fun_zero

@[simp]
lemma zero : HasCondSubexponentialMGF m hm 0 0 b μ := Kernel.HasSubexponentialMGF.zero

lemma memLp_exp_mul (h : HasCondSubexponentialMGF m hm X V b μ) {t : ℝ} (p : ℝ≥0)
    (ht : b * |(p : ℝ) * t| ≤ 1) :
    MemLp (fun ω ↦ exp (t * X ω)) p μ :=
  condExpKernel_comp_trim (μ := μ) hm ▸ Kernel.HasSubexponentialMGF.memLp_exp_mul h p ht

lemma integrable_exp_mul (h : HasCondSubexponentialMGF m hm X V b μ) {t : ℝ}
    (ht : b * |t| ≤ 1) :
    Integrable (fun ω ↦ exp (t * X ω)) μ :=
  condExpKernel_comp_trim (μ := μ) hm ▸ Kernel.HasSubexponentialMGF.integrable_exp_mul h t ht

lemma _root_.ProbabilityTheory.HasCondSubgaussianMGF.hasCondSubexponentialMGF {c : ℝ≥0}
    (h : HasCondSubgaussianMGF m hm X c μ) (b : ℝ) :
    HasCondSubexponentialMGF m hm X c b μ :=
  h.hasSubexponentialMGF b

lemma hasCondSubgaussianMGF (h : HasCondSubexponentialMGF m hm X V 0 μ) (hV : 0 ≤ V) :
    HasCondSubgaussianMGF m hm X ⟨V, hV⟩ μ :=
  Kernel.HasSubexponentialMGF.hasSubgaussianMGF h hV

end HasCondSubexponentialMGF

end Conditional

/-! ### Sub-exponential moment-generating function -/

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {V b : ℝ}

/-- `X` has a sub-exponential moment generating function with parameters `(V, b)`: for every
`t` with `b * |t| ≤ 1`, `exp (t * X)` is integrable and `mgf X μ t ≤ exp (V * t ^ 2 / 2)`.
For `b = 0` this is `HasSubgaussianMGF X V μ`.

This is equivalent to `Kernel.HasSubexponentialMGF X V b (Kernel.const Unit μ) (Measure.dirac ())`,
as proved in `hasSubexponentialMGF_iff_kernel`. -/
structure HasSubexponentialMGF (X : Ω → ℝ) (V b : ℝ) (μ : Measure Ω := by volume_tac) :
    Prop where
  integrable_exp_mul : ∀ t : ℝ, b * |t| ≤ 1 → Integrable (fun ω ↦ exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, b * |t| ≤ 1 → mgf X μ t ≤ exp (V * t ^ 2 / 2)

lemma hasSubexponentialMGF_iff_kernel :
    HasSubexponentialMGF X V b μ
      ↔ Kernel.HasSubexponentialMGF X V b (Kernel.const Unit μ) (Measure.dirac ()) :=
  ⟨fun ⟨h1, h2⟩ ↦ ⟨by simpa, by simpa⟩, fun ⟨h1, h2⟩ ↦ ⟨by simpa using h1, by simpa using h2⟩⟩

lemma Kernel.HasSubexponentialMGF.ae_hasSubexponentialMGF {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} {κ : Kernel Ω' Ω}
    (h : Kernel.HasSubexponentialMGF X V b κ ν) :
    ∀ᵐ ω' ∂ν, ProbabilityTheory.HasSubexponentialMGF X V b (κ ω') := by
  filter_upwards [h.ae_forall_integrable_exp_mul, h.mgf_le] with ω' h1 h2
  exact ⟨h1, h2⟩

namespace HasSubexponentialMGF

lemma _root_.ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (b : ℝ) :
    HasSubexponentialMGF X c b μ where
  integrable_exp_mul t _ := h.integrable_exp_mul t
  mgf_le t _ := h.mgf_le t

lemma hasSubgaussianMGF (h : HasSubexponentialMGF X V 0 μ) (hV : 0 ≤ V) :
    HasSubgaussianMGF X ⟨V, hV⟩ μ where
  integrable_exp_mul t := h.integrable_exp_mul t (by simp)
  mgf_le t := h.mgf_le t (by simp)

lemma mono (h : HasSubexponentialMGF X V b μ) {V' b' : ℝ} (hV : V ≤ V') (hb : b ≤ b') :
    HasSubexponentialMGF X V' b' μ where
  integrable_exp_mul t ht :=
    h.integrable_exp_mul t ((mul_le_mul_of_nonneg_right hb (abs_nonneg t)).trans ht)
  mgf_le t ht := by
    refine (h.mgf_le t ((mul_le_mul_of_nonneg_right hb (abs_nonneg t)).trans ht)).trans ?_
    gcongr

lemma aestronglyMeasurable (h : HasSubexponentialMGF X V b μ) : AEStronglyMeasurable X μ := by
  rw [hasSubexponentialMGF_iff_kernel] at h
  simpa using h.aestronglyMeasurable

lemma isFiniteMeasure (h : HasSubexponentialMGF X V b μ) : IsFiniteMeasure μ := by
  simpa [integrable_const_iff] using h.integrable_exp_mul 0 (by simp)

lemma congr (h : HasSubexponentialMGF X V b μ) {Y : Ω → ℝ} (h' : X =ᵐ[μ] Y) :
    HasSubexponentialMGF Y V b μ := by
  rw [hasSubexponentialMGF_iff_kernel] at h ⊢
  apply h.congr
  simpa

lemma memLp_exp_mul (h : HasSubexponentialMGF X V b μ) {t : ℝ} (p : ℝ≥0)
    (ht : b * |(p : ℝ) * t| ≤ 1) :
    MemLp (fun ω ↦ exp (t * X ω)) p μ := by
  rw [hasSubexponentialMGF_iff_kernel] at h
  simpa using h.memLp_exp_mul p ht

lemma cgf_le (h : HasSubexponentialMGF X V b μ) (hV : 0 ≤ V) {t : ℝ} (ht : b * |t| ≤ 1) :
    cgf X μ t ≤ V * t ^ 2 / 2 := by
  rw [hasSubexponentialMGF_iff_kernel] at h
  have := all_ae_of (h.cgf_le hV) t
  simp only [Kernel.const_apply, ae_dirac_eq, Filter.eventually_pure] at this
  exact this ht

@[simp]
lemma fun_zero [IsZeroOrProbabilityMeasure μ] : HasSubexponentialMGF (fun _ ↦ 0) 0 b μ := by
  simp [hasSubexponentialMGF_iff_kernel]

@[simp]
lemma zero [IsZeroOrProbabilityMeasure μ] : HasSubexponentialMGF 0 0 b μ := fun_zero

@[to_fun]
lemma neg (h : HasSubexponentialMGF X V b μ) : HasSubexponentialMGF (-X) V b μ := by
  simpa [hasSubexponentialMGF_iff_kernel] using (hasSubexponentialMGF_iff_kernel.1 h).neg

lemma of_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {Y : Ω' → Ω} {X : Ω → ℝ} (hY : AEMeasurable Y μ) (h : HasSubexponentialMGF X V b (μ.map Y)) :
    HasSubexponentialMGF (X ∘ Y) V b μ where
  integrable_exp_mul t ht := by
    have h1 := h.integrable_exp_mul t ht
    rwa [integrable_map_measure h1.aestronglyMeasurable (by fun_prop)] at h1
  mgf_le t ht := by
    convert! h.mgf_le t ht using 1
    rw [mgf_map hY (h.integrable_exp_mul t ht).1]

lemma map_iff {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {Y : Ω' → Ω} {X : Ω → ℝ} (hY : AEMeasurable Y μ) (hX : AEMeasurable X (μ.map Y)) :
    HasSubexponentialMGF X V b (μ.map Y) ↔ HasSubexponentialMGF (X ∘ Y) V b μ := by
  refine ⟨fun h ↦ .of_map hY h, fun h ↦ ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩⟩
  · rw [integrable_map_measure (by fun_prop) hY]
    exact h.integrable_exp_mul t ht
  · rw [mgf_map hY (by fun_prop)]
    exact h.mgf_le t ht

lemma id_map_iff (hX : AEMeasurable X μ) :
    HasSubexponentialMGF id V b (μ.map X) ↔ HasSubexponentialMGF X V b μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩⟩
  · rw [← Function.id_comp X]
    exact .of_map hX h
  · rw [integrable_map_measure (by fun_prop) hX]
    exact h.integrable_exp_mul t ht
  · rw [mgf_id_map hX]
    exact h.mgf_le t ht

lemma congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Y : Ω' → ℝ} (hX : HasSubexponentialMGF X V b μ) (hXY : IdentDistrib X Y μ μ') :
    HasSubexponentialMGF Y V b μ' := by
  rw [← id_map_iff hXY.aemeasurable_fst] at hX
  rwa [← id_map_iff hXY.aemeasurable_snd, ← hXY.map_eq]

lemma trim (hm : m ≤ mΩ) (hXm : Measurable[m] X) (hX : HasSubexponentialMGF X V b μ) :
    HasSubexponentialMGF X V b (μ.trim hm) where
  integrable_exp_mul t ht := by
    refine (hX.integrable_exp_mul t ht).trim hm ?_
    exact Measurable.stronglyMeasurable <| by fun_prop
  mgf_le t ht := by
    rw [mgf, ← integral_trim]
    · exact hX.mgf_le t ht
    · exact Measurable.stronglyMeasurable <| by fun_prop

protected lemma const_mul (h : HasSubexponentialMGF X V b μ) (a : ℝ) :
    HasSubexponentialMGF (fun ω ↦ a * X ω) (a ^ 2 * V) (|a| * b) μ := by
  rw [hasSubexponentialMGF_iff_kernel] at h ⊢
  exact h.const_mul a

lemma zero_mem_interior_integrableExpSet (h : HasSubexponentialMGF X V b μ) :
    0 ∈ interior (integrableExpSet X μ) := by
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [((by fun_prop : Continuous fun t : ℝ ↦ b * |t|).tendsto 0).eventually_le_const
    (by simp : b * |(0 : ℝ)| < 1)] with t ht
  exact h.integrable_exp_mul t ht

lemma aemeasurable (h : HasSubexponentialMGF X V b μ) : AEMeasurable X μ :=
  aemeasurable_of_mem_interior_integrableExpSet h.zero_mem_interior_integrableExpSet

lemma integrable (h : HasSubexponentialMGF X V b μ) : Integrable X μ :=
  integrable_of_mem_interior_integrableExpSet h.zero_mem_interior_integrableExpSet

lemma memLp (h : HasSubexponentialMGF X V b μ) (p : ℝ≥0) : MemLp X p μ :=
  memLp_of_mem_interior_integrableExpSet h.zero_mem_interior_integrableExpSet p

lemma integrable_pow (h : HasSubexponentialMGF X V b μ) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) μ :=
  integrable_pow_of_mem_interior_integrableExpSet h.zero_mem_interior_integrableExpSet n

/-- A sub-exponential random variable is centered. -/
lemma integral_eq_zero (h : HasSubexponentialMGF X V b μ) [IsProbabilityMeasure μ] : μ[X] = 0 := by
  have hd : HasDerivAt (fun t ↦ mgf X μ t - exp (V * t ^ 2 / 2)) (μ[X] - 0) 0 := by
    have h1 : HasDerivAt (mgf X μ) μ[X] 0 := by
      simpa using hasDerivAt_mgf h.zero_mem_interior_integrableExpSet
    have h2 : HasDerivAt (fun t : ℝ ↦ exp (V * t ^ 2 / 2)) 0 0 := by
      have := (((hasDerivAt_pow 2 (0 : ℝ)).const_mul V).div_const 2).exp
      simpa using this
    exact h1.sub h2
  have hmax : IsLocalMax (fun t ↦ mgf X μ t - exp (V * t ^ 2 / 2)) 0 := by
    filter_upwards [((by fun_prop : Continuous fun t : ℝ ↦ b * |t|).tendsto 0).eventually_le_const
      (by simp : b * |(0 : ℝ)| < 1)] with t ht
    simp only [mgf_zero', probReal_univ, zero_pow two_ne_zero, mul_zero, zero_div, exp_zero,
      sub_self]
    linarith [h.mgf_le t ht]
  simpa using hmax.hasDerivAt_eq_zero hd

section Zero

/-- A random variable with sub-exponential parameters `(0, b)` on a probability space vanishes
almost surely: its mgf is identically `1` near `0`, so its second moment vanishes. -/
lemma ae_eq_zero_of_hasSubexponentialMGF_zero [IsProbabilityMeasure μ]
    (h : HasSubexponentialMGF X 0 b μ) : X =ᵐ[μ] 0 := by
  have h0 := h.zero_mem_interior_integrableExpSet
  have hEX := h.integral_eq_zero
  have hmgf : mgf X μ =ᶠ[𝓝 0] fun _ ↦ 1 := by
    filter_upwards [((by fun_prop : Continuous fun t : ℝ ↦ b * |t|).tendsto 0).eventually_le_const
      (by simp : b * |(0 : ℝ)| < 1)] with t ht
    refine le_antisymm (by simpa using h.mgf_le t ht) ?_
    have := ConvexOn.map_integral_le convexOn_exp (f := fun ω ↦ t * X ω) (s := Set.univ)
      continuous_exp.continuousOn isClosed_univ (ae_of_all _ fun _ ↦ trivial)
      (h.integrable.const_mul t) (h.integrable_exp_mul t ht)
    simpa [integral_const_mul, hEX, mgf] using this
  have h2 : μ[X ^ 2] = 0 := by
    rw [← iteratedDeriv_mgf_zero h0 2, hmgf.iteratedDeriv_eq 2, iteratedDeriv_const]
    simp
  have hX2 : (fun ω ↦ X ω ^ 2) =ᵐ[μ] 0 := by
    rw [← integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun ω ↦ sq_nonneg (X ω))
      (h.integrable_pow 2)]
    exact h2
  filter_upwards [hX2] with ω hω
  simpa using hω

end Zero

section Tail

/-- Chernoff bound in the Gaussian regime `t * b ≤ V`. -/
lemma measure_ge_le_exp_neg_sq (h : HasSubexponentialMGF X V b μ) {t : ℝ}
    (ht : 0 ≤ t) (htb : t * b ≤ V) :
    μ.real {ω | t ≤ X ω} ≤ exp (-(t ^ 2 / (2 * V))) := by
  rw [hasSubexponentialMGF_iff_kernel] at h
  simpa using h.measure_ge_le_exp_neg_sq ht htb

/-- Chernoff bound in the exponential regime `V ≤ t * b`. -/
lemma measure_ge_le_exp_neg_div (h : HasSubexponentialMGF X V b μ) (hb : 0 < b) {t : ℝ}
    (htb : V ≤ t * b) :
    μ.real {ω | t ≤ X ω} ≤ exp (-(t / (2 * b))) := by
  rw [hasSubexponentialMGF_iff_kernel] at h
  simpa using h.measure_ge_le_exp_neg_div hb htb

/-- **Bernstein-type tail bound** for the upper tail of a sub-exponential random variable.
When `V ≤ 0` or `b ≤ 0`, the right-hand side is at least `1` and the bound is trivial. -/
lemma measure_ge_le (h : HasSubexponentialMGF X V b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ X ω} ≤ exp (-min (t ^ 2 / (2 * V)) (t / (2 * b))) := by
  rw [hasSubexponentialMGF_iff_kernel] at h
  simpa using h.measure_ge_le ht

/-- **Bernstein-type tail bound** for the lower tail of a sub-exponential random variable. -/
lemma measure_le_le (h : HasSubexponentialMGF X V b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | X ω ≤ -t} ≤ exp (-min (t ^ 2 / (2 * V)) (t / (2 * b))) := by
  rw [hasSubexponentialMGF_iff_kernel] at h
  simpa using h.measure_le_le ht

/-- **Bernstein-type tail bound**, two-sided. -/
lemma measure_abs_ge_le (h : HasSubexponentialMGF X V b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * exp (-min (t ^ 2 / (2 * V)) (t / (2 * b))) := by
  rw [hasSubexponentialMGF_iff_kernel] at h
  simpa using h.measure_abs_ge_le ht

/-- **Bernstein-type tail bound**, two-sided, with a strict inequality in the event. -/
lemma measure_abs_gt_le (h : HasSubexponentialMGF X V b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t < |X ω|} ≤ 2 * exp (-min (t ^ 2 / (2 * V)) (t / (2 * b))) := by
  have := h.isFiniteMeasure
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (h.measure_abs_ge_le ht)
  intro ω hω
  exact le_of_lt (Set.mem_ofPred_eq.mp hω)

end Tail

section Sum

/-- Sum of two (not necessarily independent) sub-exponential variables, by Hölder's inequality
with conjugate exponents `p` and `q`. The case `p = q = 2` is `add`. -/
lemma add_of_holderConjugate {Y : Ω → ℝ} {VX VY bX bY p q : ℝ} (hpq : p.HolderConjugate q)
    (hX : HasSubexponentialMGF X VX bX μ) (hY : HasSubexponentialMGF Y VY bY μ) :
    HasSubexponentialMGF (fun ω ↦ X ω + Y ω) (p * VX + q * VY) (max (p * bX) (q * bY)) μ := by
  rw [hasSubexponentialMGF_iff_kernel] at hX hY ⊢
  exact hX.add_of_holderConjugate hpq hY

/-- Sum of two (not necessarily independent) sub-exponential variables, by the Cauchy–Schwarz
inequality. -/
lemma add {Y : Ω → ℝ} {VX VY bX bY : ℝ}
    (hX : HasSubexponentialMGF X VX bX μ) (hY : HasSubexponentialMGF Y VY bY μ) :
    HasSubexponentialMGF (fun ω ↦ X ω + Y ω) (2 * (VX + VY)) (2 * max bX bY) μ := by
  rw [hasSubexponentialMGF_iff_kernel] at hX hY ⊢
  exact hX.add hY

lemma add_of_indepFun {Y : Ω → ℝ} {VX VY : ℝ} (hX : HasSubexponentialMGF X VX b μ)
    (hY : HasSubexponentialMGF Y VY b μ) (hindep : IndepFun X Y μ) :
    HasSubexponentialMGF (X + Y) (VX + VY) b μ where
  integrable_exp_mul t ht :=
    hindep.integrable_exp_mul_add (hX.integrable_exp_mul t ht) (hY.integrable_exp_mul t ht)
  mgf_le t ht := by
    rw [hindep.mgf_add (hX.integrable_exp_mul t ht).aestronglyMeasurable
      (hY.integrable_exp_mul t ht).aestronglyMeasurable]
    calc mgf X μ t * mgf Y μ t
        ≤ exp (VX * t ^ 2 / 2) * exp (VY * t ^ 2 / 2) :=
          mul_le_mul (hX.mgf_le t ht) (hY.mgf_le t ht) mgf_nonneg (exp_pos _).le
      _ = exp ((VX + VY) * t ^ 2 / 2) := by rw [← exp_add]; ring_nf

lemma sub_of_indepFun {Y : Ω → ℝ} {VX VY : ℝ} (hX : HasSubexponentialMGF X VX b μ)
    (hY : HasSubexponentialMGF Y VY b μ) (hindep : IndepFun X Y μ) :
    HasSubexponentialMGF (fun ω ↦ X ω - Y ω) (VX + VY) b μ := by
  simp_rw [sub_eq_add_neg]
  exact hX.add_of_indepFun hY.neg hindep.neg_right

private lemma sum_of_iIndepFun_of_forall_aemeasurable
    {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {V : ι → ℝ}
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    {s : Finset ι} (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (V i) b μ) :
    HasSubexponentialMGF (fun ω ↦ ∑ i ∈ s, X i ω) (∑ i ∈ s, V i) b μ := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his hs =>
    simp_rw [← Finset.sum_apply, Finset.sum_insert his, Pi.add_apply, Finset.sum_apply]
    have h_indep' := (h_indep.indepFun_finsetSum_of_notMem₀ h_meas his).symm
    refine add_of_indepFun (h _ (Finset.mem_insert_self _ _)) (hs ?_) ?_
    · exact fun i hi ↦ h _ (Finset.mem_insert_of_mem hi)
    · convert! h_indep'
      rw [Finset.sum_apply]

lemma sum_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {V : ι → ℝ}
    (s : Finset ι) (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (V i) b μ) :
    HasSubexponentialMGF (∑ i ∈ s, X i) (∑ i ∈ s, V i) b μ := by
  have : HasSubexponentialMGF (fun ω ↦ ∑ (i : s), X i ω) (∑ (i : s), V i) b μ := by
    apply sum_of_iIndepFun_of_forall_aemeasurable
    · exact h_indep.precomp Subtype.val_injective
    · exact fun i ↦ (h i i.2).aemeasurable
    · exact fun i _ ↦ h i i.2
  rw [Finset.sum_coe_sort] at this
  refine (this.congr (ae_of_all _ fun ω ↦ Finset.sum_attach s (fun i ↦ X i ω))).congr ?_
  exact ae_of_all _ fun ω ↦ by simp [Finset.sum_apply]

lemma fun_sum_of_iIndepFun {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {V : ι → ℝ} (h : ∀ i, HasSubexponentialMGF (X i) (V i) b μ) :
    HasSubexponentialMGF (fun ω ↦ ∑ i, X i ω) (∑ i, V i) b μ := by
  have := sum_of_iIndepFun h_indep Finset.univ fun i _ ↦ h i
  have h1 : (fun ω ↦ ∑ i, X i ω) = ∑ i, X i := by
    ext ω
    simp [Finset.sum_apply]
  rw [h1]
  exact this

/-- **Bernstein's inequality** for the upper tail of a sum of independent sub-exponential
random variables. -/
lemma measure_sum_ge_le_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {V : ι → ℝ} {s : Finset ι} (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (V i) b μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ s, X i ω}
      ≤ exp (-min (t ^ 2 / (2 * ∑ i ∈ s, V i)) (t / (2 * b))) := by
  have := (sum_of_iIndepFun h_indep s h).measure_ge_le ht
  simpa only [Finset.sum_apply] using this

/-- **Bernstein's inequality** for the lower tail of a sum of independent sub-exponential
random variables. -/
lemma measure_sum_le_le_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {V : ι → ℝ} {s : Finset ι} (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (V i) b μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ -t}
      ≤ exp (-min (t ^ 2 / (2 * ∑ i ∈ s, V i)) (t / (2 * b))) := by
  simp_rw [le_neg (b := t), ← Finset.sum_neg_distrib, ← Pi.neg_apply (f := X _),
    ← Pi.neg_apply (f := X)]
  refine measure_sum_ge_le_of_iIndepFun (X := -X) (μ := μ) ?_ ?_ ht
  · exact h_indep.comp _ (fun _ ↦ measurable_neg)
  · exact fun i hi ↦ (h i hi).neg

/-- **Bernstein's inequality** for the upper tail of a sum of `n` independent sub-exponential
random variables with the same parameters. -/
lemma measure_sum_range_ge_le_of_iIndepFun {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ)
    {n : ℕ} (h : ∀ i < n, HasSubexponentialMGF (X i) V b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ Finset.range n, X i ω}
      ≤ exp (-min (t ^ 2 / (2 * n * V)) (t / (2 * b))) := by
  have h := measure_sum_ge_le_of_iIndepFun h_indep (V := fun _ ↦ V) (s := Finset.range n)
    (by simpa) ht
  simpa [← mul_assoc] using h

/-- **Bernstein's inequality** for the lower tail of a sum of `n` independent sub-exponential
random variables with the same parameters. -/
lemma measure_sum_range_le_le_of_iIndepFun {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ)
    {n : ℕ} (h : ∀ i < n, HasSubexponentialMGF (X i) V b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∑ i ∈ Finset.range n, X i ω ≤ -t}
      ≤ exp (-min (t ^ 2 / (2 * n * V)) (t / (2 * b))) := by
  simp_rw [le_neg (b := t), ← Finset.sum_neg_distrib, ← Pi.neg_apply (f := X _),
    ← Pi.neg_apply (f := X)]
  refine measure_sum_range_ge_le_of_iIndepFun (X := -X) (μ := μ) ?_ ?_ ht
  · exact h_indep.comp _ (fun _ ↦ measurable_neg)
  · exact fun i hi ↦ (h i hi).neg

/-- The average of `K` independent sub-exponential variables with parameters `(V i, b)` has
parameters `((∑ i, V i) / K ^ 2, b / K)`. -/
lemma average_of_iIndepFun {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {V : ι → ℝ} (h : ∀ i, HasSubexponentialMGF (X i) (V i) b μ) :
    HasSubexponentialMGF (fun ω ↦ (∑ i, X i ω) / Fintype.card ι)
      ((∑ i, V i) / (Fintype.card ι : ℝ) ^ 2) (b / Fintype.card ι) μ := by
  have := (fun_sum_of_iIndepFun h_indep h).const_mul (1 / Fintype.card ι)
  have h1 : (fun ω ↦ (∑ i, X i ω) / Fintype.card ι)
      = fun ω ↦ (1 / Fintype.card ι) * ∑ i, X i ω := by
    ext ω
    ring
  have h2 : (∑ i, V i) / (Fintype.card ι : ℝ) ^ 2 = (1 / Fintype.card ι) ^ 2 * ∑ i, V i := by
    ring
  have h3 : b / Fintype.card ι = |1 / (Fintype.card ι : ℝ)| * b := by
    rw [abs_of_nonneg (by positivity)]
    ring
  rw [h1, h2, h3]
  exact this

/-- **Tail bound for an average** of independent sub-exponential variables with parameters
`(V i, b)`: writing `K` for the number of variables and `V̄ := (∑ i, V i) / K`,
`P(|(∑ i, X i) / K| ≥ t) ≤ 2 exp (-K min (t ^ 2 / (2 V̄)) (t / (2 b)))`. -/
lemma measure_abs_average_ge_le {ι : Type*} [Fintype ι] [Nonempty ι] {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) {V : ι → ℝ} (h : ∀ i, HasSubexponentialMGF (X i) (V i) b μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(∑ i, X i ω) / Fintype.card ι|}
      ≤ 2 * exp (-(Fintype.card ι
        * min (t ^ 2 / (2 * ((∑ i, V i) / Fintype.card ι))) (t / (2 * b)))) := by
  have hK : (0 : ℝ) < Fintype.card ι := by
    have := Fintype.card_pos (α := ι)
    positivity
  have hbound := (average_of_iIndepFun h_indep h).measure_abs_ge_le ht
  refine hbound.trans (le_of_eq ?_)
  congr 3
  rw [(monotone_mul_left_of_nonneg hK.le).map_min]
  congr 1
  · field_simp
  · field_simp

/-- **Tail bound for an average** of independent sub-exponential variables with the same
parameters `(V, b)`. -/
lemma measure_abs_average_ge_le_of_forall {ι : Type*} [Fintype ι] [Nonempty ι] {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h : ∀ i, HasSubexponentialMGF (X i) V b μ) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(∑ i, X i ω) / Fintype.card ι|}
      ≤ 2 * exp (-(Fintype.card ι * min (t ^ 2 / (2 * V)) (t / (2 * b)))) := by
  have hK : (0 : ℝ) < Fintype.card ι := by
    have := Fintype.card_pos (α := ι)
    positivity
  have := measure_abs_average_ge_le h_indep (V := fun _ ↦ V) h ht
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hK.ne']
    using this

/-- For `X, Y` two independent random variables with sub-exponential fluctuations such that
`μ[X] ≥ μ[Y]`, the probability that `X ≤ Y` is bounded by a Bernstein-type term. -/
lemma measureReal_le_le_exp {Y : Ω → ℝ} {VX VY : ℝ}
    (hX : HasSubexponentialMGF (fun ω ↦ X ω - μ[X]) VX b μ)
    (hY : HasSubexponentialMGF (fun ω ↦ Y ω - μ[Y]) VY b μ)
    (hindep : IndepFun X Y μ) (h_le : μ[Y] ≤ μ[X]) :
    μ.real {ω | X ω ≤ Y ω}
      ≤ exp (-min ((μ[X] - μ[Y]) ^ 2 / (2 * (VX + VY))) ((μ[X] - μ[Y]) / (2 * b))) := by
  have hXY : HasSubexponentialMGF (fun ω ↦ (Y ω - μ[Y]) - (X ω - μ[X])) (VX + VY) b μ := by
    rw [add_comm VX]
    refine sub_of_indepFun hY hX ?_
    exact hindep.symm.comp (φ := fun x ↦ x - μ[Y]) (ψ := fun x ↦ x - μ[X])
      (by fun_prop) (by fun_prop)
  calc μ.real {ω | X ω ≤ Y ω}
  _ = μ.real {ω | (μ[X] - μ[Y]) ≤ (Y ω - μ[Y]) - (X ω - μ[X])} := by
    congr with ω
    constructor <;> intro h <;> linarith
  _ ≤ exp (-min ((μ[X] - μ[Y]) ^ 2 / (2 * (VX + VY))) ((μ[X] - μ[Y]) / (2 * b))) :=
    hXY.measure_ge_le (by linarith)

end Sum

end HasSubexponentialMGF

lemma Kernel.HasSubexponentialMGF.ae_integral_eq_zero {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} {κ : Kernel Ω' Ω} [IsMarkovKernel κ]
    (h : Kernel.HasSubexponentialMGF X V b κ ν) :
    ∀ᵐ ω' ∂ν, (κ ω')[X] = 0 := by
  filter_upwards [h.ae_hasSubexponentialMGF] with ω' h using h.integral_eq_zero

lemma Kernel.HasSubexponentialMGF.ae_eq_zero_of_hasSubexponentialMGF_zero {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} {κ : Kernel Ω' Ω} [IsMarkovKernel κ]
    (h : Kernel.HasSubexponentialMGF X 0 b κ ν) :
    ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] 0 := by
  filter_upwards [h.ae_hasSubexponentialMGF] with ω' h
  exact h.ae_eq_zero_of_hasSubexponentialMGF_zero

section Bounded

/-- Second-order bound on the exponential on `[-1, 1]`, from `Real.exp_bound`. -/
lemma exp_le_one_add_add_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    exp x ≤ 1 + x + 3 / 4 * x ^ 2 := by
  have h := Real.exp_bound hx (n := 2) two_pos
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith [(abs_le.1 h).2]

/-- If `|X| ≤ M` almost surely, `X` is centered and `μ[X ^ 2] ≤ v`, then `X` has
a sub-exponential mgf with parameters `(3 * v / 2, M)`. -/
lemma hasSubexponentialMGF_of_abs_le_of_integral_eq_zero [IsProbabilityMeasure μ] {M v : ℝ}
    (hm : AEMeasurable X μ) (hM : ∀ᵐ ω ∂μ, |X ω| ≤ M) (hc : μ[X] = 0) (hv : μ[X ^ 2] ≤ v) :
    HasSubexponentialMGF X (3 * v / 2) M μ := by
  have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-M) M := hM.mono fun ω h ↦ abs_le.1 h
  have hX : Integrable X μ := Integrable.of_mem_Icc (-M) M hm hIcc
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := by
    refine Integrable.of_mem_Icc 0 (M ^ 2) (hm.pow_const 2) ?_
    filter_upwards [hM] with ω hω
    exact ⟨sq_nonneg _, by rw [← sq_abs]; gcongr⟩
  refine ⟨fun t _ ↦ integrable_exp_mul_of_mem_Icc hm hIcc, fun t ht ↦ ?_⟩
  have hpt : ∀ᵐ ω ∂μ, exp (t * X ω) ≤ 1 + t * X ω + 3 / 4 * (t * X ω) ^ 2 := by
    filter_upwards [hM] with ω hω
    refine exp_le_one_add_add_of_abs_le_one ?_
    rw [abs_mul]
    calc |t| * |X ω| ≤ |t| * M := by gcongr
      _ = M * |t| := mul_comm _ _
      _ ≤ 1 := ht
  have h_eq : (fun ω ↦ 1 + t * X ω + 3 / 4 * (t * X ω) ^ 2)
      = fun ω ↦ 1 + t * X ω + 3 / 4 * t ^ 2 * X ω ^ 2 := by
    ext ω
    ring
  calc mgf X μ t = μ[fun ω ↦ exp (t * X ω)] := rfl
  _ ≤ μ[fun ω ↦ 1 + t * X ω + 3 / 4 * (t * X ω) ^ 2] := by
    refine integral_mono_ae (integrable_exp_mul_of_mem_Icc hm hIcc) ?_ hpt
    rw [h_eq]
    exact ((integrable_const _).add (hX.const_mul t)).add (hX2.const_mul _)
  _ = 1 + t * μ[X] + 3 / 4 * t ^ 2 * μ[fun ω ↦ X ω ^ 2] := by
    have h1 : Integrable (fun ω ↦ 1 + t * X ω) μ := (integrable_const _).add (hX.const_mul t)
    have h2 : Integrable (fun ω ↦ 3 / 4 * t ^ 2 * X ω ^ 2) μ := hX2.const_mul _
    rw [h_eq, integral_add h1 h2, integral_add (integrable_const _) (hX.const_mul t),
      integral_const, integral_const_mul, integral_const_mul]
    simp
  _ ≤ 1 + 3 / 4 * t ^ 2 * v := by
    rw [hc, mul_zero, add_zero]
    gcongr
    exact hv
  _ ≤ exp (3 / 4 * t ^ 2 * v) := by linarith [add_one_le_exp (3 / 4 * t ^ 2 * v)]
  _ = exp (3 * v / 2 * t ^ 2 / 2) := by congr 1; ring

/-- If `|X| ≤ M` almost surely, then `X - μ[X]` has a sub-exponential mgf with parameters
`(3 * Var[X] / 2, 2 * M)`. -/
lemma hasSubexponentialMGF_sub_integral_of_abs_le [IsProbabilityMeasure μ] {M : ℝ}
    (hm : AEMeasurable X μ) (hM : ∀ᵐ ω ∂μ, |X ω| ≤ M) :
    HasSubexponentialMGF (fun ω ↦ X ω - μ[X]) (3 * Var[X; μ] / 2) (2 * M) μ := by
  have hX : Integrable X μ :=
    Integrable.of_mem_Icc (-M) M hm (hM.mono fun ω h ↦ abs_le.1 h)
  have hEX : |μ[X]| ≤ M := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |X ω| ∂μ ≤ ∫ _, M ∂μ := integral_mono_ae hX.abs (integrable_const _) hM
      _ = M := by simp
  refine hasSubexponentialMGF_of_abs_le_of_integral_eq_zero (hm.sub_const _) ?_ ?_ ?_
  · filter_upwards [hM] with ω hω
    calc |X ω - μ[X]| ≤ |X ω| + |μ[X]| := abs_sub _ _
      _ ≤ M + M := add_le_add hω hEX
      _ = 2 * M := by ring
  · simp [integral_sub hX (integrable_const _)]
  · simp [variance_eq_integral hm]

end Bounded

section Martingale

variable [StandardBorelSpace Ω]

/-- If `X` is sub-exponential with parameters `(VX, b)` with respect to the restriction of `μ` to
a sub-sigma-algebra `m` and `Y` is conditionally sub-exponential with parameters `(VY, b)` with
respect to `m` and `μ` then `X + Y` is sub-exponential with parameters `(VX + VY, b)` with
respect to `μ`.

`HasSubexponentialMGF X VX b (μ.trim hm)` can be obtained from `HasSubexponentialMGF X VX b μ`
if `X` is `m`-measurable. See `HasSubexponentialMGF.trim`. -/
lemma HasSubexponentialMGF.add_of_hasCondSubexponentialMGF [IsFiniteMeasure μ]
    {Y : Ω → ℝ} {VX VY : ℝ} (hm : m ≤ mΩ)
    (hX : HasSubexponentialMGF X VX b (μ.trim hm))
    (hY : HasCondSubexponentialMGF m hm Y VY b μ) :
    HasSubexponentialMGF (X + Y) (VX + VY) b μ := by
  suffices HasSubexponentialMGF (fun p ↦ X p.1 + Y p.2) (VX + VY) b
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ) by
    have h_eq : X + Y = (fun p ↦ X p.1 + Y p.2) ∘ Function.diag := rfl
    rw [h_eq]
    refine HasSubexponentialMGF.of_map ?_ this
    exact @Measurable.aemeasurable _ _ _ (m.prod mΩ) _ _
      ((measurable_id'' hm).prodMk measurable_id)
  rw [hasSubexponentialMGF_iff_kernel] at hX ⊢
  have hY' : Kernel.HasSubexponentialMGF Y VY b (condExpKernel μ m)
      (Kernel.const Unit (μ.trim hm) ∘ₘ Measure.dirac ()) := by simpa
  convert! hX.add_comp hY'
  ext
  rw [Kernel.const_apply, ← Measure.compProd, compProd_trim_condExpKernel]

variable {Y : ℕ → Ω → ℝ} {VY : ℕ → ℝ} {ℱ : Filtration ℕ mΩ}

/-- Let `Y` be a random process adapted to a filtration `ℱ`, such that for all `i : ℕ`,
`Y i` is conditionally sub-exponential with parameters `(VY i, b)` with respect to `ℱ (i - 1)`.
In particular, `n ↦ ∑ i ∈ range n, Y i` is a martingale.
Then the sum `∑ i ∈ range n, Y i` is sub-exponential with parameters
`(∑ i ∈ range n, VY i, b)`. -/
lemma HasSubexponentialMGF.sum_of_hasCondSubexponentialMGF [IsZeroOrProbabilityMeasure μ]
    (h_adapted : Adapted ℱ Y) (h0 : HasSubexponentialMGF (Y 0) (VY 0) b μ) (n : ℕ)
    (h_sub : ∀ i < n - 1,
      HasCondSubexponentialMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (VY (i + 1)) b μ) :
    HasSubexponentialMGF (fun ω ↦ ∑ i ∈ Finset.range n, Y i ω) (∑ i ∈ Finset.range n, VY i)
      b μ := by
  induction n with
  | zero => simp
  | succ n hn =>
    induction n with
    | zero => simp [h0]
    | succ n =>
      specialize hn fun i hi ↦ h_sub i (by lia)
      simp_rw [Finset.sum_range_succ _ (n + 1)]
      refine HasSubexponentialMGF.add_of_hasCondSubexponentialMGF (ℱ.le n) ?_ (h_sub n (by lia))
      refine HasSubexponentialMGF.trim (ℱ.le n) ?_ hn
      refine Finset.measurable_fun_sum (Finset.range (n + 1)) fun m hm ↦
        (h_adapted m).mono (ℱ.mono ?_) le_rfl
      simp only [Finset.mem_range] at hm
      lia

/-- **Bernstein-type inequality** for sums of conditionally sub-exponential random variables. -/
lemma measure_sum_ge_le_of_hasCondSubexponentialMGF [IsZeroOrProbabilityMeasure μ]
    (h_adapted : Adapted ℱ Y) (h0 : HasSubexponentialMGF (Y 0) (VY 0) b μ) (n : ℕ)
    (h_sub : ∀ i < n - 1,
      HasCondSubexponentialMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (VY (i + 1)) b μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ Finset.range n, Y i ω}
      ≤ exp (-min (t ^ 2 / (2 * ∑ i ∈ Finset.range n, VY i)) (t / (2 * b))) :=
  (HasSubexponentialMGF.sum_of_hasCondSubexponentialMGF h_adapted h0 n h_sub).measure_ge_le ht

end Martingale

end ProbabilityTheory
