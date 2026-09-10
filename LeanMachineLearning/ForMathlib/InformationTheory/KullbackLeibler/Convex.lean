/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.ChainRule

/-!
# Convexity of the Kullback–Leibler divergence for mixtures

For finite measures `μ i`, `ν i` on `Ω` and weights `c i ≥ 0`, the Kullback–Leibler divergence is
convex in the pair of measures:
`klDiv (∑ i, c i • μ i) (∑ i, c i • ν i) ≤ ∑ i, c i * klDiv (μ i) (ν i)`.

The proof combines the data processing inequality with the integral form of the conditional
divergence. Let `β := ∑ i, c i • δ i` be the measure with weights `c` on the index set and let
`κ`, `η` be the kernels from the index set given by `μ` and `ν`. The two mixtures are the
compositions `κ ∘ₘ β` and `η ∘ₘ β`, that is, the images of `β ⊗ₘ κ` and `β ⊗ₘ η` under the second
projection, so the data processing inequality bounds `klDiv (κ ∘ₘ β) (η ∘ₘ β)` by the conditional
divergence `klDiv (β ⊗ₘ κ) (β ⊗ₘ η)`, which is `∫⁻ i, klDiv (κ i) (η i) ∂β`.

## Main statements

* `InformationTheory.klDiv_finsetSum_smul_le`,
  `InformationTheory.klDiv_sum_smul_le`: convexity of `klDiv` in the pair of measures,
  for mixtures indexed by a `Finset` and by a `Fintype`;
* `InformationTheory.klDiv_smul_add_smul_le`: the same statement for two-point mixtures;
* `InformationTheory.klDiv_finsetSum_smul_left_le`, `InformationTheory.klDiv_sum_smul_left_le`:
  convexity of `klDiv` in its first argument;
* `InformationTheory.klDiv_finsetSum_smul_right_le`, `InformationTheory.klDiv_sum_smul_right_le`:
  convexity of `klDiv` in its second argument.
-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace InformationTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω}

section pair

variable {μ ν : ι → Measure Ω}

/-- **Convexity of the Kullback–Leibler divergence in the pair of measures**, for a mixture
indexed by a `Finset`: for finite measures `μ i`, `ν i` and weights `c i ≥ 0`,
`klDiv (∑ i ∈ s, c i • μ i) (∑ i ∈ s, c i • ν i) ≤ ∑ i ∈ s, c i * klDiv (μ i) (ν i)`.
Weights summing to `1` give the convexity of `klDiv`; no such hypothesis is needed here, since
`klDiv` is positively homogeneous. -/
lemma klDiv_finsetSum_smul_le [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, IsFiniteMeasure (ν i)] (s : Finset ι) (c : ι → ℝ≥0) :
    klDiv (∑ i ∈ s, (c i : ℝ≥0∞) • μ i) (∑ i ∈ s, (c i : ℝ≥0∞) • ν i)
      ≤ ∑ i ∈ s, (c i : ℝ≥0∞) * klDiv (μ i) (ν i) := by
  classical
  -- the index set, with the discrete measurable structure
  let _ : MeasurableSpace s := ⊤
  have : MeasurableSingletonClass s := ⟨fun _ ↦ trivial⟩
  -- the measure with weights `c` on the index set
  set β : Measure s := ∑ i : s, (c i : ℝ≥0∞) • Measure.dirac i with hβ_def
  have hβ_lintegral (f : s → ℝ≥0∞) : ∫⁻ i, f i ∂β = ∑ i : s, (c i : ℝ≥0∞) * f i := by
    simp only [hβ_def, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
      smul_eq_mul]
  have : IsFiniteMeasure β := ⟨by
    simpa using (hβ_lintegral 1).trans_lt (ENNReal.sum_lt_top.mpr fun i _ ↦ by simp)⟩
  -- the kernels from the index set given by the two families of measures
  set κ : Kernel s Ω := Kernel.ofFunOfCountable fun i ↦ μ i
  set η : Kernel s Ω := Kernel.ofFunOfCountable fun i ↦ ν i
  have hκ_apply (i : s) : κ i = μ i := rfl
  have hη_apply (i : s) : η i = ν i := rfl
  have h_fin (ρ : Kernel s Ω) (ρ' : ι → Measure Ω) [∀ i, IsFiniteMeasure (ρ' i)]
      (hρ : ∀ i : s, ρ i = ρ' i) : IsFiniteKernel ρ :=
    ⟨∑ i : s, ρ' i univ, ENNReal.sum_lt_top.mpr fun i _ ↦ measure_lt_top _ _, fun i ↦ by
      rw [hρ i]
      exact Finset.single_le_sum (f := fun j : s ↦ ρ' j univ) (fun _ _ ↦ bot_le)
        (Finset.mem_univ i)⟩
  have : IsFiniteKernel κ := h_fin κ μ hκ_apply
  have : IsFiniteKernel η := h_fin η ν hη_apply
  -- composing a kernel with `β` gives the corresponding mixture
  have h_comp (ρ : Kernel s Ω) (ρ' : ι → Measure Ω) (hρ : ∀ i : s, ρ i = ρ' i) :
      ρ ∘ₘ β = ∑ i ∈ s, (c i : ℝ≥0∞) • ρ' i := by
    ext t ht
    rw [Measure.bind_apply ht ρ.aemeasurable, hβ_lintegral, Measure.finsetSum_apply,
      ← Finset.sum_coe_sort s]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hρ i, Measure.smul_apply, smul_eq_mul]
  calc klDiv (∑ i ∈ s, (c i : ℝ≥0∞) • μ i) (∑ i ∈ s, (c i : ℝ≥0∞) • ν i)
  _ = klDiv (κ ∘ₘ β) (η ∘ₘ β) := by rw [h_comp κ μ hκ_apply, h_comp η ν hη_apply]
  -- data processing inequality for the second projection
  _ ≤ klDiv (β ⊗ₘ κ) (β ⊗ₘ η) := klDiv_comp_le_compProd β β κ η
  -- integral form of the conditional divergence
  _ = ∫⁻ i, klDiv (κ i) (η i) ∂β := klDiv_compProd_right_eq_lintegral β κ η
  _ = ∑ i ∈ s, (c i : ℝ≥0∞) * klDiv (μ i) (ν i) := by
      rw [hβ_lintegral]
      simp_rw [hκ_apply, hη_apply]
      exact Finset.sum_coe_sort s fun i ↦ (c i : ℝ≥0∞) * klDiv (μ i) (ν i)

/-- **Convexity of the Kullback–Leibler divergence in the pair of measures**: for finite measures
`μ i`, `ν i` and weights `c i ≥ 0`,
`klDiv (∑ i, c i • μ i) (∑ i, c i • ν i) ≤ ∑ i, c i * klDiv (μ i) (ν i)`. -/
lemma klDiv_sum_smul_le [Fintype ι] [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, IsFiniteMeasure (ν i)] (c : ι → ℝ≥0) :
    klDiv (∑ i, (c i : ℝ≥0∞) • μ i) (∑ i, (c i : ℝ≥0∞) • ν i)
      ≤ ∑ i, (c i : ℝ≥0∞) * klDiv (μ i) (ν i) :=
  klDiv_finsetSum_smul_le Finset.univ c

/-- **Convexity of the Kullback–Leibler divergence in the pair of measures**, for a two-point
mixture: for finite measures `μ₀, μ₁, ν₀, ν₁` and weights `a, b ≥ 0`,
`klDiv (a • μ₀ + b • μ₁) (a • ν₀ + b • ν₁) ≤ a * klDiv μ₀ ν₀ + b * klDiv μ₁ ν₁`. -/
lemma klDiv_smul_add_smul_le (μ₀ μ₁ ν₀ ν₁ : Measure Ω) [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁]
    [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] (a b : ℝ≥0) :
    klDiv ((a : ℝ≥0∞) • μ₀ + (b : ℝ≥0∞) • μ₁) ((a : ℝ≥0∞) • ν₀ + (b : ℝ≥0∞) • ν₁)
      ≤ (a : ℝ≥0∞) * klDiv μ₀ ν₀ + (b : ℝ≥0∞) * klDiv μ₁ ν₁ := by
  have : ∀ x : Bool, IsFiniteMeasure (bif x then μ₁ else μ₀) := fun x ↦ by
    cases x <;> assumption
  have : ∀ x : Bool, IsFiniteMeasure (bif x then ν₁ else ν₀) := fun x ↦ by
    cases x <;> assumption
  have h := klDiv_sum_smul_le (μ := fun x ↦ bif x then μ₁ else μ₀)
    (ν := fun x ↦ bif x then ν₁ else ν₀) (fun x ↦ bif x then b else a)
  simpa [Fintype.sum_bool, add_comm] using h

end pair

section firstArgument

variable {μ : ι → Measure Ω} {ν : Measure Ω} {c : ι → ℝ≥0}

/-- **Convexity of the Kullback–Leibler divergence in its first argument**, for a finite mixture
indexed by a `Finset`: for finite measures `μ i`, `ν` and nonnegative weights `c i` summing to
`1`, `klDiv (∑ i ∈ s, c i • μ i) ν ≤ ∑ i ∈ s, c i * klDiv (μ i) ν`. -/
lemma klDiv_finsetSum_smul_left_le [∀ i, IsFiniteMeasure (μ i)] [IsFiniteMeasure ν]
    {s : Finset ι} (hc : ∑ i ∈ s, c i = 1) :
    klDiv (∑ i ∈ s, (c i : ℝ≥0∞) • μ i) ν ≤ ∑ i ∈ s, (c i : ℝ≥0∞) * klDiv (μ i) ν := by
  have h := klDiv_finsetSum_smul_le (μ := μ) (ν := fun _ ↦ ν) s c
  rwa [← Finset.sum_smul, ← ENNReal.ofNNReal_finsetSum, hc, ENNReal.coe_one, one_smul] at h

/-- **Convexity of the Kullback–Leibler divergence in its first argument**: for finite measures
`μ i`, `ν` and nonnegative weights `c i` summing to `1`,
`klDiv (∑ i, c i • μ i) ν ≤ ∑ i, c i * klDiv (μ i) ν`. -/
lemma klDiv_sum_smul_left_le [Fintype ι] [∀ i, IsFiniteMeasure (μ i)] [IsFiniteMeasure ν]
    (hc : ∑ i, c i = 1) :
    klDiv (∑ i, (c i : ℝ≥0∞) • μ i) ν ≤ ∑ i, (c i : ℝ≥0∞) * klDiv (μ i) ν :=
  klDiv_finsetSum_smul_left_le hc

end firstArgument

section secondArgument

variable {μ : Measure Ω} {ν : ι → Measure Ω} {c : ι → ℝ≥0}

/-- **Convexity of the Kullback–Leibler divergence in its second argument**, for a finite mixture
indexed by a `Finset`: for finite measures `μ`, `ν i` and nonnegative weights `c i` summing to
`1`, `klDiv μ (∑ i ∈ s, c i • ν i) ≤ ∑ i ∈ s, c i * klDiv μ (ν i)`. -/
lemma klDiv_finsetSum_smul_right_le [IsFiniteMeasure μ] [∀ i, IsFiniteMeasure (ν i)]
    {s : Finset ι} (hc : ∑ i ∈ s, c i = 1) :
    klDiv μ (∑ i ∈ s, (c i : ℝ≥0∞) • ν i) ≤ ∑ i ∈ s, (c i : ℝ≥0∞) * klDiv μ (ν i) := by
  have h := klDiv_finsetSum_smul_le (μ := fun _ ↦ μ) (ν := ν) s c
  rwa [← Finset.sum_smul, ← ENNReal.ofNNReal_finsetSum, hc, ENNReal.coe_one, one_smul] at h

/-- **Convexity of the Kullback–Leibler divergence in its second argument**: for finite measures
`μ`, `ν i` and nonnegative weights `c i` summing to `1`,
`klDiv μ (∑ i, c i • ν i) ≤ ∑ i, c i * klDiv μ (ν i)`. -/
lemma klDiv_sum_smul_right_le [Fintype ι] [IsFiniteMeasure μ] [∀ i, IsFiniteMeasure (ν i)]
    (hc : ∑ i, c i = 1) :
    klDiv μ (∑ i, (c i : ℝ≥0∞) • ν i) ≤ ∑ i, (c i : ℝ≥0∞) * klDiv μ (ν i) :=
  klDiv_finsetSum_smul_right_le hc

end secondArgument

end InformationTheory
