/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Probability.Kernel.Composition.RadonNikodym

import LeanMachineLearning.ForMathlib.Probability.Kernel.Composition.Lemmas
import LeanMachineLearning.ForMathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

/-!
# The Kullback–Leibler divergence of composition-products, in integrated form

The chain rule `klDiv_compProd_eq_add` expresses the conditional divergence as
`klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`. When the target space of the kernels is countably generated (or the
source is countable), the function `a ↦ klDiv (κ a) (η a)` is measurable
(`measurable_klDiv_kernel`) and the conditional divergence is its integral:

* `klDiv_compProd_right_eq_lintegral`: `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ`.
* `klDiv_compProd_eq_add_lintegral`:
  `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + ∫⁻ a, klDiv (κ a) (η a) ∂μ`.

We also record the data processing inequality for the two projections
(`klDiv_le_compProd`, `klDiv_comp_le_compProd`) and the invariance of the divergence under
measurable embeddings (`klDiv_map_measurableEmbedding`) and measurable equivalences
(`klDiv_map_measurableEquiv`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

/-- The Kullback–Leibler divergence is invariant under measurable embeddings. -/
lemma klDiv_map_measurableEmbedding (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : α → β} (hf : MeasurableEmbedding f) :
    klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν hf.measurable) ?_
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [μ.eq_zero_of_isEmpty, ν.eq_zero_of_isEmpty]
  have h := klDiv_map_le (μ.map f) (ν.map f) hf.measurable_invFun
  rwa [Measure.map_map hf.measurable_invFun hf.measurable,
    Measure.map_map hf.measurable_invFun hf.measurable, hf.leftInverse_invFun.comp_eq_id,
    Measure.map_id, Measure.map_id] at h

/-- The Kullback–Leibler divergence is invariant under measurable equivalences. -/
lemma klDiv_map_measurableEquiv (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : α ≃ᵐ β) :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν :=
  klDiv_map_measurableEmbedding μ ν e.measurableEmbedding

/-- **Data processing inequality** for the first projection: for Markov kernels `κ` and `η`,
`μ` and `ν` are the images of `μ ⊗ₘ κ` and `ν ⊗ₘ η` under `Prod.fst`, hence
`klDiv μ ν ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η)`. -/
lemma klDiv_le_compProd (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    klDiv μ ν ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  conv_lhs => rw [← Measure.fst_compProd μ κ, ← Measure.fst_compProd ν η]
  rw [Measure.fst, Measure.fst]
  exact klDiv_map_le _ _ measurable_fst

/-- **Data processing inequality** for the second projection: `κ ∘ₘ μ` and `η ∘ₘ ν` are the images
of `μ ⊗ₘ κ` and `ν ⊗ₘ η` under `Prod.snd`, hence
`klDiv (κ ∘ₘ μ) (η ∘ₘ ν) ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η)`. -/
lemma klDiv_comp_le_compProd (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (κ ∘ₘ μ) (η ∘ₘ ν) ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  rw [← Measure.snd_compProd μ κ, ← Measure.snd_compProd ν η, Measure.snd, Measure.snd]
  exact klDiv_map_le _ _ measurable_snd

section kernel

variable [MeasurableSpace.CountableOrCountablyGenerated α β] {κ η : Kernel α β} [IsFiniteKernel κ]
  [IsFiniteKernel η]

/-- For finite kernels with countably generated target, `a ↦ klDiv (κ a) (η a)` is measurable. -/
lemma measurable_klDiv_kernel (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable fun a ↦ klDiv (κ a) (η a) := by
  classical
  have h_meas : Measurable fun a ↦
      ∫⁻ b, ENNReal.ofReal (klFun (κ.rnDeriv η a b).toReal) ∂(η a) :=
    Measurable.lintegral_kernel_prod_right
      ((measurable_klFun.comp (Kernel.measurable_rnDeriv κ η).ennreal_toReal).ennreal_ofReal)
  have h_eq : ∀ a, klDiv (κ a) (η a) = if κ a ≪ η a then
      ∫⁻ b, ENNReal.ofReal (klFun (κ.rnDeriv η a b).toReal) ∂(η a) else ∞ := by
    intro a
    split_ifs with hac
    · rw [klDiv_eq_lintegral_klFun_of_ac hac]
      refine lintegral_congr_ae ?_
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with b hb
      rw [hb]
    · exact klDiv_of_not_ac hac
  simp_rw [h_eq]
  exact Measurable.ite (Kernel.measurableSet_absolutelyContinuous κ η) h_meas measurable_const

/-- Integrated form of the conditional Kullback–Leibler divergence:
`klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ`. -/
lemma klDiv_compProd_right_eq_lintegral (μ : Measure α) [IsFiniteMeasure μ] (κ η : Kernel α β)
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  by_cases h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η
  · rw [klDiv_eq_lintegral_klFun_of_ac h_ac]
    have h_ae := Measure.absolutelyContinuous_compProd_right_iff.mp h_ac
    calc ∫⁻ p, ENNReal.ofReal (klFun ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal) ∂(μ ⊗ₘ η)
        = ∫⁻ p, ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal) ∂(μ ⊗ₘ η) := by
          refine lintegral_congr_ae ?_
          filter_upwards [rnDeriv_measure_compProd_right μ κ η] with p hp
          rw [hp]
      _ = ∫⁻ a, ∫⁻ b, ENNReal.ofReal (klFun (κ.rnDeriv η a b).toReal) ∂(η a) ∂μ :=
          Measure.lintegral_compProd
            ((measurable_klFun.comp (Kernel.measurable_rnDeriv κ η).ennreal_toReal).ennreal_ofReal)
      _ = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [h_ae] with a ha
          rw [klDiv_eq_lintegral_klFun_of_ac ha]
          refine lintegral_congr_ae ?_
          filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with b hb
          rw [hb]
  · rw [klDiv_of_not_ac h_ac, Measure.absolutelyContinuous_compProd_right_iff, ae_iff] at *
    symm
    rw [eq_top_iff]
    calc (∞ : ℝ≥0∞) = ∫⁻ _ in {a | ¬ κ a ≪ η a}, ∞ ∂μ := by
          rw [setLIntegral_const, ENNReal.top_mul h_ac]
      _ ≤ ∫⁻ a in {a | ¬ κ a ≪ η a}, klDiv (κ a) (η a) ∂μ :=
          setLIntegral_mono' (Kernel.measurableSet_absolutelyContinuous κ η).compl
            fun a ha ↦ by rw [klDiv_of_not_ac ha]
      _ ≤ ∫⁻ a, klDiv (κ a) (η a) ∂μ := setLIntegral_le_lintegral _ _

/-- **Chain rule** for the Kullback–Leibler divergence, in integrated form:
`klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + ∫⁻ a, klDiv (κ a) (η a) ∂μ`. -/
lemma klDiv_compProd_eq_add_lintegral (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  rw [klDiv_compProd_eq_add, klDiv_compProd_right_eq_lintegral]

omit [MeasurableSpace.CountableOrCountablyGenerated α β] in
/-- `klDiv_compProd_left` for a kernel which is only a probability measure on a measurable set of
full measure for both `μ` and `ν`. -/
lemma klDiv_compProd_left_of_ae [Nonempty β] (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ : Kernel α β) [IsSFiniteKernel κ] {S : Set α} (hS : MeasurableSet S)
    (hκ : ∀ a ∈ S, IsProbabilityMeasure (κ a)) (hμ : ∀ᵐ a ∂μ, a ∈ S) (hν : ∀ᵐ a ∂ν, a ∈ S) :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν := by
  classical
  obtain ⟨b⟩ := ‹Nonempty β›
  let κ' : Kernel α β := Kernel.piecewise hS κ (Kernel.const α (Measure.dirac b))
  have hκ' : IsMarkovKernel κ' := ⟨fun a ↦ by
    by_cases ha : a ∈ S
    · simp only [κ', Kernel.piecewise_apply, ha, ite_true]
      exact hκ a ha
    · simp only [κ', Kernel.piecewise_apply, ha, ite_false, Kernel.const_apply]
      infer_instance⟩
  have hμκ : μ ⊗ₘ κ = μ ⊗ₘ κ' := Measure.compProd_congr (by
    filter_upwards [hμ] with a ha
    simp [κ', Kernel.piecewise_apply, ha])
  have hνκ : ν ⊗ₘ κ = ν ⊗ₘ κ' := Measure.compProd_congr (by
    filter_upwards [hν] with a ha
    simp [κ', Kernel.piecewise_apply, ha])
  rw [hμκ, hνκ, klDiv_compProd_left]

end kernel

end InformationTheory
