/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.ProductMeasure

/-! # Lemmas about `HasLaw`

## Main statements

* `hasLaw_of_forall_hasLaw_cond`: a random variable which has law `μ` conditionally on each atom
  of positive probability of a countable measurable partition has law `μ`.
* `hasLaw_of_forall_eventually_eq`: if random variables with law `μ` on a product space converge
  coordinatewise and eventually constantly to `Y'`, then `Y'` has law `μ`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {P : Measure Ω}

section Prod

variable {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}

lemma hasLaw_fst_prod (μ : Measure 𝓧) (ν : Measure 𝓨) [IsProbabilityMeasure ν] :
    HasLaw Prod.fst μ (μ.prod ν) :=
  measurePreserving_fst.hasLaw

lemma hasLaw_snd_prod (μ : Measure 𝓧) [IsProbabilityMeasure μ] (ν : Measure 𝓨) [SFinite ν] :
    HasLaw Prod.snd ν (μ.prod ν) :=
  measurePreserving_snd.hasLaw

end Prod

lemma hasLaw_eval_infinitePi {ι : Type*} {𝓧 : ι → Type*} {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)}
    (μ : (i : ι) → Measure (𝓧 i)) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    HasLaw (Function.eval i) (μ i) (Measure.infinitePi μ) :=
  (measurePreserving_eval_infinitePi μ i).hasLaw

section Cond

variable {ι : Type*} [Countable ι] {mι : MeasurableSpace ι} [MeasurableSingletonClass ι]

/-- If a random variable has law `μ` conditionally on each atom of positive probability of a
countable measurable partition, then it has law `μ`. -/
lemma hasLaw_of_forall_hasLaw_cond [IsProbabilityMeasure P] {g : Ω → ι} (hg : Measurable g)
    {X : Ω → 𝓧} (hX : AEMeasurable X P) {μ : Measure 𝓧}
    (h : ∀ i, P (g ⁻¹' {i}) ≠ 0 → HasLaw X μ P[|g ⁻¹' {i}]) :
    HasLaw X μ P where
  aemeasurable := hX
  map_eq := by
    have h_eq i : (P (g ⁻¹' {i}) • P[|g ⁻¹' {i}]).map X = P (g ⁻¹' {i}) • μ := by
      by_cases hi : P (g ⁻¹' {i}) = 0
      · simp [hi]
      · rw [Measure.map_smul _ (h i hi).aemeasurable, (h i hi).map_eq]
    have h_univ : ∑' i, P (g ⁻¹' {i}) = 1 := by
      rw [← measure_iUnion (fun i j hij ↦ (Set.disjoint_singleton.2 hij).preimage g)
        fun i ↦ hg (.singleton i), ← Set.preimage_iUnion, Set.iUnion_singleton_eq_range,
        Set.range_id', Set.preimage_univ, measure_univ]
    rw [← Measure.sum_meas_smul_cond_fiber hg P] at hX ⊢
    simp_rw [Measure.map_sum hX, h_eq]
    ext s hs
    simp_rw [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, ENNReal.tsum_mul_right,
      h_univ, one_mul]

end Cond

section Pi

variable {ι : Type*} {𝓧 : ι → Type*} [∀ i, MeasurableSpace (𝓧 i)]

/-- Let `Y n : Ω → Π i, 𝓧 i` be random variables with law `μ`, indexed by a countably generated
filter `L`. If for every `i`, for almost every `ω`, `Y n ω i` is eventually equal to `Y' ω i`
along `L`, then `Y'` also has law `μ`. -/
lemma hasLaw_of_forall_eventually_eq [IsFiniteMeasure P] {κ : Type*} {L : Filter κ} [L.NeBot]
    [L.IsCountablyGenerated] {μ : Measure (Π i, 𝓧 i)} {Y : κ → Ω → Π i, 𝓧 i} {Y' : Ω → Π i, 𝓧 i}
    (hY : ∀ n, Measurable (Y n)) (hY' : AEMeasurable Y' P)
    (h_law : ∀ n, HasLaw (Y n) μ P) (h_lim : ∀ i, ∀ᵐ ω ∂P, ∀ᶠ n in L, Y n ω i = Y' ω i) :
    HasLaw Y' μ P := by
  -- we replace `Y'` by a measurable function almost everywhere equal to it
  refine HasLaw.congr ?_ hY'.ae_eq_mk
  have hY'm := hY'.measurable_mk
  have h_lim' i : ∀ᵐ ω ∂P, ∀ᶠ n in L, Y n ω i = hY'.mk Y' ω i := by
    filter_upwards [h_lim i, hY'.ae_eq_mk] with ω hω h_eq
    rwa [← h_eq]
  refine ⟨hY'm.aemeasurable, ?_⟩
  -- two finite measures which agree on measurable cylinders are equal
  refine ext_of_generate_finite (measurableCylinders _) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (fun s hs ↦ ?_) ?_
  · obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).1 hs
    rw [Measure.map_apply hY'm (hS.cylinder _)]
    have h_tendsto : Tendsto (fun n ↦ P (Y n ⁻¹' cylinder I S)) L
        (𝓝 (P (hY'.mk Y' ⁻¹' cylinder I S))) := by
      refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure L
        ((hS.cylinder _).preimage hY'm) (fun n ↦ (hS.cylinder _).preimage (hY n)) ?_
      filter_upwards [(eventually_all_finset I).2 fun i _ ↦ h_lim' i] with ω hω
      filter_upwards [(eventually_all_finset I).2 hω] with n hn
      simp only [Set.mem_preimage, mem_cylinder]
      have : I.restrict (Y n ω) = I.restrict (hY'.mk Y' ω) := funext fun i ↦ hn i i.2
      rw [this]
    have h_const : (fun n ↦ P (Y n ⁻¹' cylinder I S)) = fun _ ↦ μ (cylinder I S) := by
      funext n
      rw [← Measure.map_apply (hY n) (hS.cylinder _), (h_law n).map_eq]
    rw [h_const] at h_tendsto
    exact tendsto_nhds_unique h_tendsto tendsto_const_nhds
  · obtain ⟨n⟩ := L.nonempty_of_neBot
    rw [Measure.map_apply hY'm MeasurableSet.univ, Set.preimage_univ, ← (h_law n).map_eq,
      Measure.map_apply (hY n) MeasurableSet.univ, Set.preimage_univ]

end Pi

end ProbabilityTheory
