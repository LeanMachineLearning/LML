/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.DataProcessing
public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.Restrict
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.Probability.Martingale.Convergence

/-!
# The Kullback–Leibler divergence along a generating sequence of maps

Let `μ, ν` be finite measures on `α` and `g n : α → β n` be measurable maps whose σ-algebras
`comap (g n)` increase to the σ-algebra of `α` (for instance the projections of a sequence space
on its first `n` coordinates). Then the divergence of `μ` and `ν` is the supremum of the
divergences of their images by the `g n`:
`klDiv μ ν = ⨆ n, klDiv (μ.map (g n)) (ν.map (g n))` (`klDiv_eq_iSup_map`).

The inequality `≥` is the data-processing inequality. For `≤`, if `μ ≪ ν` the divergences of
the images are the integrals of `klFun` of the conditional expectations of the density `∂μ/∂ν`
given `comap (g n)` (`klDiv_map_eq_lintegral_klFun_condExp`), which converge almost everywhere
to the density by Lévy's upward theorem, and Fatou's lemma concludes. If `μ` is not absolutely
continuous with respect to `ν`, a set `A` with `ν A = 0 < μ A` is approximated by
`comap (g n)`-measurable sets `B n` (again by Lévy's upward theorem, applied to the indicator of
`A` under `μ + ν`), and the lower bound `μ B * log (μ B / ν B) + ν B - μ B ≤ klDiv` on `B n`
shows that the divergences of the images tend to infinity.

The sequence space case is `MeasurableSpace.iSup_comap_restrictFin`: the σ-algebras of the
projections on the first `n` coordinates generate the product σ-algebra of `ℕ → E`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace InformationTheory

variable {α : Type*} {m0 : MeasurableSpace α} {μ ν : Measure α} [IsFiniteMeasure μ]
  [IsFiniteMeasure ν]

/-- **The divergence along a generating sequence of maps.** If the σ-algebras `comap (g n)` of
measurable maps `g n : α → β n` increase to the σ-algebra of `α`, then the divergence of two
finite measures is the supremum of the divergences of their images by the `g n`. -/
lemma klDiv_eq_iSup_map {β : ℕ → Type*} [mβ : ∀ n, MeasurableSpace (β n)] {g : ∀ n, α → β n}
    (hg : ∀ n, Measurable (g n))
    (hmono : Monotone fun n ↦ (mβ n).comap (g n))
    (hsup : ⨆ n, (mβ n).comap (g n) = m0) :
    klDiv μ ν = ⨆ n, klDiv (μ.map (g n)) (ν.map (g n)) := by
  let ℱ : Filtration ℕ m0 := ⟨fun n ↦ (mβ n).comap (g n), hmono, fun n ↦ (hg n).comap_le⟩
  have hℱ : ∀ n, ℱ n = (mβ n).comap (g n) := fun _ ↦ rfl
  have hℱ_sup : (⨆ n, ℱ n) = m0 := hsup
  refine le_antisymm ?_ (iSup_le fun n ↦ klDiv_map_le μ ν (hg n))
  by_cases hμν : μ ≪ ν
  · -- Lévy's upward theorem and Fatou's lemma
    let f : α → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
    have hf_int : Integrable f ν := Measure.integrable_toReal_rnDeriv
    have hf_meas : StronglyMeasurable[⨆ n, ℱ n] f :=
      (Measure.measurable_rnDeriv μ ν).ennreal_toReal.stronglyMeasurable.mono hℱ_sup.symm.le
    have hlim := hf_int.tendsto_ae_condExp (ℱ := ℱ) hf_meas
    have hmeas : ∀ n, Measurable fun x ↦ ENNReal.ofReal (klFun ((ν[f | ℱ n]) x)) := fun n ↦
      (measurable_klFun.comp
        ((stronglyMeasurable_condExp (m := ℱ n)).measurable.mono (ℱ.le n) le_rfl)).ennreal_ofReal
    calc klDiv μ ν = ∫⁻ x, ENNReal.ofReal (klFun (f x)) ∂ν := klDiv_eq_lintegral_klFun_of_ac hμν
      _ = ∫⁻ x, liminf (fun n ↦ ENNReal.ofReal (klFun ((ν[f | ℱ n]) x))) atTop ∂ν := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlim] with x hx
          exact ((ENNReal.continuous_ofReal.tendsto _).comp
            ((continuous_klFun.tendsto _).comp hx)).liminf_eq.symm
      _ ≤ liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (klFun ((ν[f | ℱ n]) x)) ∂ν) atTop :=
          lintegral_liminf_le hmeas
      _ ≤ ⨆ n, ∫⁻ x, ENNReal.ofReal (klFun ((ν[f | ℱ n]) x)) ∂ν :=
          le_trans liminf_le_limsup limsup_le_iSup
      _ = ⨆ n, klDiv (μ.map (g n)) (ν.map (g n)) :=
          iSup_congr fun n ↦ (klDiv_map_eq_lintegral_klFun_condExp hμν (hg n)).symm
  · -- the divergences of the images tend to infinity
    rw [klDiv_of_not_ac hμν, top_le_iff, iSup_eq_top]
    obtain ⟨A, hA, hνA, hμA⟩ : ∃ A, MeasurableSet A ∧ ν A = 0 ∧ μ A ≠ 0 := by
      by_contra! h
      exact hμν (Measure.AbsolutelyContinuous.mk fun A hA hνA ↦ h A hA hνA)
    -- approximation of `A` by `comap (g n)`-measurable sets, by Lévy's upward theorem
    let ρ : Measure α := μ + ν
    let φ : α → ℝ := A.indicator fun _ ↦ (1 : ℝ)
    have hφ_int : Integrable φ ρ := (integrable_const (1 : ℝ)).indicator hA
    have hφ_meas : StronglyMeasurable[⨆ n, ℱ n] φ :=
      (measurable_const.indicator hA).stronglyMeasurable.mono hℱ_sup.symm.le
    have hlim := hφ_int.tendsto_ae_condExp (ℱ := ℱ) hφ_meas
    set B : ℕ → Set α := fun n ↦ {x | (2⁻¹ : ℝ) < (ρ[φ | ℱ n]) x} with hB
    have hB_meas : ∀ n, MeasurableSet[ℱ n] (B n) := fun n ↦
      (stronglyMeasurable_condExp (m := ℱ n)).measurable measurableSet_Ioi
    have hB_meas0 : ∀ n, MeasurableSet (B n) := fun n ↦ ℱ.le n _ (hB_meas n)
    have hB_lim : ∀ᵐ x ∂ρ, ∀ᶠ n in atTop, x ∈ B n ↔ x ∈ A := by
      filter_upwards [hlim] with x hx
      by_cases hxA : x ∈ A
      · have h1 : Tendsto (fun n ↦ (ρ[φ | ℱ n]) x) atTop (𝓝 1) := by simpa [φ, hxA] using hx
        filter_upwards [h1.eventually (lt_mem_nhds (by norm_num : (2⁻¹ : ℝ) < 1))] with n hn
        simp [hB, hn, hxA]
      · have h0 : Tendsto (fun n ↦ (ρ[φ | ℱ n]) x) atTop (𝓝 0) := by simpa [φ, hxA] using hx
        filter_upwards [h0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2⁻¹))] with n hn
        simp [hB, hxA, hn.le]
    have hμB : Tendsto (fun n ↦ μ (B n)) atTop (𝓝 (μ A)) :=
      tendsto_measure_of_ae_tendsto_indicator atTop hA hB_meas0 MeasurableSet.univ
        (measure_ne_top μ _) (Eventually.of_forall fun _ ↦ Set.subset_univ _)
        (ae_add_measure_iff.1 hB_lim).1
    have hνB : Tendsto (fun n ↦ ν (B n)) atTop (𝓝 0) := by
      rw [← hνA]
      exact tendsto_measure_of_ae_tendsto_indicator atTop hA hB_meas0 MeasurableSet.univ
        (measure_ne_top ν _) (Eventually.of_forall fun _ ↦ Set.subset_univ _)
        (ae_add_measure_iff.1 hB_lim).2
    -- lower bounds on the divergences of the images
    have hBC : ∀ n, ∃ C : Set (β n), MeasurableSet C ∧ g n ⁻¹' C = B n := fun n ↦
      MeasurableSpace.measurableSet_comap.1 (hB_meas n)
    have hkey n : ENNReal.ofReal (μ.real (B n) * Real.log (μ.real (B n) / ν.real (B n)) +
        ν.real (B n) - μ.real (B n)) ≤ klDiv (μ.map (g n)) (ν.map (g n)) := by
      obtain ⟨C, hC, hCB⟩ := hBC n
      refine le_trans ?_ (klDiv_restrict_le hC)
      have := mul_log_le_klDiv ((μ.map (g n)).restrict C) ((ν.map (g n)).restrict C)
      simpa only [measureReal_def, Measure.restrict_apply_univ, Measure.map_apply (hg n) hC, hCB]
        using this
    have hkey' n (h0 : ν (B n) = 0) (hpos : μ (B n) ≠ 0) :
        klDiv (μ.map (g n)) (ν.map (g n)) = ⊤ := by
      obtain ⟨C, hC, hCB⟩ := hBC n
      refine klDiv_of_not_ac fun hac ↦ hpos ?_
      have := hac (show (ν.map (g n)) C = 0 by rw [Measure.map_apply (hg n) hC, hCB, h0])
      rwa [Measure.map_apply (hg n) hC, hCB] at this
    -- conclusion
    intro K hK
    set a : ℝ := μ.real A with ha_def
    have ha : 0 < a := ENNReal.toReal_pos hμA (measure_ne_top μ A)
    set δ : ℝ := Real.exp (-(2 / a) * (K.toReal + 2)) with hδ_def
    have hδ : 0 < δ := Real.exp_pos _
    have hδ1 : δ ≤ 1 := by
      rw [hδ_def, Real.exp_le_one_iff]
      have : 0 ≤ K.toReal + 2 := by positivity
      nlinarith [div_pos (by norm_num : (0 : ℝ) < 2) ha]
    have hμB' : Tendsto (fun n ↦ μ.real (B n)) atTop (𝓝 a) :=
      (ENNReal.tendsto_toReal (measure_ne_top μ A)).comp hμB
    have hνB' : Tendsto (fun n ↦ ν.real (B n)) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hνB
      simpa [Function.comp_def, measureReal_def] using this
    have h_ev : ∀ᶠ n in atTop, a / 2 ≤ μ.real (B n) ∧ ν.real (B n) ≤ δ :=
      (hμB'.eventually (le_mem_nhds (by linarith))).and (hνB'.eventually (ge_mem_nhds hδ))
    obtain ⟨n, hna, hnδ⟩ := h_ev.exists
    refine ⟨n, ?_⟩
    by_cases h0 : ν (B n) = 0
    · rw [hkey' n h0 (fun h ↦ by simp [measureReal_def, h] at hna; linarith)]
      exact hK
    · have hνpos : 0 < ν.real (B n) := ENNReal.toReal_pos h0 (measure_ne_top ν _)
      have hμpos : 0 < μ.real (B n) := by linarith
      refine lt_of_lt_of_le ?_ (hkey n)
      rw [← ENNReal.ofReal_toReal hK.ne, ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        ENNReal.toReal_nonneg]
      -- `x log (x / y) + y - x ≥ -1 - x log y ≥ -1 + (a / 2) (-log δ) = K.toReal + 1`
      have h1 : μ.real (B n) - 1 ≤ μ.real (B n) * Real.log (μ.real (B n)) := by
        have := Real.one_sub_inv_le_log_of_pos hμpos
        calc μ.real (B n) - 1 = μ.real (B n) * (1 - (μ.real (B n))⁻¹) := by
              field_simp
          _ ≤ _ := by gcongr
      have h2 : Real.log (ν.real (B n)) ≤ Real.log δ := Real.log_le_log hνpos hnδ
      have h3 : Real.log δ = -(2 / a) * (K.toReal + 2) := by rw [hδ_def, Real.log_exp]
      have h4 : (a / 2) * (-Real.log δ) = K.toReal + 2 := by
        rw [h3]
        field_simp
      have h5 : (a / 2) * (-Real.log (ν.real (B n))) ≤
          μ.real (B n) * (-Real.log (ν.real (B n))) := by
        have hlog : 0 ≤ -Real.log (ν.real (B n)) := by
          have := Real.log_nonpos hνpos.le (hnδ.trans hδ1)
          linarith
        exact mul_le_mul_of_nonneg_right hna hlog
      rw [Real.log_div hμpos.ne' hνpos.ne']
      nlinarith [mul_le_mul_of_nonneg_left (neg_le_neg h2) (by positivity : (0 : ℝ) ≤ a / 2),
        measureReal_nonneg (μ := ν) (s := B n)]

end InformationTheory

namespace MeasurableSpace

/-- The σ-algebras of the projections of `ℕ → E` on the first `n` coordinates generate the
product σ-algebra. -/
lemma iSup_comap_restrictFin {E : Type*} [mE : MeasurableSpace E] :
    ⨆ n : ℕ, MeasurableSpace.comap (fun f : ℕ → E ↦ fun i : Fin n ↦ f i)
      MeasurableSpace.pi = MeasurableSpace.pi := by
  refine le_antisymm
    (iSup_le fun n ↦ (Measurable.of_eval fun _ ↦ measurable_pi_apply _).comap_le)
    (iSup_le fun i ↦ le_iSup_of_le (i + 1) ?_)
  have : (fun f : ℕ → E ↦ f i) =
      (fun h : Fin (i + 1) → E ↦ h ⟨i, i.lt_succ_self⟩) ∘
        fun f : ℕ → E ↦ fun j : Fin (i + 1) ↦ f j := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

end MeasurableSpace
