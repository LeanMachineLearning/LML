/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# The Kullback–Leibler divergence of restrictions of measures

The Kullback–Leibler divergence of two finite measures is the sum of the divergences of their
restrictions to a measurable set and to its complement, so that restricting both measures to
a measurable set does not increase the divergence, and the divergence is the supremum of the
divergences of the restrictions to an increasing sequence of measurable sets covering the space.

## Main statements

* `klDiv_restrict_add_restrict_compl`: the divergence is the sum of the divergences of
  the restrictions to a measurable set and to its complement.
* `klDiv_restrict_le`: restricting both measures to a measurable set does not increase
  the divergence.
* `klDiv_eq_iSup_restrict`: the divergence is the supremum of the divergences of the restrictions
  to an increasing sequence of measurable sets covering the space.

-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- The Radon–Nikodym derivative of `μ.restrict s` with respect to `ν.restrict s` is the
Radon–Nikodym derivative of `μ` with respect to `ν`, `ν.restrict s`-almost everywhere. -/
lemma rnDeriv_restrict_restrict (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] [SigmaFinite ν]
    {s : Set α} (hs : MeasurableSet s) :
    (μ.restrict s).rnDeriv (ν.restrict s) =ᵐ[ν.restrict s] μ.rnDeriv ν := by
  refine (eq_rnDeriv (s := (μ.singularPart ν).restrict s) (measurable_rnDeriv μ ν)
    (((mutuallySingular_singularPart μ ν).restrict s).mono le_rfl restrict_le_self) ?_).symm
  rw [← restrict_withDensity hs, ← restrict_add, ← haveLebesgueDecomposition_add μ ν]

end MeasureTheory.Measure

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} [IsFiniteMeasure μ]
  [IsFiniteMeasure ν] {s : Set α}

/-- If the restrictions of `μ` and `ν` to a measurable set `s` satisfy
`μ.restrict s ≪ ν.restrict s`, the divergence of those restrictions is the integral of
`klFun (∂μ/∂ν)` over `s`. -/
lemma klDiv_restrict_of_ac (hμν : μ.restrict s ≪ ν.restrict s) (hs : MeasurableSet s) :
    klDiv (μ.restrict s) (ν.restrict s) =
      ∫⁻ x in s, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν := by
  rw [klDiv_eq_lintegral_klFun_of_ac hμν]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_restrict_restrict μ ν hs] with x hx
  rw [hx]

/-- The divergence is the sum of the divergences of the restrictions to a measurable set and to
its complement. -/
lemma klDiv_restrict_add_restrict_compl (hs : MeasurableSet s) :
    klDiv (μ.restrict s) (ν.restrict s) + klDiv (μ.restrict sᶜ) (ν.restrict sᶜ) = klDiv μ ν := by
  by_cases hμν : μ ≪ ν
  · rw [klDiv_restrict_of_ac (hμν.restrict s) hs, klDiv_restrict_of_ac (hμν.restrict sᶜ) hs.compl,
      klDiv_eq_lintegral_klFun_of_ac hμν, lintegral_add_compl _ hs]
  · rw [klDiv_of_not_ac hμν, ENNReal.add_eq_top]
    by_contra! h
    refine hμν ?_
    rw [← Measure.restrict_add_restrict_compl (μ := μ) hs,
      ← Measure.restrict_add_restrict_compl (μ := ν) hs]
    exact (klDiv_ne_top_iff.1 h.1).1.add (klDiv_ne_top_iff.1 h.2).1

/-- Restricting both measures to a measurable set does not increase the divergence. -/
lemma klDiv_restrict_le (hs : MeasurableSet s) :
    klDiv (μ.restrict s) (ν.restrict s) ≤ klDiv μ ν := by
  rw [← klDiv_restrict_add_restrict_compl (μ := μ) (ν := ν) hs]
  exact le_add_right le_rfl

/-- The divergence of two finite measures supported on a measurable set `s` and its complement
respectively is the sum of the divergences of the two parts. -/
lemma klDiv_add_add_of_measure_eq_zero {μ' ν' : Measure α} [IsFiniteMeasure μ']
    [IsFiniteMeasure ν'] (hs : MeasurableSet s) (hμ : μ sᶜ = 0) (hν : ν sᶜ = 0) (hμ' : μ' s = 0)
    (hν' : ν' s = 0) :
    klDiv (μ + μ') (ν + ν') = klDiv μ ν + klDiv μ' ν' := by
  have h1 : ∀ (ρ ρ' : Measure α), ρ sᶜ = 0 → ρ' s = 0 → (ρ + ρ').restrict s = ρ := by
    intro ρ ρ' hρ hρ'
    rw [Measure.restrict_add, Measure.restrict_eq_zero.2 hρ', add_zero,
      Measure.restrict_eq_self_of_ae_mem]
    exact ae_iff.2 hρ
  have h2 : ∀ (ρ ρ' : Measure α), ρ sᶜ = 0 → ρ' s = 0 → (ρ + ρ').restrict sᶜ = ρ' := by
    intro ρ ρ' hρ hρ'
    rw [Measure.restrict_add, Measure.restrict_eq_zero.2 hρ, zero_add,
      Measure.restrict_eq_self_of_ae_mem]
    exact ae_iff.2 (by rw [show {a | a ∉ sᶜ} = s from compl_compl s]; exact hρ')
  rw [← klDiv_restrict_add_restrict_compl hs, h1 μ μ' hμ hμ', h1 ν ν' hν hν', h2 μ μ' hμ hμ',
    h2 ν ν' hν hν']

/-- **Monotone convergence** for the Kullback–Leibler divergence: the divergence is the supremum
of the divergences of the restrictions to an increasing sequence of measurable sets covering the
space. -/
lemma klDiv_eq_iSup_restrict {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n))
    (h_mono : Monotone s) (h_univ : ⋃ n, s n = Set.univ) :
    klDiv μ ν = ⨆ n, klDiv (μ.restrict (s n)) (ν.restrict (s n)) := by
  by_cases hμν : μ ≪ ν
  · simp_rw [klDiv_restrict_of_ac (hμν.restrict _) (hs _), klDiv_eq_lintegral_klFun_of_ac hμν,
      ← lintegral_indicator (hs _)]
    have h_meas : Measurable fun x ↦ ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) :=
      (measurable_klFun.comp (Measure.measurable_rnDeriv μ ν).ennreal_toReal).ennreal_ofReal
    rw [← lintegral_iSup (fun n ↦ h_meas.indicator (hs n)) fun n m hnm ↦
      Set.indicator_le_indicator_of_subset (h_mono hnm) fun _ ↦ zero_le]
    refine lintegral_congr fun x ↦ ?_
    obtain ⟨n, hn⟩ : ∃ n, x ∈ s n := by
      have : x ∈ ⋃ n, s n := h_univ ▸ Set.mem_univ x
      simpa using this
    refine le_antisymm (le_iSup_of_le n ?_) (iSup_le fun m ↦ Set.indicator_le_self _ _ _)
    simp [hn]
  · rw [klDiv_of_not_ac hμν, eq_comm, iSup_eq_top]
    obtain ⟨t, ht0, htpos⟩ : ∃ t, ν t = 0 ∧ μ t ≠ 0 := by
      by_contra! h
      exact hμν (Measure.AbsolutelyContinuous.mk fun t _ ht ↦ h t ht)
    have h_iUnion : μ t = ⨆ n, μ (t ∩ s n) := by
      rw [← Monotone.measure_iUnion (fun n m hnm ↦ Set.inter_subset_inter_right _ (h_mono hnm)),
        ← Set.inter_iUnion, h_univ, Set.inter_univ]
    obtain ⟨n, hn⟩ : ∃ n, μ (t ∩ s n) ≠ 0 := by
      by_contra! h
      simp [h_iUnion, h] at htpos
    refine fun b hb ↦ ⟨n, lt_of_lt_of_le hb (le_of_eq ?_)⟩
    rw [eq_comm, klDiv_of_not_ac]
    intro h
    refine hn ?_
    have := h (show ν.restrict (s n) t = 0 by
      rw [Measure.restrict_apply' (hs n)]
      exact measure_mono_null Set.inter_subset_left ht0)
    rwa [Measure.restrict_apply' (hs n)] at this

end InformationTheory
