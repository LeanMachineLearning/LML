/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym

/-! # Lemmas related to the data-processing inequality for the Kullback–Leibler divergence
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace InformationTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The divergence of the images of `μ ≪ ν` by a measurable map `g`, as the integral of `klFun`
of the conditional expectation of the density `∂μ/∂ν` given `g`.

See `klDiv_map_of_ac` for a version of this lemma with a Bochner integral. -/
lemma klDiv_map_eq_lintegral_klFun_condExp (hμν : μ ≪ ν) {g : α → β} (hg : Measurable g) :
    klDiv (μ.map g) (ν.map g) =
      ∫⁻ x, ENNReal.ofReal
        (klFun ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | mβ.comap g]) x)) ∂ν := by
  have hmeas : Measurable fun y : β ↦
      ENNReal.ofReal (klFun ((μ.map g).rnDeriv (ν.map g) y).toReal) :=
    (measurable_klFun.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal).ennreal_ofReal
  rw [klDiv_eq_lintegral_klFun_of_ac (hμν.map hg), lintegral_map hmeas hg]
  refine lintegral_congr_ae ?_
  filter_upwards [toReal_rnDeriv_map hμν hg] with x hx
  rw [hx]


end InformationTheory
