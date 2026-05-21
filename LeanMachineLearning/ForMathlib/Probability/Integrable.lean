/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.IdentDistrib

@[expose] public section

open ProbabilityTheory

namespace MeasureTheory

lemma Integrable.congr_identDistrib {Ω Ω' : Type*}
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} {μ' : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ}
    (hX : Integrable X μ) (hXY : IdentDistrib X Y μ μ') :
    Integrable Y μ' := by
  have hX' : Integrable id (μ.map X) := by
    rwa [integrable_map_measure (by fun_prop) hXY.aemeasurable_fst]
  rw [hXY.map_eq] at hX'
  rwa [integrable_map_measure (by fun_prop) hXY.aemeasurable_snd] at hX'

end MeasureTheory
