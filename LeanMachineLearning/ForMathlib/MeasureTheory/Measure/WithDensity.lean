/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Image of a measure with density

## Main statements

* `map_withDensity_comp`: the image by `g` of `μ.withDensity (f ∘ g)` is
  `(μ.map g).withDensity f`.
* `map_equiv_withDensity`: the image of a measure with density by a measurable equivalence.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ : Measure α}

lemma map_withDensity_comp {g : α → γ} {f : γ → ℝ≥0∞} (hg : Measurable g) (hf : Measurable f) :
    (μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f := by
  ext s hs
  rw [Measure.map_apply hg hs, withDensity_apply _ (hg hs), withDensity_apply _ hs,
    setLIntegral_map hs hf hg]
  rfl

lemma map_equiv_withDensity {e : α ≃ᵐ β} {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  simp_rw [← map_withDensity_comp e.measurable (hf.comp e.symm.measurable),
    Function.comp_assoc, MeasurableEquiv.symm_comp_self]
  rfl

lemma map_swap_withDensity_comp_snd {μ : Measure (α × β)} {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (fun ab ↦ f ab.2)).map Prod.swap =
      (μ.map Prod.swap).withDensity (fun ba ↦ f ba.1) := by
  rw [← map_withDensity_comp measurable_swap (by fun_prop)]
  rfl

end MeasureTheory
