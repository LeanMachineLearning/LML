/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Measurability with respect to a comap σ-algebra

## Main statements

* `measurable_comp_comap`: `g ∘ f` is measurable with respect to `mβ.comap f` if `g` is
  measurable.
-/

@[expose] public section

open MeasureTheory

variable {α β γ : Type*} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

/-- `g ∘ f` is measurable with respect to the σ-algebra on `α` induced by `f`, as soon as `g` is
measurable. -/
lemma measurable_comp_comap (f : α → β) {g : β → γ} (hg : Measurable g) :
    Measurable[mβ.comap f] (g ∘ f) :=
  hg.comp (comap_measurable f)
