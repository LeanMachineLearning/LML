/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Lemmas about probability measures

## Main statements

* `ProbabilityMeasure.ext_iff_coe`: two probability measures are equal iff the underlying
  measures are.
-/

@[expose] public section

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

lemma ProbabilityMeasure.ext_iff_coe {μ ν : ProbabilityMeasure α} :
    μ = ν ↔ (μ : Measure α) = ν := Subtype.ext_iff

end MeasureTheory
