/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import LeanMachineLearning.ForMathlib.MeasureTheory.OuterMeasure.Basic

/-!
# Absolute continuity with respect to a measure charging every singleton
-/

@[expose] public section

variable {α : Type*}

namespace MeasureTheory

variable {mα : MeasurableSpace α} {μ ν : Measure α}

namespace Measure

/-- Every measure is absolutely continuous with respect to a measure that charges all singletons. -/
lemma absolutelyContinuous_of_measure_singleton_ne_zero (h : ∀ a, ν {a} ≠ 0) : μ ≪ ν :=
  fun s hs ↦ by simp [(measure_null_iff_eq_empty_of_measure_singleton_ne_zero h).1 hs]

end Measure

end MeasureTheory
