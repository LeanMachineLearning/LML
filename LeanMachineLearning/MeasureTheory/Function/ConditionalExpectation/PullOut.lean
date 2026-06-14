/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Integrability of inner products
-/

@[expose] public section

open scoped ENNReal RealInnerProductSpace

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E} {P : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem condExp_inner_of_stronglyMeasurable_left {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {X g : Ω → E}
    (hX : StronglyMeasurable[m] X) (hXg : Integrable (fun ω ↦ ⟪X ω, g ω⟫) μ) (hg : Integrable g μ) :
    μ[fun ω ↦ ⟪X ω, g ω⟫ | m] =ᵐ[μ] fun ω ↦ ⟪X ω, μ[g | m] ω⟫ := by
  filter_upwards [condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hX hXg hg] with ω hω
  convert hω
  · rfl
  · rfl

end MeasureTheory
