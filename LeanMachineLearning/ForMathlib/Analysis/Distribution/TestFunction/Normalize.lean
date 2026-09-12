/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Test functions normalized by their integral

This file constructs real-valued test functions of integral one from normalized smooth bump
functions inside an arbitrary nonempty open subset of a finite-dimensional real normed space.
-/

@[expose] public section

noncomputable section

open Function Set TopologicalSpace MeasureTheory
open scoped Distributions

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {Ω : Opens E} {c : E} (f : ContDiffBump c) (μ : Measure E)
  [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- Regard a normalized smooth bump as a test function on an open set containing its support. -/
def toTestFunctionNormed
    (h : Metric.closedBall c f.rOut ⊆ Ω) : 𝓓(Ω, ℝ) where
  toFun := f.normed μ
  contDiff' := f.contDiff_normed
  hasCompactSupport' := f.hasCompactSupport_normed
  tsupport_subset' := by simpa only [f.tsupport_normed_eq] using h

@[simp]
theorem toTestFunctionNormed_apply
    (h : Metric.closedBall c f.rOut ⊆ Ω) (x : E) :
    f.toTestFunctionNormed μ h x = f.normed μ x :=
  rfl

/-- A normalized smooth bump, regarded as a test function, still has integral one. -/
@[simp]
theorem integral_toTestFunctionNormed
    (h : Metric.closedBall c f.rOut ⊆ Ω) :
    ∫ x, f.toTestFunctionNormed μ h x ∂μ = 1 := by
  simpa only [toTestFunctionNormed_apply] using f.integral_normed (μ := μ)

end ContDiffBump

namespace TestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens E} (μ : Measure E) [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- Every nonempty open subset of a finite-dimensional real normed space supports a smooth test
function of integral one. -/
theorem exists_integral_eq_one (hΩ : (Ω : Set E).Nonempty) :
    ∃ ρ : 𝓓(Ω, ℝ), ∫ x, ρ x ∂μ = 1 := by
  obtain ⟨c, hc⟩ := hΩ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds hc)
  let f : ContDiffBump c :=
    ContDiffBump.mk (ε / 4) (ε / 2) (by positivity) (by linarith)
  have hf : Metric.closedBall c f.rOut ⊆ Ω := by
    refine (Metric.closedBall_subset_ball ?_).trans hball
    change ε / 2 < ε
    exact half_lt_self hε
  exact ⟨f.toTestFunctionNormed μ hf, f.integral_toTestFunctionNormed μ hf⟩

end TestFunction
