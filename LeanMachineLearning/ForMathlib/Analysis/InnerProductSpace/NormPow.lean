/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormPow

import LeanMachineLearning.ForMathlib.Analysis.Calculus.Deriv.Slope

/-!
# Differentiability of the norm to a power

-/

@[expose] public section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem Differentiable.norm_pow {f : F → E} (hf : Differentiable ℝ f) {p : ℕ} (hp : 1 < p) :
    Differentiable ℝ (fun x ↦ ‖f x‖ ^ p) := by
  suffices Differentiable ℝ (fun x ↦ ‖f x‖ ^ (p : ℝ)) by
    convert this using 1
    simp
  exact hf.norm_rpow (by simp [hp])
