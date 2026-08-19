/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.NormPow

import LeanMachineLearning.ForMathlib.Analysis.Calculus.Deriv.Slope

/-!
# Differentiability of the norm to a power

-/

@[expose] public section

open scoped Gradient

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma Differentiable.norm_pow {f : F → E} (hf : Differentiable ℝ f) {p : ℕ} (hp : 1 < p) :
    Differentiable ℝ (fun x ↦ ‖f x‖ ^ p) := by
  suffices Differentiable ℝ (fun x ↦ ‖f x‖ ^ (p : ℝ)) by
    convert this using 1
    simp
  exact hf.norm_rpow (by simp [hp])

lemma gradient_norm_sub_sq [CompleteSpace E] (x y : E) :
    ∇ (fun z ↦ ‖z - x‖ ^ 2) y = 2 • (y - x) := by
  have h := ((hasFDerivAt_id y).sub_const x).norm_sq.hasGradientAt.gradient
  simp only [id_eq, map_sub, ContinuousLinearMap.comp_id, map_nsmul] at h
  rw [h]
  congr
  · exact (InnerProductSpace.toDual ℝ E).symm_apply_apply _
  · exact (InnerProductSpace.toDual ℝ E).symm_apply_apply _

lemma gradient_dist_sq [CompleteSpace E] (x y : E) : ∇ (fun z ↦ dist x z ^ 2) y = 2 • (y - x) := by
  simp only [dist_eq_norm, norm_sub_rev x]
  exact gradient_norm_sub_sq x y
