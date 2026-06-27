/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Convexity lemmas

-/

@[expose] public section

open Finset
open scoped Gradient RealInnerProductSpace

namespace ConvexOn

variable {E : Type*} [NormedAddCommGroup E] {f : E → ℝ} {x : E}

lemma fderiv_sub_le_sub [NormedSpace ℝ E] (hf : ConvexOn ℝ .univ f)
    (hfx : DifferentiableAt ℝ f x) (y : E) :
    fderiv ℝ f x (y - x) ≤ f y - f x := by
  have h_convex t (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      f (x + t • (y - x)) ≤ t * f y + (1 - t) * f x := by
    have h1 : x + t • (y - x) = (1 - t) • x + t • y := by module
    have h2 : f ((1 - t) • x + t • y) ≤ (1 - t) • f x + t • f y :=
      hf.2 (Set.mem_univ x) (Set.mem_univ y) (by grind) (by grind) (by simp)
    simp only [smul_eq_mul] at h2
    grind
  have h_path_deriv : HasDerivAt (fun t : ℝ ↦ f (x + t • (y - x)))
      (fderiv ℝ f x (y - x)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ ↦ x + t • (y - x)) (y - x) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (y - x)
    have h2 : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • (y - x)) := by
      simpa using hfx.hasFDerivAt
    exact h2.comp_hasDerivAt _ h1
  refine le_of_tendsto h_path_deriv.tendsto_slope_zero_right (Filter.eventually_of_mem
    (Ioo_mem_nhdsGT_of_mem ⟨le_rfl, zero_lt_one⟩) fun t ht ↦ ?_)
  simp [inv_mul_le_iff₀ ht.1]
  grind

lemma add_fderiv_le [NormedSpace ℝ E] (hf : ConvexOn ℝ .univ f)
    (hfx : DifferentiableAt ℝ f x) (y : E) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  suffices fderiv ℝ f x (y - x) ≤ f y - f x by grind
  exact hf.fderiv_sub_le_sub hfx y

lemma add_inner_gradient_le [InnerProductSpace ℝ E] [CompleteSpace E] (hf : ConvexOn ℝ .univ f)
    (hfx : DifferentiableAt ℝ f x) (y : E) :
    f x + ⟪y - x, ∇ f x⟫ ≤ f y := by
  have hfderiv : (fderiv ℝ f x) (y - x) = ⟪y - x, ∇ f x⟫ := by
    simp [gradient, ← InnerProductSpace.toDual_symm_apply, real_inner_comm]
  rw [← hfderiv]
  exact hf.add_fderiv_le hfx y

lemma le_add_inner_gradient [InnerProductSpace ℝ E] [CompleteSpace E] (hf : ConvexOn ℝ .univ f)
    (hfx : DifferentiableAt ℝ f x) (y : E) :
    f x ≤ f y + ⟪x - y, ∇ f x⟫ := by
  have h_add_le := hf.add_inner_gradient_le hfx y
  have h_neg : ⟪x - y, ∇ f x⟫ = -⟪y - x, ∇ f x⟫ := by
    rw [show x - y = -(y - x) by abel, inner_neg_left]
  grind

lemma sub_le_inner_gradient [InnerProductSpace ℝ E] [CompleteSpace E] (hf : ConvexOn ℝ .univ f)
    (hfx : DifferentiableAt ℝ f x) (y : E) :
    f x - f y ≤ ⟪x - y, ∇ f x⟫ := by
  simp only [tsub_le_iff_right]
  rw [add_comm]
  exact hf.le_add_inner_gradient hfx y

lemma apply_avg_sub_le_avg_sub [NormedSpace ℝ E] (hf : ConvexOn ℝ .univ f)
    (x : ℕ → E) (y : E) (n : ℕ) (hn : n ≠ 0) :
    f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y ≤ (n : ℝ)⁻¹ • ∑ i ∈ range n, (f (x i) - f y) := by
  calc f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y
  _ ≤ (n : ℝ)⁻¹ • ∑ i ∈ range n, f (x i) - f y := by
    simp_rw [smul_sum]
    grw [hf.map_sum_le (fun _ _ ↦ by positivity) (by simp; field) (by simp)]
  _ = (n : ℝ)⁻¹ * ∑ i ∈ range n, (f (x i) - f y) := by
    simp_rw [smul_eq_mul, mul_sum, mul_sub, sum_sub_distrib]
    rw [← sum_mul]
    simp
    field

lemma apply_avg_sub_le_avg_inner [InnerProductSpace ℝ E] [CompleteSpace E]
    (hf : ConvexOn ℝ .univ f) (hdf : Differentiable ℝ f) (x : ℕ → E) (y : E) (n : ℕ) (hn : n ≠ 0) :
    f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, ⟪x i - y, ∇ f (x i)⟫ := by
  calc f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y
  _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, (f (x i) - f y) := apply_avg_sub_le_avg_sub hf x y n hn
  _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, ⟪x i - y, ∇ f (x i)⟫ := by
    gcongr
    exact hf.sub_le_inner_gradient hdf.differentiableAt y

end ConvexOn
