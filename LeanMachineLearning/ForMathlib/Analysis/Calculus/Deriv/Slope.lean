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
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Convexity lemmas

-/

@[expose] public section

open Finset Filter
open scoped Gradient RealInnerProductSpace Topology

namespace ConvexOn

variable {E : Type*} [NormedAddCommGroup E] {f : E → ℝ} {x y : E} {s : Set E}

lemma fderiv_sub_le_sub [NormedSpace ℝ E] (hf : ConvexOn ℝ s f)
    (hfx : DifferentiableAt ℝ f x) (y : E) (hx : x ∈ s) (hy : y ∈ s) :
    fderiv ℝ f x (y - x) ≤ f y - f x := by
  have h_convex t (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      f (x + t • (y - x)) ≤ t * f y + (1 - t) * f x := by
    have h1 : x + t • (y - x) = (1 - t) • x + t • y := by module
    have h2 : f ((1 - t) • x + t • y) ≤ (1 - t) • f x + t • f y :=
      hf.2 hx hy (by grind) (by grind) (by simp)
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

lemma add_fderiv_le [NormedSpace ℝ E] (hf : ConvexOn ℝ s f)
    (hfx : DifferentiableAt ℝ f x) (hx : x ∈ s) (hy : y ∈ s) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  suffices fderiv ℝ f x (y - x) ≤ f y - f x by grind
  exact hf.fderiv_sub_le_sub hfx y hx hy

lemma add_inner_gradient_le [InnerProductSpace ℝ E] [CompleteSpace E] (hf : ConvexOn ℝ s f)
    (hfx : DifferentiableAt ℝ f x) (hx : x ∈ s) (hy : y ∈ s) :
    f x + ⟪y - x, ∇ f x⟫ ≤ f y := by
  rw [gradient, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  exact hf.add_fderiv_le hfx hx hy

lemma le_add_fderiv [NormedSpace ℝ E] (hf : ConvexOn ℝ s f)
    (hfx : DifferentiableAt ℝ f x) (hx : x ∈ s) (hy : y ∈ s) :
    f x ≤ f y + fderiv ℝ f x (x - y) := by
  have h_add_le := hf.add_fderiv_le hfx hx hy
  grind

lemma le_add_inner_gradient [InnerProductSpace ℝ E] [CompleteSpace E] (hf : ConvexOn ℝ s f)
    (hfx : DifferentiableAt ℝ f x) (hx : x ∈ s) (hy : y ∈ s) :
    f x ≤ f y + ⟪x - y, ∇ f x⟫ := by
  rw [gradient, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  exact le_add_fderiv hf hfx hx hy

lemma sub_le_fderiv [NormedSpace ℝ E] (hf : ConvexOn ℝ s f)
    (hfx : DifferentiableAt ℝ f x) (hx : x ∈ s) (hy : y ∈ s) :
    f x - f y ≤ fderiv ℝ f x (x - y) := by
  have h_le := hf.le_add_fderiv hfx hx hy
  grind

lemma sub_le_inner_gradient [InnerProductSpace ℝ E] [CompleteSpace E] (hf : ConvexOn ℝ s f)
    (hfx : DifferentiableAt ℝ f x) (hx : x ∈ s) (hy : y ∈ s) :
    f x - f y ≤ ⟪x - y, ∇ f x⟫ := by
  rw [gradient, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  exact sub_le_fderiv hf hfx hx hy

lemma isMinOn_of_fderiv_nonneg [NormedSpace ℝ E] (hf : ConvexOn ℝ s f)
    (hfx : DifferentiableAt ℝ f x) (hx : x ∈ s) (h_nonneg : ∀ y ∈ s, 0 ≤ fderiv ℝ f x (y - x)) :
    IsMinOn f s x := by
  intro y hy
  have h_le := hf.le_add_fderiv hfx hx hy
  specialize h_nonneg y hy
  grind

lemma isMinOn_of_inner_gradient_nonneg [InnerProductSpace ℝ E] [CompleteSpace E]
    (hf : ConvexOn ℝ s f) (hfx : DifferentiableAt ℝ f x) (hx : x ∈ s)
    (h_nonneg : ∀ y ∈ s, 0 ≤ ⟪y - x, ∇ f x⟫) :
    IsMinOn f s x := by
  refine isMinOn_of_fderiv_nonneg hf hfx hx fun y hy ↦ ?_
  convert h_nonneg y hy
  rw [gradient, ← InnerProductSpace.toDual_symm_apply, real_inner_comm]

lemma fderiv_nonneg_of_isMinOn [NormedSpace ℝ E] (hs : Convex ℝ s)
    (hfx : DifferentiableAt ℝ f x) (hx : x ∈ s) (h_min : IsMinOn f s x) {y : E} (hy : y ∈ s) :
    0 ≤ fderiv ℝ f x (y - x) := by
  refine IsLocalMinOn.hasFDerivWithinAt_nonneg h_min.localize (y := y - x)
    hfx.hasFDerivAt.hasFDerivWithinAt ?_
  refine sub_mem_posTangentConeAt_of_openSegment_subset ?_
  exact StarConvex.openSegment_subset (hs hx) hy

lemma inner_gradient_nonneg_of_isMinOn [InnerProductSpace ℝ E] [CompleteSpace E] (hs : Convex ℝ s)
    (hfx : DifferentiableAt ℝ f x) (hx : x ∈ s) (h_min : IsMinOn f s x) {y : E} (hy : y ∈ s) :
    0 ≤ ⟪y - x, ∇ f x⟫ := by
  rw [gradient, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  exact fderiv_nonneg_of_isMinOn hs hfx hx h_min hy

lemma isMinOn_iff_fderiv_nonneg [NormedSpace ℝ E] (hs : Convex ℝ s)
    (hf : ConvexOn ℝ s f) (hfx : DifferentiableAt ℝ f x) (hx : x ∈ s) :
    IsMinOn f s x ↔ ∀ y ∈ s, 0 ≤ fderiv ℝ f x (y - x) :=
  ⟨fderiv_nonneg_of_isMinOn hs hfx hx, hf.isMinOn_of_fderiv_nonneg hfx hx⟩

lemma isMinOn_iff_inner_gradient_nonneg [InnerProductSpace ℝ E] [CompleteSpace E] (hs : Convex ℝ s)
    (hf : ConvexOn ℝ s f) (hfx : DifferentiableAt ℝ f x) (hx : x ∈ s) :
    IsMinOn f s x ↔ ∀ y ∈ s, 0 ≤ ⟪y - x, ∇ f x⟫ :=
  ⟨inner_gradient_nonneg_of_isMinOn hs hfx hx, hf.isMinOn_of_inner_gradient_nonneg hfx hx⟩

lemma apply_avg_sub_le_avg_sub [NormedSpace ℝ E] (hf : ConvexOn ℝ s f)
    {x : ℕ → E} (hx : ∀ i, x i ∈ s) (y : E) (n : ℕ) (hn : n ≠ 0) :
    f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y ≤ (n : ℝ)⁻¹ • ∑ i ∈ range n, (f (x i) - f y) := by
  calc f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y
  _ ≤ (n : ℝ)⁻¹ • ∑ i ∈ range n, f (x i) - f y := by
    simp_rw [smul_sum]
    grw [hf.map_sum_le (fun _ _ ↦ by positivity) (by simp; field) (fun i _ ↦ hx i)]
  _ = (n : ℝ)⁻¹ * ∑ i ∈ range n, (f (x i) - f y) := by
    simp_rw [smul_eq_mul, mul_sum, mul_sub, sum_sub_distrib]
    rw [← sum_mul]
    simp
    field

lemma apply_avg_sub_le_avg_inner [InnerProductSpace ℝ E] [CompleteSpace E]
    (hf : ConvexOn ℝ s f) (hdf : Differentiable ℝ f) {x : ℕ → E} (hx : ∀ i, x i ∈ s)
    (hy : y ∈ s) (n : ℕ) (hn : n ≠ 0) :
    f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, ⟪x i - y, ∇ f (x i)⟫ := by
  calc f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y
  _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, (f (x i) - f y) := apply_avg_sub_le_avg_sub hf hx y n hn
  _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, ⟪x i - y, ∇ f (x i)⟫ := by
    gcongr
    exact hf.sub_le_inner_gradient hdf.differentiableAt (hx i) hy

end ConvexOn
