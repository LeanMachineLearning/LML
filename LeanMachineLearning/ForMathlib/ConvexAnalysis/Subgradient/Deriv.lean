/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.ForMathlib.ConvexAnalysis.Subgradient.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Data.Set.Basic

/-!
# Fréchet Derivatives and Subgradients

This file establishes the connection between Fréchet derivatives (`HasFDerivAt`)
and subgradients (`∂[V, x] f`) for convex functions.

## Main results

* `HasFDerivAt.mem_subdifferential`: A Fréchet derivative of a convex function
  is a subgradient.
* `HasFDerivAt.le_of_mem_subdifferential`: An interior subgradient is bounded
  above by the Fréchet derivative.
* `HasFDerivAt.eq_of_mem_subdifferential`: Uniqueness of subgradient at interior
  differentiable points.
* `mem_subdifferential_add_hasFDerivAt_iff`: Subdifferential sum rule when one
  component is Fréchet differentiable.
-/

@[expose] public section

namespace Analysis.Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [PartialOrder F] [IsOrderedAddMonoid F] [PosSMulMono ℝ F]
variable {f : E → F} {V : Set E} {x : E} {g h : E →L[ℝ] F}

open scoped Bregman Topology
open Asymptotics Filter

/-- Scaled Bregman divergence monotonicity along segments for convex functions. -/
lemma _root_.ConvexOn.bregDiv_slope_le (hf : ConvexOn ℝ V f)
    {z : E} (hx : x ∈ V) (hz : z ∈ V) (J : E →ₗ[ℝ] F)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t⁻¹ • D_[f](x + t • (z - x), x, J) ≤ D_[f](z, x, J) := by
  have : (1 - t) • x + t • z = x + t • (z - x) := by module
  simpa [this, smul_smul, inv_mul_cancel₀ ht0.ne'] using
    smul_le_smul_of_nonneg_left
      ((hf.bregDiv (y := x) J).2 hx hz (sub_nonneg.mpr ht1) ht0.le (sub_add_cancel 1 t))
      (inv_nonneg.mpr ht0.le)

omit [PartialOrder F] [IsOrderedAddMonoid F] [PosSMulMono ℝ F] in
/-- As the step size `t → 0⁺`, the linearization error of a Fréchet differentiable function
scaled by `t⁻¹` converges to `0`. -/
lemma _root_.HasFDerivAt.tendsto_bregDiv_slope_zero
    (hderiv : HasFDerivAt f g x) (w : E) :
    Tendsto (fun t : ℝ ↦ t⁻¹ • D_[f](x + t • w, x, (g : E →+ F))) (𝓝[>] 0) (𝓝 0) := by
  have h := (hderiv.hasLineDerivAt w).tendsto_slope_zero_right.sub_const (g w)
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht0
  simp [bregDiv, smul_sub, ht0.out.ne']

variable [OrderClosedTopology F]

/-- A Fréchet derivative of a convex function is a subgradient. -/
lemma _root_.HasFDerivAt.mem_subdifferential
    (hderiv : HasFDerivAt f g x) (hf : ConvexOn ℝ V f) (hx : x ∈ V) :
    (g : E →+ F) ∈ ∂[V, x] f := by
  refine ⟨hx, fun z hz ↦ le_of_tendsto (hderiv.tendsto_bregDiv_slope_zero (z - x)) ?_⟩
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_le_nhds zero_lt_one)]
    with t (ht0 : 0 < t) ht1 using hf.bregDiv_slope_le hx hz g.toLinearMap ht0 ht1

lemma subgradient_of_hasFDerivAt
    (hf : ConvexOn ℝ V f) (hx : x ∈ V) (hderiv : HasFDerivAt f g x) :
    (g : E →+ F) ∈ ∂[V, x] f :=
  hderiv.mem_subdifferential hf hx

section Real

variable {f : E → ℝ} {g h : E →L[ℝ] ℝ}

lemma _root_.HasFDerivAt.le_of_mem_subdifferential
    (hderiv : HasFDerivAt f g x) (hV : V ∈ 𝓝 x) (hsub : (h : E →+ ℝ) ∈ ∂[V, x] f) (w : E) :
    h w ≤ g w := by
  have h_nhds : (fun t : ℝ ↦ x + t • w) ⁻¹' V ∈ 𝓝 0 :=
    (continuous_const.add (continuous_id'.smul continuous_const)).continuousAt.preimage_mem_nhds
      (by simpa using hV)
  refine ge_of_tendsto (hderiv.hasLineDerivAt w).tendsto_slope_zero_right ?_
  filter_upwards [nhdsWithin_le_nhds h_nhds, self_mem_nhdsWithin] with t ht_V (ht_pos : 0 < t)
  simpa [bregDiv, add_sub_cancel_left, h.map_smul, smul_eq_mul,
    inv_mul_cancel_left₀ ht_pos.ne'] using
    mul_le_mul_of_nonneg_left (sub_nonneg.mp (hsub.2 (x + t • w) ht_V)) (inv_nonneg.mpr ht_pos.le)

/-- Uniqueness of the subgradient at an interior differentiable point. -/
lemma _root_.HasFDerivAt.eq_of_mem_subdifferential
    (hderiv : HasFDerivAt f g x) (hV : V ∈ 𝓝 x) (hsub : (h : E →+ ℝ) ∈ ∂[V, x] f) :
    h = g := by
  ext v
  exact le_antisymm (hderiv.le_of_mem_subdifferential hV hsub v)
    (by simpa using hderiv.le_of_mem_subdifferential hV hsub (-v))

/--
Subdifferential sum rule when `f₁` is convex and Fréchet differentiable at `x`
and `f₂` is convex on `V`: `g` is a subgradient of `f₁ + f₂` at `x` if and only if
`g - g₁` is a subgradient of `f₂` at `x`.
-/
lemma _root_.HasFDerivAt.mem_subdifferential_add_iff {f₁ f₂ : E → ℝ}
    {g₁ g : E →L[ℝ] ℝ}
    (hderiv₁ : HasFDerivAt f₁ g₁ x) (hf₁ : ConvexOn ℝ V f₁) (hf₂ : ConvexOn ℝ V f₂) (hx : x ∈ V) :
    (g : E →+ ℝ) ∈ ∂[V, x] (f₁ + f₂) ↔ (g - g₁ : E →+ ℝ) ∈ ∂[V, x] f₂ := by
  have h_eq : (g : E →+ ℝ) = (g₁ : E →+ ℝ) + (g - g₁ : E →+ ℝ) := by ext; simp
  constructor
  · rintro ⟨-, hg⟩
    refine ⟨hx, fun z hz ↦ le_of_tendsto
      (by simpa using (hderiv₁.tendsto_bregDiv_slope_zero (z - x)).neg) ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_le_nhds zero_lt_one)] with t (ht0 : 0 < t) ht1
    have h_slope : t⁻¹ • D_[f₂](x + t • (z - x), x, (g - g₁ : E →+ ℝ)) ≤
        D_[f₂](z, x, (g - g₁ : E →+ ℝ)) :=
      hf₂.bregDiv_slope_le hx hz (g - g₁).toLinearMap ht0 ht1
    have h_nonneg := smul_nonneg (inv_nonneg.mpr ht0.le)
      (hg _ (hf₂.1.add_smul_sub_mem hx hz ⟨ht0.le, ht1⟩))
    rw [h_eq, bregDiv_add, smul_add] at h_nonneg
    dsimp at *
    linarith
  · intro h₂
    have := IsSubgradient.add (hderiv₁.mem_subdifferential hf₁ hx) h₂
    rwa [← h_eq] at this

lemma mem_subdifferential_add_hasFDerivAt_iff {f₁ f₂ : E → ℝ}
    {g₁ g : E →L[ℝ] ℝ}
    (hf₁ : ConvexOn ℝ V f₁) (hf₂ : ConvexOn ℝ V f₂) (hx : x ∈ V)
    (hderiv₁ : HasFDerivAt f₁ g₁ x) :
    (g : E →+ ℝ) ∈ ∂[V, x] (f₁ + f₂) ↔ (g - g₁ : E →+ ℝ) ∈ ∂[V, x] f₂ :=
  hderiv₁.mem_subdifferential_add_iff hf₁ hf₂ hx

end Real

end Analysis.Convex
