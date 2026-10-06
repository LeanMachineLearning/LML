/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.Basic
public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.Common.Domain
public import Mathlib.Analysis.Calculus.Deriv.Basic
import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.MVT
import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Scaled Unnormalized Negative Entropy Regularizer for LEA

This file defines the scaled unnormalized negative entropy regularizer
$$\psi_\alpha(x) = \alpha \sum_{i=1}^d (x_i \ln x_i - x_i),$$
its Fréchet derivative $\nabla\psi_\alpha(x)$, its Hessian second-derivative bilinear map,
and proves:
1. `hasFDerivAt_unnormEntropy`: Formula for the Fréchet derivative
   $\nabla\psi_\alpha(x) = \alpha (\ln x_i)_i$.
2. `hasFDerivAt_unnormEntropyFDeriv`: Formula for the Hessian bilinear form.
3. `bregDiv_unnormEntropy_mvt`: Second-order Taylor/MVT remainder for the Bregman divergence.
4. `convexOn_unnormEntropy_stdSimplex`: Convexity of `unnormEntropy α` on the standard simplex
   `stdSimplex` for $\alpha \ge 0$.

## Main definitions
* `unnormEntropy`
* `unnormEntropyFDeriv`
* `unnormEntropyHessian`
-/

open scoped BigOperators Bregman Topology
open Finset

@[expose] public section

namespace Online.OCO.LEA

variable {d : ℕ}

/-! ### Definitions -/

/-- The scaled unnormalized negative entropy regularizer with scale $\alpha \in \mathbb{R}$:
$$\psi_\alpha(x) = \alpha \sum_{i=1}^d (x_i \ln x_i - x_i)$$ -/
noncomputable def unnormEntropy (α : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  α * ∑ i, (x i * Real.log (x i) - x i)

/-- Coordinate projection on `EuclideanSpace ℝ (Fin d)` as a continuous linear map. -/
noncomputable abbrev eucProj (i : Fin d) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i

lemma hasDerivAt_mul_log_sub {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t ↦ t * Real.log t - t) (Real.log x) x := by
  have := (Real.hasDerivAt_mul_log hx).sub (hasDerivAt_id x)
  ring_nf at this
  exact this

/-- The Fréchet derivative of scaled unnormalized negative entropy at $x \in \mathbb{R}^d_{>0}$:
$$v \mapsto \alpha \sum_{i=1}^d v_i \ln x_i$$ -/
noncomputable def unnormEntropyFDeriv (α : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  α • (∑ i, (Real.log (x i)) • eucProj i)

@[simp]
lemma unnormEntropyFDeriv_apply (α : ℝ) (x v : EuclideanSpace ℝ (Fin d)) :
    unnormEntropyFDeriv α x v = α * ∑ i, v i * Real.log (x i) := by
  simp [unnormEntropyFDeriv, mul_comm]

/-- The Hessian (second Fréchet derivative) of scaled unnormalized negative entropy at
$x \in \mathbb{R}^d_{>0}$:
$$(v, w) \mapsto \alpha \sum_{i=1}^d \frac{v_i w_i}{x_i}$$ -/
noncomputable def unnormEntropyHessian (α : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :=
  α • (∑ i, (x i)⁻¹ • ContinuousLinearMap.smulRight (eucProj i) (eucProj i))

@[simp]
lemma unnormEntropyHessian_apply (α : ℝ) (x v w : EuclideanSpace ℝ (Fin d)) :
    unnormEntropyHessian α x v w = α * ∑ i, (v i * w i) / x i := by
  simp [unnormEntropyHessian, div_eq_inv_mul, mul_sum]

/-- The Bregman divergence of unnormalized negative entropy decomposes coordinate-wise:
$$D_{\psi_\alpha}(x, y) = \alpha \sum_{i=1}^d (x_i \ln(x_i / y_i) - x_i + y_i).$$ -/
lemma bregDiv_unnormEntropy_apply (α : ℝ) (x y : EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    D_[unnormEntropy α](x, y, unnormEntropyFDeriv α y) =
      α * ∑ i, (x i * Real.log (x i / y i) - x i + y i) := by
  dsimp [bregDiv, unnormEntropy]
  rw [unnormEntropyFDeriv_apply, mul_sum, mul_sum, mul_sum, mul_sum]
  simp_rw [← sum_sub_distrib, Real.log_div (hx _).ne' (hy _).ne']
  refine sum_congr rfl fun i _ ↦ by dsimp; ring

/-! ### Fréchet Derivatives -/

/-- Fréchet derivative of scaled unnormalized negative entropy at any $y \in \mathbb{R}^d_{>0}$. -/
theorem hasFDerivAt_unnormEntropy (α : ℝ) (y : EuclideanSpace ℝ (Fin d)) (hy : ∀ i, 0 < y i) :
    HasFDerivAt (unnormEntropy α) (unnormEntropyFDeriv α y) y := by
  have h := HasFDerivAt.sum (u := (univ : Finset (Fin d)))
    (fun i _ ↦ (hasDerivAt_mul_log_sub (hy i).ne').comp_hasFDerivAt y (eucProj i).hasFDerivAt)
  have h_scaled := h.const_smul α
  have h_eq_fun : (α • (∑ i : Fin d, (fun t ↦ t * Real.log t - t) ∘ ⇑(eucProj i))) =
      unnormEntropy α := by
    ext x; simp [unnormEntropy, smul_eq_mul]
  have h_eq_deriv : α • (∑ i : Fin d, (Real.log (y i)) • eucProj i) =
      unnormEntropyFDeriv α y := rfl
  rw [h_eq_deriv] at h_scaled
  rwa [h_eq_fun] at h_scaled

/-- Second Fréchet derivative (Hessian) of scaled unnormalized negative entropy at
$y \in \mathbb{R}^d_{>0}$. -/
theorem hasFDerivAt_unnormEntropyFDeriv (α : ℝ) (y : EuclideanSpace ℝ (Fin d)) (hy : ∀ i, 0 < y i) :
    HasFDerivAt (unnormEntropyFDeriv α) (unnormEntropyHessian α y) y := by
  have h (i : Fin d) : HasFDerivAt (fun x ↦ (Real.log (x i)) • eucProj i)
      ((y i)⁻¹ • ContinuousLinearMap.smulRight (eucProj i) (eucProj i)) y := by
    have hlog : HasFDerivAt (fun x ↦ Real.log (x i)) ((y i)⁻¹ • eucProj i) y := by
      change HasFDerivAt (Real.log ∘ fun x ↦ x i) ((y i)⁻¹ • eucProj i) y
      exact (Real.hasDerivAt_log (hy i).ne').comp_hasFDerivAt y (eucProj i).hasFDerivAt
    have h_smul := hlog.smul_const (eucProj i)
    have h_clm : ((y i)⁻¹ • eucProj i).smulRight (eucProj i) =
        (y i)⁻¹ • ContinuousLinearMap.smulRight (eucProj i) (eucProj i) := by
      ext v w; simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_assoc]
    rwa [h_clm] at h_smul
  have h_sum := (HasFDerivAt.sum (u := univ) (fun i _ ↦ h i)).const_smul α
  have h_eq_fun :
      (α • (∑ i : Fin d, fun x : EuclideanSpace ℝ (Fin d) ↦ (Real.log (x i)) • eucProj i)) =
        unnormEntropyFDeriv α := by
    ext x; simp [unnormEntropyFDeriv]
  have h_eq_deriv : α • (∑ i, (y i)⁻¹ • ContinuousLinearMap.smulRight (eucProj i) (eucProj i)) =
      unnormEntropyHessian α y := rfl
  rw [h_eq_deriv] at h_sum
  rwa [h_eq_fun] at h_sum

/-! ### Second-Order Taylor Remainder (MVT) for Bregman Divergence -/

theorem bregDiv_unnormEntropy_mvt (α : ℝ) (x y : EuclideanSpace ℝ (Fin d))
    (h_pos : ∀ z ∈ segment ℝ x y, ∀ i, 0 < (z : EuclideanSpace ℝ (Fin d)) i) :
    ∃ z ∈ segment ℝ x y,
      D_[unnormEntropy α](x, y, unnormEntropyFDeriv α y) = (α / 2) * ∑ i, (x i - y i)^2 / z i := by
  obtain ⟨z, hz, hz_eq⟩ := bregDiv_mvt x y
    (fun z hz ↦ hasFDerivAt_unnormEntropy α z (h_pos z hz))
    (fun z hz ↦ hasFDerivAt_unnormEntropyFDeriv α z (h_pos z hz))
  exact ⟨z, hz, by rw [hz_eq, unnormEntropyHessian_apply]; simp_rw [PiLp.sub_apply, sq]; ring⟩

/-! ### Convexity of Regularizer -/

/-- Convexity of scaled unnormalized negative entropy on the non-negative orthant
$\{x \mid \forall i, 0 \le x_i\}$ for $\alpha \ge 0$. -/
theorem convexOn_unnormEntropy_nonneg (α : ℝ) (hα : 0 ≤ α) :
    ConvexOn ℝ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i} (unnormEntropy α) := by
  refine ⟨fun x hx y hy a b ha hb _ i ↦ add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i)),
    fun x hx y hy a b ha hb hab ↦ ?_⟩
  dsimp [unnormEntropy]
  have h_base : ∑ i, ((a * x i + b * y i) * Real.log (a * x i + b * y i) - (a * x i + b * y i)) ≤
      a * ∑ i, (x i * Real.log (x i) - x i) + b * ∑ i, (y i * Real.log (y i) - y i) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun i _ ↦ by
      have := Real.convexOn_mul_log.2 (hx i) (hy i) ha hb hab
      dsimp at this; linarith
  have := mul_le_mul_of_nonneg_left h_base hα
  linarith

/-- Convexity of scaled unnormalized negative entropy on the standard simplex `stdSimplex`
for $\alpha \ge 0$. -/
theorem convexOn_unnormEntropy_stdSimplex (α : ℝ) (hα : 0 ≤ α) :
    ConvexOn ℝ (stdSimplex (d := d)) (unnormEntropy α) :=
  (convexOn_unnormEntropy_nonneg α hα).subset (fun _ hx ↦ (mem_stdSimplex_iff _).mp hx |>.1)
    convex_stdSimplex

/-- Non-negativity of unnormalized negative entropy Bregman divergence for $\alpha \ge 0$:
$$D_{\psi_\alpha}(x, y) \ge 0 \quad \text{for } x, y > 0.$$ -/
lemma bregDiv_unnormEntropy_nonneg (α : ℝ) (hα : 0 ≤ α) (x y : EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    0 ≤ D_[unnormEntropy α](x, y, unnormEntropyFDeriv α y) :=
  (hasFDerivAt_unnormEntropy α y hy).hasSubgradientWithinAt
    (convexOn_unnormEntropy_nonneg α hα) (fun i ↦ (hy i).le) x (fun i ↦ (hx i).le)

/-! ### Shifted Regularizer -/

/-- Shifted unnormalized negative entropy regularizer with offset $\alpha (\ln d + 1)$:
$$\psi^{\mathrm{shift}}_\alpha(x) = \psi_\alpha(x) + \alpha (\ln d + 1)$$ -/
noncomputable def unnormEntropyShifted (α : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  unnormEntropy α x + α * (Real.log d + 1)

lemma unnormEntropyShifted_smul (α : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    unnormEntropyShifted α x = α • unnormEntropyShifted 1 x := by
  dsimp [unnormEntropyShifted, unnormEntropy]; ring

@[simp]
lemma bregDiv_unnormEntropyShifted (α : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    D_[unnormEntropyShifted α](x, y, unnormEntropyFDeriv α y) =
      D_[unnormEntropy α](x, y, unnormEntropyFDeriv α y) := by
  dsimp [bregDiv, unnormEntropyShifted]; ring

/-- The Bregman divergence $D_{\psi_\alpha}(u, w_1)$ from the uniform distribution $w_1$ to any
comparator $u \in \Delta^{d-1}$ is exactly $\alpha (\ln d + \sum_{i=1}^d u_i \ln u_i)$. -/
theorem bregDiv_unnormEntropy_uniformSimplex (α : ℝ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ stdSimplex (d := d)) :
    D_[unnormEntropy α](u, uniformSimplex d, unnormEntropyFDeriv α (uniformSimplex d)) =
      α * (Real.log d + ∑ i, u i * Real.log (u i)) := by
  have hu_sum := (mem_stdSimplex_iff u).mp hu |>.2
  have hw_sum : ∑ i, uniformSimplex d i = 1 := (mem_stdSimplex_uniformSimplex hd).2
  have hlog (i : Fin d) : Real.log (uniformSimplex d i) = -Real.log d := by
    simp [uniformSimplex_apply, one_div, Real.log_inv]
  rw [bregDiv, unnormEntropy, unnormEntropy, unnormEntropyFDeriv_apply]
  simp_rw [sum_sub_distrib, hlog, PiLp.sub_apply, ← sum_mul, sum_sub_distrib, hw_sum, hu_sum]
  ring

/-- For any comparator $u \in \Delta^{d-1}$, the entropy sum $\sum_{i=1}^d u_i \ln u_i \le 0$. -/
lemma sum_mul_log_nonpos_of_mem_stdSimplex {u : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ stdSimplex (d := d)) :
    ∑ i, u i * Real.log (u i) ≤ 0 := by
  rw [mem_stdSimplex_iff] at hu
  refine sum_nonpos fun i _ ↦ ?_
  by_cases h0 : u i = 0
  · simp [h0]
  · have h_le1 : u i ≤ 1 := by
      have : u i ≤ ∑ j, u j := single_le_sum (fun j _ ↦ hu.1 j) (Finset.mem_univ i)
      rwa [hu.2] at this
    have hlog_nonpos : Real.log (u i) ≤ 0 := Real.log_nonpos (hu.1 i) h_le1
    exact mul_nonpos_of_nonneg_of_nonpos (hu.1 i) hlog_nonpos

/-- For any comparator $u \in \Delta^{d-1}$ and $\alpha \ge 0$, the Bregman divergence from the
uniform distribution is upper-bounded by $\alpha \ln d$:
$$D_{\psi_\alpha}(u, w_1) \le \alpha \ln d.$$ -/
theorem bregDiv_unnormEntropy_uniformSimplex_le (α : ℝ) (hα : 0 ≤ α) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ stdSimplex (d := d)) :
    D_[unnormEntropy α](u, uniformSimplex d, unnormEntropyFDeriv α (uniformSimplex d)) ≤
      α * Real.log d := by
  rw [bregDiv_unnormEntropy_uniformSimplex α hd u hu]
  have h_nonpos := sum_mul_log_nonpos_of_mem_stdSimplex hu
  nlinarith

/-- The shifted unnormalized negative entropy evaluates to zero at the uniform distribution
$w_1 = (1/d, \dots, 1/d)$. -/
lemma unnormEntropyShifted_uniformSimplex (hd : 0 < d) (α : ℝ) :
    unnormEntropyShifted α (uniformSimplex d) = 0 := by
  rw [unnormEntropyShifted, unnormEntropy]
  have hlog : ∀ i : Fin d, Real.log (uniformSimplex d i) = -Real.log d := by
    intro i; simp [uniformSimplex_apply, one_div, Real.log_inv]
  have hw_sum : ∑ i, uniformSimplex d i = 1 := (mem_stdSimplex_uniformSimplex hd).2
  simp_rw [sum_sub_distrib, hlog, ← sum_mul, hw_sum, one_mul]
  ring

/-- For any comparator $u \in \Delta^{d-1}$ and $\alpha \ge 0$, the shifted unnormalized negative
entropy is upper-bounded by $\alpha \ln d$:
$$\psi^{\mathrm{shift}}_\alpha(u) \le \alpha \ln d.$$ -/
theorem unnormEntropyShifted_le_log_card (α : ℝ) (hα : 0 ≤ α)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ stdSimplex (d := d)) :
    unnormEntropyShifted α u ≤ α * Real.log d := by
  dsimp [unnormEntropyShifted, unnormEntropy]
  have hu_sum : ∑ i, (u i * Real.log (u i) - u i) = (∑ i, u i * Real.log (u i)) - 1 := by
    rw [sum_sub_distrib, (mem_stdSimplex_iff u).mp hu |>.2]
  have h_nonpos := sum_mul_log_nonpos_of_mem_stdSimplex hu
  rw [hu_sum]
  nlinarith

/-- Base shifted regularizer $\psi^{\mathrm{shift}}_1(x) \ge 0$ on the standard simplex
$\Delta^{d-1}$ when $d > 0$. -/
theorem unnormEntropyShifted_nonneg_of_mem_stdSimplex (hd : 0 < d) (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ stdSimplex (d := d)) :
    0 ≤ unnormEntropyShifted 1 x := by
  have hw_pos : ∀ i, 0 < uniformSimplex d i := uniformSimplex_pos hd
  have hw_mem : uniformSimplex d ∈ stdSimplex (d := d) := mem_stdSimplex_uniformSimplex hd
  have h_sub := (hasFDerivAt_unnormEntropy 1 (uniformSimplex d) hw_pos).hasSubgradientWithinAt
    (convexOn_unnormEntropy_stdSimplex 1 (by norm_num)) hw_mem x hx
  rw [bregDiv_unnormEntropy_uniformSimplex 1 hd x hx, one_mul] at h_sub
  have h_sum : ∑ i, (x i * Real.log (x i) - x i) = (∑ i, x i * Real.log (x i)) - 1 := by
    rw [sum_sub_distrib, (mem_stdSimplex_iff x).mp hx |>.2]
  dsimp [unnormEntropyShifted, unnormEntropy]; rw [h_sum]; linarith

end Online.OCO.LEA
