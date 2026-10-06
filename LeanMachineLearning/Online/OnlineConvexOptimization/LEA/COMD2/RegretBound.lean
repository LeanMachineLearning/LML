/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.COMD2.Formula
public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.Common.Shift
public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.Common.Stability
public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Basic
import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.COMD2.Boundary

/-!
# Regret Bound for Online Mirror Descent in Learning with Expert Advice (LEA)

This file proves the multi-round regret bound for Learning with Expert Advice (LEA) using
Online Mirror Descent (OMD) with time-varying unnormalized negative entropy regularization
and non-negative loss subgradients $g_t \ge 0$.

## Main results

* `regret_bound`: The cumulative regret bound for the Exponential Weights
  (Hedge / Entropic OMD) trajectory `omdExpWeights hd α g`.
-/

open scoped BigOperators Bregman Topology
open Finset

@[expose] public section

namespace Online.OCO.LEA.COMD2

variable {d : ℕ}

/-- Cumulative regret upper bound for Exponential Weights (Hedge / Entropic OMD) with non-negative
losses $g_t \ge 0$, where the stability term is bounded directly with $w_t$:
$$\sum_{t=1}^T (l_t(w_t) - l_t(u)) \le \alpha_1 \ln d + (\psi_{\alpha(T+1)}(u) - \psi_{\alpha 1}(u))
  + \sum_{t=1}^T \frac{1}{2\alpha_t} \sum_{i=1}^d w_{t, i} (g_t)_i^2.$$ -/
theorem regret_bound (α : ℕ → ℝ) (T : ℕ)
    (hα_pos : ∀ t ∈ Ico 1 (T + 2), 0 < α t)
    (h_mono : ∀ t ∈ Ico 1 (T + 1), α t ≤ α (t + 1))
    (hd : 0 < d)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw_def : w = omdExpWeights hd α g)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ stdSimplex)
    (l : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hg : ∀ t ∈ Ico 1 (T + 1), HasSubgradientWithinAt (l t) (g t) stdSimplex (w t))
    (hg_nonneg : ∀ t ∈ Ico 1 (T + 1),
      ∀ i, 0 ≤ g t (EuclideanSpace.basisFun (Fin d) ℝ i)) :
    ∑ t ∈ Ico 1 (T + 1), (l t (w t) - l t u) ≤
      α 1 * Real.log d + (unnormEntropyShifted (α (T + 1)) u - unnormEntropyShifted (α 1) u)
      + ∑ t ∈ Ico 1 (T + 1), (1 / (2 * α t)) *
        ∑ i, (w t i) * (g t (EuclideanSpace.basisFun (Fin d) ℝ i)) ^ 2 := by
  subst hw_def
  have hw1 : omdExpWeights hd α g 1 = uniformSimplex d := omdExpWeights_one hd α g
  have hw : ∀ t ∈ Ico 1 (T + 2), omdExpWeights hd α g t ∈ stdSimplex (d := d) := fun t ht ↦
    omdExpWeights_mem_stdSimplex hd α g t (mem_Ico.mp ht).1
  have hw_pos : ∀ t ∈ Ico 1 (T + 2), ∀ i, 0 < omdExpWeights hd α g t i := fun t ht ↦
    omdExpWeights_pos hd α g t (mem_Ico.mp ht).1
  have h_decomp := regret_decomposition_eq (fun s ↦ unnormEntropyShifted (α s))
    (fun s ↦ unnormEntropyFDeriv (α s)) u (omdExpWeights hd α g) g l T
  have h_bound := boundary_shifted_le_log_card α (hα_pos 1 (by simp)).le T
    (hα_pos (T + 1) (by simp)).le hd u hu (omdExpWeights hd α g) hw1
    (hw (T + 1) (by simp)) (hw_pos (T + 1) (by simp))
  have h_opt_sum := omdExpWeights_sum_optimality_nonneg hd α g T
    (fun t ht ↦ hα_pos (t + 1) (by rw [mem_Ico] at ht ⊢; omega)) hu
  have h_lin_sum : ∑ t ∈ Ico 1 (T + 1), linearization u (omdExpWeights hd α g) g l t ≤ 0 :=
    sum_nonpos fun t ht ↦ by dsimp [linearization]; linarith [hg t ht u hu]
  have h_stab := sum_stability_le_dual_norm_wt (w := omdExpWeights hd α g) (g := g) α T
    (fun t ht ↦ hα_pos t (by rw [mem_Ico] at ht ⊢; omega)) hw_pos hg_nonneg
  have h_shift_le := sum_shift_unnormEntropyShifted_nonpos hd α (omdExpWeights hd α g) T h_mono hw
  linarith

end Online.OCO.LEA.COMD2
