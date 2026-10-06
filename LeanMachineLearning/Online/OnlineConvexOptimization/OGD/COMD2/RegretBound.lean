/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.Common.Regularizer
public import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.Common.Shift
public import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.Common.Stability
import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.COMD2.Boundary
import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.COMD2.Optimality
import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.COMD2.Pathlength

/-!
# Regret Bound for Online Mirror Descent (OMD / Projected OGD)

This file proves the multi-round cumulative dynamic regret bound for Online Mirror Descent
(OMD / Projected OGD) on an arbitrary convex set $s \subseteq E$:
$$\sum_{t=1}^T (l_t(w_t) - l_t(u_t)) \le
  \frac{\alpha_{T+1}}{2} \|u_T\|^2 + R_w \sum_{t=1}^T \alpha_t \|u_{t-1} - u_t\| +
  \sum_{t=1}^T \frac{1}{2\alpha_t} \|g_t\|^2.$$

## Main results
* `regret_bound`: The cumulative dynamic regret bound for OMD on an arbitrary convex set $s$.
-/

open scoped RealInnerProductSpace BigOperators Bregman Topology
open Finset

@[expose] public section

namespace Online.OCO.OGD.COMD2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cumulative dynamic regret upper bound for Euclidean OMD / Projected OGD on convex set $s$:
$$\sum_{t=1}^T (l_t(w_t) - l_t(u_t)) \le
  \frac{\alpha_{T+1}}{2} \|u_T\|^2 + R_w \sum_{t=1}^T \alpha_t \|u_{t-1} - u_t\| +
  \sum_{t=1}^T \frac{1}{2\alpha_t} \|g_t\|^2.$$ -/
theorem regret_bound (T : ℕ)
    (α : ℕ → ℝ) (hα_pos : ∀ t ∈ Ico 1 (T + 2), 0 < α t)
    (h_mono : ∀ t ∈ Ico 1 (T + 1), α t ≤ α (t + 1))
    (s : Set E) (hs : Convex ℝ s)
    (l : ℕ → E → ℝ)
    (g : ℕ → (E →L[ℝ] ℝ))
    (w : ℕ → E) (hw1 : w 1 = 0)
    (hw_mem : ∀ t ∈ Ico 1 (T + 2), w t ∈ s)
    (hw_min : ∀ t ∈ Ico 1 (T + 1),
      IsMinOn (fun x ↦ (g t) x + (α (t + 1) / 2) * ‖x‖ ^ 2 - α t * ⟪w t, x⟫) s (w (t + 1)))
    (hg : ∀ t ∈ Ico 1 (T + 1), HasSubgradientWithinAt (l t) (g t) s (w t))
    (u : ℕ → E) (hu : ∀ t ∈ Ico 1 (T + 1), u t ∈ s)
    (R_w : ℝ) (hw_norm : ∀ t ∈ Ico 1 (T + 1), ‖w t‖ ≤ R_w) :
    ∑ t ∈ Ico 1 (T + 1), (l t (w t) - l t (u t)) ≤
      (α (T + 1) / 2) * ‖u T‖^2
      + R_w * (∑ t ∈ Ico 1 (T + 1), α t * ‖u (t - 1) - u t‖)
      + ∑ t ∈ Ico 1 (T + 1), (1 / (2 * α t)) * ‖g t‖^2 := by
  have hT1 : T + 1 ∈ Ico 1 (T + 2) := by rw [mem_Ico]; omega
  have h_bound := boundary_eucSq_le α T (hα_pos (T + 1) hT1).le u w hw1
  have h_shift := OGD.sum_shift_eucSq_nonpos α w T h_mono
  have h_stab := OGD.sum_stability_le_norm_sq α T
    (fun t ht ↦ hα_pos t (Ico_subset_Ico_right (by omega) ht)) w g
  have h_path := sum_pathlength_eucSq_le α T
    (fun t ht ↦ (hα_pos t (Ico_subset_Ico_right (by omega) ht)).le) u w R_w hw_norm
  have h_lin : ∑ t ∈ Ico 1 (T + 1), linearization u w g l t ≤ 0 :=
    sum_nonpos fun t ht ↦ by dsimp [linearization]; linarith [hg t ht (u t) (hu t ht)]
  have h_opt := sum_optimality_nonneg_of_isMinOn
    (ψ := fun k ↦ eucSq (α k)) (gψ := fun k ↦ eucSqFDeriv (α k)) T
    (fun t _ ↦ hasFDerivAt_eucSq (α (t + 1)) (w (t + 1)))
    (fun t ht ↦ convexOn_eucSq (α (t + 1))
      (hα_pos (t + 1) (by rw [mem_Ico] at ht ⊢; omega)).le s hs)
    hw_mem hu hw_min
  linarith [regret_decomposition_eq (fun k ↦ eucSq (E := E) (α k))
    (fun k ↦ eucSqFDeriv (α k)) u w g l T]

end Online.OCO.OGD.COMD2
