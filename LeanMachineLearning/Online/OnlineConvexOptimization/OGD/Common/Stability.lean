/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.Common.RegretTerms
public import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.Common.Regularizer

/-!
# Stability Bound for Online Gradient Descent (OGD / OMD / FTRL)

This file bounds the stability term:
$$\mathrm{stability}_t = (g_t)(w_t - w_{t+1}) - D_{\psi_t}(w_{t+1}, w_t)$$
for Euclidean quadratic regularizer $\psi_t(w) = \frac{\alpha_t}{2} \|w\|^2$.

By Cauchy-Schwarz / Hölder's inequality on inner product spaces:
$$(g_t)(w_t - w_{t+1}) - \frac{\alpha_t}{2} \|w_{t+1} - w_t\|^2 \le \frac{1}{2\alpha_t} \|g_t\|^2.$$

## Main definitions
* `stability`: One-round stability tradeoff between loss reduction and regularizer divergence.

## Main results
* `stability_le_norm_sq`: One-round stability upper bound via Cauchy-Schwarz / Hölder.
* `sum_stability_le_norm_sq`: Cumulative multi-round stability upper bound.
-/

open scoped RealInnerProductSpace BigOperators Bregman
open Finset


@[expose] public section

namespace Online.OCO.OGD

variable {E : Type*} [NormedAddCommGroup E]

variable [InnerProductSpace ℝ E]

/-- One-round stability bound for Euclidean quadratic regularization via Cauchy-Schwarz / Hölder:
$$(g_t)(w_t - w_{t+1}) - \frac{\alpha_t}{2} \|w_{t+1} - w_t\|^2 \le
\frac{1}{2\alpha_t} \|g_t\|^2.$$ -/
theorem stability_le_norm_sq (α : ℕ → ℝ) (t : ℕ) (hα_pos : 0 < α t)
    (w : ℕ → E) (g : ℕ → (E →L[ℝ] ℝ)) :
    stability (fun s ↦ eucSq (α s)) (fun s ↦ eucSqFDeriv (α s)) w g t ≤
      (1 / (2 * α t)) * ‖g t‖^2 := by
  dsimp [stability]
  rw [bregDiv_eucSq_eq]
  have h_dual : (g t) (w t - w (t + 1)) ≤ ‖g t‖ * ‖w (t + 1) - w t‖ := by
    rw [norm_sub_rev (w (t + 1))]
    exact le_trans (le_abs_self _) ((g t).le_opNorm _)
  have h_scale :
    (2 * α t) * ((g t) (w t - w (t + 1)) - (α t / 2) * ‖w (t + 1) - w t‖^2) ≤ ‖g t‖^2 := by
    have h_sq : 0 ≤ (α t * ‖w (t + 1) - w t‖ - ‖g t‖)^2 := sq_nonneg _
    have h_expand :
      2 * α t * (‖g t‖ * ‖w (t + 1) - w t‖) - 2 * α t * ((α t / 2) * ‖w (t + 1) - w t‖^2) =
        ‖g t‖^2 - (α t * ‖w (t + 1) - w t‖ - ‖g t‖)^2 := by ring
    nlinarith
  have h_div := mul_le_mul_of_nonneg_left h_scale (show 0 ≤ 1 / (2 * α t) by positivity)
  have h_cancel :
    (1 / (2 * α t)) * ((2 * α t) * ((g t) (w t - w (t + 1)) - (α t / 2) * ‖w (t + 1) - w t‖^2)) =
      (g t) (w t - w (t + 1)) - (α t / 2) * ‖w (t + 1) - w t‖^2 := by
    field_simp [hα_pos.ne']
  rwa [h_cancel] at h_div

/-- Cumulative multi-round stability bound for Euclidean quadratic regularization:
$$\sum_{t=1}^T \mathrm{stability}_t \le \sum_{t=1}^T \frac{1}{2\alpha_t} \|g_t\|^2.$$ -/
theorem sum_stability_le_norm_sq (α : ℕ → ℝ) (T : ℕ)
    (hα_pos : ∀ t ∈ Ico 1 (T + 1), 0 < α t)
    (w : ℕ → E) (g : ℕ → (E →L[ℝ] ℝ)) :
    (∑ t ∈ Ico 1 (T + 1),
      stability (fun s ↦ eucSq (α s)) (fun s ↦ eucSqFDeriv (α s)) w g t) ≤
      ∑ t ∈ Ico 1 (T + 1), (1 / (2 * α t)) * ‖g t‖^2 :=
  sum_le_sum fun t ht ↦ stability_le_norm_sq α t (hα_pos t ht) w g

end Online.OCO.OGD
