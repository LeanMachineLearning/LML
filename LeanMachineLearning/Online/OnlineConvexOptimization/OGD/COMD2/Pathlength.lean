/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.COMD2.RegretDecomposition
public import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.Common.Regularizer

/-!
# Pathlength Term Bound for OMD Dynamic Regret

This file bounds the dynamic comparator pathlength term:
$$\mathrm{pathlength}_t = (g\psi_t(w_t))(u_{t-1} - u_t)$$
for Euclidean quadratic regularizers $\psi_t(w) = \frac{\alpha_t}{2} \|w\|^2$, where
$\nabla\psi_t(w_t) = \alpha_t \langle w_t, \cdot \rangle$.

By Cauchy-Schwarz:
$$\mathrm{pathlength}_t \le \alpha_t \|w_t\| \|u_{t-1} - u_t\|.$$

## Main results
* `pathlength_eucSq_le`: Upper bound on one-round pathlength via Cauchy-Schwarz.
* `sum_pathlength_eucSq_le`: Cumulative pathlength bound over rounds $t \in [1, T]$.
-/

open scoped RealInnerProductSpace BigOperators
open Finset

set_option linter.style.longLine false

@[expose] public section

namespace Online.OCO.OGD.COMD2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One-round pathlength upper bound for Euclidean quadratic regularizer via Cauchy-Schwarz:
$$\mathrm{pathlength}_t \le \alpha_t \|w_t\| \|u_{t-1} - u_t\|.$$ -/
theorem pathlength_eucSq_le (α : ℕ → ℝ) (t : ℕ) (hα_nonneg : 0 ≤ α t)
    (u : ℕ → E) (w : ℕ → E) :
    pathlength (fun s ↦ eucSqFDeriv (α s)) u w t ≤
      α t * ‖w t‖ * ‖u (t - 1) - u t‖ := by
  dsimp [pathlength]
  rw [eucSqFDeriv_apply]
  nlinarith [real_inner_le_norm (w t) (u (t - 1) - u t)]

/-- Cumulative pathlength upper bound for Euclidean quadratic regularizer with bounded iterates $\|w_t\| \le R$:
$$\sum_{t=1}^T \mathrm{pathlength}_t \le R \sum_{t=1}^T \alpha_t \|u_{t-1} - u_t\|.$$ -/
theorem sum_pathlength_eucSq_le (α : ℕ → ℝ) (T : ℕ)
    (hα_nonneg : ∀ t ∈ Ico 1 (T + 1), 0 ≤ α t)
    (u : ℕ → E) (w : ℕ → E) (R : ℝ) (hw_norm : ∀ t ∈ Ico 1 (T + 1), ‖w t‖ ≤ R) :
    ∑ t ∈ Ico 1 (T + 1), pathlength (fun s ↦ eucSqFDeriv (α s)) u w t ≤
      R * ∑ t ∈ Ico 1 (T + 1), α t * ‖u (t - 1) - u t‖ := by
  rw [mul_sum]
  refine sum_le_sum fun t ht ↦ ?_
  have h1 := pathlength_eucSq_le α t (hα_nonneg t ht) u w
  have h2 : α t * ‖w t‖ * ‖u (t - 1) - u t‖ ≤ R * (α t * ‖u (t - 1) - u t‖) := by
    have := mul_le_mul_of_nonneg_right (hw_norm t ht)
      (mul_nonneg (hα_nonneg t ht) (norm_nonneg (u (t - 1) - u t)))
    linarith
  exact h1.trans h2

end Online.OCO.OGD.COMD2

