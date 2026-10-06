/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.FTRL.RegretDecomposition
public import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.Common.Regularizer

/-!
# Boundary Term Bound for Euclidean FTRL / Lazy OGD

This file bounds the boundary term:
$$\mathrm{boundary}(\psi, u, w, T) = \psi_{T+1}(u) - \psi_1(w_1)$$
for $\psi_t(w) = \frac{\alpha_t}{2} \|w\|^2$.

When initialized at $w_1 = 0$ (or $\|w_1\| \ge 0$), and $\|u\| \le R$:
$$\mathrm{boundary}(\psi_\alpha, u, w, T) \le \frac{\alpha_{T+1}}{2} R^2.$$

## Main results
* `boundary_eucSq_le`: Upper bound on the boundary term.
-/

open scoped RealInnerProductSpace BigOperators

@[expose] public section

namespace Online.OCO.OGD.FTRL

variable {E : Type*} [NormedAddCommGroup E]

/-- Exact boundary term formula for Euclidean quadratic regularization initialized at $w_1 = 0$:
$$\mathrm{boundary}(\psi_\alpha, u, w, T) = \frac{\alpha_{T+1}}{2} \|u\|^2.$$ -/
theorem boundary_eucSq_eq (α : ℕ → ℝ) (T : ℕ)
    (u : E) (w : ℕ → E) (hw1 : w 1 = 0) :
    boundary (fun s ↦ eucSq (α s)) u w T = (α (T + 1) / 2) * ‖u‖^2 := by
  dsimp [boundary, eucSq]
  rw [hw1, norm_zero, zero_pow two_ne_zero, mul_zero, sub_zero]

/-- Boundary term bound for Euclidean quadratic regularization:
$$\mathrm{boundary}(\psi_\alpha, u, w, T) \le \frac{\alpha_{T+1}}{2} R^2$$
when $\|u\| \le R$, $w_1 = 0$, and $\alpha_{T+1} \ge 0$. -/
theorem boundary_eucSq_le (α : ℕ → ℝ) (T : ℕ) (hα : 0 ≤ α (T + 1)) (R : ℝ)
    (u : E) (hu_norm : ‖u‖ ≤ R)
    (w : ℕ → E) (hw1 : w 1 = 0) :
    boundary (fun s ↦ eucSq (α s)) u w T ≤ (α (T + 1) / 2) * R^2 := by
  rw [boundary_eucSq_eq α T u w hw1]
  have h_scale : 0 ≤ α (T + 1) / 2 := by linarith
  have h_sq : ‖u‖^2 ≤ R^2 := by nlinarith [norm_nonneg u]
  nlinarith

end Online.OCO.OGD.FTRL
