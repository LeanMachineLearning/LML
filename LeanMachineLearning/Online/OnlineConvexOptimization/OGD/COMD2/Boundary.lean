/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.COMD2.RegretDecomposition
public import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.Common.Regularizer

/-!
# Boundary Term Bound for Euclidean OMD / Projected OGD

This file bounds the dynamic boundary term:
$$\mathrm{boundary}(\psi_\alpha, \nabla\psi_\alpha, u, w, T) =
  D_{\psi_1}(u_0, w_1) - D_{\psi_{T+1}}(u_T, w_{T+1}) + \psi_{T+1}(u_T) - \psi_1(u_0)$$
for $\psi_t(w) = \frac{\alpha_t}{2} \|w\|^2$.

When initialized at $w_1 = 0$ and $\alpha_{T+1} \ge 0$:
$$\mathrm{boundary}(\psi_\alpha, \nabla\psi_\alpha, u, w, T) \le \frac{\alpha_{T+1}}{2} \|u_T\|^2.$$

## Main results
* `boundary_eucSq_le`: Upper bound on the boundary term for dynamic comparators.
-/

open scoped RealInnerProductSpace BigOperators

@[expose] public section

namespace Online.OCO.OGD.COMD2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Boundary term bound for Euclidean quadratic regularizer in OMD / Projected OGD:
$$\mathrm{boundary}(\psi_\alpha, \nabla\psi_\alpha, u, w, T) \le \frac{\alpha_{T+1}}{2} \|u_T\|^2$$
when $w_1 = 0$ and $\alpha_{T+1} \ge 0$. -/
theorem boundary_eucSq_le (α : ℕ → ℝ) (T : ℕ) (hα : 0 ≤ α (T + 1))
    (u : ℕ → E) (w : ℕ → E) (hw1 : w 1 = 0) :
    boundary (fun s ↦ eucSq (α s)) (fun s ↦ eucSqFDeriv (α s)) u w T ≤
      (α (T + 1) / 2) * ‖u T‖^2 := by
  dsimp [boundary, eucSq]
  rw [bregDiv_eucSq_eq, bregDiv_eucSq_eq, hw1, sub_zero]
  have h_div_nonneg : 0 ≤ (α (T + 1) / 2) * ‖u T - w (T + 1)‖^2 := by
    have : 0 ≤ α (T + 1) / 2 := by linarith
    positivity
  linarith

end Online.OCO.OGD.COMD2
