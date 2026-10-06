/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.FTRL.RegretDecomposition
public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.Common.Regularizer

/-!
# Boundary Term Bound for Follow-the-Regularized-Leader (FTRL)

This file bounds the boundary term
$$\mathrm{boundary}(\psi, u, w, T) = \psi_{T+1}(u) - \psi_1(w_1)$$
for FTRL with shifted unnormalized negative entropy regularizers $\psi^{\mathrm{shift}}_t$.

## Main results

* `boundary_shifted_le_log_card`: Boundary term bound:
  $$\mathrm{boundary}(\psi^{\mathrm{shift}}_\alpha, u, w, T) \le
    \alpha_1 \ln d + (\psi^{\mathrm{shift}}_{\alpha(T+1)}(u) -
      \psi^{\mathrm{shift}}_{\alpha 1}(u)).$$
-/

open scoped BigOperators Bregman Topology
open Finset

@[expose] public section

namespace Online.OCO.LEA.FTRL

variable {d : ℕ}

/-- Boundary term bound for FTRL with uniform initialization $w_1 = (1/d, \dots, 1/d)$ and
sequence of shifted regularizers $\psi^{\mathrm{shift}}_t = \text{unnormEntropyShifted}(\alpha_t)$:
$$\mathrm{boundary}(\psi^{\mathrm{shift}}_\alpha, u, w, T)
  = \psi^{\mathrm{shift}}_{\alpha(T+1)}(u) - \psi^{\mathrm{shift}}_{\alpha 1}(w_1)
  \le \alpha_1 \ln d + (\psi^{\mathrm{shift}}_{\alpha(T+1)}(u) -
    \psi^{\mathrm{shift}}_{\alpha 1}(u)).$$ -/
theorem boundary_shifted_le_log_card (α : ℕ → ℝ) (hα1 : 0 ≤ α 1) (T : ℕ)
    (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ stdSimplex (d := d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw1 : w 1 = uniformSimplex d) :
    boundary (fun t ↦ unnormEntropyShifted (α t)) u w T ≤
      α 1 * Real.log d + (unnormEntropyShifted (α (T + 1)) u - unnormEntropyShifted (α 1) u) := by
  dsimp [boundary]
  rw [hw1, unnormEntropyShifted_uniformSimplex hd, sub_zero]
  have hu_le := unnormEntropyShifted_le_log_card (α 1) hα1 u hu
  linarith

end Online.OCO.LEA.FTRL
