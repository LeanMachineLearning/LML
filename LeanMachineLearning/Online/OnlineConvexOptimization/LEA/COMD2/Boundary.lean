/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.COMD2.RegretDecomposition
public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.Common.Regularizer
import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Deriv

/-!
# Boundary Term Bound for Learning with Expert Advice (LEA)

This file bounds the boundary term
$$\mathrm{boundary}(\psi, \nabla\psi, u, w, T) =
  D_{\psi_1}(u, w_1) - D_{\psi_{T+1}}(u, w_{T+1}) + \psi_{T+1}(u) - \psi_1(u)$$
for LEA under shifted unnormalized negative entropy regularizers $\psi^{\mathrm{shift}}_t$
when the initial iterate $w_1$ is chosen as the uniform distribution on the standard simplex
$\Delta^{d-1}$:
$$w_1 = \left( \frac{1}{d}, \dots, \frac{1}{d} \right) \in \Delta^{d-1}.$$

## Main results

* `boundary_shifted_le_log_card`: When $\alpha_1 \ge 0, \alpha_{T+1} \ge 0$,
  the multi-round boundary term satisfies:
  $$\mathrm{boundary}(\psi^{\mathrm{shift}}_\alpha, \nabla\psi_\alpha, u, w, T)
    \le \alpha_1 \ln d + (\psi^{\mathrm{shift}}_{\alpha(T+1)}(u) -
      \psi^{\mathrm{shift}}_{\alpha 1}(u)).$$
-/

open scoped BigOperators Bregman Topology
open Finset

@[expose] public section

namespace Online.OCO.LEA.COMD2

variable {d : ℕ}

/-- Boundary term bound for LEA with uniform initialization $w_1 = (1/d, \dots, 1/d)$ and
sequence of shifted regularizers $\psi^{\mathrm{shift}}_t = \text{unnormEntropyShifted}(\alpha_t)$
with $\alpha_1 \ge 0$ and $\alpha_{T+1} \ge 0$:
$$\mathrm{boundary}(\psi^{\mathrm{shift}}_\alpha, \nabla\psi_\alpha, u, w, T)
  \le \alpha_1 \ln d + (\psi^{\mathrm{shift}}_{\alpha(T+1)}(u) -
    \psi^{\mathrm{shift}}_{\alpha 1}(u)).$$ -/
theorem boundary_shifted_le_log_card (α : ℕ → ℝ) (hα1 : 0 ≤ α 1) (T : ℕ)
    (hαT : 0 ≤ α (T + 1)) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ stdSimplex)
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw1 : w 1 = uniformSimplex d)
    (hwT : w (T + 1) ∈ stdSimplex (d := d))
    (hwT_pos : ∀ i, 0 < w (T + 1) i) :
    boundary (fun t ↦ unnormEntropyShifted (α t)) (fun t ↦ unnormEntropyFDeriv (α t)) u w T ≤
      α 1 * Real.log d + (unnormEntropyShifted (α (T + 1)) u - unnormEntropyShifted (α 1) u) := by
  dsimp [boundary]
  simp only [bregDiv_unnormEntropyShifted, hw1]
  have h_breg_end :=
    (hasFDerivAt_unnormEntropy (α (T + 1)) (w (T + 1)) hwT_pos).hasSubgradientWithinAt
      (convexOn_unnormEntropy_stdSimplex (α (T + 1)) hαT) hwT u hu
  have h_init := bregDiv_unnormEntropy_uniformSimplex_le (α 1) hα1 hd u hu
  linarith

end Online.OCO.LEA.COMD2
