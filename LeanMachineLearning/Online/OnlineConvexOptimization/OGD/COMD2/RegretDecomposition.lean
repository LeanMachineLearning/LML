/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.Common.RegretTerms

/-!
# Dynamic Regret Decomposition for Online Mirror Descent (OMD / Projected OGD)

This file defines the exact multi-round algebraic dynamic regret decomposition for
Online Mirror Descent (OMD) / Projected OGD on a real normed space $E$
with time-varying regularizers $\psi_t$.

## Main definitions
* `boundary`
* `pathlength`
* `linearization`
* `optimality`

## Main results
* `regret_decomposition_eq`: The dynamic algebraic multi-round regret equality for OMD.
-/

open scoped BigOperators Bregman
open Finset

@[expose] public section

namespace Online.OCO.OGD.COMD2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Terms

variable (ψ : ℕ → E → ℝ)
variable (gψ : ℕ → E → (E →L[ℝ] ℝ))
variable (u : ℕ → E)
variable (w : ℕ → E)
variable (g : ℕ → (E →L[ℝ] ℝ))
variable (l : ℕ → E → ℝ)

/-- Boundary term comprising initial and final Bregman divergences and regularizer drift at $u$. -/
def boundary (T : ℕ) : ℝ :=
  D_[ψ 1](u 0, w 1, gψ 1 (w 1))
  - D_[ψ (T + 1)](u T, w (T + 1), gψ (T + 1) (w (T + 1)))
  + ψ (T + 1) (u T) - ψ 1 (u 0)

/-- Linear coupling penalty measuring the variation in the comparator sequence $u_t$:
$$(g\psi_t(w_t))(u_{t-1} - u_t).$$ -/
def pathlength (t : ℕ) : ℝ :=
  (gψ t (w t)) (u (t - 1) - u t)

/-- Error incurred by linearizing the loss with subgradient `g_t` at $w_t$. -/
def linearization (t : ℕ) : ℝ :=
  - D_[l t](u t, w t, g t)

/-- First-order optimality deficit of the update step:
$$(g_t + \nabla\psi_{t+1}(w_{t+1}) - \nabla\psi_t(w_t))(u_t - w_{t+1}).$$ -/
def optimality (t : ℕ) : ℝ :=
  (g t + gψ (t + 1) (w (t + 1)) - gψ t (w t)) (u t - w (t + 1))

/-- Exact multi-round algebraic dynamic regret decomposition for OMD / Projected OGD. -/
theorem regret_decomposition_eq (T : ℕ) :
    (∑ t ∈ Ico 1 (T + 1), (l t (w t) - l t (u t))) =
    boundary ψ gψ u w T
    + (∑ t ∈ Ico 1 (T + 1), pathlength gψ u w t)
    + (∑ t ∈ Ico 1 (T + 1), OGD.stability ψ gψ w g t)
    + (∑ t ∈ Ico 1 (T + 1), OGD.shift ψ w t)
    - (∑ t ∈ Ico 1 (T + 1), optimality gψ u w g t)
    + (∑ t ∈ Ico 1 (T + 1), linearization u w g l t) := by
  induction T with
  | zero =>
    simp [boundary]
  | succ T ih =>
    simp_rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ T + 1), ih]
    dsimp [boundary, pathlength, optimality, OGD.shift, OGD.stability, linearization, bregDiv]
    simp only [map_sub, add_apply, sub_apply]
    ring

end Terms

end Online.OCO.OGD.COMD2
