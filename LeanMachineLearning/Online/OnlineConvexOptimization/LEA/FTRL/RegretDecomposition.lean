/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.Common.RegretTerms

/-!
# Static Regret Decomposition for Follow-the-Regularized-Leader (FTRL)

This file defines the exact multi-round algebraic regret decomposition for
Follow-the-Regularized-Leader (FTRL) in the Learning with Expert Advice (LEA) setting,
where the predictor optimizes the cumulative linearized objective
$$F_t(y) = \psi_t(y) + \sum_{i=1}^{t-1} g_i(y).$$

## Main definitions
* `FObj`
* `boundary`
* `linearization`
* `optimality`
* `terminalOptimality`

## Main results
* `regret_decomposition_eq`: The algebraic multi-round regret equality for FTRL.
-/

open scoped BigOperators Bregman
open Finset

@[expose] public section

namespace Online.OCO.LEA.FTRL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Terms

variable (ψ : ℕ → E → ℝ)
variable (gψ : ℕ → E → (E →L[ℝ] ℝ))
variable (u : E)
variable (w : ℕ → E)
variable (g : ℕ → (E →L[ℝ] ℝ))
variable (l : ℕ → E → ℝ)

/--
The cumulative linearized objective function $F_t(y) = \psi_t(y) + \sum_{i=1}^{t-1} g_i(y)$.
-/
def FObj (t : ℕ) (y : E) : ℝ :=
  ψ t y + ∑ i ∈ Ico 1 t, g i y

/-- Boundary regularizer term: $\psi_{T+1}(u) - \psi_1(w_1)$. -/
def boundary (T : ℕ) : ℝ :=
  ψ (T + 1) u - ψ 1 (w 1)

/-- Error incurred by linearizing the loss with subgradient `g_t` at $w_t$. -/
def linearization (t : ℕ) : ℝ :=
  - D_[l t](u, w t, g t)

/-- First-order optimality deficit of iterate $w_t$ under the cumulative objective $F_t$. -/
def optimality (t : ℕ) : ℝ :=
  (gψ t (w t) + ∑ i ∈ Ico 1 t, g i) (w (t + 1) - w t)

/-- Terminal optimality deficit of $w_{T+1}$ under full objective $F_{T+1}$ relative to $u$. -/
def terminalOptimality (T : ℕ) : ℝ :=
  FObj ψ g (T + 1) (w (T + 1)) - FObj ψ g (T + 1) u

/-- Exact multi-round algebraic regret decomposition for FTRL with cumulative linearized losses. -/
theorem regret_decomposition_eq (T : ℕ) :
    (∑ t ∈ Ico 1 (T + 1), (l t (w t) - l t u)) =
    boundary ψ u w T
    + (∑ t ∈ Ico 1 (T + 1), LEA.shift ψ w t)
    + (∑ t ∈ Ico 1 (T + 1), LEA.stability ψ gψ w g t)
    + (∑ t ∈ Ico 1 (T + 1), linearization u w g l t)
    - (∑ t ∈ Ico 1 (T + 1), optimality gψ w g t)
    + terminalOptimality ψ u w g T := by
  induction T with
  | zero =>
    simp [boundary, terminalOptimality, FObj]
  | succ T ih =>
    simp_rw [sum_Ico_succ_top (by omega : 1 ≤ T + 1), ih]
    dsimp [boundary, terminalOptimality, LEA.shift, LEA.stability, linearization, optimality,
      bregDiv, FObj]
    simp only [map_sub, add_apply, _root_.sum_apply]
    simp_rw [sum_sub_distrib, sum_Ico_succ_top (by omega : 1 ≤ T + 1)]
    ring

end Terms

end Online.OCO.LEA.FTRL
