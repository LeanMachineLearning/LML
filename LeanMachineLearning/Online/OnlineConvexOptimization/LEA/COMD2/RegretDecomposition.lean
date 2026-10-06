/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.Common.RegretTerms

/-!
# Static Regret Decomposition for Online Mirror Descent (LEA Specialization)

This file defines the direct, algebraic regret decomposition for Online Mirror Descent
tailored to the Learning with Expert Advice (LEA) setting:
* **Static comparator**: $u_t = u$ for all rounds $t$.
* **No centering**: $\varphi_t = 0$.
* **No state adjustment**: $\tilde{w}_t = w_t$.

Under these conditions, the regret is governed by the boundary divergence & potential drift,
and four per-round regret terms:
1. `boundary`: Initial divergence minus final divergence plus regularizer drift at $u$.
2. `stability`: Movement of the loss balanced against regularizer divergence (from `LEA.Common`).
3. `shift`: Cross-round regularizer potential drift on iterates $w_t$ (from `LEA.Common`).
4. `optimality`: First-order optimality deficit of the update step.
5. `linearization`: Loss linearization error via subgradients.

## Main definitions
* `boundary`
* `linearization`
* `optimality`

## Main results
* `regret_decomposition_eq`: The algebraic multi-round regret equality.
-/

open scoped BigOperators Bregman
open Finset

@[expose] public section

namespace Online.OCO.LEA.COMD2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Terms

variable (ψ : ℕ → E → ℝ)
variable (gψ : ℕ → E → (E →L[ℝ] ℝ))
variable (u : E)
variable (w : ℕ → E)
variable (g : ℕ → (E →L[ℝ] ℝ))
variable (l : ℕ → E → ℝ)

/-- Boundary term comprising initial and final Bregman divergences and regularizer drift at $u$. -/
def boundary (T : ℕ) : ℝ :=
  D_[ψ 1](u, w 1, gψ 1 (w 1))
  - D_[ψ (T + 1)](u, w (T + 1), gψ (T + 1) (w (T + 1)))
  + ψ (T + 1) u - ψ 1 u

/-- Error incurred by linearizing the loss with subgradient `g_t` at $w_t$. -/
def linearization (t : ℕ) : ℝ :=
  - D_[l t](u, w t, g t)

/-- Encodes the update implicitly via first-order optimality conditions:
$\text{optimality}(t) \le 0$ when $w_{t+1}$ satisfies first-order optimality. -/
def optimality (t : ℕ) : ℝ :=
  (g t + gψ (t + 1) (w (t + 1)) - gψ t (w t)) (u - w (t + 1))

/-- Exact multi-round algebraic regret decomposition for static, uncentered, unadjusted OMD. -/
theorem regret_decomposition_eq (T : ℕ) :
    (∑ t ∈ Ico 1 (T + 1), (l t (w t) - l t u)) =
    boundary ψ gψ u w T
    + (∑ t ∈ Ico 1 (T + 1), LEA.stability ψ gψ w g t)
    + (∑ t ∈ Ico 1 (T + 1), LEA.shift ψ w t)
    - (∑ t ∈ Ico 1 (T + 1), optimality gψ u w g t)
    + (∑ t ∈ Ico 1 (T + 1), linearization u w g l t) := by
  induction T with
  | zero =>
    simp [boundary]
  | succ T ih =>
    simp_rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ T + 1), ih]
    dsimp [boundary, optimality, LEA.shift, LEA.stability, linearization, bregDiv]
    simp only [map_sub, add_apply, sub_apply]
    ring

end Terms

end Online.OCO.LEA.COMD2
