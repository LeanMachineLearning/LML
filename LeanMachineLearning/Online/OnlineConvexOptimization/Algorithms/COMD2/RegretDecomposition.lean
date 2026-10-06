/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.Basic

/-!
# Master Regret Decomposition for Centered Online Mirror Descent (COMD2)

This file establishes the exact multi-round algebraic regret decomposition for Centered
Online Mirror Descent (version 2) with pure potential shifts and direct regularizer updates,
as a variation of Lemma A.1.1 (Strong Centered Mirror Descent Lemma) from Andrew Jacobsen's thesis,
*Adapting to Non-Stationarity in Online Learning*.

The regret decomposition holds for any sequence of comparators `u_t` and any sequence
of centering potentials `φ_t`. Specializations (e.g. static regret `u_t = u`, or uncentered
settings `φ_t = 0`) are derived as corollaries in separate modules.

## Main definitions
* `boundary`
* `linearization`
* `pathlength`
* `stability`
* `optimality`
* `centering`
* `adjustment`
* `shift`

## Main results
* `regret_decomposition_eq`: The master multi-round algebraic regret equality holding
  for all $T \ge 0$.
-/

open scoped BigOperators Bregman
open Finset

@[expose] public section

namespace OnlineConvexOptimization.COMD2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Auxiliary Term Definitions -/

section AuxTerms

variable (η : ℝ)
variable (ψ φ : ℕ → E → ℝ)
variable (gψ gφ : ℕ → E → (E →L[ℝ] ℝ))
variable (u w w_tilde : ℕ → E)
variable (g : ℕ → (E →L[ℝ] ℝ))
variable (l : ℕ → E → ℝ)

/-- Boundary term comprising initial and final Bregman divergences anchored at $\tilde{w}_1$:
$$D_{\psi_1}(u_0,\tilde w_1,g\psi_1(\tilde w_1))
  - D_{\psi_{T+1}}(u_T,\tilde w_{T+1},g\psi_{T+1}(\tilde w_{T+1}))
  + \psi_{T+1}(u_T) - \psi_1(u_0).$$ -/
def boundary (T : ℕ) : ℝ :=
  D_[ψ 1](u 0, w_tilde 1, gψ 1 (w_tilde 1))
  - D_[ψ (T + 1)](u T, w_tilde (T + 1), gψ (T + 1) (w_tilde (T + 1)))
  + ψ (T + 1) (u T) - ψ 1 (u 0)

/-- Linearization slack from replacing $l_t$ with $g_t$: $-D_{l_t}(u_t, w_{t+1}, g_t)$. -/
def linearization (t : ℕ) : ℝ :=
  - D_[l t](u t, w (t + 1), g t)

/-- Regret budget for varying comparator:
$$(g\psi_t(\tilde w_t))(u_{t-1} - u_t).$$ -/
def pathlength (t : ℕ) : ℝ :=
  gψ t (w_tilde t) (u (t - 1) - u t)

/-- One-round stability penalty balancing the movement of the loss `l_t` between
the anchor `w̃_t` and iterate `w_{t+1}` against the divergence regularizer step:
$$\eta\,(l_t(\tilde w_t) - l_t(w_{t+1}))
  - D_{\psi_t}(w_{t+1}, \tilde w_t, g\psi_t(\tilde w_t)).$$ -/
def stability (t : ℕ) : ℝ :=
  η * (l t (w_tilde t) - l t (w (t + 1))) - D_[ψ t](w (t + 1), w_tilde t, gψ t (w_tilde t))

/-- Encodes the update implicitly via first-order optimality conditions:
$$(\eta\,g_t + g\varphi_t(w_{t+1}) + g\psi_{t+1}(w_{t+1}) - g\psi_t(\tilde w_t))(u_t - w_{t+1}).$$
$\text{optimality}(t) \le 0$ when $w_{t+1}$ satisfies first-order optimality. -/
def optimality (t : ℕ) : ℝ :=
  ((η : ℝ) • g t + gφ t (w (t + 1)) + gψ (t + 1) (w (t + 1)) - gψ t (w_tilde t)) (u t - w (t + 1))

/-- Surplus contribution induced by the centering potential `φ_t`:
$$\varphi_t(u_t) - \varphi_t(w_{t+1}) - D_{\varphi_t}(u_t, w_{t+1}, g\varphi_t(w_{t+1})).$$
Zero when no centering is used (`φ_t = 0`). -/
def centering (t : ℕ) : ℝ :=
  φ t (u t) - φ t (w (t + 1)) - D_[φ t](u t, w (t + 1), gφ t (w (t + 1)))

/-- Divergence drift capturing arbitrary post-processing or state adjustments
from iterate `w_{t+1}` to anchor `w̃_{t+1}`:
$$D_{\psi_{t+1}}(u_t,\tilde w_{t+1},g\psi_{t+1}(\tilde w_{t+1}))
  - D_{\psi_{t+1}}(u_t,w_{t+1},g\psi_{t+1}(w_{t+1})).$$
Vanishes for unadjusted or projection-free
updates (`w̃_{t+1} = w_{t+1}`), and yields small controllable penalties for schemes
like Fixed Share. -/
def adjustment (t : ℕ) : ℝ :=
  D_[ψ (t+1)](u t, w_tilde (t + 1), gψ (t+1) (w_tilde (t + 1)))
  - D_[ψ (t+1)](u t, w (t + 1), gψ (t+1) (w (t + 1)))

/-- Regularizer shift evaluated on iterate $w_{t+1}$:
$$-(\psi_{t+1} - \psi_t)(w_{t+1}).$$ -/
def shift (t : ℕ) : ℝ :=
  - (ψ (t + 1) - ψ t) (w (t + 1))

/-- Master Centered Online Mirror Descent (version 2) Regret Decomposition Identity
(variation of Andrew Jacobsen, *Adapting to Non-Stationarity in Online Learning*, Lemma A.1.1). -/
theorem regret_decomposition_eq (T : ℕ) :
    η * (∑ t ∈ Ico 1 (T + 1), (l t (w_tilde t) - l t (u t))) =
    boundary ψ gψ u w_tilde T
    + (∑ t ∈ Ico 1 (T + 1), adjustment ψ gψ u w w_tilde t)
    + (∑ t ∈ Ico 1 (T + 1), pathlength gψ u w_tilde t)
    + (∑ t ∈ Ico 1 (T + 1), stability η ψ gψ w w_tilde l t)
    + (∑ t ∈ Ico 1 (T + 1), shift ψ w t)
    - (∑ t ∈ Ico 1 (T + 1), optimality η gψ gφ u w w_tilde g t)
    + (∑ t ∈ Ico 1 (T + 1), centering φ gφ u w t)
    + η * (∑ t ∈ Ico 1 (T + 1), linearization u w g l t) := by
  induction T with
  | zero => simp [boundary]
  | succ T ih =>
    simp_rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ T + 1), mul_add, ih]
    dsimp [boundary, optimality, adjustment, shift, pathlength,
      stability, centering, linearization, bregDiv]
    simp only [map_sub, add_apply, sub_apply, smul_apply, smul_eq_mul]
    ring

end AuxTerms

end OnlineConvexOptimization.COMD2
