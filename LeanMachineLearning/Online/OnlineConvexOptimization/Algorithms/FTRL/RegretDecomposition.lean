/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Master Regret Decomposition for Follow-the-Regularized-Leader (FTRL)

This file establishes the exact multi-round algebraic regret decomposition for
Follow-the-Regularized-Leader (FTRL), corresponding to Lemma 7.1 in Francesco Orabona's
*A Modern Introduction to Online Learning* (v10). Writing
$F_t(x) = \psi_t(x) + \sum_{i=1}^{t-1} \ell_i(x)$ and
$x_t \in \arg\min_{x \in V} F_t(x)$, the regret satisfies, for all $u$,
$$\sum_{t=1}^T (\ell_t(x_t) - \ell_t(u))
  = \psi_{T+1}(u) - \min_{x \in V} \psi_1(x)
  + \sum_{t=1}^T (F_t(x_t) - F_{t+1}(x_{t+1}) + \ell_t(x_t))
  + F_{T+1}(x_{T+1}) - F_{T+1}(u).$$

## Main definitions
* `Fobj`
* `boundary`
* `stability`
* `terminalOptimality`

## Main results
* `regret_decomposition_eq`: The master algebraic regret equality holding for all $T \ge 0$.
-/

open scoped BigOperators
open Finset

@[expose] public section

namespace OnlineConvexOptimization.FTRL

variable {E : Type*}

section Terms

variable (ψ : ℕ → E → ℝ)
variable (u : E)
variable (w : ℕ → E)
variable (l : ℕ → E → ℝ)

/--
Cumulative objective (Orabona's $F_t$): $F_t(x) = \psi_t(x) + \sum_{i=1}^{t-1} \ell_i(x)$.
-/
def Fobj (t : ℕ) (y : E) : ℝ :=
  ψ t y + ∑ i ∈ Ico 1 t, l i y

/-- Boundary term: $\psi_{T+1}(u) - \min_{x \in V} \psi_1(x) = \psi_{T+1}(u) - F_1(x_1)$. -/
def boundary (T : ℕ) : ℝ :=
  ψ (T + 1) u - Fobj ψ l 1 (w 1)

/-- One-round stability penalty $F_t(x_t) - F_{t+1}(x_{t+1}) + \ell_t(x_t)$,
measuring the advance of $F_t + \ell_t$ between $x_t$ and $x_{t+1}$. -/
def stability (t : ℕ) : ℝ :=
  Fobj ψ l t (w t) - Fobj ψ l (t + 1) (w (t + 1)) + l t (w t)

/-- Terminal optimality deficit $F_{T+1}(x_{T+1}) - F_{T+1}(u)$ of $x_{T+1}$ relative to $u$. -/
def terminalOptimality (T : ℕ) : ℝ :=
  Fobj ψ l (T + 1) (w (T + 1)) - Fobj ψ l (T + 1) u

/-- Master Algebraic Regret Decomposition Identity for FTRL (Orabona, Lemma 7.1):
$$\sum_{t=1}^T (\ell_t(x_t) - \ell_t(u))
  = \psi_{T+1}(u) - \min_{x \in V} \psi_1(x)
  + \sum_{t=1}^T (F_t(x_t) - F_{t+1}(x_{t+1}) + \ell_t(x_t))
  + F_{T+1}(x_{T+1}) - F_{T+1}(u).$$ -/
theorem regret_decomposition_eq (T : ℕ) :
    (∑ t ∈ Ico 1 (T + 1), (l t (w t) - l t u)) =
    boundary ψ u w l T
    + (∑ t ∈ Ico 1 (T + 1), stability ψ w l t)
    + terminalOptimality ψ u w l T := by
  induction T with
  | zero =>
    simp [boundary, terminalOptimality, Fobj]
  | succ T ih =>
    simp_rw [sum_Ico_succ_top (by omega : 1 ≤ T + 1), ih]
    dsimp [boundary, terminalOptimality, stability, Fobj]
    simp_rw [sum_Ico_succ_top (by omega : 1 ≤ T + 1)]
    ring

end Terms

end OnlineConvexOptimization.FTRL
