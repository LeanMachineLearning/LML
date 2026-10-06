/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.Common.RegretTerms
public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.Common.Regularizer

/-!
# Shift Term Bound for LEA Regularizers

This file bounds the regularizer potential shift term:
$$\mathrm{shift}(t) = -(\psi_{t+1} - \psi_t)(w_{t+1})$$
when the time-dependent regularizers are scaled versions $\psi_t = \alpha_t \psi_0$ of a base
regularizer $\psi_0$.

With a non-negative regularizer $\psi_0 \ge 0$ and decreasing step sizes $\eta_t$
(i.e., non-decreasing regularization weights $\alpha_t \le \alpha_{t+1}$ where
$\alpha_t \propto 1/\eta_t$), the shift terms are non-positive ($\mathrm{shift}(t) \le 0$),
contributing non-positively to regret.

## Main definitions

* `shift`: Potential shift $-(\psi_{t+1} - \psi_t)(w_{t+1})$.

## Main results

* `shift_nonpos_of_nondecreasing`:
  $\alpha_t \le \alpha_{t+1}$ and $\psi_0(w_{t+1}) \ge 0 \implies \mathrm{shift}(t) \le 0$.
* `sum_shift_nonpos_of_nondecreasing`:
  $\sum_{t=1}^T \mathrm{shift}(t) \le 0$ under non-decreasing weights and non-negative regularizer.
* `sum_shift_unnormEntropyShifted_nonpos`:
  Cumulative shift with shifted unnormalized negative entropy regularizers
  $\psi^{\mathrm{shift}}_t = \text{unnormEntropyShifted}(\alpha_t)$ is unconditionally non-positive
  for iterates on the simplex.
-/

open scoped BigOperators
open Finset

@[expose] public section

namespace Online.OCO.LEA

variable {E : Type*}

/-- If the regularizer weight sequence is non-decreasing ($\alpha_t \le \alpha_{t+1}$)
(i.e., decreasing step sizes $\eta_t = 1/\alpha_t$)
and the base regularizer is non-negative ($\psi_0(x) \ge 0$),
then the shift term is non-positive ($\mathrm{shift}(t) \le 0$). -/
theorem shift_nonpos_of_nondecreasing (α : ℕ → ℝ) (ψ₀ : E → ℝ) (w : ℕ → E) (t : ℕ)
    (h_mono : α t ≤ α (t + 1)) (h_pos : 0 ≤ ψ₀ (w (t + 1))) :
    shift (fun s ↦ α s • ψ₀) w t ≤ 0 := by
  dsimp [shift]
  nlinarith

/-- Cumulative shift is non-positive when the regularizer weights are non-decreasing
(decreasing step size schedule) and $\psi_0 \ge 0$. -/
theorem sum_shift_nonpos_of_nondecreasing (α : ℕ → ℝ) (ψ₀ : E → ℝ) (w : ℕ → E) (T : ℕ)
    (h_mono : ∀ t ∈ Ico 1 (T + 1), α t ≤ α (t + 1))
    (h_pos : ∀ t ∈ Ico 1 (T + 1), 0 ≤ ψ₀ (w (t + 1))) :
    ∑ t ∈ Ico 1 (T + 1), shift (fun s ↦ α s • ψ₀) w t ≤ 0 :=
  sum_nonpos fun t ht ↦ shift_nonpos_of_nondecreasing α ψ₀ w t (h_mono t ht) (h_pos t ht)

/-- For shifted regularizers $\psi^{\mathrm{shift}}(t) = \text{unnormEntropyShifted}(\alpha_t)$
with non-decreasing weights $\alpha_t \le \alpha_{t+1}$ and iterates on the standard simplex
`stdSimplex`, cumulative shift is non-positive. -/
theorem sum_shift_unnormEntropyShifted_nonpos {d : ℕ} (hd : 0 < d) (α : ℕ → ℝ)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ)
    (h_mono : ∀ t ∈ Ico 1 (T + 1), α t ≤ α (t + 1))
    (hw : ∀ t ∈ Ico 1 (T + 2), w t ∈ stdSimplex (d := d)) :
    ∑ t ∈ Ico 1 (T + 1), shift (fun s ↦ unnormEntropyShifted (α s)) w t ≤ 0 := by
  have h_eq : (fun s ↦ unnormEntropyShifted (α s)) =
      fun s ↦ α s • (unnormEntropyShifted 1 : EuclideanSpace ℝ (Fin d) → ℝ) := by
    ext s x; exact unnormEntropyShifted_smul (α s) x
  rw [h_eq]
  refine sum_shift_nonpos_of_nondecreasing α (unnormEntropyShifted 1) w T h_mono fun t ht ↦ ?_
  have hw_succ : w (t + 1) ∈ stdSimplex (d := d) := hw (t + 1) (by rw [mem_Ico] at ht ⊢; omega)
  exact unnormEntropyShifted_nonneg_of_mem_stdSimplex hd (w (t + 1)) hw_succ

end Online.OCO.LEA
