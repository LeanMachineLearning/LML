/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.Common.RegretTerms
public import LeanMachineLearning.Online.OnlineConvexOptimization.OGD.Common.Regularizer

/-!
# Shift Term Bound for OGD Regularizers

This file bounds the regularizer potential shift term:
$$\mathrm{shift}(t) = -(\psi_{t+1} - \psi_t)(w_{t+1})$$
when $\psi_t = \text{eucSq}(\alpha_t)$ with non-decreasing weights $\alpha_t \le \alpha_{t+1}$.

## Main definitions
* `shift`: Potential shift $-(\psi_{t+1} - \psi_t)(w_{t+1})$.

## Main results
* `shift_nonpos_of_nondecreasing`: $\alpha_t \le \alpha_{t+1} \implies \mathrm{shift}(t) \le 0$.
* `sum_shift_nonpos_of_nondecreasing`: Cumulative shift is non-positive.
-/

open scoped BigOperators
open Finset

@[expose] public section

namespace Online.OCO.OGD

variable {E : Type*} [NormedAddCommGroup E]

/-- Shift term for `eucSq` is non-positive under non-decreasing regularization weights. -/
theorem shift_eucSq_nonpos (α : ℕ → ℝ) (w : ℕ → E) (t : ℕ)
    (h_mono : α t ≤ α (t + 1)) :
    shift (fun s ↦ eucSq (α s)) w t ≤ 0 := by
  dsimp [shift, eucSq]
  have h_diff : 0 ≤ α (t + 1) - α t := sub_nonneg.mpr h_mono
  have : 0 ≤ ((α (t + 1) - α t) / 2) * ‖w (t + 1)‖^2 := by positivity
  linarith

/-- Cumulative shift for `eucSq` is non-positive under non-decreasing regularization weights. -/
theorem sum_shift_eucSq_nonpos (α : ℕ → ℝ) (w : ℕ → E) (T : ℕ)
    (h_mono : ∀ t ∈ Ico 1 (T + 1), α t ≤ α (t + 1)) :
    ∑ t ∈ Ico 1 (T + 1), shift (fun s ↦ eucSq (α s)) w t ≤ 0 :=
  sum_nonpos fun t ht ↦ shift_eucSq_nonpos α w t (h_mono t ht)

end Online.OCO.OGD
