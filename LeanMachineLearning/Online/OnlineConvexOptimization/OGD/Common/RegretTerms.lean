/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.Basic

/-!
# Common Regret Terms for Online Gradient Descent (OGD / OMD / FTRL)

This file collects the per-round regret terms shared across the OGD algorithms:
the stability tradeoff and the regularizer potential shift.

## Main definitions

* `stability`: One-round stability tradeoff between loss reduction and divergence.
* `shift`: Regularizer potential shift across rounds.
-/

open scoped Bregman

@[expose] public section

namespace Online.OCO.OGD

variable {E : Type*}

/-- Stability tradeoff between loss reduction and regularizer distance:
$$(g_t)(w_t - w_{t+1}) - D_{\psi_t}(w_{t+1}, w_t, \nabla\psi_t(w_t)).$$ -/
def stability [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℕ → E → ℝ) (gψ : ℕ → E → (E →L[ℝ] ℝ)) (w : ℕ → E) (g : ℕ → (E →L[ℝ] ℝ)) (t : ℕ) : ℝ :=
  (g t) (w t - w (t + 1)) - D_[ψ t](w (t + 1), w t, gψ t (w t))

/-- Potential shift accounting for changes in regularizers across rounds:
$$- (\psi_{t+1} - \psi_t)(w_{t+1}).$$ -/
def shift (ψ : ℕ → E → ℝ) (w : ℕ → E) (t : ℕ) : ℝ :=
  - (ψ (t + 1) - ψ t) (w (t + 1))

end Online.OCO.OGD
