/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.FTRL.RegretDecomposition
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Optimality Bounds for Follow-the-Regularized-Leader (FTRL)

This file handles the optimality terms in the FTRL regret decomposition:
1. **Per-round first-order optimality**:
   $$\mathrm{optimality}_t = \left(g\psi_t(w_t) + \sum_{i=1}^{t-1} g_i\right)(w_{t+1} - w_t) \ge 0$$
   whenever $w_t$ minimizes $F_t(y) = \psi_t(y) + \sum_{i=1}^{t-1} g_i(y)$ over convex domain $s$,
   and $w_{t+1} \in s$.
2. **Terminal optimality**:
   $$\mathrm{terminalOptimality}_T = F_{T+1}(w_{T+1}) - F_{T+1}(u) \le 0$$
   whenever $w_{T+1}$ minimizes $F_{T+1}$ over $s$, and comparator $u \in s$.

Because $\mathrm{optimality}_t$ enters with a minus sign and $\mathrm{terminalOptimality}_T$
enters with a plus sign in `regret_decomposition_eq`:
$$- \sum_{t=1}^T \mathrm{optimality}_t \le 0$$
and
$$\mathrm{terminalOptimality}_T \le 0,$$
these bounds establish that both terms can be upper-bounded by $0$ in the regret bound.

## Main results
* `optimality_nonneg_of_isMinOn`: $0 \le \mathrm{optimality}_t$.
* `terminalOptimality_nonpos_of_isMinOn`: $\mathrm{terminalOptimality}_T \le 0$.
-/

open scoped BigOperators Bregman Topology
open Filter Finset

@[expose] public section

namespace Online.OCO.LEA.FTRL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Optimality

variable {ψ : ℕ → E → ℝ}
variable {gψ : ℕ → E → (E →L[ℝ] ℝ)}
variable {u : E}
variable {w : ℕ → E}
variable {g : ℕ → (E →L[ℝ] ℝ)}
variable {s : Set E}

/-- Per-round first-order optimality deficit is non-negative when $w_t$ minimizes
the cumulative objective $F_t$ over $s$, $\psi_t$ is convex with Fréchet derivative
$g\psi_t(w_t)$, and $w_{t+1} \in s$. -/
lemma optimality_nonneg_of_isMinOn (t : ℕ)
    (hψ_diff : HasFDerivAt (ψ t) (gψ t (w t)) (w t))
    (hψ_conv : ConvexOn ℝ s (ψ t))
    (hwt : w t ∈ s)
    (hwt1 : w (t + 1) ∈ s)
    (h_min : IsMinOn (FObj ψ g t) s (w t)) :
    0 ≤ optimality gψ w g t := by
  let lin : E →L[ℝ] ℝ := ∑ i ∈ Ico 1 t, g i
  have h_conv : ConvexOn ℝ s (ψ t + ⇑lin) :=
    hψ_conv.add (lin.toLinearMap.convexOn hψ_conv.1)
  have h_min' : IsMinOn ((ψ t + ⇑lin) + fun _ : E ↦ (0 : ℝ)) s (w t) := by
    intro x hx
    simpa [FObj, lin, add_zero] using h_min hx
  have h_subg := ((hψ_diff.add lin.hasFDerivAt).hasSubgradientWithinAt_add_iff
    (g := 0) h_conv (convexOn_const 0 h_conv.1) hwt).mp
    (hasSubgradientWithinAt_zero_iff_isMinOn.mpr h_min') (w (t + 1)) hwt1
  dsimp [bregDiv, optimality, lin] at h_subg ⊢
  simpa using h_subg

/-- Cumulative first-order optimality deficit is non-negative when each $w_t$ minimizes
the cumulative objective $F_t$ over $s$. -/
lemma sum_optimality_nonneg_of_isMinOn (T : ℕ)
    (hψ_diff : ∀ t ∈ Ico 1 (T + 1), HasFDerivAt (ψ t) (gψ t (w t)) (w t))
    (hψ_conv : ∀ t ∈ Ico 1 (T + 1), ConvexOn ℝ s (ψ t))
    (hw_mem : ∀ t ∈ Ico 1 (T + 2), w t ∈ s)
    (hw_min : ∀ t ∈ Ico 1 (T + 1), IsMinOn (FObj ψ g t) s (w t)) :
    0 ≤ ∑ t ∈ Ico 1 (T + 1), optimality gψ w g t := by
  refine sum_nonneg fun t ht ↦ ?_
  have ht1 : t ∈ Ico 1 (T + 2) := Ico_subset_Ico_right (by omega) ht
  have ht2 : t + 1 ∈ Ico 1 (T + 2) := by rw [mem_Ico] at ht ⊢; omega
  exact optimality_nonneg_of_isMinOn t (hψ_diff t ht) (hψ_conv t ht)
    (hw_mem t ht1) (hw_mem (t + 1) ht2) (hw_min t ht)

/-- Terminal optimality deficit is non-positive when $w_{T+1}$ minimizes
the terminal cumulative objective $F_{T+1}$ over $s$ and $u \in s$. -/
lemma terminalOptimality_nonpos_of_isMinOn (T : ℕ)
    (hu : u ∈ s)
    (h_min : IsMinOn (FObj ψ g (T + 1)) s (w (T + 1))) :
    terminalOptimality ψ u w g T ≤ 0 := by
  dsimp [terminalOptimality]
  have h_le : FObj ψ g (T + 1) (w (T + 1)) ≤ FObj ψ g (T + 1) u := h_min hu
  linarith

end Optimality

end Online.OCO.LEA.FTRL
