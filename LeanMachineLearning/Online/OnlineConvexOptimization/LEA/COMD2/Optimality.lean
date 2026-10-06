/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.COMD2.RegretDecomposition
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# First-Order Optimality Bounds for Online Mirror Descent (LEA Specialization)

This file proves that the first-order optimality deficit:
$$\mathrm{optimality}_t = (\eta g_t + \nabla \psi_{t+1}(w_{t+1}) -
  \nabla \psi_t(w_t))(u - w_{t+1})$$
is **non-negative** (i.e. $0 \le \mathrm{optimality}_t$) whenever $w_{t+1}$ minimizes the
linearized mirror descent step:
$$x \mapsto \eta g_t(x) + \psi_{t+1}(x) - \nabla \psi_t(w_t)(x)$$
over a convex domain $s \subseteq E$, $\psi_{t+1}$ is convex and differentiable at $w_{t+1}$,
and the comparator $u \in s$.

## Main results
* `optimality_nonneg_of_isMinOn`: $0 \le \mathrm{optimality}_t$
  whenever $w_{t+1}$ is a constrained minimizer on $s$ and $u \in s$.
-/

open scoped BigOperators Bregman Topology
open Filter Finset

@[expose] public section

namespace Online.OCO.LEA.COMD2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Optimality

variable {ψ : ℕ → E → ℝ}
variable {gψ : ℕ → E → (E →L[ℝ] ℝ)}
variable {u : E}
variable {w : ℕ → E}
variable {g : ℕ → (E →L[ℝ] ℝ)}
variable {s : Set E}

/-- First-order optimality deficit is non-negative when $w_{t+1}$ minimizes the mirror
descent step objective over $s$, $\psi_{t+1}$ is convex with Fréchet derivative
$g\psi_{t+1}(w_{t+1})$, and $u \in s$. -/
lemma optimality_nonneg_of_isMinOn (t : ℕ)
    (hψ_diff : HasFDerivAt (ψ (t + 1)) (gψ (t + 1) (w (t + 1))) (w (t + 1)))
    (hψ_conv : ConvexOn ℝ s (ψ (t + 1)))
    (hw : w (t + 1) ∈ s)
    (hu : u ∈ s)
    (h_min : IsMinOn (fun x ↦ (g t) x + ψ (t + 1) x - (gψ t (w t)) x) s (w (t + 1))) :
    0 ≤ optimality gψ u w g t := by
  let lin : E →L[ℝ] ℝ := g t - gψ t (w t)
  have h_conv : ConvexOn ℝ s (ψ (t + 1) + ⇑lin) :=
    hψ_conv.add (lin.toLinearMap.convexOn hψ_conv.1)
  have h_min' : IsMinOn ((ψ (t + 1) + ⇑lin) + fun _ : E ↦ (0 : ℝ)) s (w (t + 1)) := by
    intro x hx
    have := h_min hx
    dsimp [lin] at this ⊢
    simp only [add_zero, sub_apply] at this ⊢
    linarith
  have h_subg := ((hψ_diff.add lin.hasFDerivAt).hasSubgradientWithinAt_add_iff
    (g := 0) h_conv (convexOn_const 0 h_conv.1) hw).mp
    (hasSubgradientWithinAt_zero_iff_isMinOn.mpr h_min') u hu
  dsimp [bregDiv, optimality, lin] at h_subg ⊢
  simp only [sub_self, zero_sub, neg_apply, neg_neg, add_apply, sub_apply] at h_subg ⊢
  linarith

/-- Cumulative first-order optimality deficit is non-negative when each $w_{t+1}$ is a
constrained minimizer of the mirror descent step objective over $s$. -/
lemma sum_optimality_nonneg_of_isMinOn (T : ℕ)
    (hψ_diff : ∀ t ∈ Ico 1 (T + 1), HasFDerivAt (ψ (t + 1)) (gψ (t + 1) (w (t + 1))) (w (t + 1)))
    (hψ_conv : ∀ t ∈ Ico 1 (T + 1), ConvexOn ℝ s (ψ (t + 1)))
    (hw_mem : ∀ t ∈ Ico 1 (T + 2), w t ∈ s)
    (hu : u ∈ s)
    (hw_min : ∀ t ∈ Ico 1 (T + 1),
      IsMinOn (fun x ↦ (g t) x + ψ (t + 1) x - (gψ t (w t)) x) s (w (t + 1))) :
    0 ≤ ∑ t ∈ Ico 1 (T + 1), optimality gψ u w g t := by
  refine sum_nonneg fun t ht ↦ ?_
  have ht2 : t + 1 ∈ Ico 1 (T + 2) := by rw [mem_Ico] at ht ⊢; omega
  exact optimality_nonneg_of_isMinOn t (hψ_diff t ht) (hψ_conv t ht) (hw_mem (t + 1) ht2) hu
    (hw_min t ht)

end Optimality

end Online.OCO.LEA.COMD2
