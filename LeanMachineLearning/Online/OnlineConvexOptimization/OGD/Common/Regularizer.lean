/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Euclidean Regularizer and Divergences for Online Gradient Descent (OGD)

This file defines the scaled Euclidean regularizer $\psi_\alpha(w) = \frac{\alpha}{2} \|w\|^2$
on a real inner product space $E$, its Fréchet derivative
$\nabla\psi_\alpha(w) = \alpha \langle w, \cdot \rangle$,
its Bregman divergence $D_{\psi_\alpha}(x, y) = \frac{\alpha}{2} \|x - y\|^2$, and convexity.

## Main definitions

* `eucSq`: The scaled squared Euclidean regularizer $\psi_\alpha(w) = \frac{\alpha}{2} \|w\|^2$.
* `eucSqFDeriv`: Fréchet derivative map $\alpha \langle w, \cdot \rangle$.

## Main results

* `bregDiv_eucSq_eq`: $D_{\psi_\alpha}(x, y) = \frac{\alpha}{2} \|x - y\|^2$.
* `bregDiv_eucSq_nonneg`: Non-negativity of Euclidean Bregman divergence for $\alpha \ge 0$.
* `hasFDerivAt_eucSq`: Fréchet differentiability of `eucSq`.
* `differentiable_eucSq`: Differentiability of `eucSq`.
* `convexOn_eucSq`: Convexity of `eucSq` for $\alpha \ge 0$.
* `hasSubgradientWithinAt_eucSq`: Subgradient property of `eucSqFDeriv`.
-/

open scoped RealInnerProductSpace Bregman

@[expose] public section

namespace Online.OCO.OGD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The scaled Euclidean quadratic regularizer $\psi_\alpha(w) = \frac{\alpha}{2} \|w\|^2$. -/
noncomputable def eucSq (α : ℝ) (w : E) : ℝ :=
  (α / 2) * ‖w‖^2

/-- Gradient of `eucSq α w` as a continuous linear functional $\alpha \cdot \mathrm{innerSL}(w)$. -/
noncomputable def eucSqFDeriv (α : ℝ) (w : E) : E →L[ℝ] ℝ :=
  α • innerSL ℝ w

@[simp]
lemma eucSqFDeriv_apply (α : ℝ) (w v : E) : eucSqFDeriv α w v = α * ⟪w, v⟫ := by
  simp [eucSqFDeriv, innerSL_apply_apply]

/-- Bregman divergence of $\psi_\alpha(w) = \frac{\alpha}{2} \|w\|^2$
is $\frac{\alpha}{2} \|x - y\|^2$. -/
@[simp]
theorem bregDiv_eucSq_eq (α : ℝ) (x y : E) :
    D_[eucSq α](x, y, eucSqFDeriv α y) = (α / 2) * ‖x - y‖^2 := by
  dsimp [bregDiv, eucSq]
  rw [eucSqFDeriv_apply, norm_sub_sq_real, sq,
    inner_sub_right, real_inner_self_eq_norm_mul_norm, real_inner_comm x y]
  ring

/-- Non-negativity of Euclidean Bregman divergence for $\alpha \ge 0$. -/
lemma bregDiv_eucSq_nonneg (α : ℝ) (hα : 0 ≤ α) (x y : E) :
    0 ≤ D_[eucSq α](x, y, eucSqFDeriv α y) := by
  rw [bregDiv_eucSq_eq]
  positivity

/-- Fréchet derivative of `eucSq α` at any point $w \in E$. -/
theorem hasFDerivAt_eucSq (α : ℝ) (w : E) :
    HasFDerivAt (eucSq α) (eucSqFDeriv α w) w := by
  have := (hasStrictFDerivAt_norm_sq (F := E) w).hasFDerivAt.const_smul (α / 2)
  convert this using 1
  · ext x; simp [eucSq, smul_eq_mul]
  · ext v; simp [eucSqFDeriv]; ring

/-- Differentiability of `eucSq α` on the entire space $E$. -/
theorem differentiable_eucSq (α : ℝ) : Differentiable ℝ (eucSq (E := E) α) :=
  fun w ↦ (hasFDerivAt_eucSq α w).differentiableAt

/-- Convexity of `eucSq α` on any convex set $s \subseteq E$ when $\alpha \ge 0$. -/
theorem convexOn_eucSq (α : ℝ) (hα : 0 ≤ α) (s : Set E) (hs : Convex ℝ s) :
    ConvexOn ℝ s (eucSq α) := by
  refine ⟨hs, fun x _ y _ a b _ _ hab ↦ ?_⟩
  dsimp [eucSq]
  have h_id : ⟪a • x + b • y, a • x + b • y⟫ =
      a * ⟪x, x⟫ + b * ⟪y, y⟫ - a * b * ⟪x - y, x - y⟫ := by
    have ha : a * a = a - a * b := by nlinarith
    have hb : b * b = b - a * b := by nlinarith
    rw [inner_add_left, inner_add_right, inner_add_right,
      inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [inner_smul_left, inner_smul_right, conj_trivial, real_inner_comm y x]
    linear_combination ⟪x, x⟫ * ha + ⟪y, y⟫ * hb
  simp only [sq, ← real_inner_self_eq_norm_mul_norm]
  rw [h_id]
  have : 0 ≤ (α / 2) * (a * b * ⟪x - y, x - y⟫) := by
    have : 0 ≤ ⟪x - y, x - y⟫ := real_inner_self_nonneg
    positivity
  linarith

/-- Subgradient property of `eucSqFDeriv α w` on any set $s \subseteq E$ when $\alpha \ge 0$. -/
theorem hasSubgradientWithinAt_eucSq (α : ℝ) (hα : 0 ≤ α) (s : Set E) (w : E) :
    HasSubgradientWithinAt (eucSq α) (eucSqFDeriv α w) s w := by
  intro y _
  rw [bregDiv_eucSq_eq]
  positivity

end Online.OCO.OGD
