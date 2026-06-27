/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic

import LeanMachineLearning.ForMathlib.Analysis.Calculus.Deriv.Slope

/-!
# Online regret

-/

@[expose] public section

open  Filter Real Finset
open scoped Gradient ENNReal NNReal RealInnerProductSpace

namespace Learning

variable {E : Type*} [NormedAddCommGroup E]

section OnlineRegret

/-- The regret of a sequence `x : ℕ → E` compared to a point `y : E` in an online learning task
with losses `ℓ : ℕ → E → F`. -/
def onlineRegret {E F : Type*} [AddCommGroup F] (ℓ : ℕ → E → F) (y : E) (x : ℕ → E) (n : ℕ) : F :=
  ∑ i ∈ range n, (ℓ i (x i) - ℓ i y)

lemma apply_avg_sub_le_onlineRegret [NormedSpace ℝ E] {f : E → ℝ} (hf : ConvexOn ℝ .univ f)
    (x : ℕ → E) (y : E) (n : ℕ) (hn : n ≠ 0) :
    f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y ≤ (n : ℝ)⁻¹ • onlineRegret (fun _ ↦ f) y x n :=
  hf.apply_avg_sub_le_avg_sub x y n hn

variable [InnerProductSpace ℝ E] [CompleteSpace E]

lemma onlineRegret_le_onlineRegret_inner_gradient {f : ℕ → E → ℝ}
    (hf : ∀ n, ConvexOn ℝ .univ (f n)) (hdf : ∀ n, Differentiable ℝ (f n))
    (x : ℕ → E) (y : E) (n : ℕ) :
    onlineRegret f y x n ≤ onlineRegret (fun n y ↦ ⟪y, ∇ (f n) (x n)⟫) y x n := by
  simp only [onlineRegret, ← inner_sub_left]
  gcongr with i hi
  exact (hf i).sub_le_inner_gradient (hdf i).differentiableAt _

lemma apply_avg_sub_le_onlineRegret_inner_gradient {f : E → ℝ}
    (hf : ConvexOn ℝ .univ f) (hdf : Differentiable ℝ f)
    (x : ℕ → E) (y : E) (n : ℕ) (hn : n ≠ 0) :
    f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y ≤
      (n : ℝ)⁻¹ * (onlineRegret (fun n y ↦ ⟪y, ∇ f (x n)⟫) y x n) := by
  simpa [onlineRegret, ← inner_sub_left] using
    hf.apply_avg_sub_le_avg_inner hdf x y n hn

end OnlineRegret

end Learning
