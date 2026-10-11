/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.Basic

/-!
# Second-Order Mean Value Theorem for Bregman Divergences

This file provides the second-order Mean Value Theorem (Lagrange remainder form)
for generalized Bregman divergences `D_[f](x, y, J)`:

* `exists_repeated_rolle`: Repeated Rolle's Theorem for an `n`-th order sequence of derivatives.
* `bregDiv_mvt`: If `f` is twice differentiable along
  `segment ℝ x y`, then there exists `z ∈ segment ℝ x y` such that
  `D_[f](x, y, f' y) = 1/2 * f'' z (x - y) (x - y)`.
-/

@[expose] public section

/-- NOTE: This lemma is a general 1D calculus result and should probably go
to `Mathlib.Analysis.Calculus.Deriv.MeanValue`. -/
lemma exists_repeated_rolle (n : ℕ) {g : Fin (n + 2) → (ℝ → ℝ)} {b : ℝ} (hb : 0 < b)
    (hg_diff : ∀ k : Fin (n + 1), ∀ t ∈ Set.Icc 0 b, HasDerivAt (g k.castSucc) (g k.succ t) t)
    (hg_zero : ∀ k : Fin (n + 1), g k.castSucc 0 = 0)
    (hgb : g 0 b = 0) :
    ∃ c ∈ Set.Ioo 0 b, g (Fin.last (n + 1)) c = 0 := by
  obtain ⟨c1, hc1, hc1_eq⟩ := exists_hasDerivAt_eq_zero hb
    (fun t ht ↦ (hg_diff 0 t ht).continuousAt.continuousWithinAt)
    ((hg_zero 0).trans hgb.symm)
    (fun t ht ↦ hg_diff 0 t (Set.Ioo_subset_Icc_self ht))
  cases n with
  | zero => exact ⟨c1, hc1, hc1_eq⟩
  | succ n =>
    obtain ⟨c, hc, hc_eq⟩ := exists_repeated_rolle n (g := fun k ↦ g k.succ) hc1.1
      (fun k t ht ↦ hg_diff k.succ t ⟨ht.1, ht.2.trans (le_of_lt hc1.2)⟩)
      (fun k ↦ hg_zero k.succ) hc1_eq
    exact ⟨c, ⟨hc.1, hc.2.trans hc1.2⟩, hc_eq⟩

open scoped Bregman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bregDiv_mvt
    {f : E → ℝ} {f' : E → (E →L[ℝ] ℝ)} {f'' : E → (E →L[ℝ] (E →L[ℝ] ℝ))}
    (x y : E)
    (hf' : ∀ z ∈ segment ℝ x y, HasFDerivAt f (f' z) z)
    (hf'' : ∀ z ∈ segment ℝ x y, HasFDerivAt f' (f'' z) z) :
    ∃ z ∈ segment ℝ x y,
      D_[f](x, y, f' y) = (1/2 : ℝ) * (f'' z (x - y)) (x - y) := by
  have hp {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : AffineMap.lineMap y x t ∈ segment ℝ x y := by
    rw [segment_symm]; exact lineMap_mem_segment (𝕜 := ℝ) y x ht
  let D := D_[f](x, y, f' y)
  let g (k : Fin 3) (t : ℝ) : ℝ := match k with
    | 0 => f (AffineMap.lineMap y x t) - f y - t * f' y (x - y) - t^2 * D
    | 1 => f' (AffineMap.lineMap y x t) (x - y) - f' y (x - y) - 2 * t * D
    | 2 => f'' (AffineMap.lineMap y x t) (x - y) (x - y) - 2 * D
  obtain ⟨c, hc, hc_eq⟩ := exists_repeated_rolle 1 (g := g) zero_lt_one
    (by intro k t ht
        fin_cases k
        · exact (by ring : f' (AffineMap.lineMap y x t) (x - y) - 1 * f' y (x - y) -
              2 * t ^ (2 - 1) * D = g 1 t) ▸
            ((((hf' _ (hp ht)).comp_hasDerivAt t AffineMap.hasDerivAt_lineMap).sub_const
                (f y)).sub
              ((hasDerivAt_id t).mul_const (f' y (x - y))) |>.sub
              ((hasDerivAt_pow 2 t).mul_const D))
        · exact (by ring : f'' (AffineMap.lineMap y x t) (x - y) (x - y) - 2 * 1 * D = g 2 t) ▸
            (((ContinuousLinearMap.apply ℝ ℝ (x - y)).hasFDerivAt.comp_hasDerivAt t
              ((hf'' _ (hp ht)).comp_hasDerivAt t AffineMap.hasDerivAt_lineMap)).sub_const
                (f' y (x - y)) |>.sub
              ((hasDerivAt_id t |>.const_mul 2).mul_const D)))
    (by intro k; fin_cases k <;> simp [g])
    (by simp [g, D, bregDiv])
  exact ⟨AffineMap.lineMap y x c, hp (Set.Ioo_subset_Icc_self hc),
    by linarith [show g 2 c = 0 from hc_eq]⟩
