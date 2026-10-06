/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Standard Simplex Domain for Online Convex Optimization

This file defines the standard simplex `stdSimplex` directly as a convex subset of
`EuclideanSpace ℝ (Fin d)` and provides basic properties of the uniform distribution.

## Main definitions

* `stdSimplex`: The standard simplex $\Delta^{d-1} \subset \mathbb{R}^d$
  defined as $\{x \in \mathbb{R}^d \mid (\forall i, 0 \le x_i) \wedge \sum_i x_i = 1\}$.
* `uniformSimplex`: The uniform distribution $w_1 = (1/d, \dots, 1/d)$.

## Main results

* `convex_stdSimplex`: Convexity of `stdSimplex`.
* `mem_stdSimplex_uniformSimplex`: Membership $w_1 \in \Delta^{d-1}$.
-/

open scoped BigOperators
open Finset

@[expose] public section

namespace Online.OCO.LEA

variable {d : ℕ}

/-- The standard simplex $\Delta^{d-1} \subset \mathbb{R}^d$ in `EuclideanSpace ℝ (Fin d)`:
$$\Delta^{d-1} = \left\{ x \in \mathbb{R}^d \;\middle|\; \forall i, 0 \le x_i
\;\text{and}\; \sum_{i=1}^d x_i = 1 \right\}$$ -/
def stdSimplex : Set (EuclideanSpace ℝ (Fin d)) :=
  { x : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 }

lemma mem_stdSimplex_iff (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ stdSimplex ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 :=
  Iff.rfl

/-- The standard simplex is a convex set in `EuclideanSpace ℝ (Fin d)`. -/
theorem convex_stdSimplex : Convex ℝ (stdSimplex (d := d)) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i ↦ add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)), ?_⟩
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, sum_add_distrib,
    ← mul_sum, hx.2, hy.2, mul_one, hab]

/-- The uniform distribution vector on `EuclideanSpace ℝ (Fin d)`:
$$w_1 = \left( \frac{1}{d}, \dots, \frac{1}{d} \right)$$ -/
noncomputable def uniformSimplex (d : ℕ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun _ ↦ (1 : ℝ) / d)

@[simp]
lemma uniformSimplex_apply (i : Fin d) : uniformSimplex d i = (1 : ℝ) / d :=
  rfl

lemma uniformSimplex_pos (hd : 0 < d) (i : Fin d) : 0 < uniformSimplex d i :=
  div_pos zero_lt_one (Nat.cast_pos.mpr hd)

/-- The uniform distribution lies in the standard simplex `stdSimplex`. -/
theorem mem_stdSimplex_uniformSimplex (hd : 0 < d) : uniformSimplex d ∈ stdSimplex (d := d) := by
  refine ⟨fun i ↦ (uniformSimplex_pos hd i).le, ?_⟩
  simp [Nat.cast_ne_zero.mpr hd.ne']

end Online.OCO.LEA
