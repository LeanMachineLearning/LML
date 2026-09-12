/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Affine changes of variables in polynomials

This file records that composition with a polynomial of degree at most one preserves the
submodule `Polynomial.degreeLT`. In particular, this applies to affine changes of variables.
It also provides simp lemmas for evaluating the resulting polynomials.
-/

@[expose] public section

namespace Polynomial

universe u

variable {R : Type u}

/-- Composing with a polynomial of degree at most one preserves a strict degree bound. -/
theorem comp_mem_degreeLT_of_natDegree_le_one [Semiring R]
    {p q : R[X]} {n : ℕ} (hp : p ∈ degreeLT R n) (hq : q.natDegree ≤ 1) :
    p.comp q ∈ degreeLT R n := by
  rw [mem_degreeLT] at hp ⊢
  by_cases hcomp : p.comp q = 0
  · simp [hcomp]
  rw [← natDegree_lt_iff_degree_lt hcomp]
  calc
    (p.comp q).natDegree ≤ p.natDegree * q.natDegree := natDegree_comp_le
    _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ hq
    _ = p.natDegree := Nat.mul_one _
    _ < n := by
      by_cases hp0 : p = 0
      · simp [hp0] at hcomp
      · exact (natDegree_lt_iff_degree_lt hp0).2 hp

/-- Composition with the affine polynomial `C a * X + C b` preserves a strict degree bound. -/
theorem compAffineDegreeLT [Semiring R] {p : R[X]} {n : ℕ}
    (hp : p ∈ degreeLT R n) (a b : R) :
    p.comp (C a * X + C b) ∈ degreeLT R n := by
  apply comp_mem_degreeLT_of_natDegree_le_one hp
  calc
    (C a * X + C b).natDegree ≤ max (C a * X).natDegree (C b).natDegree :=
      natDegree_add_le _ _
    _ ≤ 1 := max_le (by simpa using natDegree_C_mul_X_pow_le a 1) (by simp)

/-- Evaluation of the polynomial representing the affine function `x ↦ a * x + b`. -/
@[simp]
theorem eval_C_mul_X_add_C [CommSemiring R] (a b x : R) :
    eval x (C a * X + C b) = a * x + b := by
  simp

/-- Evaluation after composition with the affine polynomial `C a * X + C b`. -/
@[simp]
theorem eval_comp_C_mul_X_add_C [CommSemiring R] (p : R[X]) (a b x : R) :
    eval x (p.comp (C a * X + C b)) = eval (a * x + b) p := by
  rw [eval_comp, eval_C_mul_X_add_C]

end Polynomial
