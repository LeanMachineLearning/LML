/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.ContinuousMap.Polynomial

/-!
# Functions represented by polynomials

This file defines the predicate that a function is globally represented by a univariate
polynomial. This is different from the local analytic predicate `CPolynomialOn`.
-/

@[expose] public section

open Polynomial

namespace Function

/-- A function from a semiring to itself is polynomial if it agrees everywhere with the
evaluation of a univariate polynomial. -/
def IsPolynomial {R : Type*} [Semiring R] (f : R → R) : Prop :=
  ∃ p : R[X], ∀ x, p.eval x = f x

namespace IsPolynomial

section CommSemiring

variable {R : Type*} [CommSemiring R] {f g : R → R}

protected theorem const (c : R) : IsPolynomial (fun _ : R ↦ c) :=
  ⟨C c, by simp⟩

protected theorem id : IsPolynomial (id : R → R) :=
  ⟨X, by simp⟩

protected theorem add (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (f + g) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun x ↦ by simp only [eval_add, Pi.add_apply, hp x, hq x]⟩

protected theorem mul (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (f * g) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun x ↦ by simp only [eval_mul, Pi.mul_apply, hp x, hq x]⟩

protected theorem comp (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (f ∘ g) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p.comp q, fun x ↦ by rw [eval_comp, hp, hq]; rfl⟩

/-- A bundled continuous map is polynomial exactly when it is in the range of
`Polynomial.toContinuousMap`. -/
theorem iff_exists_toContinuousMap [TopologicalSpace R] [IsTopologicalSemiring R]
    (f : C(R, R)) :
    IsPolynomial f ↔ ∃ p : R[X], p.toContinuousMap = f := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, ContinuousMap.ext hp⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, by simp⟩

protected theorem continuous [TopologicalSpace R] [IsTopologicalSemiring R]
    (hf : IsPolynomial f) : Continuous f := by
  obtain ⟨p, hp⟩ := hf
  rw [← funext hp]
  exact p.continuous

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {f g : R → R}

protected theorem neg (hf : IsPolynomial f) : IsPolynomial (-f) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨-p, fun x ↦ by simp only [eval_neg, Pi.neg_apply, hp x]⟩

protected theorem sub (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

end CommRing

end IsPolynomial

end Function
