/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import LeanMachineLearning.NeuralNetwork.UniversalApproximation.Nonpolynomial
public import LeanMachineLearning.NeuralNetwork.UniversalApproximation.PolynomialObstruction

/-!
# The Leshno--Lin--Pinkus--Schocken theorem

This file states the precise universal approximation theorem.  The input space is required to be
nontrivial: in dimension zero, every shallow-network function is constant, and a polynomial
activation can still be universal.

The sufficient direction follows from the distributional, convolution-smoothing, and
Stone--Weierstrass arguments, while the reverse implication follows from the polynomial
obstruction.
-/

@[expose] public section

namespace Learning.ShallowNetwork

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every continuous nonpolynomial activation is universal on compact subsets of a real
inner-product space. -/
theorem isUniversal_of_not_isPolynomial
    (σ : C(ℝ, ℝ)) (hσ : ¬ Function.IsPolynomial σ) : IsUniversal (E := E) σ :=
  (isUniversal_iff_isDiscriminatory σ).2
    (isDiscriminatory_of_not_isPolynomial σ hσ)

/-- Abstract form of the Leshno--Lin--Pinkus--Schocken equivalence on an arbitrary nontrivial real
inner-product space. -/
theorem not_isPolynomial_iff_isUniversal [Nontrivial E] (σ : C(ℝ, ℝ)) :
    ¬ Function.IsPolynomial σ ↔ IsUniversal (E := E) σ :=
  ⟨isUniversal_of_not_isPolynomial σ,
    fun hUniversal hPolynomial ↦
      not_isUniversal_of_isPolynomial σ hPolynomial hUniversal⟩

/-- Precise compact-set form of the Leshno--Lin--Pinkus--Schocken equivalence.

The approximating subspace is `spaceOn σ K`, whose generators are exactly the restrictions to
`K` of biased ridge functions `x ↦ σ (⟪w, x⟫ + b)`.
-/
theorem not_isPolynomial_iff_dense_on_compact [Nontrivial E] (σ : C(ℝ, ℝ)) :
    ¬ Function.IsPolynomial σ ↔
      ∀ (K : Set E), IsCompact K → Dense (spaceOn σ K : Set C(K, ℝ)) :=
  (not_isPolynomial_iff_isUniversal σ).trans (isUniversal_iff σ)

/-- The classical theorem on `ℝ^d`, represented as `EuclideanSpace ℝ (Fin d)`.

The hypothesis `0 < d` is essential: the claimed equivalence is false for the zero-dimensional
input space.
-/
theorem leshno_lin_pinkus_schocken {d : ℕ} (hd : 0 < d)
    (σ : C(ℝ, ℝ)) :
    ¬ Function.IsPolynomial σ ↔
      ∀ (K : Set (EuclideanSpace ℝ (Fin d))), IsCompact K →
        Dense (spaceOn σ K : Set C(K, ℝ)) := by
  let _ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  exact not_isPolynomial_iff_dense_on_compact σ

end Learning.ShallowNetwork
