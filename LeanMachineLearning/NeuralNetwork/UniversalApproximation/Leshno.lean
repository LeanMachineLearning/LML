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

This file combines the sufficient direction from `Nonpolynomial` with the necessary direction
from `PolynomialObstruction` to characterize continuous universal activations.

The input space is required to be nontrivial: in dimension zero, every shallow-network function
is constant, and a polynomial activation can still be universal. We characterize density on
every compact subset of an arbitrary nontrivial real inner-product space, express it as
`(spaceOn σ K).topologicalClosure = ⊤`, and specialize to the classical Euclidean-space theorem.
-/

@[expose] public section

namespace Learning.ShallowNetwork

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Precise compact-set form of the Leshno--Lin--Pinkus--Schocken equivalence.

The approximating subspace is `spaceOn σ K`, whose generators are exactly the restrictions to
`K` of biased ridge functions `x ↦ σ (⟪w, x⟫ + b)`.
-/
theorem not_isPolynomial_iff_dense_on_compact [Nontrivial E] (σ : C(ℝ, ℝ)) :
    ¬ Function.IsPolynomial σ ↔ ∀ (K : Set E), IsCompact K → Dense (spaceOn σ K : Set C(K, ℝ)) :=
  ⟨fun hσ _ hK ↦ dense_spaceOn_of_not_isPolynomial hσ hK, not_isPolynomial_of_dense_spaceOn σ⟩

/-- A continuous activation is nonpolynomial if and only if its network space has full
topological closure on every compact subset of a nontrivial real inner-product space. -/
theorem not_isPolynomial_iff_spaceOn_topologicalClosure_eq_top [Nontrivial E] (σ : C(ℝ, ℝ)) :
    ¬ Function.IsPolynomial σ ↔
      ∀ (K : Set E), IsCompact K → (spaceOn σ K).topologicalClosure = ⊤ := by
  simpa only [Submodule.dense_iff_topologicalClosure_eq_top] using
    (not_isPolynomial_iff_dense_on_compact (E := E) σ)

/-- The classical theorem on `ℝ^d`, represented as `EuclideanSpace ℝ (Fin d)`.

The hypothesis `0 < d` is essential: the claimed equivalence is false for the zero-dimensional
input space.
-/
theorem leshno_lin_pinkus_schocken {d : ℕ} (hd : 0 < d) (σ : C(ℝ, ℝ)) :
    ¬ Function.IsPolynomial σ ↔
      ∀ (K : Set (EuclideanSpace ℝ (Fin d))), IsCompact K →
        (spaceOn σ K).topologicalClosure = ⊤ := by
  let _ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  exact not_isPolynomial_iff_spaceOn_topologicalClosure_eq_top σ

end Learning.ShallowNetwork
