/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.LocallyConvex.Annihilator
public import LeanMachineLearning.NeuralNetwork.Shallow.Basic

/-!
# Discriminatory activation functions

An activation is discriminatory on an input space if the only continuous linear functional on
`C(K, ℝ)` that annihilates every neuron is zero, for every compact `K`. Hahn--Banach makes this
property equivalent to universal approximation.
-/

@[expose] public section

namespace Learning.ShallowNetwork

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An activation is discriminatory on `E` if no nonzero continuous linear functional annihilates
all of its neurons on a compact subset of `E`. -/
class IsDiscriminatory (σ : C(ℝ, ℝ)) : Prop where
  annihilator_eq_zero :
    ∀ (K : Set E), IsCompact K → ∀ Λ : StrongDual ℝ C(K, ℝ),
      (∀ w b, Λ ((neuron σ w b).restrict K) = 0) → Λ = 0

/-- For shallow networks, the discriminatory-functional criterion is equivalent to universal
approximation. -/
theorem isUniversal_iff_isDiscriminatory (σ : C(ℝ, ℝ)) :
    IsUniversal (E := E) σ ↔ IsDiscriminatory (E := E) σ := by
  constructor
  · rintro ⟨h_dense⟩
    constructor
    intro K hK
    let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
    intro Λ hΛ
    refine (spaceOn σ K).dense_iff_forall_dual_eq_zero.mp (h_dense K hK) Λ ?_
    intro f hf
    have hle : spaceOn σ K ≤ Λ.ker := by
      rw [spaceOn]
      apply Submodule.span_le.2
      rintro g ⟨p, rfl⟩
      exact hΛ p.1 p.2
    exact hle hf
  · rintro ⟨h_disc⟩
    constructor
    intro K hK
    let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
    rw [Submodule.dense_iff_forall_dual_eq_zero]
    intro Λ hΛ
    apply h_disc K hK Λ
    intro w b
    exact hΛ _ (Submodule.subset_span ⟨(w, b), rfl⟩)

end Learning.ShallowNetwork
