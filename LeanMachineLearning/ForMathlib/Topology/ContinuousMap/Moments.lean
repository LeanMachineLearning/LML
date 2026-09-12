/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import LeanMachineLearning.ForMathlib.LinearAlgebra.Multilinear.Polarization
public import LeanMachineLearning.ForMathlib.Topology.ContinuousMap.InnerProduct
public import Mathlib.Algebra.Group.Submonoid.Membership

/-!
# Determinacy by polynomial moments

This file proves that a continuous linear functional on continuous functions over a compact space
vanishes if all of its moments along a linearly parametrized, algebraically generating family
vanish.  Polarization first recovers mixed moments from pure powers; the algebraic span description
of `Algebra.adjoin` and density then finish the proof.

The general theorem works over any characteristic-zero nontrivially normed field.  We also provide
the specialization to the inner-product coordinates of a compact subset of a real inner-product
space.  No finite-dimensionality assumption on the ambient inner-product space is needed.
-/

@[expose] public section

open scoped BigOperators

namespace StrongDual

section Coordinate

variable {𝕜 X V : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- The multilinear moment obtained by applying `Λ` to a product of coordinate functions. -/
noncomputable def coordinateMoment (coordinate : V →L[𝕜] C(X, 𝕜))
    (Λ : StrongDual 𝕜 C(X, 𝕜)) (n : ℕ) : V [×n]→L[𝕜] 𝕜 :=
  Λ.compContinuousMultilinearMap <|
    (ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin n) C(X, 𝕜)).compContinuousLinearMap
      fun _ ↦ coordinate

@[simp]
theorem coordinateMoment_apply (coordinate : V →L[𝕜] C(X, 𝕜))
    (Λ : StrongDual 𝕜 C(X, 𝕜)) (n : ℕ) (v : Fin n → V) :
    coordinateMoment coordinate Λ n v = Λ (∏ i, coordinate (v i)) := by
  simp [coordinateMoment]

instance coordinateMoment_isSymm (coordinate : V →L[𝕜] C(X, 𝕜))
    (Λ : StrongDual 𝕜 C(X, 𝕜)) (n : ℕ) : (coordinateMoment coordinate Λ n).IsSymm := by
  rw [ContinuousMultilinearMap.IsSymm.isSymm_iff]
  intro v e
  simp only [coordinateMoment_apply, Function.comp_apply]
  congr 1
  exact Equiv.prod_comp e (fun i ↦ coordinate (v i))

end Coordinate

section CharZero

variable {𝕜 X V : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- A continuous linear functional is zero if it annihilates every pure coordinate power and the
coordinates algebraically generate a dense subalgebra.

The proof first uses polarization to show that all mixed coordinate products vanish.  Such products
span the generated algebra, so continuity and density imply that the functional is zero everywhere.
-/
theorem eq_zero_of_coordinate_powers
    (coordinate : V →L[𝕜] C(X, 𝕜))
    (hdense : Dense (Algebra.adjoin 𝕜 (Set.range coordinate) : Set C(X, 𝕜)))
    (Λ : StrongDual 𝕜 C(X, 𝕜))
    (hpow : ∀ (n : ℕ) (v : V), Λ ((coordinate v) ^ n) = 0) :
    Λ = 0 := by
  have hproduct : ∀ (n : ℕ) (v : Fin n → V), Λ (∏ i, coordinate (v i)) = 0 := by
    intro n v
    have hdiag : ∀ w : V, coordinateMoment coordinate Λ n (fun _ ↦ w) = 0 := by
      intro w
      rw [coordinateMoment_apply]
      simpa using hpow n w
    have hm : coordinateMoment coordinate Λ n = 0 :=
      (coordinateMoment coordinate Λ n).eq_zero_of_diagonal_eq_zero hdiag
    have hv := congrArg (fun p : V [×n]→L[𝕜] 𝕜 ↦ p v) hm
    simpa using hv
  have hmonoid : ∀ p ∈ Submonoid.closure (Set.range coordinate), Λ p = 0 := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hp
    have hexi : ∀ i : Fin l.length, ∃ v : V, coordinate v = l[i] := by
      intro i
      exact hl l[i] (List.getElem_mem ..)
    choose v hv using hexi
    rw [← Fin.prod_univ_getElem l]
    convert hproduct l.length v using 1
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact (hv i).symm
  have hadjoin : ∀ p ∈ Algebra.adjoin 𝕜 (Set.range coordinate), Λ p = 0 := by
    intro p hp
    change p ∈ (Algebra.adjoin 𝕜 (Set.range coordinate)).toSubmodule at hp
    rw [Algebra.adjoin_eq_span] at hp
    have hle : Submodule.span 𝕜
        (Submonoid.closure (Set.range coordinate) : Set C(X, 𝕜)) ≤ Λ.ker := by
      rw [Submodule.span_le]
      intro q hq
      exact hmonoid q hq
    exact hle hp
  apply ContinuousLinearMap.ext_on
    (hdense.mono (Submodule.subset_span (R := 𝕜)))
  intro p hp
  simpa using hadjoin p hp

end CharZero

end StrongDual

namespace ContinuousMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real inner-product coordinate `x ↦ ⟪w, x⟫` on a subtype. -/
def innerProductCoordinate (K : Set E) (w : E) : C(K, ℝ) :=
  ⟨fun x ↦ inner ℝ w x.1, continuous_const.inner continuous_subtype_val⟩

@[simp]
theorem innerProductCoordinate_apply (K : Set E) (w : E) (x : K) :
    innerProductCoordinate K w x = inner ℝ w x.1 := rfl

/-- The continuous linear map sending a vector to its inner-product coordinate on a compact
subtype.  Compactness bounds the subtype, so finite-dimensionality is not required. -/
noncomputable def innerProductCoordinateCLM (K : Set E) [CompactSpace K] :
    E →L[ℝ] C(K, ℝ) := by
  let coordinate : E →ₗ[ℝ] C(K, ℝ) :=
    { toFun := innerProductCoordinate K
      map_add' := by
        intro x y
        ext z
        simp [innerProductCoordinate, inner_add_left]
      map_smul' := by
        intro c x
        ext z
        simp [innerProductCoordinate, real_inner_smul_left] }
  apply coordinate.mkContinuousOfExistsBound
  have hcompact : IsCompact (Set.range fun x : K ↦ x.1) :=
    isCompact_range continuous_subtype_val
  obtain ⟨R, hRpos, hR⟩ := hcompact.isBounded.exists_pos_norm_le
  refine ⟨R, fun w ↦
    (ContinuousMap.norm_le (innerProductCoordinate K w) ?_).2 (fun x ↦ ?_)⟩
  · positivity
  · change ‖inner ℝ w x.1‖ ≤ R * ‖w‖
    calc
      ‖inner ℝ w x.1‖ ≤ ‖w‖ * ‖x.1‖ := norm_inner_le_norm _ _
      _ ≤ ‖w‖ * R := mul_le_mul_of_nonneg_left (hR x.1 ⟨x, rfl⟩) (norm_nonneg _)
      _ = R * ‖w‖ := mul_comm _ _

@[simp]
theorem innerProductCoordinateCLM_apply (K : Set E) [CompactSpace K] (w : E) :
    innerProductCoordinateCLM K w = innerProductCoordinate K w := by
  rfl

end ContinuousMap

namespace StrongDual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A continuous linear functional on a compact subtype of a real inner-product space is zero if
it annihilates every power of every inner-product coordinate. -/
theorem eq_zero_of_innerProductCoordinate_powers (K : Set E) [CompactSpace K]
    (Λ : StrongDual ℝ C(K, ℝ))
    (hpow : ∀ (n : ℕ) (w : E),
      Λ ((ContinuousMap.innerProductCoordinate K w) ^ n) = 0) :
    Λ = 0 := by
  apply eq_zero_of_coordinate_powers (ContinuousMap.innerProductCoordinateCLM K)
    (Λ := Λ)
  · have hrange : Set.range (ContinuousMap.innerProductCoordinateCLM K) =
        Set.range (ContinuousMap.innerProductCoordinate K) := by
      ext f
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨w, (ContinuousMap.innerProductCoordinateCLM_apply K w).symm⟩
      · rintro ⟨w, rfl⟩
        exact ⟨w, ContinuousMap.innerProductCoordinateCLM_apply K w⟩
    rw [hrange]
    exact ContinuousMap.dense_innerProduct_adjoin K
  · intro n w
    simpa only [ContinuousMap.innerProductCoordinateCLM_apply] using hpow n w

end StrongDual
