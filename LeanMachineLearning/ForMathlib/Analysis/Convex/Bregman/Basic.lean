/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Bregman Divergences

Generalized vector-valued Bregman divergences `bregDiv f x y J` (notation: `D_[f](x, y, J)`
in `scoped Bregman`) measure the error of the linear approximation of `f` around `y`.
They satisfy algebraic properties linked to derivatives, including chain rules,
product rules, affine invariance, and convexity preservation.

## Main definitions

* `bregDiv f x y J`: The generalized vector-valued Bregman divergence `f x - f y - J (x - y)`
  for a function `f : E → F` and a continuous linear map `J : E →L[R] F`
  (e.g. a derivative, gradient, or subgradient).

## Notation

* `D_[f](x, y, J)`: Scoped notation in `Bregman` for `bregDiv f x y J`.
-/

@[expose] public section

variable {R E E₁ E₂ F G : Type*} [Ring R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup E₁] [Module R E₁] [TopologicalSpace E₁]
  [AddCommGroup E₂] [Module R E₂] [TopologicalSpace E₂]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]
  [AddCommGroup G] [Module R G] [TopologicalSpace G]
  {f : E → F} {x y z : E} {J J₁ J₂ J_x J_y : E →L[R] F}

/-- The generalized vector-valued Bregman divergence.
`f` maps `E → F`. `J` is the Jacobian / subgradient continuous linear mapping `E →L[R] F`. -/
def bregDiv (f : E → F) (x y : E) (J : E →L[R] F) : F :=
  f x - f y - J (x - y)

/-- Scoped notation for `bregDiv`. -/
scoped[Bregman] notation "D_[" f "](" x ", " y ", " J ")" => bregDiv f x y J

open scoped Bregman

@[simp]
lemma bregDiv_self :
    D_[f](x, x, J_x) = 0 := by
  simp [bregDiv]

lemma bregDiv_three_point [IsTopologicalAddGroup F] :
    D_[f](z, x, J_x) + D_[f](x, y, J_y) - D_[f](z, y, J_y) = (J_y - J_x) (z - x) := by
  simp only [bregDiv, map_sub, sub_apply]
  abel

lemma bregDiv_add_swap [IsTopologicalAddGroup F] :
    D_[f](y, x, J_x) + D_[f](x, y, J_y) = (J_x - J_y) (x - y) := by
  simp only [bregDiv, map_sub, sub_apply]
  abel

lemma bregDiv_fun_bregDiv [IsTopologicalAddGroup F] :
    D_[fun w ↦ D_[f](w, y, J_y)](z, x, J_x - J_y) = D_[f](z, x, J_x) := by
  simp only [bregDiv, map_sub, sub_apply]
  abel

@[to_fun]
lemma bregDiv_add [ContinuousAdd F] (f₁ f₂ : E → F) :
    D_[f₁ + f₂](x, y, J₁ + J₂) = D_[f₁](x, y, J₁) + D_[f₂](x, y, J₂) := by
  simp only [bregDiv, Pi.add_apply, add_apply, map_sub]
  abel

lemma bregDiv_prod [ContinuousAdd F]
    (f₁ : E₁ → F) (f₂ : E₂ → F) (x y : E₁ × E₂) (J₁ : E₁ →L[R] F) (J₂ : E₂ →L[R] F) :
    D_[fun p : E₁ × E₂ ↦ f₁ p.1 + f₂ p.2](x, y, J₁.coprod J₂) =
      D_[f₁](x.1, y.1, J₁) + D_[f₂](x.2, y.2, J₂) := by
  simp only [bregDiv, ContinuousLinearMap.coprod_apply, map_sub]
  abel

@[simp]
lemma bregDiv_const (c : F) :
    D_[fun _ ↦ c](x, y, (0 : E →L[R] F)) = 0 := by
  simp [bregDiv]

@[simp]
lemma bregDiv_linear (h : E →L[R] F) :
    D_[h](x, y, h) = 0 := by
  simp [bregDiv]

@[simp]
lemma bregDiv_add_const (c : F) :
    D_[fun z ↦ f z + c](x, y, J) = D_[f](x, y, J) := by
  simp [bregDiv]

@[simp]
lemma bregDiv_const_add (c : F) :
    D_[fun z ↦ c + f z](x, y, J) = D_[f](x, y, J) := by
  simp [bregDiv]

@[simp]
lemma bregDiv_add_linear [ContinuousAdd F] (h : E →L[R] F) :
    D_[fun z ↦ f z + h z](x, y, J + h) = D_[f](x, y, J) := by
  simp only [bregDiv, add_apply, map_sub]
  abel

@[to_fun (attr := simp)]
lemma bregDiv_neg [IsTopologicalAddGroup F] :
    D_[-f](x, y, -J) = - D_[f](x, y, J) := by
  simp only [bregDiv, Pi.neg_apply, neg_apply, map_sub]
  abel

lemma bregDiv_comp_neg [IsTopologicalAddGroup F] :
    D_[fun z ↦ f (-z)](x, y, -J) = D_[f](-x, -y, J) := by
  simp [bregDiv, map_sub]

lemma bregDiv_comp_add_right (x₀ : E) :
    D_[fun z ↦ f (z + x₀)](x, y, J) = D_[f](x + x₀, y + x₀, J) := by
  simp [bregDiv]

section ChainRules

variable {f₁ : E → F} {f₂ : F → G} {J₁ : E →L[R] F} {J₂ : F →L[R] G}
  {A : E₁ →L[R] E} {b : E} {x y : E₁}

lemma bregDiv_comp_affine :
    D_[fun z ↦ f (A z + b)](x, y, J.comp A) = D_[f](A x + b, A y + b, J) := by
  simp [bregDiv]

lemma bregDiv_comp {x y : E} :
    D_[f₂ ∘ f₁](x, y, J₂.comp J₁) = D_[f₂](f₁ x, f₁ y, J₂) + J₂ (D_[f₁](x, y, J₁)) := by
  simp [bregDiv]

end ChainRules

section CommRing

variable {R' : Type*} [CommRing R'] [TopologicalSpace R'] [ContinuousAdd R']
  [ContinuousConstSMul R' R'] [Module R' E]

/-- First-order product rule for Bregman divergences. -/
@[to_fun]
lemma bregDiv_mul (f₁ f₂ : E → R') (x y : E) (J₁ J₂ : E →L[R'] R') :
    D_[f₁ * f₂](x, y, f₂ y • J₁ + f₁ y • J₂) =
      D_[f₁](x, y, J₁) * f₂ y + f₁ y * D_[f₂](x, y, J₂) +
      (f₁ x - f₁ y) * (f₂ x - f₂ y) := by
  dsimp only [bregDiv]
  simp only [Pi.mul_apply, add_apply, smul_apply, map_sub, smul_eq_mul]
  ring

end CommRing

section Order

variable {F' : Type*} [AddCommGroup F'] [Module R F'] [TopologicalSpace F']
  [Preorder F'] [AddRightMono F']

lemma bregDiv_le_of_le_of_eq {f₁ f₂ : E → F'} {x y : E} {J_y : E →L[R] F'}
    (h_le : f₁ x ≤ f₂ x) (h_eq : f₁ y = f₂ y) :
    D_[f₁](x, y, J_y) ≤ D_[f₂](x, y, J_y) := by
  simp [bregDiv, h_eq, h_le]

end Order

section Module

variable {R' : Type*} [CommRing R'] [Module R' E] [Module R' F] [ContinuousConstSMul R' F]

lemma bregDiv_smul (c : R') (f : E → F) (x y : E) (J : E →L[R'] F) :
    D_[c • f](x, y, c • J) = c • D_[f](x, y, J) := by
  simp [bregDiv, smul_sub]

lemma bregDiv_convexCombination [ContinuousAdd F]
    (f : E → F) (x y : E) (J₁ J₂ : E →L[R'] F) {a b : R'} (hab : a + b = 1) :
    D_[f](x, y, a • J₁ + b • J₂) = a • D_[f](x, y, J₁) + b • D_[f](x, y, J₂) := by
  calc D_[f](x, y, a • J₁ + b • J₂)
  _ = D_[(a + b) • f](x, y, a • J₁ + b • J₂) := by rw [hab, one_smul]
  _ = D_[a • f](x, y, a • J₁) + D_[b • f](x, y, b • J₂) := by rw [add_smul, bregDiv_add]
  _ = a • D_[f](x, y, J₁) + b • D_[f](x, y, J₂) := by simp only [bregDiv_smul]

end Module

section Convexity

variable [PartialOrder R] [PartialOrder F] [IsOrderedAddMonoid F]

/-- If `f` is convex on `s`, then `x ↦ D_[f](x, y, J)` is convex on `s` for any
continuous linear map `J`. -/
nonrec lemma ConvexOn.bregDiv {s : Set E} (hf : ConvexOn R s f) (J : E →L[R] F) (y : E) :
    ConvexOn R s (fun x ↦ D_[f](x, y, J)) := by
  simp only [bregDiv, sub_eq_add_neg, map_add, map_neg, neg_add_rev, neg_neg]
  apply ConvexOn.add
  · apply hf.add
    exact convexOn_const (-f y) hf.1
  · apply ConvexOn.add
    · exact convexOn_const (J y) hf.1
    · exact (-J.toLinearMap).convexOn hf.1

end Convexity
