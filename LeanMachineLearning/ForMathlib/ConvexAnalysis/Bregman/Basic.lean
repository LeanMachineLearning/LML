/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic

/-!
# Bregman Divergences

Generalized vector-valued Bregman divergences `bregDiv f x y J` (notation: `D_[f](x, y, J)`
in `scoped Bregman`) measure the error of the linear approximation of `f` around `y`.
They satisfy algebraic properties linked to derivatives, including chain rules,
product rules, affine invariance, and convexity preservation.

## Main definitions

* `Analysis.Convex.bregDiv f x y J`: The generalized vector-valued Bregman divergence
  `f x - f y - J (x - y)` for a function `f : E → F` and
  an additive map `J : E →+ F` (e.g. a derivative, gradient, or subgradient).

## Notation

* `D_[f](x, y, J)`: Scoped notation in `Bregman` for `bregDiv f x y J`.
-/

@[expose] public section

namespace Analysis.Convex

variable {E F G : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]

/-- The generalized vector-valued Bregman divergence.
`f` maps `E → F`. `J` is the Jacobian / subgradient additive mapping `E →+ F`. -/
def bregDiv (f : E → F) (x y : E) (J : E →+ F) : F :=
  f x - f y - J (x - y)

scoped[Bregman] notation "D_[" f "](" x ", " y ", " J ")" => Analysis.Convex.bregDiv f x y J

open scoped Bregman

@[app_unexpander bregDiv]
meta def unexpandBregDiv : Lean.PrettyPrinter.Unexpander
  | `($_ $f $x $y $J) => `(D_[$f]($x, $y, $J))
  | _                 => throw ()

@[simp]
lemma bregDiv_self (f : E → F) (x : E) (J_x : E →+ F) :
    D_[f](x, x, J_x) = 0 := by
  simp [bregDiv]

lemma bregDiv_three_point (f : E → F) (x y z : E) (J_x J_y : E →+ F) :
    D_[f](z, x, J_x) + D_[f](x, y, J_y) - D_[f](z, y, J_y) = (J_y - J_x) (z - x) := by
  simp only [bregDiv, map_sub, AddMonoidHom.sub_apply]
  abel

lemma bregDiv_add_swap (f : E → F) (x y : E) (J_x J_y : E →+ F) :
    D_[f](y, x, J_x) + D_[f](x, y, J_y) = (J_x - J_y) (x - y) := by
  simp only [bregDiv, map_sub, AddMonoidHom.sub_apply]
  abel

lemma bregDiv_fun_bregDiv (f : E → F) (x y z : E) (J_x J_y : E →+ F) :
    D_[fun w ↦ D_[f](w, y, J_y)](z, x, J_x - J_y) = D_[f](z, x, J_x) := by
  simp only [bregDiv, map_sub, AddMonoidHom.sub_apply]
  abel

lemma bregDiv_add (f₁ f₂ : E → F) (x y : E) (J₁ J₂ : E →+ F) :
    D_[f₁ + f₂](x, y, J₁ + J₂) = D_[f₁](x, y, J₁) + D_[f₂](x, y, J₂) := by
  simp only [bregDiv, Pi.add_apply, AddMonoidHom.add_apply, map_sub]
  abel

lemma bregDiv_prod {E₁ E₂ : Type*} [AddCommGroup E₁] [AddCommGroup E₂]
    (f₁ : E₁ → F) (f₂ : E₂ → F) (x y : E₁ × E₂) (J₁ : E₁ →+ F) (J₂ : E₂ →+ F) :
    D_[fun p : E₁ × E₂ ↦ f₁ p.1 + f₂ p.2](x, y, J₁.coprod J₂) =
      D_[f₁](x.1, y.1, J₁) + D_[f₂](x.2, y.2, J₂) := by
  simp only [bregDiv, AddMonoidHom.coprod_apply, map_sub]
  abel

@[simp]
lemma bregDiv_const (c : F) (x y : E) :
    D_[fun _ ↦ c](x, y, 0) = 0 := by
  simp [bregDiv]

@[simp]
lemma bregDiv_linear (h : E →+ F) (x y : E) :
    D_[h](x, y, h) = 0 := by
  simp [bregDiv]

@[simp]
lemma bregDiv_add_const (f : E → F) (c : F) (x y : E) (J : E →+ F) :
    D_[fun z ↦ f z + c](x, y, J) = D_[f](x, y, J) := by
  simp [bregDiv]

@[simp]
lemma bregDiv_const_add (c : F) (f : E → F) (x y : E) (J : E →+ F) :
    D_[fun z ↦ c + f z](x, y, J) = D_[f](x, y, J) := by
  simp [bregDiv]

@[simp]
lemma bregDiv_add_linear (f : E → F) (h : E →+ F) (x y : E) (J : E →+ F) :
    D_[fun z ↦ f z + h z](x, y, J + h) = D_[f](x, y, J) := by
  simp only [bregDiv, AddMonoidHom.add_apply, map_sub]
  abel

@[simp]
lemma bregDiv_neg (f : E → F) (x y : E) (J : E →+ F) :
    D_[-f](x, y, -J) = - D_[f](x, y, J) := by
  simp only [bregDiv, Pi.neg_apply, AddMonoidHom.neg_apply, map_sub]
  abel

lemma bregDiv_comp_neg (f : E → F) (x y : E) (J : E →+ F) :
    D_[fun z ↦ f (-z)](x, y, -J) = D_[f](-x, -y, J) := by
  simp [bregDiv, map_sub]

lemma bregDiv_translate (f : E → F) (x₀ : E) (x y : E) (J : E →+ F) :
    D_[fun z ↦ f (z + x₀)](x, y, J) = D_[f](x + x₀, y + x₀, J) := by
  simp [bregDiv]

section ChainRules

lemma bregDiv_comp_affine {E₁ : Type*} [AddCommGroup E₁]
    (f : E → F) (A : E₁ →+ E) (b : E) (x y : E₁) (J : E →+ F) :
    D_[fun z ↦ f (A z + b)](x, y, J.comp A) = D_[f](A x + b, A y + b, J) := by
  simp [bregDiv]

lemma bregDiv_comp (f₂ : F → G) (f₁ : E → F) (x y : E) (J₂ : F →+ G) (J₁ : E →+ F) :
    D_[f₂ ∘ f₁](x, y, J₂.comp J₁) = D_[f₂](f₁ x, f₁ y, J₂) + J₂ (D_[f₁](x, y, J₁)) := by
  simp [bregDiv]

end ChainRules

section CommRing

variable {R : Type*} [CommRing R]

/-- First-order product rule for Bregman divergences. -/
lemma bregDiv_mul (f₁ f₂ : E → R) (x y : E) (J₁ J₂ : E →+ R) :
    D_[f₁ * f₂](x, y, f₂ y • J₁ + f₁ y • J₂) =
      D_[f₁](x, y, J₁) * f₂ y + f₁ y * D_[f₂](x, y, J₂) +
      (f₁ x - f₁ y) * (f₂ x - f₂ y) := by
  dsimp only [bregDiv]
  simp only [Pi.mul_apply, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, map_sub, smul_eq_mul]
  ring


end CommRing

section Order

variable {F' : Type*} [AddCommGroup F'] [Preorder F'] [AddRightMono F']

lemma bregDiv_le_of_le_of_eq {f₁ f₂ : E → F'} {x y : E} {J_y : E →+ F'}
    (h_le : f₁ x ≤ f₂ x) (h_eq : f₁ y = f₂ y) :
    D_[f₁](x, y, J_y) ≤ D_[f₂](x, y, J_y) := by
  simp [bregDiv, h_eq, h_le]

end Order

section Module

variable {R : Type*} [CommRing R] [Module R F]

lemma bregDiv_smul (c : R) (f : E → F) (x y : E) (J : E →+ F) :
    D_[c • f](x, y, c • J) = c • D_[f](x, y, J) := by
  simp [bregDiv, smul_sub]

lemma bregDiv_convexCombination (f : E → F) (x y : E) (J₁ J₂ : E →+ F) (w : R) :
    D_[f](x, y, w • J₁ + (1 - w) • J₂) = w • D_[f](x, y, J₁) + (1 - w) • D_[f](x, y, J₂) := by
  calc
    D_[f](x, y, w • J₁ + (1 - w) • J₂)
      = D_[(w + (1 - w)) • f](x, y, w • J₁ + (1 - w) • J₂) := by
        rw [add_sub_cancel, one_smul]
    _ = D_[w • f](x, y, w • J₁) + D_[(1 - w) • f](x, y, (1 - w) • J₂) := by
      rw [add_smul, bregDiv_add]
    _ = w • D_[f](x, y, J₁) + (1 - w) • D_[f](x, y, J₂) := by
        simp only [bregDiv_smul]

end Module

section Convexity

variable {𝕜 E' F' : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup E'] [Module 𝕜 E']
variable [AddCommGroup F'] [Module 𝕜 F'] [PartialOrder F'] [IsOrderedAddMonoid F']

/-- If `f` is convex on `s`, then `x ↦ D_[f](x, y, J)` is convex on `s` for any linear map `J`. -/
lemma _root_.ConvexOn.bregDiv {s : Set E'} {f : E' → F'} (hf : ConvexOn 𝕜 s f)
    (J : E' →ₗ[𝕜] F') (y : E') :
    ConvexOn 𝕜 s (fun x ↦ D_[f](x, y, J)) := by
  simp only [Analysis.Convex.bregDiv, sub_eq_add_neg, map_add, map_neg, neg_add_rev, neg_neg]
  apply ConvexOn.add
  · apply ConvexOn.add
    · exact hf
    · exact convexOn_const (-f y) hf.1
  · apply ConvexOn.add
    · exact convexOn_const (J y) hf.1
    · exact (-J).convexOn hf.1

end Convexity

end Analysis.Convex
