/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Basic
public import Mathlib.Algebra.Order.Group.CompleteLattice
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Fenchel Conjugates (Legendre–Fenchel Transform)

This file defines the domain-constrained generalized Fenchel conjugate `f^*[s]`
for functions `f : E → F` into conditionally complete ordered groups `F`.

It establishes Fenchel–Young inequalities, the equivalence between subgradient
membership and Fenchel–Young equality, and dual Bregman divergence identities.

## Main definitions

* `fenchelConjugateWithin f s`: The Fenchel conjugate
  $f^*[s](g) = \sup_{x \in s} (g(x) - f(x))$.
* `rangeSubdifferentialWithin f s`: The range of the subdifferential operator
  $\bigcup_{y \in s} \partial[s, y] f$.

## Notation

* `f^*[s]`: Scoped notation in `Bregman` for `fenchelConjugateWithin f s`.

## Main results

* `fenchel_young`: Fenchel–Young inequality $g(x) \le f(x) + f^*[s](g)$.
* `fenchel_young_eq`: Equivalence
  $f(x) + f^*[s](g) = g(x) \iff g \in \partial[s, x] f$.
* `bregman_eq_dual_bregman`: Bregman duality
  $D_f(x, y, g_y) = D_{f^*[s]}(g_y, g_x, x)$.
* `dual_subgradient`: Dual subgradient identity
  $x \in \partial[\text{rangeSubdifferentialWithin } f s, g_x] f^*[s]$.
-/

@[expose] public section

variable {R E F : Type*} [Ring R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ConditionallyCompleteLattice F] [IsOrderedAddMonoid F]

/-! ### 1. Definitions and Notation -/

/-- The Fenchel conjugate of `f : E → F` evaluated at `g : E →L[R] F` over a set `s`.
Defined as $f^*[s](g) = \sup_{x \in s} (g(x) - f(x))$. -/
noncomputable def fenchelConjugateWithin (f : E → F) (s : Set E) (g : E →L[R] F) : F :=
  ⨆ x : s, (g x.1 - f x.1)

/-- Scoped notation for Fenchel conjugate on a set `s`. -/
scoped[Bregman] notation:max f "^*[" s "]" => fenchelConjugateWithin f s

open scoped Bregman

variable {s : Set E} {f : E → F} {x y : E} {g gx gy : E →L[R] F}

omit [ConditionallyCompleteLattice F] [IsOrderedAddMonoid F] in
lemma fenchel_objective_eq_bregman (f : E → F) (x y : E) (g gy : E →L[R] F) :
    g x - f x = (g y - f y) + (g - gy) (x - y) - D_[f](x, y, gy) := by
  simp only [bregDiv, sub_apply, map_sub]
  abel

/-! ### 2. Fenchel–Young Inequality and Subgradients -/

omit [IsTopologicalAddGroup F] in
/-- Fenchel–Young inequality: $g(x) \le f(x) + f^*[s](g)$ for all $x \in s$. -/
lemma fenchel_young (hx : x ∈ s)
    (hbd : BddAbove (Set.range (fun (y : s) ↦ g y.1 - f y.1))) :
    g x ≤ f x + f^*[s] g :=
  sub_le_iff_le_add'.mp (le_ciSup hbd ⟨x, hx⟩)

/-- Characterization of subgradients via Fenchel–Young equality. -/
lemma fenchel_young_eq (hx : x ∈ s) :
    (f x + f^*[s] g = g x ∧ BddAbove (Set.range (fun (y : s) ↦ g y.1 - f y.1))) ↔
      HasSubgradientWithinAt f g s x := by
  have : Nonempty s := ⟨⟨x, hx⟩⟩
  constructor
  · rintro ⟨h, hbd⟩ y hy
    have h_le : g y - f y ≤ f^*[s] g := le_ciSup hbd ⟨y, hy⟩
    simp_all [fenchel_objective_eq_bregman f y x g g, eq_sub_of_add_eq' h]
  · intro h
    have h_le (y : s) : g y.1 - f y.1 ≤ g x - f x := by
      simpa [fenchel_objective_eq_bregman f y.1 x g g] using sub_le_self (g x - f x) (h y.1 y.2)
    have hbd : BddAbove (Set.range (fun (y : s) ↦ g y.1 - f y.1)) :=
      ⟨_, by rintro _ ⟨y, rfl⟩; exact h_le y⟩
    have h_eq : f^*[s] g = g x - f x := le_antisymm (ciSup_le h_le) (le_ciSup hbd ⟨x, hx⟩)
    exact ⟨by simp [h_eq], hbd⟩

/-- The Fenchel conjugate at any subgradient is exactly $g(x) - f(x)$. -/
lemma HasSubgradientWithinAt.fenchelConjugateWithin (h : HasSubgradientWithinAt f g s x)
    (hx : x ∈ s) :
    f^*[s] g = g x - f x :=
  eq_sub_of_add_eq' ((fenchel_young_eq hx).2 h).1

/-! ### 3. Dual Space and Dual Subgradients -/

/-- The range of the subdifferential operator over `s`,
defined as $\bigcup_{y \in s} \partial[s, y] f$. -/
def rangeSubdifferentialWithin (f : E → F) (s : Set E) : Set (E →L[R] F) :=
  { g | ∃ y ∈ s, HasSubgradientWithinAt f g s y }

section NormedDual

variable {R E F : Type*} [NontriviallyNormedField R]
  [NormedAddCommGroup E] [NormedSpace R E]
  [NormedAddCommGroup F] [NormedSpace R F]
  [ConditionallyCompleteLattice F] [IsOrderedAddMonoid F]

lemma bregman_eq_dual_bregman {s : Set E} {f : E → F}
    {x y : E} {gx gy : E →L[R] F}
    (hx : x ∈ s) (h_gx : HasSubgradientWithinAt f gx s x)
    (hy : y ∈ s) (h_gy : HasSubgradientWithinAt f gy s y) :
    D_[f](x, y, gy) = D_[f^*[s]](gy, gx, ContinuousLinearMap.apply R F x) := by
  dsimp [bregDiv]
  simp only [h_gx.fenchelConjugateWithin hx, h_gy.fenchelConjugateWithin hy, map_sub, sub_apply]
  abel

lemma dual_subgradient {s : Set E} {f : E → F}
    {x : E} {gx : E →L[R] F}
    (hx : x ∈ s) (h_gx : HasSubgradientWithinAt f gx s x) :
    HasSubgradientWithinAt (f^*[s]) (ContinuousLinearMap.apply R F x)
      (rangeSubdifferentialWithin f s) gx :=
  fun _ ⟨_, hy, h_gy⟩ ↦ (bregman_eq_dual_bregman hx h_gx hy h_gy) ▸ h_gy x hx

end NormedDual
