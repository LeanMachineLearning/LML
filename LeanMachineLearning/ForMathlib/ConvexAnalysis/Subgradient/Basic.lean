/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.ForMathlib.ConvexAnalysis.Bregman.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic

/-!
# Subgradients and Subdifferentials

Subgradients of functions `f : E → F` defined
via the non-negativity of the Bregman divergence `0 ≤ D_[f](x, y, g_y)` on an explicit
domain `V` (i.e. the linearization error is non-negative on `V`).

Carrying the domain `V : Set E` explicitly avoids using indicator functions
while supporting constrained convex analysis.

## Main definitions

* `Analysis.Convex.IsSubgradient V f y g_y`: `g_y : E →+ F` is a subgradient of `f` at `y` on `V`.
* `Analysis.Convex.subdifferential V f y`: The subdifferential set `∂[V, y] f`.

## Main results

* Chain rules: `Analysis.Convex.IsSubgradient.comp_affine` and `Analysis.Convex.IsSubgradient.comp`.
* Equivalence with classical inequality: `Analysis.Convex.mem_subdifferential_iff_le`.
* Fermat's rule: `Analysis.Convex.zero_mem_subdifferential_iff_isMinOn`.
* Suprema and maxima: `Analysis.Convex.IsSubgradient.max_left`,
  `Analysis.Convex.IsSubgradient.max_right`, `Analysis.Convex.IsSubgradient.finset_sup`,
  and `Analysis.Convex.IsSubgradient.ciSup`.

## Notation

* `∂[V, y] f`: Scoped notation in `Bregman` for `subdifferential V f y`.
-/

@[expose] public section

namespace Analysis.Convex

open scoped Bregman

variable {E F : Type*} [AddCommGroup E] [AddCommGroup F] [Preorder F]

/-- `g_y` is a subgradient of `f` at `y` on domain `V` (non-negativity of Bregman divergence). -/
def IsSubgradient (V : Set E) (f : E → F) (y : E) (g_y : E →+ F) : Prop :=
  y ∈ V ∧ ∀ x ∈ V, 0 ≤ D_[f](x, y, g_y)

/-- The subdifferential `∂[V, y] f` of `f` at `y` on `V`. -/
def subdifferential (V : Set E) (f : E → F) (y : E) : Set (E →+ F) :=
  { g | IsSubgradient V f y g }

/-- Scoped notation for `subdifferential`. -/
scoped[Bregman] notation:60 "∂[" V ", " y "] " f:50 => Analysis.Convex.subdifferential V f y

/-- Unexpander for `subdifferential`. -/
@[app_unexpander subdifferential]
meta def unexpandSubdifferential : Lean.PrettyPrinter.Unexpander
  | `($_ $V $f $y) => `(∂[$V, $y] $f)
  | _              => throw ()

variable {V : Set E} {f : E → F} {y x : E} {g_y : E →+ F}

@[local simp]
lemma mem_subdifferential_iff :
    g_y ∈ ∂[V, y] f ↔ y ∈ V ∧ ∀ x ∈ V, 0 ≤ D_[f](x, y, g_y) := Iff.rfl

@[simp]
lemma mem_subdifferential_const_iff {c : F} :
    (0 : E →+ F) ∈ ∂[V, y] (fun _ ↦ c) ↔ y ∈ V := by simp

@[simp]
lemma mem_subdifferential_linear_iff {h : E →+ F} :
    h ∈ ∂[V, y] h ↔ y ∈ V := by simp

@[simp]
lemma mem_subdifferential_add_const_iff {c : F} :
    g_y ∈ ∂[V, y] (fun x ↦ f x + c) ↔ g_y ∈ ∂[V, y] f := by simp

@[simp]
lemma mem_subdifferential_const_add_iff {c : F} :
    g_y ∈ ∂[V, y] (fun x ↦ c + f x) ↔ g_y ∈ ∂[V, y] f := by simp

@[simp]
lemma mem_subdifferential_add_linear_iff {h : E →+ F} :
    (g_y + h) ∈ ∂[V, y] (fun x ↦ f x + h x) ↔ g_y ∈ ∂[V, y] f := by simp

@[simp]
lemma mem_subdifferential_bregDiv_iff {g_x g_y : E →+ F} :
    (g_x - g_y) ∈ ∂[V, x] (fun z ↦ D_[f](z, y, g_y)) ↔ g_x ∈ ∂[V, x] f := by
  simp [bregDiv_fun_bregDiv]

lemma zero_mem_subdifferential_iff :
    (0 : E →+ F) ∈ ∂[V, y] f ↔ y ∈ V ∧ ∀ x ∈ V, 0 ≤ f x - f y := by simp [bregDiv]

lemma IsSubgradient.comp_affine {E₁ : Type*} [AddCommGroup E₁]
    {V₁ : Set E₁} {y₁ : E₁} {A : E₁ →+ E} {b : E}
    (hy₁ : y₁ ∈ V₁) (h_map : ∀ x ∈ V₁, A x + b ∈ V)
    (h_sub : g_y ∈ ∂[V, A y₁ + b] f) :
    (g_y.comp A) ∈ ∂[V₁, y₁] (fun x ↦ f (A x + b)) :=
  ⟨hy₁, fun x hx ↦ by simp [bregDiv_comp_affine, h_sub.2 (A x + b) (h_map x hx)]⟩

/-- **Chain rule**: `g₂ ∘ g₁` is a subgradient of `f₂ ∘ f₁` when `g₂` is non-negative. -/
lemma IsSubgradient.comp {G : Type*} [AddCommGroup G] [Preorder G] [IsOrderedAddMonoid G]
    {f₂ : F → G} {f₁ : E → F} {g₂ : F →+ G} {g₁ : E →+ F}
    (h₂ : g₂ ∈ ∂[f₁ '' V, f₁ y] f₂) (h₁ : g₁ ∈ ∂[V, y] f₁)
    (hg₂_nonneg : ∀ z ≥ 0, 0 ≤ g₂ z) :
    (g₂.comp g₁) ∈ ∂[V, y] (f₂ ∘ f₁) :=
  ⟨h₁.1, fun x hx ↦ by
    simp only [bregDiv_comp, add_nonneg (h₂.2 (f₁ x) ⟨x, hx, rfl⟩) (hg₂_nonneg _ (h₁.2 x hx))]⟩

section OrderedGroup

variable [IsOrderedAddMonoid F]

/-- Equivalence with the classical definition. -/
lemma mem_subdifferential_iff_le :
    g_y ∈ ∂[V, y] f ↔ y ∈ V ∧ ∀ x ∈ V, f y + g_y (x - y) ≤ f x := by
  simp [bregDiv, sub_sub, sub_nonneg]

lemma IsSubgradient.monotonicity {g_x : E →+ F}
    (hx_sub : g_x ∈ ∂[V, x] f) (hy_sub : g_y ∈ ∂[V, y] f) :
    0 ≤ (g_x - g_y) (x - y) := by
  rw [← bregDiv_add_swap f x y g_x g_y]
  exact add_nonneg (hx_sub.2 y hy_sub.1) (hy_sub.2 x hx_sub.1)


/-- **Fermat's rule**: `0` is a subgradient of `f` at `y` iff `y` is a minimizer of `f` on `V`. -/
lemma zero_mem_subdifferential_iff_isMinOn :
    (0 : E →+ F) ∈ ∂[V, y] f ↔ y ∈ V ∧ IsMinOn f V y := by
  simp [bregDiv, sub_nonneg, isMinOn_iff]

lemma IsSubgradient.add {f₁ f₂ : E → F} {g₁ g₂ : E →+ F}
    (h₁ : g₁ ∈ ∂[V, y] f₁) (h₂ : g₂ ∈ ∂[V, y] f₂) :
    (g₁ + g₂) ∈ ∂[V, y] (f₁ + f₂) :=
  ⟨h₁.1, fun x hx ↦ by simp [bregDiv_add, add_nonneg (h₁.2 x hx) (h₂.2 x hx)]⟩

lemma IsSubgradient.add_isMinOn {f₁ f₂ : E → F} {x : E} {g : E →+ F}
    (h_min : IsMinOn f₁ V x) (hx_mem : x ∈ V) (h_sub : g ∈ ∂[V, x] f₂) :
    g ∈ ∂[V, x] (f₁ + f₂) := by
  simpa using IsSubgradient.add (zero_mem_subdifferential_iff_isMinOn.mpr ⟨hx_mem, h_min⟩) h_sub

lemma IsSubgradient.of_le_of_eq {f₁ f₂ : E → F} {g_y : E →+ F}
    (h_sub : g_y ∈ ∂[V, y] f₁) (h_le : ∀ x ∈ V, f₁ x ≤ f₂ x) (h_eq : f₁ y = f₂ y) :
    g_y ∈ ∂[V, y] f₂ :=
  ⟨h_sub.1, fun x hx ↦ le_trans (h_sub.2 x hx)
    (bregDiv_le_of_le_of_eq (h_le x hx) h_eq)⟩

end OrderedGroup

section ModuleBasic

variable {R : Type*} [CommRing R] [PartialOrder R] [Module R F] [PosSMulMono R F]

lemma IsSubgradient.smul {c : R} (hc : 0 ≤ c) {f : E → F} {g_y : E →+ F}
    (h_sub : g_y ∈ ∂[V, y] f) :
    (c • g_y) ∈ ∂[V, y] (c • f) :=
  ⟨h_sub.1, fun x hx ↦ by simp [bregDiv_smul, smul_nonneg hc (h_sub.2 x hx)]⟩

end ModuleBasic

section Module

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
    [IsOrderedAddMonoid F] [Module R F] [PosSMulMono R F]

lemma IsSubgradient.convexCombination {f : E → F} {g₁ g₂ : E →+ F}
    (h₁ : g₁ ∈ ∂[V, y] f) (h₂ : g₂ ∈ ∂[V, y] f) {w : R} (hw : w ∈ Set.Icc (0 : R) 1) :
    (w • g₁ + (1 - w) • g₂) ∈ ∂[V, y] f :=
  ⟨h₁.1, fun x hx ↦ by
    simp [bregDiv_convexCombination, hw.1, sub_nonneg.mpr hw.2,
      h₁.2 x hx, h₂.2 x hx, smul_nonneg, add_nonneg]⟩

end Module

section LinearOrder

variable {F_lin : Type*} [AddCommGroup F_lin] [LinearOrder F_lin] [IsOrderedAddMonoid F_lin]

lemma IsSubgradient.max_left {f₁ f₂ : E → F_lin} {g_y : E →+ F_lin}
    (h_sub : g_y ∈ ∂[V, y] f₁) (h_active : f₁ y = max (f₁ y) (f₂ y)) :
    g_y ∈ ∂[V, y] (fun x ↦ max (f₁ x) (f₂ x)) :=
  IsSubgradient.of_le_of_eq h_sub (fun x _ ↦ le_max_left (f₁ x) (f₂ x)) h_active

lemma IsSubgradient.max_right {f₁ f₂ : E → F_lin} {g_y : E →+ F_lin}
    (h_sub : g_y ∈ ∂[V, y] f₂) (h_active : f₂ y = max (f₁ y) (f₂ y)) :
    g_y ∈ ∂[V, y] (fun x ↦ max (f₁ x) (f₂ x)) :=
  IsSubgradient.of_le_of_eq h_sub (fun x _ ↦ le_max_right (f₁ x) (f₂ x)) h_active

lemma IsSubgradient.finset_sup {ι : Type*} {s : Finset ι}
    {f_i : ι → E → F_lin} {i : ι} {g_y : E →+ F_lin}
    (his : i ∈ s)
    (h_sub : g_y ∈ ∂[V, y] (f_i i)) (h_active : f_i i y = s.sup' ⟨i, his⟩ (fun j ↦ f_i j y)) :
    g_y ∈ ∂[V, y] (fun x ↦ s.sup' ⟨i, his⟩ (fun j ↦ f_i j x)) :=
  IsSubgradient.of_le_of_eq h_sub (fun _ _ ↦ Finset.le_sup'_of_le _ his (le_refl _)) h_active

end LinearOrder

section Lattice

variable {F_lat : Type*} [AddCommGroup F_lat]
    [ConditionallyCompleteLattice F_lat] [IsOrderedAddMonoid F_lat]

lemma IsSubgradient.ciSup {ι : Type*} {f_i : ι → E → F_lat} {i : ι} {g_y : E →+ F_lat}
    (h_sub : g_y ∈ ∂[V, y] (f_i i))
    (h_active : f_i i y = ⨆ j, f_i j y)
    (h_bdd : ∀ x ∈ V, BddAbove (Set.range (fun j ↦ f_i j x))) :
    g_y ∈ ∂[V, y] (fun x ↦ ⨆ j, f_i j x) :=
  IsSubgradient.of_le_of_eq h_sub (fun x hx ↦ le_ciSup (h_bdd x hx) i) h_active

end Lattice

end Analysis.Convex
