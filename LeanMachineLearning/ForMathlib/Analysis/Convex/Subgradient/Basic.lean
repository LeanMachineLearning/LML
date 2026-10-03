/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.Basic

/-!
# Subgradients and Subdifferentials

Subgradients of functions `f : E → F` defined
via the non-negativity of the Bregman divergence `0 ≤ D_[f](y, x, g)` on an explicit
domain `s` (i.e. the linearization error is non-negative on `s`).

Carrying the domain `s : Set E` explicitly avoids using indicator functions
while supporting constrained convex analysis.

## Main definitions

* `HasSubgradientWithinAt f g s x`: `g : E →L[R] F` is a subgradient of `f` at `x` on `s`.
* `subdifferentialWithin R f s x`: The subdifferential set `∂[R, s, x](f)`.

## Main results

* Monotonicity in the domain: `HasSubgradientWithinAt.mono`.
* Chain rules: `HasSubgradientWithinAt.comp_affine` and `HasSubgradientWithinAt.comp`.
* Equivalence with classical inequality: `hasSubgradientWithinAt_iff_le`.
* Fermat's rule: `hasSubgradientWithinAt_zero_iff_isMinOn`.
* Suprema and maxima: `HasSubgradientWithinAt.sup_left`, `HasSubgradientWithinAt.sup_right`,
  `HasSubgradientWithinAt.finset_sup'`, and `HasSubgradientWithinAt.ciSup`.

## Notation

* `∂[R, s, x](f)`: Scoped notation in `Bregman` for `subdifferentialWithin R f s x`.
-/

@[expose] public section

open scoped Bregman

variable {R E E₁ F G : Type*} [Ring R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup E₁] [Module R E₁] [TopologicalSpace E₁]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]
  [AddCommGroup G] [Module R G] [TopologicalSpace G]
  [Preorder F]

/-- `g` is a subgradient of `f` at `x` on domain `s` (non-negativity of Bregman divergence). -/
def HasSubgradientWithinAt (f : E → F) (g : E →L[R] F) (s : Set E) (x : E) : Prop :=
  ∀ y ∈ s, 0 ≤ D_[f](y, x, g)

variable (R) in
/-- The subdifferential `∂[R, s, x](f)` of `f` at `x` on `s`. -/
def subdifferentialWithin (f : E → F) (s : Set E) (x : E) : Set (E →L[R] F) :=
  { g | HasSubgradientWithinAt f g s x }

/-- Scoped notation for `subdifferentialWithin`. -/
scoped[Bregman] notation "∂[" R ", " s ", " x "](" f ")" => subdifferentialWithin R f s x

variable {s t : Set E} {f : E → F} {x y : E} {g : E →L[R] F}

@[simp]
lemma mem_subdifferentialWithin :
    g ∈ ∂[R, s, x](f) ↔ HasSubgradientWithinAt f g s x := Iff.rfl

lemma HasSubgradientWithinAt.mono
    (h : HasSubgradientWithinAt f g t x) (hst : s ⊆ t) :
    HasSubgradientWithinAt f g s x :=
  fun y hy ↦ h y (hst hy)

@[simp]
lemma hasSubgradientWithinAt_const (c : F) :
    HasSubgradientWithinAt (fun _ ↦ c) (0 : E →L[R] F) s x := by
  simp [HasSubgradientWithinAt]

@[simp]
lemma hasSubgradientWithinAt_linear (h : E →L[R] F) :
    HasSubgradientWithinAt h h s x := by
  simp [HasSubgradientWithinAt]

@[simp]
lemma hasSubgradientWithinAt_add_const_iff {c : F} :
    HasSubgradientWithinAt (fun y ↦ f y + c) g s x ↔ HasSubgradientWithinAt f g s x := by
  simp [HasSubgradientWithinAt, bregDiv]

@[simp]
lemma hasSubgradientWithinAt_const_add_iff {c : F} :
    HasSubgradientWithinAt (fun y ↦ c + f y) g s x ↔ HasSubgradientWithinAt f g s x := by
  simp [HasSubgradientWithinAt, bregDiv]

@[simp]
lemma hasSubgradientWithinAt_add_linear_iff [ContinuousAdd F] {h : E →L[R] F} :
    HasSubgradientWithinAt (fun y ↦ f y + h y) (g + h) s x ↔ HasSubgradientWithinAt f g s x := by
  simp [HasSubgradientWithinAt, bregDiv_add_linear]

@[simp]
lemma hasSubgradientWithinAt_bregDiv_iff [IsTopologicalAddGroup F] {g_x g_y : E →L[R] F} :
    HasSubgradientWithinAt (fun z ↦ D_[f](z, y, g_y)) (g_x - g_y) s x ↔
      HasSubgradientWithinAt f g_x s x := by
  simp [HasSubgradientWithinAt, bregDiv_fun_bregDiv]

lemma hasSubgradientWithinAt_zero_iff :
    HasSubgradientWithinAt f (0 : E →L[R] F) s x ↔ ∀ y ∈ s, 0 ≤ f y - f x := by
  simp [HasSubgradientWithinAt, bregDiv]

lemma HasSubgradientWithinAt.comp_affine
    {s₁ : Set E₁} {x₁ : E₁} {A : E₁ →L[R] E} {b : E}
    (h_map : ∀ y ∈ s₁, A y + b ∈ s)
    (h_sub : HasSubgradientWithinAt f g s (A x₁ + b)) :
    HasSubgradientWithinAt (fun y ↦ f (A y + b)) (g.comp A) s₁ x₁ := fun y hy ↦ by
  rw [bregDiv_comp_affine]
  exact h_sub (A y + b) (h_map y hy)

/-- **Chain rule**: `g₂ ∘ g₁` is a subgradient of `f₂ ∘ f₁` when `g₂` is monotone. -/
lemma HasSubgradientWithinAt.comp [Preorder G] [IsOrderedAddMonoid G]
    {f₂ : F → G} {f₁ : E → F} {g₂ : F →L[R] G} {g₁ : E →L[R] F}
    (h₂ : HasSubgradientWithinAt f₂ g₂ (f₁ '' s) (f₁ x)) (h₁ : HasSubgradientWithinAt f₁ g₁ s x)
    (hg₂ : Monotone g₂) :
    HasSubgradientWithinAt (f₂ ∘ f₁) (g₂.comp g₁) s x := fun y hy ↦ by
  rw [bregDiv_comp]
  exact add_nonneg (h₂ (f₁ y) ⟨y, hy, rfl⟩) (by grw [← hg₂ (h₁ y hy)]; simp)

section OrderedGroup

variable [IsOrderedAddMonoid F]

/-- Equivalence with the classical definition. -/
lemma hasSubgradientWithinAt_iff_le :
    HasSubgradientWithinAt f g s x ↔ ∀ y ∈ s, f x + g (y - x) ≤ f y := by
  simp [HasSubgradientWithinAt, bregDiv, sub_sub, sub_nonneg]

lemma HasSubgradientWithinAt.sub_apply_sub_nonneg [IsTopologicalAddGroup F] {g_x g_y : E →L[R] F}
    (hx : x ∈ s) (hy : y ∈ s)
    (hx_sub : HasSubgradientWithinAt f g_x s x) (hy_sub : HasSubgradientWithinAt f g_y s y) :
    0 ≤ (g_x - g_y) (x - y) := by
  rw [← bregDiv_add_swap]
  exact add_nonneg (hx_sub y hy) (hy_sub x hx)

lemma hasSubgradientWithinAt_zero_iff_isMinOn :
    HasSubgradientWithinAt f (0 : E →L[R] F) s x ↔ IsMinOn f s x := by
  simp [HasSubgradientWithinAt, bregDiv, sub_nonneg, isMinOn_iff]

@[to_fun]
lemma HasSubgradientWithinAt.add [ContinuousAdd F] {f₁ f₂ : E → F} {g₁ g₂ : E →L[R] F}
    (h₁ : HasSubgradientWithinAt f₁ g₁ s x) (h₂ : HasSubgradientWithinAt f₂ g₂ s x) :
    HasSubgradientWithinAt (f₁ + f₂) (g₁ + g₂) s x := fun y hy ↦ by
  rw [bregDiv_add]
  exact add_nonneg (h₁ y hy) (h₂ y hy)

@[to_fun]
lemma HasSubgradientWithinAt.add_isMinOn [ContinuousAdd F] {f₁ f₂ : E → F} {x : E} {g : E →L[R] F}
    (h_min : IsMinOn f₁ s x) (h_sub : HasSubgradientWithinAt f₂ g s x) :
    HasSubgradientWithinAt (f₁ + f₂) g s x := by
  simpa using (hasSubgradientWithinAt_zero_iff_isMinOn.mpr h_min).add h_sub

end OrderedGroup

lemma HasSubgradientWithinAt.of_le_of_eq [AddRightMono F] {f₁ f₂ : E → F} {g : E →L[R] F}
    (h_sub : HasSubgradientWithinAt f₁ g s x) (h_le : ∀ y ∈ s, f₁ y ≤ f₂ y) (h_eq : f₁ x = f₂ x) :
    HasSubgradientWithinAt f₂ g s x :=
  fun y hy ↦ le_trans (h_sub y hy)
    (bregDiv_le_of_le_of_eq (h_le y hy) h_eq)

section ModuleBasic

variable {R' : Type*} [CommRing R'] [PartialOrder R']
  [Module R' E] [Module R' F] [ContinuousConstSMul R' F] [PosSMulMono R' F]

@[to_fun]
lemma HasSubgradientWithinAt.smul {c : R'} (hc : 0 ≤ c) {f : E → F} {g : E →L[R'] F}
    (h_sub : HasSubgradientWithinAt f g s x) :
    HasSubgradientWithinAt (c • f) (c • g) s x := fun y hy ↦ by
  rw [bregDiv_smul]
  exact smul_nonneg hc (h_sub y hy)

end ModuleBasic

section Module

variable {R' : Type*} [CommRing R'] [PartialOrder R']
    [Module R' E] [IsOrderedAddMonoid F] [Module R' F] [ContinuousConstSMul R' F] [PosSMulMono R' F]
    [ContinuousAdd F]

lemma HasSubgradientWithinAt.convexCombination {f : E → F} {g₁ g₂ : E →L[R'] F}
    (h₁ : HasSubgradientWithinAt f g₁ s x) (h₂ : HasSubgradientWithinAt f g₂ s x)
    {a b : R'} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    HasSubgradientWithinAt f (a • g₁ + b • g₂) s x := fun y hy ↦ by
  rw [bregDiv_convexCombination _ _ _ _ _ hab]
  exact add_nonneg (smul_nonneg ha (h₁ y hy)) (smul_nonneg hb (h₂ y hy))

lemma convex_subdifferentialWithin : Convex R' (∂[R', s, x](f)) := by
  intro g₁ hg₁ g₂ hg₂ a b ha hb hab
  simp only [mem_subdifferentialWithin] at hg₁ hg₂ ⊢
  exact hg₁.convexCombination hg₂ ha hb hab

end Module

section SemilatticeSup

variable {F_lin : Type*} [AddCommGroup F_lin] [Module R F_lin] [TopologicalSpace F_lin]
  [SemilatticeSup F_lin] [IsOrderedAddMonoid F_lin]

@[to_fun]
lemma HasSubgradientWithinAt.sup_left {f₁ f₂ : E → F_lin} {g : E →L[R] F_lin}
    (h_sub : HasSubgradientWithinAt f₁ g s x) (h_active : f₂ x ≤ f₁ x) :
    HasSubgradientWithinAt (f₁ ⊔ f₂) g s x :=
  h_sub.of_le_of_eq (fun y _ ↦ le_sup_left) (by simpa)

@[to_fun]
lemma HasSubgradientWithinAt.sup_right {f₁ f₂ : E → F_lin} {g : E →L[R] F_lin}
    (h_sub : HasSubgradientWithinAt f₂ g s x) (h_active : f₁ x ≤ f₂ x) :
    HasSubgradientWithinAt (f₁ ⊔ f₂) g s x :=
  h_sub.of_le_of_eq (fun y _ ↦ le_sup_right) (by simpa)

lemma HasSubgradientWithinAt.finset_sup' {ι : Type*} {s_ι : Finset ι}
    {f_i : ι → E → F_lin} {i : ι} {g : E →L[R] F_lin}
    (his : i ∈ s_ι)
    (h_sub : HasSubgradientWithinAt (f_i i) g s x)
    (h_active : ∀ j ∈ s_ι, f_i j x ≤ f_i i x) :
    HasSubgradientWithinAt (fun y ↦ s_ι.sup' ⟨i, his⟩ (f_i · y)) g s x := by
  refine h_sub.of_le_of_eq (fun _ _ ↦ Finset.le_sup'_of_le _ his le_rfl) ?_
  exact le_antisymm (Finset.le_sup' (f := fun j => f_i j x) his) (Finset.sup'_le _ _ h_active)

end SemilatticeSup

section Lattice

variable {F_lat : Type*} [AddCommGroup F_lat] [Module R F_lat] [TopologicalSpace F_lat]
    [ConditionallyCompleteLattice F_lat] [IsOrderedAddMonoid F_lat]

lemma HasSubgradientWithinAt.ciSup {ι : Type*} {f_i : ι → E → F_lat} {i : ι} {g : E →L[R] F_lat}
    (h_sub : HasSubgradientWithinAt (f_i i) g s x)
    (h_active : f_i i x = ⨆ j, f_i j x)
    (h_bdd : ∀ y ∈ s, BddAbove (Set.range (f_i · y))) :
    HasSubgradientWithinAt (fun y ↦ ⨆ j, f_i j y) g s x :=
  h_sub.of_le_of_eq (fun y hy ↦ le_ciSup (h_bdd y hy) i) h_active

end Lattice
