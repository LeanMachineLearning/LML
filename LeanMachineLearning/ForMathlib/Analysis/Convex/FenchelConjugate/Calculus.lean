/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.FenchelConjugate.Basic

/-!
# Calculus of Fenchel Conjugates

This file establishes algebraic transformation laws and calculus rules for
the domain-constrained generalized Fenchel conjugate `f^*[s]`.

## Main results

* Constant shifts: `fenchelConjugateWithin_add_const` and
  `fenchelConjugateWithin_sub_const`.
* Linear perturbations: `fenchelConjugateWithin_add_linear` and
  `fenchelConjugateWithin_sub_linear`.
* Bregman divergence objectives: `fenchelConjugateWithin_bregDiv` and
  `fenchelConjugateWithin_bregDiv_of_hasSubgradientWithinAt`.
* Monotonicity and order: `fenchelConjugateWithin_antitone` and
  `fenchelConjugateWithin_mono_set`.
* Support functions: `fenchelConjugateWithin_zero`.
-/

@[expose] public section


variable {R E F : Type*} [Ring R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]
  [ConditionallyCompleteLattice F] [IsOrderedAddMonoid F]

open scoped Bregman

attribute [local simp] fenchelConjugateWithin

variable {s s₁ s₂ : Set E} {f f₁ f₂ : E → F} {x y : E} {g gx gy h : E →L[R] F} {c : F}

/-! ### 1. Constant Shifts -/

@[simp]
lemma fenchelConjugateWithin_add_const [Nonempty s]
    (hbd : BddAbove (Set.range (fun (y : s) ↦ g y.1 - f y.1))) :
    (fun x ↦ f x + c)^*[s] g = f^*[s] g - c := by
  simp [sub_add_eq_sub_sub, ciSup_sub hbd c]

@[simp]
lemma fenchelConjugateWithin_sub_const [Nonempty s]
    (hbd : BddAbove (Set.range (fun (y : s) ↦ g y.1 - f y.1))) :
    (fun x ↦ f x - c)^*[s] g = f^*[s] g + c := by
  simp [sub_sub_eq_add_sub, add_sub_right_comm, ciSup_add hbd c]

section LinearOps

variable [IsTopologicalAddGroup F]

/-! ### 2. Linear Perturbations -/

omit [IsOrderedAddMonoid F] in
@[simp]
lemma fenchelConjugateWithin_add_linear :
    (fun x ↦ f x + h x)^*[s] g = f^*[s] (g - h) := by
  simp [sub_add_eq_sub_sub, sub_right_comm]

omit [IsOrderedAddMonoid F] in
@[simp]
lemma fenchelConjugateWithin_sub_linear :
    (fun x ↦ f x - h x)^*[s] g = f^*[s] (g + h) := by
  simp [sub_sub_eq_add_sub, add_sub_right_comm]

/-! ### 3. Bregman Divergence as Objective -/

lemma fenchelConjugateWithin_bregDiv [Nonempty s]
    (hbd : BddAbove (Set.range (fun (z : s) ↦ (g + gy) z.1 - f z.1))) :
    (fun x ↦ D_[f](x, y, gy))^*[s] g = f^*[s] (g + gy) + (f y - gy y) := by
  have (x : E) : g x - D_[f](x, y, gy) = (g + gy) x - f x + (f y - gy y) := by simp [bregDiv]; abel
  simp_rw [fenchelConjugateWithin, this, ← ciSup_add hbd]

/-- At any subgradient $gy$, the conjugate of the Bregman divergence
evaluates to $(D_f(\cdot, y, gy))^*[s](g) = f^*[s](g + gy) - f^*[s](gy)$. -/
lemma fenchelConjugateWithin_bregDiv_of_hasSubgradientWithinAt (hy : y ∈ s)
    (h_gy : HasSubgradientWithinAt f gy s y)
    (hbd : BddAbove (Set.range (fun (z : s) ↦ (g + gy) z.1 - f z.1))) :
    (fun x ↦ D_[f](x, y, gy))^*[s] g = f^*[s] (g + gy) - f^*[s] gy := by
  have : Nonempty s := ⟨⟨y, hy⟩⟩
  simp only [fenchelConjugateWithin_bregDiv hbd, h_gy.fenchelConjugateWithin hy]
  abel

end LinearOps

/-! ### 4. Monotonicity Rules -/

/-- Pointwise function dominance implies reverse ordering of Fenchel conjugates. -/
lemma fenchelConjugateWithin_antitone (h_le : ∀ x ∈ s, f₁ x ≤ f₂ x) [Nonempty s]
    (hbd : BddAbove (Set.range (fun (y : s) ↦ g y.1 - f₁ y.1))) :
    f₂^*[s] g ≤ f₁^*[s] g :=
  ciSup_le fun ⟨x, hx⟩ ↦ (sub_le_sub_left (h_le x hx) (g x)).trans (le_ciSup hbd ⟨x, hx⟩)

omit [IsOrderedAddMonoid F] in
/-- Inclusion of domains implies ordering of Fenchel conjugates. -/
lemma fenchelConjugateWithin_mono_set (hs : s₁ ⊆ s₂)
    [Nonempty s₁] (hbd : BddAbove (Set.range (fun (y : s₂) ↦ g y.1 - f y.1))) :
    f^*[s₁] g ≤ f^*[s₂] g :=
  ciSup_le fun ⟨x, hx⟩ ↦ le_ciSup hbd ⟨x, hs hx⟩

/-! ### 5. Support Functions & Dual Norms -/

omit [IsOrderedAddMonoid F] in
@[simp]
lemma fenchelConjugateWithin_zero (s : Set E) (g : E →L[R] F) :
    (fun _ : E ↦ (0 : F))^*[s] g = ⨆ x : s, g x.1 := by
  simp [fenchelConjugateWithin]
