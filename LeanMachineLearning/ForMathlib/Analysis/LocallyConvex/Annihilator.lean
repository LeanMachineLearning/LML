/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Density and annihilators

This file characterizes dense real submodules of locally convex spaces in terms of their
continuous dual annihilators. The reverse implication is an application of geometric
Hahn--Banach separation.
-/

@[expose] public section

open Set

namespace Submodule

/-- A real submodule of a locally convex topological vector space is dense exactly when every
continuous linear functional vanishing on it is zero. -/
theorem dense_iff_forall_dual_eq_zero
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    (s : Submodule ℝ E) :
    Dense (s : Set E) ↔
      ∀ f : StrongDual ℝ E, (∀ x ∈ s, f x = 0) → f = 0 := by
  constructor
  · intro hs f hf
    ext x
    have hfun : (f : E → ℝ) = (0 : E → ℝ) :=
      Continuous.ext_on hs f.continuous continuous_zero (by
        intro y hy
        simpa using hf y hy)
    exact congrFun hfun x
  · intro h
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    apply top_unique
    intro x hx
    by_contra hxc
    obtain ⟨f, u, hfc, hfx⟩ :=
      geometric_hahn_banach_closed_point
        s.topologicalClosure.convex
        s.isClosed_topologicalClosure hxc
    have hfzero : ∀ y ∈ s.topologicalClosure, f y = 0 := by
      intro y hy
      by_contra hfy
      have hlt := hfc ((u / f y) • y)
        (s.topologicalClosure.smul_mem (u / f y) hy)
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ u hfy] at hlt
      exact (lt_irrefl u) hlt
    have hf : f = 0 :=
      h f fun y hy ↦ hfzero y (s.le_topologicalClosure hy)
    have hu0 : 0 < u := by
      simpa using hfc 0 s.topologicalClosure.zero_mem
    have hux0 : u < 0 := by
      simpa [hf] using hfx
    exact (not_lt_of_ge hu0.le) hux0

/-- If a real submodule of a locally convex space is not dense, a nonzero continuous linear
functional annihilates it. -/
theorem exists_dual_annihilator_of_not_dense
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    (s : Submodule ℝ E) (hs : ¬ Dense (s : Set E)) :
    ∃ f : StrongDual ℝ E, f ≠ 0 ∧ ∀ x ∈ s, f x = 0 := by
  grind [Submodule.dense_iff_forall_dual_eq_zero]

/-- A real submodule is dense exactly when its polar submodule is trivial. -/
theorem dense_iff_polarSubmodule_eq_bot
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    (s : Submodule ℝ E) :
    Dense (s : Set E) ↔ StrongDual.polarSubmodule ℝ s = ⊥ := by
  rw [dense_iff_forall_dual_eq_zero]
  constructor
  · intro h
    ext f
    rw [StrongDual.mem_polarSubmodule, Submodule.mem_bot]
    constructor
    · exact h f
    · rintro rfl x hx
      rfl
  · intro h f hf
    have hmem : f ∈ StrongDual.polarSubmodule ℝ s :=
      (StrongDual.mem_polarSubmodule ℝ s f).2 hf
    rw [h] at hmem
    exact hmem

end Submodule
