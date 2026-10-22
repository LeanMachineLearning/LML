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
continuous dual annihilators. Geometric Hahn--Banach separation bounds a functional on a
nondense submodule. Its restriction must vanish, since a nonzero linear functional is surjective.
-/

@[expose] public section

open Set

namespace Submodule

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  (s : Submodule ℝ E)

theorem dense_iff_forall_dual_eq_zero :
    Dense (s : Set E) ↔ ∀ f : StrongDual ℝ E, (∀ x ∈ s, f x = 0) → f = 0 := by
  constructor
  · intro hs f hf
    exact ContinuousLinearMap.ext_on (by simpa using hs) hf
  · intro h
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    apply top_unique
    intro x hx
    by_contra hxc
    obtain ⟨f, u, hfc, hfx⟩ := geometric_hahn_banach_closed_point s.topologicalClosure.convex
      s.isClosed_topologicalClosure hxc
    have hrestr : f.toLinearMap.comp s.subtype = 0 := by
      by_contra hf
      obtain ⟨y, hy⟩ := (f.toLinearMap.comp s.subtype).surjective hf u
      exact (hfc y (s.le_topologicalClosure y.property)).ne hy
    have hf : f = 0 := h f fun y hy ↦ DFunLike.congr_fun hrestr ⟨y, hy⟩
    simpa [hf] using (hfc 0 s.topologicalClosure.zero_mem).trans hfx

theorem exists_dual_annihilator_of_not_dense (hs : ¬ Dense (s : Set E)) :
    ∃ f : StrongDual ℝ E, f ≠ 0 ∧ ∀ x ∈ s, f x = 0 := by
  simpa only [dense_iff_forall_dual_eq_zero, not_forall, exists_prop, and_comm] using hs

theorem dense_iff_polarSubmodule_eq_bot :
    Dense (s : Set E) ↔ StrongDual.polarSubmodule ℝ s = ⊥ := by
  simp only [dense_iff_forall_dual_eq_zero, Submodule.eq_bot_iff,
    StrongDual.mem_polarSubmodule]

end Submodule
