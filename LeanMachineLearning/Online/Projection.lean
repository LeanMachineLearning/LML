/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib

import LeanMachineLearning.ForMathlib.Analysis.Calculus.Deriv.Slope

/-!
# Projection on a nonempty closed convex set in an inner product space

-/

@[expose] public section

open Real Finset Metric
open scoped RealInnerProductSpace

namespace Learning

section Definition

variable {E : Type*} [PseudoMetricSpace E] {s : Set E}

open Classical in
/-- Projection on a set: closest point to `x` in the set `s`, taking an arbitrary value if there is
no such point. -/
noncomputable
def proj [Zero E] (s : Set E) (x : E) : E :=
  if h : ∃ y ∈ s, IsMinOn (dist x) s y then h.choose else 0

lemma _root_.IsClosed.exists_isMinOn_dist [ProperSpace E]
    (h_closed : IsClosed s) (h_nonempty : s.Nonempty) (x : E) :
    ∃ y ∈ s, IsMinOn (dist x) s y := by
  have h_cont : Continuous (dist x) := by fun_prop
  obtain ⟨z, hz⟩ := h_nonempty
  have h_compact : IsCompact (closedBall x (dist x z) ∩ s) :=
    IsCompact.inter_right (isCompact_closedBall _ _) h_closed
  have h3 : (closedBall x (dist x z) ∩ s).Nonempty := ⟨z, ⟨by simp [dist_comm], hz⟩⟩
  obtain ⟨y, hy, hy_min⟩ := h_compact.exists_isMinOn h3 h_cont.continuousOn
  refine ⟨y, hy.2, ?_⟩
  intro u hu
  simp only [Set.mem_setOf_eq]
  by_cases h1 : u ∈ closedBall x (dist x z)
  · specialize hy_min ⟨h1, hu⟩
    grind
  · simp only [mem_closedBall, not_le, Set.mem_inter_iff] at h1 hy
    grind [dist_comm]

lemma _root_.IsClosed.proj_mem [Zero E] [ProperSpace E]
    (h_closed : IsClosed s) (h_nonempty : s.Nonempty) (x : E) :
    proj s x ∈ s := by
  have h := h_closed.exists_isMinOn_dist h_nonempty x
  rw [proj, dif_pos h]
  exact h.choose_spec.1

lemma _root_.IsClosed.isMinOn_proj [Zero E] [ProperSpace E]
    (h_closed : IsClosed s) (h_nonempty : s.Nonempty) (x : E) :
    IsMinOn (dist x) s (proj s x) := by
  have h := h_closed.exists_isMinOn_dist h_nonempty x
  rw [proj, dif_pos h]
  exact h.choose_spec.2

end Definition

lemma _root_.IsClosed.isMinOn_norm_sq_proj {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {s : Set E} (h_closed : IsClosed s) (h_nonempty : s.Nonempty) (x : E) :
    IsMinOn (fun y ↦ ‖y - x‖ ^ 2) s (proj s x) := by
  intro y hy
  simp only [Set.mem_setOf_eq, sq_le_sq, abs_dist, ← dist_eq_norm]
  have h_min := h_closed.isMinOn_proj h_nonempty x hy
  simp_rw [dist_comm _ x]
  exact h_min

section Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {s : Set E}

lemma gradient_norm_sub_sq (x y : E) : gradient (fun z ↦ ‖z - x‖ ^ 2) y = 2 • (y - x) := by
  have h := ((hasFDerivAt_id y).sub_const x).norm_sq.hasGradientAt.gradient
  simp only [id_eq, map_sub, ContinuousLinearMap.comp_id, map_nsmul] at h
  rw [h]
  congr
  · exact (InnerProductSpace.toDual ℝ E).symm_apply_apply _
  · exact (InnerProductSpace.toDual ℝ E).symm_apply_apply _

lemma gradient_dist_sq (x y : E) : gradient (fun z ↦ dist x z ^ 2) y = 2 • (y - x) := by
  simp only [dist_eq_norm, norm_sub_rev x]
  exact gradient_norm_sub_sq x y

lemma dist_proj_le (h_closed : IsClosed s) (h_convex : Convex ℝ s) (h_nonempty : s.Nonempty)
    (x : E) {y : E} (hy : y ∈ s) :
    dist (proj s x) y ≤ dist x y := by
  suffices dist (proj s x) y ^ 2 ≤ dist x y ^ 2 by simpa [sq_le_sq] using this
  calc dist (proj s x) y ^ 2
  _ = ‖proj s x - y‖ ^ 2 := by simp [dist_eq_norm]
  _ ≤ ‖proj s x - y‖ ^ 2 + ‖proj s x - x‖ ^ 2 + 2 * ⟪proj s x - x, y - proj s x⟫ := by
    rw [add_assoc]
    refine le_add_of_nonneg_right ?_
    suffices 0 ≤ 2 * ⟪proj s x - x, y - proj s x⟫ by positivity
    have h_min := h_closed.isMinOn_norm_sq_proj h_nonempty x hy
    have h_inner := ConvexOn.inner_gradient_nonneg_of_isMinOn h_convex ?_ ?_ ?_ (x := proj s x)
      (y := y) (f := fun z ↦ ‖z - x‖ ^ 2) hy
    · rw [real_inner_comm, ← inner_smul_right]
      convert h_inner using 2
      symm
      convert gradient_norm_sub_sq x (proj s x)
      exact ofNat_smul_eq_nsmul ℝ 2 (proj s x - x)
    · suffices DifferentiableAt ℝ (fun z ↦ ‖z - x‖ ^ (2 : ℝ)) (proj s x) by
        convert this
        simp
      refine Differentiable.differentiableAt ?_
      refine Differentiable.norm_rpow ?_ (by simp)
      fun_prop
    · exact h_closed.proj_mem h_nonempty x
    · exact h_closed.isMinOn_norm_sq_proj h_nonempty x
  _ = ‖y - proj s x + (proj s x - x)‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℝ), RCLike.re_to_real, norm_sub_rev, add_assoc, add_comm _ (2 * _),
      ← add_assoc, real_inner_comm]
  _ = ‖y - x‖ ^ 2 := by congr 2; simp
  _ = dist x y ^ 2 := by simp [dist_eq_norm, norm_sub_rev]

end Convex

end Learning
