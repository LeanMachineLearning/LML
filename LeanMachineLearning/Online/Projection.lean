/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.NormPow

import LeanMachineLearning.ForMathlib.Analysis.Calculus.Deriv.Slope

/-!
# Projection on a nonempty closed convex set in an inner product space

-/

@[expose] public section

open Real Finset Metric
open scoped RealInnerProductSpace Gradient

namespace Learning

section Definition

variable {E : Type*} [PseudoMetricSpace E] {s : Set E}

open Classical in
/-- Projection on a set: closest point to `x` in the set `s`, taking an arbitrary value if there is
no such point. -/
noncomputable
def proj [Zero E] (s : Set E) (x : E) : E :=
  if h : ∃ y ∈ s, IsMinOn (dist x) s y then h.choose else 0

/-- If the set is closed and nonempty, then the projection exists. -/
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

/-- If the set is closed and nonempty, then the projection belongs to the set. -/
lemma _root_.IsClosed.proj_mem [Zero E] [ProperSpace E]
    (h_closed : IsClosed s) (h_nonempty : s.Nonempty) (x : E) :
    proj s x ∈ s := by
  have h := h_closed.exists_isMinOn_dist h_nonempty x
  rw [proj, dif_pos h]
  exact h.choose_spec.1

lemma isMinOn_proj_of_exists [Zero E] {x : E} (h : ∃ y ∈ s, IsMinOn (dist x) s y) :
    IsMinOn (dist x) s (proj s x) := by
  rw [proj, dif_pos h]
  exact h.choose_spec.2

/-- If the set is closed and nonempty, then the projection is a minimizer of the distance. -/
lemma _root_.IsClosed.isMinOn_proj [Zero E] [ProperSpace E]
    (h_closed : IsClosed s) (h_nonempty : s.Nonempty) (x : E) :
    IsMinOn (dist x) s (proj s x) :=
  isMinOn_proj_of_exists (h_closed.exists_isMinOn_dist h_nonempty x)

/-- If `x ∈ s`, then the projection of `x` onto `s` is `x`. -/
@[simp]
lemma proj_of_mem {E : Type*} [MetricSpace E] [Zero E] {s : Set E} {x : E}
    (hx : x ∈ s) :
    proj s x = x := by
  have h_min : IsMinOn (dist x) s x := fun y hy ↦ by simp
  have h_min_proj := isMinOn_proj_of_exists ⟨x, hx, h_min⟩ hx
  symm
  simpa using h_min_proj

end Definition

lemma _root_.IsClosed.isMinOn_norm_sq_proj {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {s : Set E} (h_closed : IsClosed s) (h_nonempty : s.Nonempty) (x : E) :
    IsMinOn (fun y ↦ ‖y - x‖ ^ 2) s (proj s x) := by
  intro y hy
  simp only [Set.mem_setOf_eq, sq_le_sq, abs_dist, ← dist_eq_norm, dist_comm _ x]
  exact h_closed.isMinOn_proj h_nonempty x hy

section Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {s : Set E}

lemma gradient_norm_sub_sq (x y : E) : ∇ (fun z ↦ ‖z - x‖ ^ 2) y = 2 • (y - x) := by
  have h := ((hasFDerivAt_id y).sub_const x).norm_sq.hasGradientAt.gradient
  simp only [id_eq, map_sub, ContinuousLinearMap.comp_id, map_nsmul] at h
  rw [h]
  congr
  · exact (InnerProductSpace.toDual ℝ E).symm_apply_apply _
  · exact (InnerProductSpace.toDual ℝ E).symm_apply_apply _

lemma gradient_dist_sq (x y : E) : ∇ (fun z ↦ dist x z ^ 2) y = 2 • (y - x) := by
  simp only [dist_eq_norm, norm_sub_rev x]
  exact gradient_norm_sub_sq x y

section
-- Mathlib.Analysis.InnerProductSpace.NormPow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem Differentiable.norm_pow {f : F → E} (hf : Differentiable ℝ f) {p : ℕ} (hp : 1 < p) :
    Differentiable ℝ (fun x ↦ ‖f x‖ ^ p) := by
  suffices Differentiable ℝ (fun x ↦ ‖f x‖ ^ (p : ℝ)) by
    convert this using 1
    simp
  exact hf.norm_rpow (by simp [hp])

end

lemma inner_proj_nonpos (h_closed : IsClosed s) (h_convex : Convex ℝ s) (h_nonempty : s.Nonempty)
    (x : E) {y : E} (hy : y ∈ s) :
    ⟪proj s x - x, proj s x - y⟫ ≤ 0 := by
  suffices 0 ≤ 2 * ⟪proj s x - x, y - proj s x⟫ by
    simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left] at this
    rwa [← neg_sub y, inner_neg_right, neg_nonpos]
  have h_inner := ConvexOn.inner_gradient_nonneg_of_isMinOn h_convex ?_ ?_ ?_ (x := proj s x)
    (y := y) (f := fun z ↦ ‖z - x‖ ^ 2) hy
  · rw [real_inner_comm, ← inner_smul_right]
    convert h_inner using 2
    symm
    convert gradient_norm_sub_sq x (proj s x)
    exact ofNat_smul_eq_nsmul ℝ 2 (proj s x - x)
  · refine Differentiable.differentiableAt ?_
    refine Differentiable.norm_pow ?_ (by simp)
    fun_prop
  · exact h_closed.proj_mem h_nonempty x
  · exact h_closed.isMinOn_norm_sq_proj h_nonempty x

lemma inner_proj_nonneg (h_closed : IsClosed s) (h_convex : Convex ℝ s) (h_nonempty : s.Nonempty)
    (x : E) {y : E} (hy : y ∈ s) :
    0 ≤ ⟪proj s x - x, y - proj s x⟫ := by
  rw [← neg_sub _ y, inner_neg_right, neg_nonneg]
  exact inner_proj_nonpos h_closed h_convex h_nonempty x hy

lemma dist_proj_proj_le (h_closed : IsClosed s) (h_convex : Convex ℝ s) (h_nonempty : s.Nonempty)
    (x y : E) :
    dist (proj s x) (proj s y) ≤ dist x y := by
  suffices dist (proj s x) (proj s y) ^ 2 ≤ dist x y ^ 2 by simpa [sq_le_sq] using this
  have h_eq : ‖x - y‖ ^ 2 = ‖proj s x - proj s y‖ ^ 2 + ‖x - y + proj s y - proj s x‖ ^ 2 +
      2 * ⟪proj s x - x, proj s y - proj s x⟫ + 2 * ⟪proj s y - y, proj s x - proj s y⟫ := by
    calc ‖x - y‖ ^ 2
    _ = ‖proj s x - proj s y + (x - y + proj s y - proj s x)‖ ^ 2 := by congr; abel
    _ = ‖proj s x - proj s y‖ ^ 2 + ‖x - y + proj s y - proj s x‖ ^ 2 +
        2 * ⟪proj s x - proj s y, x - y + proj s y - proj s x⟫ := by
      rw [norm_add_sq (𝕜 := ℝ)]
      simp only [RCLike.re_to_real]
      ring
    _ = ‖proj s x - proj s y‖ ^ 2 + ‖x - y + proj s y - proj s x‖ ^ 2 +
        2 * ⟪proj s x - x, proj s y - proj s x⟫ + 2 * ⟪proj s y - y, proj s x - proj s y⟫ := by
      simp_rw [add_assoc]
      congr
      rw [← mul_add, ← neg_sub _ (proj s y), inner_neg_right, add_comm (- _), ← sub_eq_add_neg,
        ← inner_sub_left, real_inner_comm]
      congr 2
      abel
  simp_rw [dist_eq_norm, h_eq, add_assoc]
  refine le_add_of_nonneg_right ?_
  have h1 : 0 ≤ ⟪proj s x - x, proj s y - proj s x⟫ :=
    inner_proj_nonneg h_closed h_convex h_nonempty x (h_closed.proj_mem h_nonempty y)
  have h2 : 0 ≤ ⟪proj s y - y, proj s x - proj s y⟫ :=
    inner_proj_nonneg h_closed h_convex h_nonempty y (h_closed.proj_mem h_nonempty x)
  positivity

lemma dist_proj_le (h_closed : IsClosed s) (h_convex : Convex ℝ s) (h_nonempty : s.Nonempty)
    (x : E) {y : E} (hy : y ∈ s) :
    dist (proj s x) y ≤ dist x y := by
  nth_rw 1 [← proj_of_mem hy]
  exact dist_proj_proj_le h_closed h_convex h_nonempty x y

lemma lipschitz_proj {s : Set E}
    (h_closed : IsClosed s) (h_convex : Convex ℝ s) (h_nonempty : s.Nonempty) :
    LipschitzWith 1 (proj s) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_dist]
  grw [dist_proj_proj_le h_closed h_convex h_nonempty x y]

lemma continuous_proj {s : Set E}
    (h_closed : IsClosed s) (h_convex : Convex ℝ s) (h_nonempty : s.Nonempty) :
  Continuous (proj s) := (lipschitz_proj h_closed h_convex h_nonempty).continuous

end Convex

end Learning
