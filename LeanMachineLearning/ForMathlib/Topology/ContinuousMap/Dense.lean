/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Dense families of continuous maps on compact spaces

This file gives the uniform epsilon formulation of density in a continuous-map space with
compact domain.
-/

@[expose] public section

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [PseudoMetricSpace Y]

/-- A family of continuous maps on a compact space is dense exactly when every continuous map can
be approximated pointwise with one uniform positive error bound. -/
theorem dense_iff_forall_exists_forall_dist_lt {S : Set C(X, Y)} :
    Dense S ↔ ∀ (f : C(X, Y)) (ε : ℝ), 0 < ε →
      ∃ g ∈ S, ∀ x, dist (g x) (f x) < ε := by
  rw [Metric.dense_iff]
  constructor
  · intro h f ε hε
    obtain ⟨g, hgBall, hgS⟩ := h f ε hε
    refine ⟨g, hgS, ?_⟩
    rwa [Metric.mem_ball, ContinuousMap.dist_lt_iff hε] at hgBall
  · intro h f ε hε
    obtain ⟨g, hgS, hg⟩ := h f ε hε
    refine ⟨g, ?_, hgS⟩
    rw [Metric.mem_ball, ContinuousMap.dist_lt_iff hε]
    exact hg

end ContinuousMap
