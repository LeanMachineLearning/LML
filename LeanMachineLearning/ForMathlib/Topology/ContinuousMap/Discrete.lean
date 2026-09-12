/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Continuous maps from a discrete space

This file upgrades the equivalence between continuous maps from a discrete space and arbitrary
functions to a linear equivalence.
-/

universe u v w

@[expose] public section

namespace ContinuousMap

variable (R : Type u) {X : Type v} {M : Type w}
variable [Semiring R] [TopologicalSpace X] [DiscreteTopology X]
variable [TopologicalSpace M] [AddCommMonoid M] [ContinuousAdd M]
variable [Module R M] [ContinuousConstSMul R M]

/-- Continuous maps from a discrete space are linearly equivalent to arbitrary functions. -/
def linearEquivFnOfDiscrete : C(X, M) ≃ₗ[R] (X → M) :=
  equivFnOfDiscrete.toLinearEquiv
    { map_add := fun _ _ ↦ rfl
      map_smul := fun _ _ ↦ rfl }

end ContinuousMap
