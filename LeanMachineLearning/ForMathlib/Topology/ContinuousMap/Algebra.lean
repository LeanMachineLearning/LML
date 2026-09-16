/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Continuous linear maps on continuous function spaces

This file bundles coercion from continuous maps to arbitrary functions as a continuous linear map.
-/

universe u v w

@[expose] public section

namespace ContinuousMap

variable (R : Type u) {X : Type v} {M : Type w}
variable [Semiring R] [TopologicalSpace X]
variable [TopologicalSpace M] [AddCommMonoid M] [ContinuousAdd M]
variable [Module R M] [ContinuousConstSMul R M]

/-- Coercion to a function as a continuous linear map. -/
@[simps! apply]
def coeFnCLM : C(X, M) →L[R] (X → M) where
  __ := coeFnLinearMap R
  cont := continuous_coeFun

end ContinuousMap
