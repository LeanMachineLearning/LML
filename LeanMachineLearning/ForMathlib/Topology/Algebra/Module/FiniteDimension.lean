/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Density and finite-dimensional submodules

This file records that no subset of a proper finite-dimensional submodule can be dense.
-/

@[expose] public section

open Set

namespace Submodule

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [Module 𝕜 E] [ContinuousSMul 𝕜 E] [T2Space E]

/-- A subset of a proper finite-dimensional submodule is not dense in the ambient space. -/
theorem not_dense_of_subset_of_finiteDimensional (s : Submodule 𝕜 E)
    [FiniteDimensional 𝕜 s] (hs : s ≠ ⊤) {t : Set E} (ht : t ⊆ s) :
    ¬ Dense t := by
  intro ht_dense
  apply hs
  apply top_unique
  intro x _
  have hx : x ∈ closure (s : Set E) := by
    rw [(ht_dense.mono ht).closure_eq]
    exact Set.mem_univ x
  rwa [s.closed_of_finiteDimensional.closure_eq] at hx

/-- A proper finite-dimensional submodule is not dense in the ambient space. -/
theorem not_dense_of_finiteDimensional (s : Submodule 𝕜 E)
    [FiniteDimensional 𝕜 s] (hs : s ≠ ⊤) :
    ¬ Dense (s : Set E) :=
  s.not_dense_of_subset_of_finiteDimensional hs fun _ ↦ id

end Submodule
