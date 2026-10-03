/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Bochner integrals valued in closed submodules

This file proves that a Bochner integral of a function taking values almost everywhere in a
closed submodule still belongs to that submodule.  The main ingredient is the continuous linear
quotient map: after passing to the quotient, the integrand is almost everywhere zero.
-/

@[expose] public section

open MeasureTheory

namespace ContinuousLinearMap

variable {α E F 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α}
  [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- The Bochner integral of a function valued almost everywhere in the kernel of a continuous
linear map still belongs to its kernel. -/
theorem integral_mem_ker (L : E →L[𝕜] F) {f : α → E}
    (hf : ∀ᵐ x ∂μ, f x ∈ L.ker) :
    (∫ x, f x ∂μ) ∈ L.ker := by
  by_cases hE : CompleteSpace E
  · let _ := hE
    by_cases hfi : Integrable f μ
    · simp only [LinearMap.mem_ker, coe_coe, ← L.integral_comp_comm hfi]
      exact integral_eq_zero_of_ae (hf.mono fun x hx ↦ LinearMap.mem_ker.mp hx)
    · simp [integral_undef hfi]
  · simp [integral, hE]

end ContinuousLinearMap

namespace Submodule

variable {α E 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α}
  [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]

/-- The Bochner integral of a function valued almost everywhere in a closed submodule belongs to
that submodule.  No integrability or completeness assumption is needed: in the remaining cases,
the Bochner integral is defined to be zero. -/
theorem integral_mem (S : Submodule 𝕜 E) (hS : IsClosed (S : Set E))
    {f : α → E} (hf : ∀ᵐ x ∂μ, f x ∈ S) :
    (∫ x, f x ∂μ) ∈ S := by
  by_cases hE : CompleteSpace E
  · let _ := hE
    let _ : IsClosed (S : Set E) := hS
    rw [← S.ker_mkQ]
    exact S.mkQL.integral_mem_ker (by
      filter_upwards [hf] with x hx
      exact LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero S).2 hx))
  · simp [integral, hE]

/-- The Bochner integral of a function valued almost everywhere in a submodule belongs to the
topological closure of that submodule. -/
theorem integral_mem_topologicalClosure (S : Submodule 𝕜 E) {f : α → E}
    (hf : ∀ᵐ x ∂μ, f x ∈ S) :
    (∫ x, f x ∂μ) ∈ S.topologicalClosure :=
  S.topologicalClosure.integral_mem S.isClosed_topologicalClosure
    (hf.mono fun _ hx ↦ S.le_topologicalClosure hx)

end Submodule

namespace ClosedSubmodule

variable {α E 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α}
  [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]

/-- The Bochner integral of a function valued almost everywhere in a closed submodule belongs to
that closed submodule. -/
theorem integral_mem (S : ClosedSubmodule 𝕜 E) {f : α → E}
    (hf : ∀ᵐ x ∂μ, f x ∈ S) :
    (∫ x, f x ∂μ) ∈ S :=
  S.toSubmodule.integral_mem S.isClosed (by simpa using hf)

end ClosedSubmodule
