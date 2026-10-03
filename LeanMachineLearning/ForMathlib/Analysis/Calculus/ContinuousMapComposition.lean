/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Differentiating curves of continuous maps

This file supplies a general criterion for differentiating a curve with values in `C(X, E)`
when `X` is compact: pointwise differentiability and continuity of the proposed derivative as a
`C(X, E)`-valued curve suffice.  As an application, it differentiates a continuously
differentiable function after composition with a continuously varying affine argument.

The results are stated for maps into an arbitrary real Banach space rather than only for
real-valued maps.
-/

open MeasureTheory

universe u v

@[expose] public section

namespace HasDerivAt

variable {X : Type u} {E : Type v} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A curve of continuous maps has a derivative if all of its evaluations have the proposed
derivative and the proposed derivative is continuous in the uniform norm.

The compactness of `X` equips `C(X, E)` with its supremum norm.  The proof uses the fundamental
theorem of calculus after applying each continuous evaluation map. -/
theorem continuousMap_of_continuous {f f' : ℝ → C(X, E)}
    (hf : ∀ x t, HasDerivAt (fun s ↦ f s x) (f' t x) t) (hf' : Continuous f') (t : ℝ) :
    HasDerivAt f (f' t) t := by
  have hfi : ∀ a b, IntervalIntegrable f' volume a b :=
    fun a b ↦ hf'.intervalIntegrable a b
  let q : ℝ → C(X, E) :=
    (fun _ ↦ f 0) + fun s ↦ ∫ r in 0..s, f' r
  have hEq : q = f := by
    funext s
    apply ContinuousMap.ext
    intro x
    have hFTC : ∫ r in 0..s, (ContinuousMap.evalCLM ℝ x) (f' r) = f s x - f 0 x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ ↦ hf x r)
        (((ContinuousMap.evalCLM ℝ x).continuous.comp hf').intervalIntegrable 0 s)
    change f 0 x + (ContinuousMap.evalCLM ℝ x) (∫ r in 0..s, f' r) = f s x
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousMap.evalCLM ℝ x) (hfi 0 s), hFTC]
    simp
  have hder : HasDerivAt q (0 + f' t) t :=
    (hasDerivAt_const t (f 0)).add (hf'.integral_hasStrictDerivAt 0 t).hasDerivAt
  simpa [hEq] using hder

/-- Compose a differentiable Banach-valued function with the family of affine arguments
`x ↦ u x + t * v x`.  Differentiation in `t` may be performed in the uniform norm on
`C(X, E)`.

Bundling `g` and `dg` as continuous maps records exactly the continuity needed to upgrade the
pointwise derivatives `hg` to a derivative in the function space. -/
theorem continuousMap_comp_affine {g dg : C(ℝ, E)} (hg : ∀ y, HasDerivAt g (dg y) y)
   (u v : C(X, ℝ)) (t : ℝ) : HasDerivAt (fun s ↦ g.comp (u + ContinuousMap.const X s * v))
    ⟨fun x ↦ v x • dg (u x + t * v x), by fun_prop⟩ t := by
  apply continuousMap_of_continuous (t := t)
  · intro x s
    convert (hg (u x + s * v x)).scomp s
        ((hasDerivAt_const s (u x)).add (hasDerivAt_mul_const (v x))) using 1 <;>
      simp [Function.comp_def]
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact (v.continuous.comp continuous_snd).smul <| by fun_prop

end HasDerivAt
