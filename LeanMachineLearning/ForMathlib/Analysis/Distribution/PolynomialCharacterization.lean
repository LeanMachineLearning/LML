/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Distribution.Polynomial

/-!
# Characterizing polynomial functions by distributional derivatives

This file proves the converse to the elementary fact that a sufficiently high distributional
derivative of a polynomial vanishes. The analytic input is isolated in
`TestFunction.HasCompactSupportPrimitive`: every test function of integral zero must be the
derivative of a compactly supported test function.

The main results are:

* `Distribution.exists_polynomial_of_iteratedLineDerivOp_eq_zero`, for arbitrary distributions;
* `Distribution.ofFun_eq_iff_eq_of_continuous`, a general injectivity result for regular
  distributions induced by continuous functions;
* `Distribution.isPolynomial_iff_exists_iteratedLineDerivOp_ofFun_eq_zero`, the desired
  characterization for continuous real functions.
-/

@[expose] public section

open MeasureTheory
open scoped Distributions

namespace Distribution

open LineDeriv

/-- A distribution on an open subset of the real line whose `k`th derivative vanishes is induced
by a polynomial, provided compactly supported primitives exist.

No smoothness or regularity assumption is made on the distribution. The proof repeatedly uses
that a distribution with zero derivative is constant and the surjectivity of polynomial
differentiation over `ℝ`. -/
theorem exists_polynomial_of_iteratedLineDerivOp_eq_zero
    {Ω : TopologicalSpace.Opens ℝ} [TestFunction.HasCompactSupportPrimitive Ω]
    (ρ : 𝓓(Ω, ℝ)) (hρ : ∫ x, ρ x = 1)
    (T : 𝓓'(Ω, ℝ)) (k : ℕ)
    (hT : iteratedLineDerivOp (fun _ : Fin k => (1 : ℝ)) T = 0) :
    ∃ p : Polynomial ℝ, T = ofFun Ω (fun x => p.eval x) volume ⊤ := by
  induction k generalizing T with
  | zero =>
      refine ⟨0, ?_⟩
      rwa [show (fun x : ℝ => (0 : Polynomial ℝ).eval x) = 0 by funext x; simp, ofFun_zero]
  | succ k ih =>
      let DT : 𝓓'(Ω, ℝ) := ∂_{(1 : ℝ)} T
      have hDT : iteratedLineDerivOp (fun _ : Fin k => (1 : ℝ)) DT = 0 := by
        rwa [iteratedLineDerivOp_const_eq_iter_lineDerivOp] at hT ⊢
      obtain ⟨p, hp⟩ := ih DT hDT
      obtain ⟨q, hq⟩ := Polynomial.derivative_surjective_of_charZero p
      let Q : 𝓓'(Ω, ℝ) := ofFun Ω (fun x => q.eval x) volume ⊤
      have hqLoc : LocallyIntegrableOn (fun x => q.eval x) Ω volume :=
        q.continuous.locallyIntegrable.locallyIntegrableOn _
      have hDsub : (lineDerivCLM (1 : ℝ) (T - Q) : 𝓓'(Ω, ℝ)) = 0 := by
        rw [map_sub, lineDerivCLM_ofFun_eq_of_hasDerivAt (fun x => q.hasDerivAt x) hqLoc
          ((q.derivative.continuous).locallyIntegrable.locallyIntegrableOn _), hq, ← hp]
        exact sub_self _
      have hcLoc : LocallyIntegrableOn (fun _ : ℝ => (T - Q) ρ) Ω volume :=
        continuous_const.locallyIntegrable.locallyIntegrableOn _
      refine ⟨q + Polynomial.C ((T - Q) ρ), ?_⟩
      have heval : (fun x => (q + Polynomial.C ((T - Q) ρ)).eval x) =
          (fun x => q.eval x) + (fun _ : ℝ => (T - Q) ρ) := by
        funext x
        simp
      rw [heval, ofFun_add hqLoc hcLoc, ← sub_eq_iff_eq_add']
      exact eq_ofFun_const_of_lineDerivCLM_eq_zero_of_hasCompactSupportPrimitive ρ hρ (T - Q) hDsub

/-- Two locally integrable continuous functions on a finite-dimensional real normed space induce
the same regular distribution if and only if they are equal.

This packages `Distribution.ofFun_injective`, whose conclusion is only almost-everywhere equality,
with the fact that a full-support measure detects equality of continuous functions. -/
theorem ofFun_eq_iff_eq_of_continuous
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure E} [μ.IsOpenPosMeasure] {n : ℕ∞} {f g : E → F}
    (hf : Continuous f) (hg : Continuous g)
    (hfloc : LocallyIntegrableOn f (Set.univ : Set E) μ)
    (hgloc : LocallyIntegrableOn g (Set.univ : Set E) μ) :
    ofFun (⊤ : TopologicalSpace.Opens E) f μ n =
      ofFun (⊤ : TopologicalSpace.Opens E) g μ n ↔ f = g := by
  constructor
  · intro h
    have hae : f =ᵐ[μ.restrict (Set.univ : Set E)] g := ofFun_injective hfloc hgloc h
    exact (Continuous.ae_eq_iff_eq μ hf hg).mp <| by simpa using hae
  · rintro rfl
    rfl

/-- A continuous real function is polynomial if one of its distributional derivatives vanishes,
assuming the compactly supported primitive property on the real line. -/
theorem isPolynomial_of_iteratedLineDerivOp_ofFun_eq_zero
    [TestFunction.HasCompactSupportPrimitive (⊤ : TopologicalSpace.Opens ℝ)]
    (ρ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) (hρ : ∫ x, ρ x = 1)
    {f : ℝ → ℝ} (hf : Continuous f) (k : ℕ)
    (h : iteratedLineDerivOp (fun _ : Fin k => (1 : ℝ))
      (ofFun (⊤ : TopologicalSpace.Opens ℝ) f volume ⊤) = 0) :
    Function.IsPolynomial f := by
  obtain ⟨p, hp⟩ := exists_polynomial_of_iteratedLineDerivOp_eq_zero ρ hρ
    (ofFun (⊤ : TopologicalSpace.Opens ℝ) f volume ⊤) k h
  have hfloc : LocallyIntegrableOn f (Set.univ : Set ℝ) volume :=
    hf.locallyIntegrable.locallyIntegrableOn _
  have hploc : LocallyIntegrableOn (fun x => p.eval x) (Set.univ : Set ℝ) volume :=
    p.continuous.locallyIntegrable.locallyIntegrableOn _
  have heq : f = fun x => p.eval x :=
    (ofFun_eq_iff_eq_of_continuous hf p.continuous hfloc hploc).mp hp
  exact ⟨p, fun x => (congrFun heq x).symm⟩

/-- A continuous real function is polynomial exactly when one of its distributional derivatives
vanishes, assuming the compactly supported primitive property on the real line. -/
theorem isPolynomial_iff_exists_iteratedLineDerivOp_ofFun_eq_zero
    [TestFunction.HasCompactSupportPrimitive (⊤ : TopologicalSpace.Opens ℝ)]
    (ρ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) (hρ : ∫ x, ρ x = 1) {f : ℝ → ℝ} (hf : Continuous f) :
    Function.IsPolynomial f ↔ ∃ k : ℕ, iteratedLineDerivOp (fun _ : Fin k => (1 : ℝ))
      (ofFun (⊤ : TopologicalSpace.Opens ℝ) f volume ⊤) = 0 := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.natDegree + 1, ?_⟩
    have heval : f = fun x => p.eval x := funext fun x => (hp x).symm
    rw [heval]
    exact iteratedLineDerivOp_ofFun_polynomial_natDegree_add_one_eq_zero p
  · rintro ⟨k, hk⟩
    exact isPolynomial_of_iteratedLineDerivOp_ofFun_eq_zero ρ hρ hf k hk

end Distribution
