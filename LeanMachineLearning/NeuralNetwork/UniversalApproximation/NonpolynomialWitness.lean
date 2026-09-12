/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Distribution.PolynomialCharacterization
public import LeanMachineLearning.ForMathlib.Analysis.Distribution.TestFunction.Normalize

/-!
# Test-function witnesses for nonpolynomial activations

This file extracts the analytic witness needed by convolution-based universal-approximation
arguments.  A continuous nonpolynomial function defines a regular distribution whose derivative
of every order is nonzero.  Evaluating such a derivative on a suitable test function gives a
nonzero integral involving the corresponding iterated derivative of the test function.

The final theorem uses the reflected activation `x ↦ σ (-x)`.  This is exactly the orientation
that occurs when evaluating the left convolution `φ ⋆ σ` at zero.
-/

@[expose] public section

open MeasureTheory
open scoped Distributions

namespace Learning.ShallowNetwork

/-- Reflect a continuous real function through the origin. -/
noncomputable def reflectedActivation (σ : C(ℝ, ℝ)) : C(ℝ, ℝ) :=
  σ.comp (-ContinuousMap.id ℝ)

@[simp]
theorem reflectedActivation_apply (σ : C(ℝ, ℝ)) (x : ℝ) :
    reflectedActivation σ x = σ (-x) := rfl

/-- Reflection preserves the property of being a polynomial function. -/
theorem isPolynomial_reflectedActivation_iff (σ : C(ℝ, ℝ)) :
    Function.IsPolynomial (reflectedActivation σ) ↔ Function.IsPolynomial σ := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.comp (-Polynomial.X), fun x ↦ ?_⟩
    simp only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
      hp, reflectedActivation_apply, neg_neg]
  · rintro ⟨p, hp⟩
    refine ⟨p.comp (-Polynomial.X), fun x ↦ ?_⟩
    simp only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
      hp, reflectedActivation_apply]

end Learning.ShallowNetwork

namespace Distribution

open LineDeriv

/-- Evaluate an iterated distributional derivative by moving all derivatives onto the test
function.  The statement is vector-valued and valid on every open subset of the real line. -/
theorem iteratedLineDerivOp_apply_iterated_testFunction
    {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {Ω : TopologicalSpace.Opens ℝ} (T : 𝓓'(Ω, F)) (n : ℕ) (φ : 𝓓(Ω, ℝ)) :
    iteratedLineDerivOp (fun _ : Fin n ↦ (1 : ℝ)) T φ =
      (-1 : ℝ) ^ n • T (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n]) φ) := by
  rw [iteratedLineDerivOp_const_eq_iter_lineDerivOp]
  induction n generalizing T φ with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change Distribution.lineDerivCLM (1 : ℝ) ((∂_{(1 : ℝ)})^[n] T) φ =
        (-1 : ℝ) ^ (n + 1) •
          T (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n + 1]) φ)
      rw [Distribution.lineDerivCLM_apply, ih]
      rw [Function.iterate_succ_apply]
      simp only [pow_succ]
      module

/-- Every distributional derivative of a continuous nonpolynomial function is nonzero.

The compactly-supported-primitive class is the exactness input used by the converse
characterization of polynomial regular distributions. -/
theorem iteratedLineDerivOp_ofFun_ne_zero_of_not_isPolynomial
    (f : C(ℝ, ℝ)) (hf : ¬ Function.IsPolynomial f) (n : ℕ) :
    iteratedLineDerivOp (fun _ : Fin n ↦ (1 : ℝ))
      (ofFun (⊤ : TopologicalSpace.Opens ℝ) f volume ⊤) ≠ 0 := by
  intro hzero
  apply hf
  exact isPolynomial_of_iteratedLineDerivOp_ofFun_eq_zero
    TestFunction.normalizedBumpReal TestFunction.integral_normalizedBumpReal
    f.continuous n hzero

end Distribution

namespace Learning.ShallowNetwork

/-- For each order, a continuous nonpolynomial activation admits a test function whose iterated
derivative has nonzero pairing with the reflected activation.

Equivalently, this is the nonzero value at the origin of the corresponding derivative of the
left convolution of the test function with `σ`. -/
theorem exists_testFunction_iteratedLineDeriv_integral_mul_reflected_ne_zero
    (σ : C(ℝ, ℝ)) (hσ : ¬ Function.IsPolynomial σ) (n : ℕ) :
    ∃ φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ),
      ∫ s : ℝ, (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n]) φ) s * σ (-s) ≠ 0 := by
  let f : C(ℝ, ℝ) := reflectedActivation σ
  let T : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ) :=
    LineDeriv.iteratedLineDerivOp (fun _ : Fin n ↦ (1 : ℝ))
      (Distribution.ofFun (⊤ : TopologicalSpace.Opens ℝ) f volume ⊤)
  have hf : ¬ Function.IsPolynomial f := by
    simpa only [f, isPolynomial_reflectedActivation_iff] using hσ
  have hT : T ≠ 0 := by
    dsimp only [T]
    exact Distribution.iteratedLineDerivOp_ofFun_ne_zero_of_not_isPolynomial f hf n
  obtain ⟨φ, hφ⟩ := T.exists_ne_zero hT
  refine ⟨φ, ?_⟩
  have hfloc : LocallyIntegrableOn f (Set.univ : Set ℝ) volume :=
    f.continuous.locallyIntegrable.locallyIntegrableOn _
  have heval : T φ = (-1 : ℝ) ^ n *
      ∫ s : ℝ, (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n]) φ) s * σ (-s) := by
    dsimp only [T]
    rw [Distribution.iteratedLineDerivOp_apply_iterated_testFunction]
    rw [Distribution.ofFun_apply hfloc]
    simp only [smul_eq_mul, f, reflectedActivation_apply]
  intro hzero
  apply hφ
  exact heval.trans (by rw [hzero, mul_zero])

end Learning.ShallowNetwork
