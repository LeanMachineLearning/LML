/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import LeanMachineLearning.NeuralNetwork.UniversalApproximation.Convolution
public import LeanMachineLearning.NeuralNetwork.UniversalApproximation.NonpolynomialWitness
public import LeanMachineLearning.NeuralNetwork.UniversalApproximation.SmoothActivation

/-!
# Derivative towers for convolution-smoothed activations

Convolving a continuous real activation with a smooth compactly supported test function produces
a smooth activation.  More precisely, its `n`-th derivative is the convolution whose kernel is
obtained by applying `TestFunction.lineDerivCLM` `n` times.

The resulting derivative tower is registered as an instance of
`HasContinuousDerivativeTower`.  The last theorem combines its value at the origin with the
distributional witness for a nonpolynomial activation.
-/

@[expose] public section

open MeasureTheory
open scoped Distributions

namespace Learning.ShallowNetwork

/-- Successive derivatives of the left kernel give successive derivatives of its convolution
with a continuous activation. -/
theorem hasDerivAt_convolutionActivation_iterate_lineDerivCLM
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) (σ : C(ℝ, ℝ)) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (convolutionActivation
        (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n]) φ) σ)
      (convolutionActivation
        (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n + 1]) φ) σ x) x := by
  let _ : (volume : Measure ℝ).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular volume
  have h :=
    (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n]) φ).hasCompactSupport
      |>.hasDerivAt_convolution_left
        (μ := volume) (ContinuousLinearMap.mul ℝ ℝ)
        ((TestFunction.contDiff
          (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n]) φ)).of_le (by simp))
        σ.continuous.locallyIntegrable x
  convert h using 1
  · rfl
  · rw [Function.iterate_succ_apply']
    congr 1

/-- The canonical continuous derivative tower on the convolution of a test function with a
continuous activation. -/
noncomputable instance instHasContinuousDerivativeTowerConvolutionActivation
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) (σ : C(ℝ, ℝ)) :
    HasContinuousDerivativeTower (convolutionActivation φ σ) where
  derivative n :=
    convolutionActivation (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n]) φ) σ
  derivative_zero := by simp
  hasDerivAt_derivative :=
    hasDerivAt_convolutionActivation_iterate_lineDerivCLM φ σ

/-- The `n`-th member of the canonical derivative tower is convolution with the `n`-fold
derivative of the test-function kernel. -/
@[simp]
theorem derivative_convolutionActivation_testFunction
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) (σ : C(ℝ, ℝ)) (n : ℕ) :
    HasContinuousDerivativeTower.derivative (convolutionActivation φ σ) n =
      convolutionActivation (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n]) φ) σ :=
  rfl

/-- At the origin, the `n`-th derivative of a test-function convolution is the pairing of the
`n`-fold derivative of its kernel with the reflected activation. -/
theorem derivative_convolutionActivation_testFunction_apply_zero
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) (σ : C(ℝ, ℝ)) (n : ℕ) :
    HasContinuousDerivativeTower.derivative (convolutionActivation φ σ) n 0 =
      ∫ s : ℝ, (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n]) φ) s * σ (-s) := by
  rw [derivative_convolutionActivation_testFunction, convolutionActivation_apply]
  simp only [zero_sub]

/-- For every order, a nonpolynomial continuous activation has a test-function convolution whose
canonical derivative tower is nonzero at the origin in that order. -/
theorem exists_testFunction_derivative_convolutionActivation_ne_zero
    (σ : C(ℝ, ℝ)) (hσ : ¬ Function.IsPolynomial σ) (n : ℕ) :
    ∃ φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ),
      HasContinuousDerivativeTower.derivative (convolutionActivation φ σ) n 0 ≠ 0 := by
  obtain ⟨φ, hφ⟩ :=
    exists_testFunction_iteratedLineDeriv_integral_mul_reflected_ne_zero σ hσ n
  refine ⟨φ, ?_⟩
  rw [derivative_convolutionActivation_testFunction_apply_zero]
  exact hφ

end Learning.ShallowNetwork
