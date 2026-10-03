/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import LeanMachineLearning.ForMathlib.Analysis.Distribution.TestFunction
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ClosedSubmodule
public import LeanMachineLearning.NeuralNetwork.UniversalApproximation.Discriminatory

/-!
# Convolution smoothing of activation functions

Convolution against a compactly supported continuous kernel turns an activation into another
continuous activation. On a compact domain, a ridge function for the convolved activation is a
Bochner integral of ridge functions for the original activation. Consequently it belongs to the
closure of their span, and every functional annihilating the original neurons also annihilates the
convolved neurons.

The kernel is abstracted by `CompactlySupportedContinuousMapClass`, so the closure and annihilator
results apply both to compactly supported continuous maps and to smooth test functions.

For a smooth test-function kernel, successive derivatives of the kernel give successive
derivatives of the convolution. The resulting `iteratedDeriv` formula also identifies their
values at the origin.
-/

@[expose] public section

open MeasureTheory
open scoped Distributions

namespace Learning.ShallowNetwork

/-! ## Compactly supported convolution kernels -/

/-- Convolution of a continuous activation with a compactly supported continuous kernel.

The convention is
`convolutionActivation φ σ t = ∫ s, φ s * σ (t - s)`. -/
noncomputable def convolutionActivation {B : Type*} [FunLike B ℝ ℝ]
    [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) (σ : C(ℝ, ℝ)) : C(ℝ, ℝ) :=
  ⟨MeasureTheory.convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume,
    (CompactlySupportedContinuousMapClass.hasCompactSupport φ).continuous_convolution_left
      _ (ContinuousMapClass.map_continuous φ) σ.continuous.locallyIntegrable⟩

@[simp]
theorem convolutionActivation_apply {B : Type*} [FunLike B ℝ ℝ]
    [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) (σ : C(ℝ, ℝ)) (t : ℝ) :
    convolutionActivation φ σ t = ∫ s, φ s * σ (t - s) := MeasureTheory.convolution_mul

/-- Convolution with a compactly supported `C^n` kernel makes a continuous activation `C^n`. -/
theorem convolutionActivation_contDiff {B : Type*} [FunLike B ℝ ℝ]
    [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) (σ : C(ℝ, ℝ)) {n : ℕ∞} (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (convolutionActivation φ σ) :=
  (CompactlySupportedContinuousMapClass.hasCompactSupport φ).contDiff_convolution_left
    _ hφ σ.continuous.locallyIntegrable

/-! ## Network spaces and annihilator transfer -/

/-- The activation `σ` applied to a scalar-valued continuous feature `u`, with bias `b`. -/
def activationAlong {X : Type*} [TopologicalSpace X] (σ : C(ℝ, ℝ))
    (u : C(X, ℝ)) (b : ℝ) : C(X, ℝ) :=
  σ.comp (u + ContinuousMap.const X b)

@[simp]
theorem activationAlong_apply {X : Type*} [TopologicalSpace X]
    (σ : C(ℝ, ℝ)) (u : C(X, ℝ)) (b : ℝ) (x : X) :
    activationAlong σ u b x = σ (u x + b) := rfl

/-- The `C(X, ℝ)`-valued integrand expressing a ridge function of a convolved activation is
Bochner integrable. -/
theorem integrable_smul_activationAlong_sub
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {B : Type*} [FunLike B ℝ ℝ] [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) (σ : C(ℝ, ℝ)) (u : C(X, ℝ)) (b : ℝ) :
    Integrable (fun s : ℝ => φ s • activationAlong σ u (b - s)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (ContinuousMapClass.map_continuous φ).smul
      (ContinuousMap.continuous_of_continuous_uncurry _ <|
        (σ.continuous.comp
          ((u.continuous.comp continuous_snd).add (continuous_const.sub continuous_fst))))
  · exact (CompactlySupportedContinuousMapClass.hasCompactSupport φ).smul_right

/-- A ridge function of a convolved activation is the Bochner integral of shifted ridge functions
of the original activation. -/
theorem activationAlong_convolutionActivation
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {B : Type*} [FunLike B ℝ ℝ] [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) (σ : C(ℝ, ℝ)) (u : C(X, ℝ)) (b : ℝ) :
    activationAlong (convolutionActivation φ σ) u b =
      ∫ s : ℝ, φ s • activationAlong σ u (b - s) := by
  apply ContinuousMap.ext
  intro x
  rw [ContinuousMap.integral_apply (integrable_smul_activationAlong_sub φ σ u b)]
  simp only [activationAlong_apply, convolutionActivation_apply]
  congr 1
  funext s
  simp [sub_eq_add_neg, add_assoc]

/-- A continuous functional annihilating all translates of a ridge function also annihilates the
corresponding ridge function for every compactly supported convolution smoothing. -/
theorem annihilates_convolutionActivation
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {B : Type*} [FunLike B ℝ ℝ] [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) {σ : C(ℝ, ℝ)} {u : C(X, ℝ)} {Λ : StrongDual ℝ C(X, ℝ)} {b : ℝ}
    (hΛ : ∀ b, Λ (activationAlong σ u b) = 0) :
    Λ (activationAlong (convolutionActivation φ σ) u b) = 0 := by
  rw [activationAlong_convolutionActivation,
    ← Λ.integral_comp_comm (integrable_smul_activationAlong_sub φ σ u b)]
  simp [hΛ]

/-- A continuous functional annihilating all neurons for `σ` also annihilates all neurons for a
compactly supported convolution smoothing of `σ`. -/
theorem annihilates_convolutionActivation_neurons
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : Type*} [FunLike B ℝ ℝ] [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) {σ : C(ℝ, ℝ)} {K : Set E} {Λ : StrongDual ℝ C(K, ℝ)}
    (hK : IsCompact K) (hΛ : ∀ w b, Λ ((neuron σ w b).restrict K) = 0) :
    ∀ w b, Λ ((neuron (convolutionActivation φ σ) w b).restrict K) = 0 := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  intro w b
  let u : C(K, ℝ) :=
    ⟨fun x ↦ inner ℝ w (x : E), continuous_const.inner continuous_subtype_val⟩
  have htrans : ∀ c, Λ (activationAlong σ u c) = 0 := by
    intro c
    rw [show activationAlong σ u c = (neuron σ w c).restrict K by rfl]
    exact hΛ w c
  rw [show (neuron (convolutionActivation φ σ) w b).restrict K =
      activationAlong (convolutionActivation φ σ) u b by rfl]
  exact annihilates_convolutionActivation φ htrans

/-! ## Iterated derivatives for smooth kernels -/

/-- Successive derivatives of the left kernel give successive derivatives of its convolution
with a continuous activation. -/
theorem hasDerivAt_convolutionActivation_iterate_lineDerivCLM
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) (σ : C(ℝ, ℝ)) (n : ℕ) (x : ℝ) :
    HasDerivAt (convolutionActivation (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n]) φ) σ)
      (convolutionActivation (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n + 1]) φ) σ x) x := by
  have h := (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n]) φ).hasCompactSupport
    |>.hasDerivAt_convolution_left (μ := volume) (ContinuousLinearMap.mul ℝ ℝ)
      ((TestFunction.contDiff (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n]) φ)).of_le (by simp))
      σ.continuous.locallyIntegrable x
  convert h using 1
  · rfl
  · rw [Function.iterate_succ_apply']
    congr 1

/-- The `n`-th derivative of a test-function convolution is the convolution with the
`n`-fold derivative of its kernel. -/
@[simp]
theorem iteratedDeriv_convolutionActivation_testFunction
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) (σ : C(ℝ, ℝ)) (n : ℕ) :
    iteratedDeriv n (convolutionActivation φ σ) =
      convolutionActivation (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n]) φ) σ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (hasDerivAt_convolutionActivation_iterate_lineDerivCLM φ σ n x).deriv

end Learning.ShallowNetwork
