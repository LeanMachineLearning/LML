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
continuous activation.  On a compact domain, a ridge function for the convolved activation is a
Bochner integral of ridge functions for the original activation.  Consequently it belongs to the
closure of their span, and every functional annihilating the original neurons also annihilates the
convolved neurons.

The kernel is abstracted by `CompactlySupportedContinuousMapClass`, so this file applies directly
both to compactly supported continuous maps and to smooth test functions.
-/

@[expose] public section

open MeasureTheory

namespace Learning.ShallowNetwork

/-- Convolution of a continuous activation with a compactly supported continuous kernel.

The convention is
`convolutionActivation φ σ t = ∫ s, φ s * σ (t - s)`. -/
noncomputable def convolutionActivation {B : Type*} [FunLike B ℝ ℝ]
    [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) (σ : C(ℝ, ℝ)) : C(ℝ, ℝ) := by
  letI : (volume : Measure ℝ).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular volume
  exact
    ⟨MeasureTheory.convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume,
      (CompactlySupportedContinuousMapClass.hasCompactSupport φ).continuous_convolution_left
        (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousMapClass.map_continuous φ) σ.continuous.locallyIntegrable⟩

@[simp]
theorem convolutionActivation_apply {B : Type*} [FunLike B ℝ ℝ]
    [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) (σ : C(ℝ, ℝ)) (t : ℝ) :
    convolutionActivation φ σ t = ∫ s, φ s * σ (t - s) := by
  exact MeasureTheory.convolution_mul

/-- Convolution with a compactly supported `C^n` kernel makes a continuous activation `C^n`. -/
theorem convolutionActivation_contDiff {B : Type*} [FunLike B ℝ ℝ]
    [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) (σ : C(ℝ, ℝ)) {n : ℕ∞} (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (convolutionActivation φ σ) := by
  let _ : (volume : Measure ℝ).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular volume
  exact (CompactlySupportedContinuousMapClass.hasCompactSupport φ).contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℝ) hφ σ.continuous.locallyIntegrable

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
        σ.continuous.comp
          ((u.continuous.comp continuous_snd).add
            (continuous_const.sub continuous_fst)))
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
  change φ s * σ (u x + b - s) = φ s * σ (u x + (b - s))
  simp only [sub_eq_add_neg, add_assoc]

/-- A ridge function of a convolved activation belongs to the closure of any submodule containing
all bias translates of the corresponding ridge function for the original activation. -/
theorem activationAlong_convolutionActivation_mem_topologicalClosure
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {B : Type*} [FunLike B ℝ ℝ] [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) (σ : C(ℝ, ℝ)) (u : C(X, ℝ)) (b : ℝ)
    (S : Submodule ℝ C(X, ℝ)) (hS : ∀ c, activationAlong σ u c ∈ S) :
    activationAlong (convolutionActivation φ σ) u b ∈ S.topologicalClosure := by
  rw [activationAlong_convolutionActivation]
  apply S.integral_mem_topologicalClosure
  filter_upwards with s
  exact S.smul_mem (φ s) (hS (b - s))

/-- Every neuron for a convolved activation lies in the closure of the shallow-network space for
the original activation. -/
theorem convolved_neuron_mem_spaceOn_topologicalClosure
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : Type*} [FunLike B ℝ ℝ] [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) (σ : C(ℝ, ℝ)) (K : Set E) (hK : IsCompact K) (w : E) (b : ℝ) :
    (neuron (convolutionActivation φ σ) w b).restrict K ∈
      (spaceOn σ K).topologicalClosure := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let u : C(K, ℝ) :=
    ⟨fun x => inner ℝ w (x : E), continuous_const.inner continuous_subtype_val⟩
  rw [show (neuron (convolutionActivation φ σ) w b).restrict K =
      activationAlong (convolutionActivation φ σ) u b by ext; rfl]
  apply activationAlong_convolutionActivation_mem_topologicalClosure φ σ u b
  intro c
  rw [show activationAlong σ u c = (neuron σ w c).restrict K by ext; rfl]
  exact Submodule.subset_span ⟨(w, c), rfl⟩

/-- On every compact set, the network space of a convolved activation is contained in the closure
of the network space of the original activation. -/
theorem convolved_spaceOn_le_topologicalClosure
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : Type*} [FunLike B ℝ ℝ] [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) (σ : C(ℝ, ℝ)) (K : Set E) (hK : IsCompact K) :
    spaceOn (convolutionActivation φ σ) K ≤ (spaceOn σ K).topologicalClosure := by
  rw [spaceOn]
  apply Submodule.span_le.2
  rintro f ⟨p, rfl⟩
  exact convolved_neuron_mem_spaceOn_topologicalClosure φ σ K hK p.1 p.2

/-- A continuous functional annihilating all translates of a ridge function also annihilates the
corresponding ridge function for every compactly supported convolution smoothing. -/
theorem annihilates_convolutionActivation
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {B : Type*} [FunLike B ℝ ℝ] [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) (σ : C(ℝ, ℝ)) (u : C(X, ℝ)) (Λ : StrongDual ℝ C(X, ℝ))
    (hΛ : ∀ b, Λ (activationAlong σ u b) = 0) (b : ℝ) :
    Λ (activationAlong (convolutionActivation φ σ) u b) = 0 := by
  rw [activationAlong_convolutionActivation,
    ← Λ.integral_comp_comm (integrable_smul_activationAlong_sub φ σ u b)]
  simp [hΛ]

/-- A continuous functional annihilating all neurons for `σ` also annihilates all neurons for a
compactly supported convolution smoothing of `σ`. -/
theorem annihilates_convolutionActivation_neurons
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : Type*} [FunLike B ℝ ℝ] [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) (σ : C(ℝ, ℝ)) (K : Set E) (hK : IsCompact K)
    (Λ : StrongDual ℝ C(K, ℝ))
    (hΛ : ∀ w b, Λ ((neuron σ w b).restrict K) = 0) :
    ∀ w b, Λ ((neuron (convolutionActivation φ σ) w b).restrict K) = 0 := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  intro w b
  let u : C(K, ℝ) :=
    ⟨fun x => inner ℝ w (x : E), continuous_const.inner continuous_subtype_val⟩
  have htrans : ∀ c, Λ (activationAlong σ u c) = 0 := by
    intro c
    rw [show activationAlong σ u c = (neuron σ w c).restrict K by ext; rfl]
    exact hΛ w c
  rw [show (neuron (convolutionActivation φ σ) w b).restrict K =
      activationAlong (convolutionActivation φ σ) u b by ext; rfl]
  exact annihilates_convolutionActivation φ σ u Λ htrans b

/-- If one convolution smoothing of `σ` is discriminatory, then `σ` itself is discriminatory. -/
theorem isDiscriminatory_of_convolutionActivation
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : Type*} [FunLike B ℝ ℝ] [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) (σ : C(ℝ, ℝ))
    [IsDiscriminatory (E := E) (convolutionActivation φ σ)] :
    IsDiscriminatory (E := E) σ := by
  constructor
  intro K hK Λ hΛ
  apply IsDiscriminatory.annihilator_eq_zero
    (σ := convolutionActivation φ σ) (E := E) K hK Λ
  exact annihilates_convolutionActivation_neurons φ σ K hK Λ hΛ

/-- Universality of one compactly supported convolution smoothing implies universality of the
original activation. -/
theorem isUniversal_of_convolutionActivation
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : Type*} [FunLike B ℝ ℝ] [CompactlySupportedContinuousMapClass B ℝ ℝ]
    (φ : B) (σ : C(ℝ, ℝ))
    [IsUniversal (E := E) (convolutionActivation φ σ)] :
    IsUniversal (E := E) σ := by
  apply (isUniversal_iff_isDiscriminatory σ).mpr
  let _ : IsDiscriminatory (E := E) (convolutionActivation φ σ) :=
    (isUniversal_iff_isDiscriminatory (convolutionActivation φ σ)).mp
    (inferInstance : IsUniversal (E := E) (convolutionActivation φ σ))
  exact isDiscriminatory_of_convolutionActivation φ σ

end Learning.ShallowNetwork
