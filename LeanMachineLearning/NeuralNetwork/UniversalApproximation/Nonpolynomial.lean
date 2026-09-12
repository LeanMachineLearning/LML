/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Distribution.PolynomialCharacterization
public import LeanMachineLearning.ForMathlib.Analysis.Distribution.TestFunction.Normalize
public import LeanMachineLearning.NeuralNetwork.UniversalApproximation.Convolution

/-!
# Universal approximation for nonpolynomial activations

A continuous nonpolynomial function defines a regular distribution whose derivative of every
order is nonzero. Evaluating the derivative on a suitable test function gives a nonzero integral
against the reflected activation `x ↦ σ (-x)`.

For each order `n`, this constructs a smooth test-function convolution whose `n`-th derivative
at the origin is nonzero. The kernel may depend on `n`. Annihilator transfer for convolution
and the degree-by-degree smooth ridge criterion then prove that the original activation is
discriminatory and universal.

The result applies to arbitrary real inner-product spaces. Neither nontriviality nor finite
dimensionality is needed for this sufficient direction.
-/

@[expose] public section

open MeasureTheory
open scoped Distributions

namespace Learning.ShallowNetwork

/-! ## Reflection of the activation -/

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
    exact ⟨p.comp (-Polynomial.X), by simp [hp]⟩
  · rintro ⟨p, hp⟩
    exact ⟨p.comp (-Polynomial.X), by simp [hp]⟩

end Learning.ShallowNetwork

namespace Distribution

/-! ## Nonzero distributional derivatives -/

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
        (-1 : ℝ) ^ (n + 1) • T (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n + 1]) φ)
      simp [Distribution.lineDerivCLM_apply, ih, Function.iterate_succ_apply, pow_succ]

/-- Every distributional derivative of a continuous nonpolynomial function is nonzero.

The compactly-supported-primitive class is the exactness input used by the converse
characterization of polynomial regular distributions. -/
theorem iteratedLineDerivOp_ofFun_ne_zero_of_not_isPolynomial
    {f : C(ℝ, ℝ)} (hf : ¬ Function.IsPolynomial f) (n : ℕ) :
    iteratedLineDerivOp (fun _ : Fin n ↦ (1 : ℝ))
      (ofFun (⊤ : TopologicalSpace.Opens ℝ) f volume ⊤) ≠ 0 := by
  intro hzero
  apply hf
  obtain ⟨ρ, hρ⟩ := TestFunction.exists_integral_eq_one
    (Ω := (⊤ : TopologicalSpace.Opens ℝ)) volume Set.univ_nonempty
  exact isPolynomial_of_iteratedLineDerivOp_ofFun_eq_zero ρ hρ f.continuous n hzero

end Distribution

namespace Learning.ShallowNetwork

/-! ## Test-function and convolution witnesses -/

/-- For each order, a continuous nonpolynomial activation admits a test function whose iterated
derivative has nonzero pairing with the reflected activation.

Equivalently, this is the nonzero value at the origin of the corresponding derivative of the
left convolution of the test function with `σ`. -/
theorem exists_testFunction_iteratedLineDeriv_integral_mul_reflected_ne_zero
    {σ : C(ℝ, ℝ)} (hσ : ¬ Function.IsPolynomial σ) (n : ℕ) :
    ∃ φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ),
      ∫ s : ℝ, (((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n]) φ) s * σ (-s) ≠ 0 := by
  let f : C(ℝ, ℝ) := reflectedActivation σ
  let T : 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ) :=
    LineDeriv.iteratedLineDerivOp (fun _ : Fin n ↦ (1 : ℝ))
      (Distribution.ofFun (⊤ : TopologicalSpace.Opens ℝ) f volume ⊤)
  have hf : ¬ Function.IsPolynomial f := by
    simpa [f, isPolynomial_reflectedActivation_iff] using hσ
  have hT : T ≠ 0 := Distribution.iteratedLineDerivOp_ofFun_ne_zero_of_not_isPolynomial hf n
  obtain ⟨φ, hφ⟩ := T.exists_ne_zero hT
  refine ⟨φ, ?_⟩
  have hfloc : LocallyIntegrableOn f ⊤ volume :=
    f.continuous.locallyIntegrable.locallyIntegrableOn _
  have heval : T φ = (-1 : ℝ) ^ n *
      ∫ s : ℝ, ((TestFunction.lineDerivCLM ℝ (1 : ℝ))^[n]) φ s * σ (-s) := by
    rw [Distribution.iteratedLineDerivOp_apply_iterated_testFunction,
      Distribution.ofFun_apply hfloc]
    simp [smul_eq_mul, f, reflectedActivation_apply]
  intro hzero
  apply hφ
  exact heval.trans (by rw [hzero, mul_zero])

/-- For every order, a nonpolynomial continuous activation has a test-function convolution whose
derivative is nonzero at the origin in that order. -/
theorem exists_testFunction_iteratedDeriv_convolutionActivation_ne_zero
    {σ : C(ℝ, ℝ)} (hσ : ¬ Function.IsPolynomial σ) (n : ℕ) :
    ∃ φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ),
      iteratedDeriv n (convolutionActivation φ σ) 0 ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_testFunction_iteratedLineDeriv_integral_mul_reflected_ne_zero hσ n
  exact ⟨φ, by rwa [iteratedDeriv_convolutionActivation_testFunction_apply_zero]⟩

/-! ## Universality of nonpolynomial activations -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every continuous nonpolynomial activation is discriminatory on compact subsets of an arbitrary
real inner-product space. -/
theorem isDiscriminatory_of_not_isPolynomial {σ : C(ℝ, ℝ)}
    (hσ : ¬ Function.IsPolynomial σ) : IsDiscriminatory E σ := by
  apply isDiscriminatory_of_smooth_ridges
  intro n
  obtain ⟨φ, hφ⟩ := exists_testFunction_iteratedDeriv_convolutionActivation_ne_zero hσ n
  refine ⟨convolutionActivation φ σ, 0, convolutionActivation_contDiff φ σ φ.contDiff, hφ, ?_⟩
  intro K hK Λ hΛ
  exact annihilates_convolutionActivation_neurons φ hK hΛ

/-- Every continuous nonpolynomial activation is universal on compact subsets of a real
inner-product space. -/
theorem isUniversal_of_not_isPolynomial
    {σ : C(ℝ, ℝ)} (hσ : ¬ Function.IsPolynomial σ) : IsUniversal E σ :=
  (isUniversal_iff_isDiscriminatory σ).2 (isDiscriminatory_of_not_isPolynomial hσ)

end Learning.ShallowNetwork
