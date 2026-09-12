/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Polynomial
public import LeanMachineLearning.ForMathlib.Algebra.Polynomial.Function

/-!
# Regular distributions induced by polynomials

This file proves that distributional differentiation agrees with classical differentiation for
regular distributions on the real line. The result is first established for functions with a
classical derivative and then iterated for arbitrary derivative towers. Polynomials are obtained as
a special case.

The converse statement, that a distribution whose sufficiently high derivative vanishes is a
regular polynomial distribution, needs an additional exactness result for the derivative on the
space of test functions. In particular, one needs that every compactly supported smooth function
with integral zero has a compactly supported smooth primitive. That result is not currently
available in Mathlib.
-/

@[expose] public section

open MeasureTheory
open scoped Distributions

namespace Polynomial

/-- Over a field of characteristic zero, formal differentiation of univariate polynomials is
surjective.

This is the algebraic input for recovering a polynomial from its derivative. The construction
divides the coefficient of `X ^ n` by `n + 1`. -/
theorem derivative_surjective_of_charZero {K : Type*} [Field K] [CharZero K] :
    Function.Surjective (derivative : Polynomial K → Polynomial K) := by
  intro p
  refine ⟨p.sum fun n a ↦ C (a / (n + 1 : ℕ)) * X ^ (n + 1), ?_⟩
  rw [sum_def, derivative_sum]
  simp only [derivative_C_mul_X_pow, Nat.add_sub_cancel]
  calc
    (∑ n ∈ p.support, C (p.coeff n / (n + 1 : ℕ) * (n + 1 : ℕ)) * X ^ n) =
        ∑ n ∈ p.support, C (p.coeff n) * X ^ n := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 2
      rw [div_mul_cancel₀]
      exact_mod_cast Nat.succ_ne_zero n
    _ = p := p.as_sum_support_C_mul_X_pow.symm

end Polynomial

namespace MeasureTheory

/-- The integral of an integrable continuous function over `Set.Iic y`, regarded as a function of
the upper endpoint `y`, has derivative equal to the integrand.

This vector-valued version is obtained by comparing two lower-ray integrals and applying the
fundamental theorem of calculus to the resulting interval integral. -/
theorem hasDerivAt_integral_Iic
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℝ → F} (hf : Continuous f) (hfi : Integrable f) (b : ℝ) :
    HasDerivAt (fun y ↦ ∫ x in Set.Iic y, f x) (f b) b := by
  have hEq : (fun y ↦ ∫ x in Set.Iic y, f x) =
      fun y ↦ (∫ x in b..y, f x) + ∫ x in Set.Iic b, f x := by
    funext y
    exact sub_eq_iff_eq_add.mp <| intervalIntegral.integral_Iic_sub_Iic
      (hfi.integrableOn : IntegrableOn f (Set.Iic b))
      (hfi.integrableOn : IntegrableOn f (Set.Iic y))
  rw [hEq]
  exact (hf.integral_hasStrictDerivAt b b).hasDerivAt.add_const _

/-- If a compactly supported integrable function on the real line has integral zero, then its
indefinite integral over lower rays is compactly supported.

This statement is independent of differentiability and works for functions with values in any
complete real normed space. -/
theorem hasCompactSupport_integral_Iic_of_integral_eq_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hfc : HasCompactSupport f) (hfi : Integrable f)
    (hzero : ∫ x, f x = 0) :
    HasCompactSupport (fun b ↦ ∫ x in Set.Iic b, f x) := by
  obtain ⟨R, hR, hout⟩ := hfc.exists_pos_le_norm
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-R) R))
  intro x hx
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    change y ≤ x at hy
    apply hout y
    rw [Real.norm_eq_abs, abs_of_nonpos]
    · linarith
    · linarith
  · have hIoi : ∫ y in Set.Ioi x, f y = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro y hy
      change x < y at hy
      apply hout y
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · linarith
      · linarith
    have hsplit := intervalIntegral.integral_Iic_add_Ioi
      (hfi.integrableOn : IntegrableOn f (Set.Iic x))
      (hfi.integrableOn : IntegrableOn f (Set.Ioi x))
    rw [hIoi, hzero, add_zero] at hsplit
    exact hsplit

/-- Every smooth compactly supported function on the real line with integral zero has a smooth
compactly supported primitive.

The codomain is allowed to be any complete real normed space. This is the vector-valued analytic
core of exactness of differentiation and integration on real test functions. -/
theorem exists_contDiff_primitive_hasCompactSupport
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℝ → F} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (hzero : ∫ x, f x = 0) :
    ∃ g : ℝ → F, ContDiff ℝ (↑(⊤ : ℕ∞)) g ∧ HasCompactSupport g ∧
      ∀ x, HasDerivAt g (f x) x := by
  have hfcont : Continuous f := hf.continuous
  have hfi : Integrable f := hfcont.integrable_of_hasCompactSupport hfc
  let g : ℝ → F := fun b ↦ ∫ x in Set.Iic b, f x
  have hgDeriv (x : ℝ) : HasDerivAt g (f x) x :=
    hasDerivAt_integral_Iic hfcont hfi x
  have hgDiff : Differentiable ℝ g := fun x ↦ (hgDeriv x).differentiableAt
  have hgderiv : deriv g = f := by
    funext x
    exact (hgDeriv x).deriv
  have hgSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) g := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨hgDiff, hgderiv ▸ hf⟩
  have hgCompact : HasCompactSupport g :=
    hasCompactSupport_integral_Iic_of_integral_eq_zero hfc hfi hzero
  exact ⟨g, hgSmooth, hgCompact, hgDeriv⟩

end MeasureTheory

namespace LinearMap

/-- A linear map annihilating the first map in an exact pair is determined by its value on any
element sent to `1` by the second map.

This is the algebraic factorization argument underlying the fact that a distribution with zero
derivative is constant. -/
theorem apply_eq_smul_apply_of_exact {R X Y : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (D : X →ₗ[R] X) (I : X →ₗ[R] R) (T : X →ₗ[R] Y)
    (hExact : Function.Exact D I) {ρ : X} (hρ : I ρ = 1)
    (hTD : ∀ x, T (D x) = 0) (x : X) :
    T x = I x • T ρ := by
  let ψ := x - I x • ρ
  have hIψ : I ψ = 0 := by simp [ψ, hρ]
  obtain ⟨θ, hθ⟩ := (hExact ψ).mp hIψ
  have hTψ : T ψ = 0 := by
    rw [← hθ]
    exact hTD θ
  calc
    T x = T (ψ + I x • ρ) := by simp [ψ]
    _ = I x • T ρ := by simp [hTψ]

end LinearMap

namespace TestFunction

/-- On real-valued test functions on the real line, the directional derivative in direction `1`
is the usual one-dimensional derivative. -/
lemma lineDerivCLM_one_apply {Ω : TopologicalSpace.Opens ℝ} (φ : 𝓓(Ω, ℝ)) (x : ℝ) :
    (lineDerivCLM ℝ (1 : ℝ) φ : 𝓓(Ω, ℝ)) x = deriv φ x := by
  rw [lineDerivCLM_apply_of_le]
  · calc
      lineDeriv ℝ (φ : ℝ → ℝ) x 1 = (fderiv ℝ (φ : ℝ → ℝ) x) 1 :=
        (φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv
      _ = deriv (φ : ℝ → ℝ) x := fderiv_apply_one_eq_deriv
  · simp

/-- The analytic exactness property needed to recognize constant distributions on an open subset
of the real line: every test function of integral zero is the derivative of another test
function.

This is a class so downstream distribution theory can be stated independently of the particular
construction of compactly supported primitives. -/
class HasCompactSupportPrimitive (Ω : TopologicalSpace.Opens ℝ) : Prop where
  exists_eq_lineDerivCLM (φ : 𝓓(Ω, ℝ)) (hφ : ∫ x, φ x = 0) :
    ∃ ψ : 𝓓(Ω, ℝ), lineDerivCLM ℝ (1 : ℝ) ψ = φ

/-- On the whole real line, smooth compactly supported primitives exist. -/
instance instHasCompactSupportPrimitiveTop :
    HasCompactSupportPrimitive (⊤ : TopologicalSpace.Opens ℝ) where
  exists_eq_lineDerivCLM φ hφ := by
    obtain ⟨g, hgSmooth, hgCompact, hgDeriv⟩ :=
      MeasureTheory.exists_contDiff_primitive_hasCompactSupport
        φ.contDiff φ.hasCompactSupport hφ
    let ψ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ) :=
      ⟨g, hgSmooth, hgCompact, by simp⟩
    refine ⟨ψ, ?_⟩
    ext x
    rw [lineDerivCLM_one_apply]
    simpa [ψ] using (hgDeriv x).deriv

end TestFunction

namespace Distribution

open LineDeriv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The distributional derivative of the regular distribution induced by `f` is the regular
distribution induced by the classical derivative of `f`.

This vector-valued version only assumes the local integrability needed to define the two regular
distributions. -/
theorem lineDerivCLM_ofFun_eq_of_hasDerivAt {Ω : TopologicalSpace.Opens ℝ}
    {f f' : ℝ → F} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfloc : LocallyIntegrableOn f Ω volume)
    (hf'loc : LocallyIntegrableOn f' Ω volume) :
    lineDerivCLM (1 : ℝ) (ofFun Ω f volume ⊤) = ofFun Ω f' volume ⊤ := by
  ext φ
  rw [lineDerivCLM_apply, ofFun_apply hfloc, ofFun_apply hf'loc]
  let dφ : 𝓓(Ω, ℝ) := TestFunction.lineDerivCLM ℝ (1 : ℝ) φ
  have hdφ (x : ℝ) : dφ x = deriv (φ : ℝ → ℝ) x :=
    TestFunction.lineDerivCLM_one_apply φ x
  have hibp := MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (u := (φ : ℝ → ℝ)) (v := f)
    (u' := fun x => deriv (φ : ℝ → ℝ) x) (v' := f')
    (fun _ _ => (φ.contDiff.differentiable (by simp)).differentiableAt.hasDerivAt)
    (fun x _ => hf x)
    (φ.integrable_smul hf'loc)
    (by simpa only [hdφ, ContinuousLinearMap.lsmul_apply] using dφ.integrable_smul hfloc)
    (φ.integrable_smul hfloc)
  simp only [ContinuousLinearMap.lsmul_apply] at hibp
  rw [show (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ : 𝓓(Ω, ℝ)) = dφ from rfl]
  simp_rw [hdφ]
  exact hibp.symm

/-- The distributional derivative of a regular constant distribution vanishes. -/
theorem lineDerivCLM_ofFun_const_eq_zero {Ω : TopologicalSpace.Opens ℝ} (c : F) :
    (lineDerivCLM (1 : ℝ) (ofFun Ω (fun _ : ℝ => c) volume ⊤) : 𝓓'(Ω, F)) = 0 := by
  have hc : LocallyIntegrableOn (fun _ : ℝ => c) Ω volume :=
    (continuous_const : Continuous (fun _ : ℝ => c)).locallyIntegrable.locallyIntegrableOn Ω
  rw [lineDerivCLM_ofFun_eq_of_hasDerivAt
    (fun x => hasDerivAt_const x c) hc locallyIntegrableOn_zero]
  exact ofFun_zero

/-- Integration annihilates derivatives of test functions. This is the easy half of the
derivative--integral exactness statement. -/
theorem ofFun_one_comp_testFunction_lineDerivCLM_eq_zero
    {Ω : TopologicalSpace.Opens ℝ} :
    (ofFun Ω (fun _ : ℝ => (1 : ℝ)) volume ⊤) ∘
      (TestFunction.lineDerivCLM ℝ (1 : ℝ) : 𝓓(Ω, ℝ) → 𝓓(Ω, ℝ)) = 0 := by
  funext φ
  have h := congrArg (fun T : 𝓓'(Ω, ℝ) => T φ)
    (lineDerivCLM_ofFun_const_eq_zero (Ω := Ω) (1 : ℝ))
  rw [lineDerivCLM_apply] at h
  exact neg_eq_zero.mp h

/-- Compactly supported primitives identify the range of differentiation with the kernel of
integration on test functions. -/
theorem exact_testFunction_lineDerivCLM_of_hasCompactSupportPrimitive
    {Ω : TopologicalSpace.Opens ℝ} [TestFunction.HasCompactSupportPrimitive Ω] :
    Function.Exact
      (TestFunction.lineDerivCLM ℝ (1 : ℝ) : 𝓓(Ω, ℝ) → 𝓓(Ω, ℝ))
      (ofFun Ω (fun _ : ℝ => (1 : ℝ)) volume ⊤) := by
  apply Function.Exact.of_comp_of_mem_range
    ofFun_one_comp_testFunction_lineDerivCLM_eq_zero
  intro φ hφ
  have hOneLoc : LocallyIntegrableOn (fun _ : ℝ => (1 : ℝ)) Ω volume :=
    (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).locallyIntegrable
      |>.locallyIntegrableOn Ω
  have hIntegral : ∫ x, φ x = 0 := by
    rw [ofFun_apply hOneLoc] at hφ
    simpa using hφ
  exact TestFunction.HasCompactSupportPrimitive.exists_eq_lineDerivCLM φ hIntegral

/-- A distribution with zero derivative is a regular constant distribution, provided the
derivative--integral pair on test functions is exact and a normalized test function is given.

The exactness hypothesis precisely isolates the missing analytic input: every test function with
integral zero must have a compactly supported smooth primitive. -/
theorem eq_ofFun_const_of_lineDerivCLM_eq_zero [CompleteSpace F]
    {Ω : TopologicalSpace.Opens ℝ} (ρ : 𝓓(Ω, ℝ))
    (hρ : ofFun Ω (fun _ : ℝ => (1 : ℝ)) volume ⊤ ρ = 1)
    (hExact : Function.Exact
      (TestFunction.lineDerivCLM ℝ (1 : ℝ) : 𝓓(Ω, ℝ) → 𝓓(Ω, ℝ))
      (ofFun Ω (fun _ : ℝ => (1 : ℝ)) volume ⊤))
    (T : 𝓓'(Ω, F)) (hT : (lineDerivCLM (1 : ℝ) T : 𝓓'(Ω, F)) = 0) :
    T = ofFun Ω (fun _ => T ρ) volume ⊤ := by
  have hOneLoc : LocallyIntegrableOn (fun _ : ℝ => (1 : ℝ)) Ω volume :=
    (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).locallyIntegrable
      |>.locallyIntegrableOn Ω
  have hConstLoc : LocallyIntegrableOn (fun _ : ℝ => T ρ) Ω volume :=
    (continuous_const : Continuous (fun _ : ℝ => T ρ)).locallyIntegrable
      |>.locallyIntegrableOn Ω
  have hTD (φ : 𝓓(Ω, ℝ)) :
      T (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ) = 0 := by
    have h := congrArg (fun S : 𝓓'(Ω, F) => S φ) hT
    rw [lineDerivCLM_apply] at h
    exact neg_eq_zero.mp h
  ext φ
  rw [ofFun_apply hConstLoc]
  calc
    T φ = (ofFun Ω (fun _ : ℝ => (1 : ℝ)) volume ⊤) φ • T ρ :=
      LinearMap.apply_eq_smul_apply_of_exact
        (TestFunction.lineDerivCLM ℝ (1 : ℝ)).toLinearMap
        (ofFun Ω (fun _ : ℝ => (1 : ℝ)) volume ⊤).toLinearMap
        T.toLinearMap hExact hρ hTD φ
    _ = (∫ x, φ x) • T ρ := by
      rw [ofFun_apply hOneLoc]
      congr 1
      simp
    _ = ∫ x, φ x • T ρ := (integral_smul_const (φ : ℝ → ℝ) (T ρ)).symm

/-- A distribution with zero derivative is constant whenever compactly supported primitives exist.
The test function `ρ` fixes the normalization of the resulting constant. -/
theorem eq_ofFun_const_of_lineDerivCLM_eq_zero_of_hasCompactSupportPrimitive [CompleteSpace F]
    {Ω : TopologicalSpace.Opens ℝ} [TestFunction.HasCompactSupportPrimitive Ω]
    (ρ : 𝓓(Ω, ℝ)) (hρ : ∫ x, ρ x = 1) (T : 𝓓'(Ω, F))
    (hT : (lineDerivCLM (1 : ℝ) T : 𝓓'(Ω, F)) = 0) :
    T = ofFun Ω (fun _ => T ρ) volume ⊤ := by
  have hOneLoc : LocallyIntegrableOn (fun _ : ℝ => (1 : ℝ)) Ω volume :=
    (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).locallyIntegrable
      |>.locallyIntegrableOn Ω
  apply eq_ofFun_const_of_lineDerivCLM_eq_zero ρ
  · rw [ofFun_apply hOneLoc]
    simpa using hρ
  · exact exact_testFunction_lineDerivCLM_of_hasCompactSupportPrimitive
  · exact hT

/-- Iterated distributional differentiation commutes with a tower of classical derivatives.

Using a sequence rather than iterating `deriv` makes the statement applicable when the classical
derivatives are supplied together with proofs of their values. -/
theorem iteratedLineDerivOp_ofFun_eq_of_hasDerivAt {Ω : TopologicalSpace.Opens ℝ}
    (f : ℕ → ℝ → F) (hf : ∀ n x, HasDerivAt (f n) (f (n + 1) x) x)
    (hfloc : ∀ n, LocallyIntegrableOn (f n) Ω volume) (k : ℕ) :
    iteratedLineDerivOp (fun _ : Fin k => (1 : ℝ)) (ofFun Ω (f 0) volume ⊤) =
      ofFun Ω (f k) volume ⊤ := by
  rw [iteratedLineDerivOp_const_eq_iter_lineDerivOp]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      exact lineDerivCLM_ofFun_eq_of_hasDerivAt (hf k) (hfloc k) (hfloc (k + 1))

/-- Iterated distributional differentiation of the regular distribution induced by a polynomial
agrees with iterated formal differentiation of that polynomial. -/
theorem iteratedLineDerivOp_ofFun_polynomial {Ω : TopologicalSpace.Opens ℝ}
    (p : Polynomial ℝ) (k : ℕ) :
    iteratedLineDerivOp (fun _ : Fin k => (1 : ℝ))
        (ofFun Ω (fun x => p.eval x) volume ⊤) =
      ofFun Ω
        (fun x => (((Polynomial.derivative : Polynomial ℝ → Polynomial ℝ)^[k]) p).eval x)
        volume ⊤ := by
  apply iteratedLineDerivOp_ofFun_eq_of_hasDerivAt
    (f := fun n x => (((Polynomial.derivative : Polynomial ℝ → Polynomial ℝ)^[n]) p).eval x)
  · intro n x
    simpa only [Function.iterate_succ_apply'] using
      (((Polynomial.derivative : Polynomial ℝ → Polynomial ℝ)^[n]) p).hasDerivAt x
  · intro n
    exact (((Polynomial.derivative : Polynomial ℝ → Polynomial ℝ)^[n]) p).continuous
      |>.locallyIntegrable.locallyIntegrableOn Ω

/-- Every distributional derivative of order strictly larger than the degree of a regular
polynomial distribution vanishes. -/
theorem iteratedLineDerivOp_ofFun_polynomial_eq_zero_of_natDegree_lt
    {Ω : TopologicalSpace.Opens ℝ} (p : Polynomial ℝ) (k : ℕ) (hpk : p.natDegree < k) :
    iteratedLineDerivOp (fun _ : Fin k => (1 : ℝ))
        (ofFun Ω (fun x => p.eval x) volume ⊤) = 0 := by
  rw [iteratedLineDerivOp_ofFun_polynomial, Polynomial.iterate_derivative_eq_zero hpk]
  have hz : (fun x : ℝ => Polynomial.eval x (0 : Polynomial ℝ)) = 0 := by
    funext x
    simp
  rw [hz]
  exact ofFun_zero

/-- The derivative of order one above the natural degree of a regular polynomial distribution
vanishes. -/
theorem iteratedLineDerivOp_ofFun_polynomial_natDegree_add_one_eq_zero
    {Ω : TopologicalSpace.Opens ℝ} (p : Polynomial ℝ) :
    iteratedLineDerivOp (fun _ : Fin (p.natDegree + 1) => (1 : ℝ))
        (ofFun Ω (fun x => p.eval x) volume ⊤) = 0 :=
  iteratedLineDerivOp_ofFun_polynomial_eq_zero_of_natDegree_lt p _ (Nat.lt_succ_self _)

end Distribution
