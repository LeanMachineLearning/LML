/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Calculus.ContinuousMapComposition
public import LeanMachineLearning.ForMathlib.Topology.ContinuousMap.Moments
public import LeanMachineLearning.NeuralNetwork.UniversalApproximation.Discriminatory

/-!
# Universal approximation for smooth activations

This file isolates the smooth part of the discriminatory-function argument.  A continuous
derivative tower is packaged as a class, so later convolution arguments may supply a different
smooth ridge function at each required degree.  The core lemma says that annihilating all ridges
of a function whose `n`-th derivative is nonzero forces a functional to annihilate every `n`-th
power of a linear coordinate.
-/

@[expose] public section

namespace Learning.ShallowNetwork

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A choice of all successive continuous derivatives of a continuous real function. -/
class HasContinuousDerivativeTower (g : C(ℝ, ℝ)) : Type where
  /-- The `n`-th derivative, bundled as a continuous map. -/
  derivative : ℕ → C(ℝ, ℝ)
  derivative_zero : derivative 0 = g
  hasDerivAt_derivative :
    ∀ (n : ℕ) (x : ℝ), HasDerivAt (derivative n) (derivative (n + 1) x) x

/-- A smooth function whose derivative of every order is not identically zero. -/
class HasNonzeroContinuousDerivativeTower (g : C(ℝ, ℝ)) : Type
    extends HasContinuousDerivativeTower g where
  exists_derivative_ne_zero : ∀ n, ∃ x, derivative n x ≠ 0

namespace HasContinuousDerivativeTower

variable {g : C(ℝ, ℝ)} [hg : HasContinuousDerivativeTower g]

@[simp]
theorem derivative_zero_eq : hg.derivative 0 = g :=
  hg.derivative_zero

/-- A functional annihilating every ridge of `g` also annihilates every power of a linear
coordinate for which the corresponding derivative of `g` is nonzero somewhere. -/
theorem annihilates_coordinate_pow_of_derivative_ne_zero
    (K : Set E) (hK : IsCompact K) (Λ : StrongDual ℝ C(K, ℝ))
    (hΛ : ∀ w b, Λ ((neuron g w b).restrict K) = 0)
    (n : ℕ) {b : ℝ} (hb : hg.derivative n b ≠ 0) (w : E) :
    Λ ((ContinuousMap.innerProductCoordinate K w) ^ n) = 0 := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let u : C(K, ℝ) := ContinuousMap.innerProductCoordinate K w
  have hstep : ∀ m t,
      Λ (u ^ m * (hg.derivative m).comp
        (ContinuousMap.const K b + ContinuousMap.const K t * u)) = 0 := by
    intro m
    induction m with
    | zero =>
        intro t
        rw [hg.derivative_zero]
        have heq : g.comp
            (ContinuousMap.const K b + ContinuousMap.const K t * u) =
            (neuron g (t • w) b).restrict K := by
          ext x
          simp only [ContinuousMap.comp_apply, ContinuousMap.add_apply,
            ContinuousMap.const_apply, ContinuousMap.mul_apply, u,
            ContinuousMap.innerProductCoordinate_apply,
            neuron_apply, ContinuousMap.restrict_apply, real_inner_smul_left]
          congr 1
          ring
        rw [heq]
        simpa using hΛ (t • w) b
    | succ m ihm =>
        intro t
        have hcurve := HasDerivAt.continuousMap_comp_affine
          (fun y ↦ hg.hasDerivAt_derivative m y)
          (ContinuousMap.const K b) u t
        have hmul := hcurve.const_mul (u ^ m)
        have hmul' : HasDerivAt
            (fun s ↦ u ^ m * (hg.derivative m).comp
              (ContinuousMap.const K b + ContinuousMap.const K s * u))
            (u ^ m * (u * (hg.derivative (m + 1)).comp
              (ContinuousMap.const K b + ContinuousMap.const K t * u))) t := by
          convert hmul using 1
          ext x
          simp [smul_eq_mul]
        have happly : HasDerivAt
            (fun s ↦ Λ (u ^ m * (hg.derivative m).comp
              (ContinuousMap.const K b + ContinuousMap.const K s * u)))
            (Λ (u ^ m * (u * (hg.derivative (m + 1)).comp
              (ContinuousMap.const K b + ContinuousMap.const K t * u)))) t := by
          simpa [Function.comp_def] using
            Λ.hasFDerivAt.comp_hasDerivAt_of_eq t hmul' rfl
        have hzero : HasDerivAt
            (fun s ↦ Λ (u ^ m * (hg.derivative m).comp
              (ContinuousMap.const K b + ContinuousMap.const K s * u))) 0 t := by
          convert hasDerivAt_const t (0 : ℝ) using 1
          funext s
          exact ihm s
        have hz := happly.unique hzero
        simpa [pow_succ, mul_assoc] using hz
  have h := hstep n 0
  have harg : (hg.derivative n).comp
      (ContinuousMap.const K b + ContinuousMap.const K 0 * u) =
      ContinuousMap.const K (hg.derivative n b) := by
    ext x
    simp
  rw [harg] at h
  have heq : u ^ n * ContinuousMap.const K (hg.derivative n b) =
      hg.derivative n b • u ^ n := by
    ext x
    simp [mul_comm]
  rw [heq, map_smul] at h
  exact (mul_eq_zero.mp h).resolve_left hb

/-- A degree-by-degree smooth ridge family is enough for the discriminatory property.  The
smooth function may depend on the degree; this is the form needed after mollification. -/
theorem isDiscriminatory_of_smooth_ridges
    (σ : C(ℝ, ℝ))
    (hsmooth : ∀ n : ℕ,
      ∃ (g : C(ℝ, ℝ)) (hg : HasContinuousDerivativeTower g) (b : ℝ),
        hg.derivative n b ≠ 0 ∧
        ∀ (K : Set E) (_hK : IsCompact K) (Λ : StrongDual ℝ C(K, ℝ)),
          (∀ w c, Λ ((neuron σ w c).restrict K) = 0) →
          ∀ w c, Λ ((neuron g w c).restrict K) = 0) :
    IsDiscriminatory (E := E) σ := by
  constructor
  intro K hK Λ hΛ
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply StrongDual.eq_zero_of_innerProductCoordinate_powers K Λ
  intro n w
  obtain ⟨g, hg, b, hb, htransfer⟩ := hsmooth n
  let _ : HasContinuousDerivativeTower g := hg
  exact annihilates_coordinate_pow_of_derivative_ne_zero K hK Λ
    (htransfer K hK Λ hΛ) n hb w

/-- A smooth activation with no identically-zero derivative is discriminatory on every real
inner-product space. -/
theorem isDiscriminatory_of_hasNonzeroContinuousDerivativeTower
    (g : C(ℝ, ℝ)) [hg : HasNonzeroContinuousDerivativeTower g] :
    IsDiscriminatory (E := E) g := by
  apply isDiscriminatory_of_smooth_ridges g
  intro n
  obtain ⟨b, hb⟩ := hg.exists_derivative_ne_zero n
  exact ⟨g, hg.toHasContinuousDerivativeTower, b, hb, by
    intro K hK Λ hΛ
    exact hΛ⟩

/-- A smooth activation with no identically-zero derivative has the universal approximation
property on every real inner-product space. -/
theorem isUniversal_of_hasNonzeroContinuousDerivativeTower
    (g : C(ℝ, ℝ)) [HasNonzeroContinuousDerivativeTower g] :
    IsUniversal (E := E) g :=
  (isUniversal_iff_isDiscriminatory g).2
    (isDiscriminatory_of_hasNonzeroContinuousDerivativeTower g)

end HasContinuousDerivativeTower

end Learning.ShallowNetwork
