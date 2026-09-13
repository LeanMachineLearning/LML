/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Calculus.ContinuousMapComposition
public import LeanMachineLearning.ForMathlib.Analysis.LocallyConvex.Annihilator
public import LeanMachineLearning.ForMathlib.Topology.ContinuousMap.Moments
public import LeanMachineLearning.NeuralNetwork.Shallow.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Discriminatory criteria for universal approximation

An activation is discriminatory on an input space if the only continuous linear functional on
`C(K, ℝ)` that annihilates every neuron is zero, for every compact `K`. Hahn--Banach makes this
property equivalent to universal approximation.

For smooth activations, annihilating all ridges whose `n`-th derivative is nonzero somewhere
forces a functional to annihilate every `n`-th power of a linear coordinate. The resulting
criterion permits a different smooth ridge function at each degree. Smoothness and successive
derivatives are expressed using mathlib's `ContDiff` and `iteratedDeriv`.
-/

@[expose] public section

open scoped ContDiff

namespace Learning.ShallowNetwork

/-! ## The dual criterion -/

section Discriminatory

/-- An activation is discriminatory on `E` if no nonzero continuous linear functional annihilates
all of its neurons on a compact subset of `E`. -/
class IsDiscriminatory (E : Type*) [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (σ : C(ℝ, ℝ)) : Prop where
  annihilator_eq_zero : ∀ (K : Set E), IsCompact K → ∀ Λ : StrongDual ℝ C(K, ℝ),
      (∀ w b, Λ ((neuron σ w b).restrict K) = 0) → Λ = 0

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Density of the network space on every compact set is equivalent to the
discriminatory-functional criterion. -/
theorem dense_spaceOn_iff_isDiscriminatory (σ : C(ℝ, ℝ)) :
    (∀ (K : Set E), IsCompact K → Dense (spaceOn σ K : Set C(K, ℝ))) ↔
      IsDiscriminatory E σ := by
  constructor
  · intro h_dense
    constructor
    intro K hK
    let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
    intro Λ hΛ
    refine (spaceOn σ K).dense_iff_forall_dual_eq_zero.mp (h_dense K hK) Λ ?_
    intro f hf
    have hle : spaceOn σ K ≤ Λ.ker := by
      rw [spaceOn]
      apply Submodule.span_le.2
      rintro g ⟨p, rfl⟩
      exact hΛ p.1 p.2
    exact hle hf
  · rintro ⟨h_disc⟩
    intro K hK
    let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
    rw [Submodule.dense_iff_forall_dual_eq_zero]
    intro Λ hΛ
    apply h_disc K hK Λ
    intro w b
    exact hΛ _ (Submodule.subset_span ⟨(w, b), rfl⟩)

end Discriminatory

/-! ## Smooth ridge criteria -/

section SmoothActivation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A functional annihilating every ridge of `g` also annihilates every power of a linear
coordinate for which the corresponding derivative of `g` is nonzero somewhere. -/
theorem annihilates_coordinate_pow_of_iteratedDeriv_ne_zero
    {g : C(ℝ, ℝ)} {K : Set E} {Λ : StrongDual ℝ C(K, ℝ)} {n : ℕ} {b : ℝ} {w : E}
    (hg : ContDiff ℝ ∞ g) (hK : IsCompact K)
    (hΛ : ∀ w b, Λ ((neuron g w b).restrict K) = 0) (hb : iteratedDeriv n g b ≠ 0) :
    Λ ((ContinuousMap.innerProductCoordinate K w) ^ n) = 0 := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let u : C(K, ℝ) := ContinuousMap.innerProductCoordinate K w
  let arg (t : ℝ) : C(K, ℝ) := ContinuousMap.const K b + ContinuousMap.const K t * u
  let d (m : ℕ) : C(ℝ, ℝ) := ⟨iteratedDeriv m g, hg.continuous_iteratedDeriv m (by simp)⟩
  have hstep : ∀ m t, Λ (u ^ m * (d m).comp (arg t)) = 0 := by
    intro m
    induction m with
    | zero =>
        intro t
        have hd0 : d 0 = g := by
          ext x
          simp [d]
        rw [hd0]
        have heq : g.comp (arg t) = (neuron g (t • w) b).restrict K := by
          ext x
          simp [arg, u, neuron_apply, real_inner_smul_left, add_comm]
        rw [heq]
        simpa using hΛ (t • w) b
    | succ m ihm =>
        intro t
        have hd : ∀ y, HasDerivAt (d m) (d (m + 1) y) y := by
          intro y
          simpa [d, ContinuousMap.coe_mk, iteratedDeriv_succ] using
            (hg.differentiable_iteratedDeriv m
              (by exact_mod_cast ENat.natCast_lt_top m) y).hasDerivAt
        have hcurve := HasDerivAt.continuousMap_comp_affine hd (ContinuousMap.const K b) u t
        have hmul' : HasDerivAt (fun s ↦ u ^ m * (d m).comp (arg s))
            (u ^ m * (u * (d (m + 1)).comp (arg t))) t := by
          convert hcurve.const_mul (u ^ m) using 1
          ext x
          simp [arg, smul_eq_mul]
        have happly : HasDerivAt (fun s ↦ Λ (u ^ m * (d m).comp (arg s)))
            (Λ (u ^ m * (u * (d (m + 1)).comp (arg t)))) t := by
          simpa [Function.comp_def] using Λ.hasFDerivAt.comp_hasDerivAt_of_eq t hmul' rfl
        have hzero : HasDerivAt (fun s ↦ Λ (u ^ m * (d m).comp (arg s))) 0 t := by
          convert hasDerivAt_const t (0 : ℝ) using 1
          funext s
          exact ihm s
        simpa [pow_succ, mul_assoc] using happly.unique hzero
  have h : d n b * Λ (u ^ n) = 0 := calc
    d n b * Λ (u ^ n) = Λ (d n b • u ^ n) := by simp
    _ = Λ (u ^ n * (d n).comp (arg 0)) := by
      congr 1
      ext x
      simp [arg, mul_comm]
    _ = 0 := hstep n 0
  exact (mul_eq_zero.mp h).resolve_left hb

/-- A degree-by-degree smooth ridge family is enough for the discriminatory property.  The
smooth function may depend on the degree, as needed after mollification. -/
theorem isDiscriminatory_of_smooth_ridges {σ : C(ℝ, ℝ)} (hsmooth : ∀ n : ℕ, ∃ (g : C(ℝ, ℝ)) (b : ℝ),
    ContDiff ℝ ∞ g ∧ iteratedDeriv n g b ≠ 0 ∧
      ∀ (K : Set E) (_hK : IsCompact K) (Λ : StrongDual ℝ C(K, ℝ)),
        (∀ w c, Λ ((neuron σ w c).restrict K) = 0) → ∀ w c, Λ ((neuron g w c).restrict K) = 0) :
    IsDiscriminatory E σ := by
  constructor
  intro K hK Λ hΛ
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply StrongDual.eq_zero_of_innerProductCoordinate_powers K Λ
  intro n w
  obtain ⟨g, b, hg, hb, htransfer⟩ := hsmooth n
  exact annihilates_coordinate_pow_of_iteratedDeriv_ne_zero hg hK (htransfer K hK Λ hΛ) hb

/-- A smooth activation with no identically-zero derivative is discriminatory on every real
inner-product space. -/
theorem isDiscriminatory_of_contDiff_of_iteratedDeriv_ne_zero
    {g : C(ℝ, ℝ)} (hg : ContDiff ℝ ∞ g) (hne : ∀ n : ℕ, ∃ b : ℝ, iteratedDeriv n g b ≠ 0) :
    IsDiscriminatory E g := by
  apply isDiscriminatory_of_smooth_ridges
  intro n
  obtain ⟨b, hb⟩ := hne n
  exact ⟨g, b, hg, hb, by simp⟩

/-- A smooth activation with no identically-zero derivative has dense network space on every
compact subset of a real inner-product space. -/
theorem dense_spaceOn_of_contDiff_of_iteratedDeriv_ne_zero
    {g : C(ℝ, ℝ)} (hg : ContDiff ℝ ∞ g)
    (hne : ∀ n : ℕ, ∃ b : ℝ, iteratedDeriv n g b ≠ 0) {K : Set E} (hK : IsCompact K) :
    Dense (spaceOn g K : Set C(K, ℝ)) :=
  (dense_spaceOn_iff_isDiscriminatory g).2
    (isDiscriminatory_of_contDiff_of_iteratedDeriv_ne_zero hg hne) K hK

end SmoothActivation

end Learning.ShallowNetwork
