/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import LeanMachineLearning.ForMathlib.Algebra.Polynomial.Function
public import LeanMachineLearning.ForMathlib.Topology.Algebra.Module.FiniteDimension
public import LeanMachineLearning.ForMathlib.Topology.ContinuousMap.Algebra
public import LeanMachineLearning.NeuralNetwork.Shallow.Basic
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.Topology.Separation.Basic

/-!
# Polynomial obstructions to universal approximation

On sufficiently many collinear sample points, every ridge function obtained from a polynomial
activation belongs to a fixed finite-dimensional space of univariate polynomials.  This gives the
necessary direction of the Leshno--Lin--Pinkus--Schocken theorem.
-/

@[expose] public section

open Polynomial

namespace Learning.ShallowNetwork

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The space of continuous real-valued functions on `n` distinct scalar multiples of a nonzero
vector has dimension `n`.

The statement is phrased using a range, so it applies without choosing a finite set enumeration.
-/
theorem finrank_continuousMap_range_fin_smul {e : E} (he : e ≠ 0) (n : ℕ) :
    Module.finrank ℝ C(Set.range (fun i : Fin n ↦ (i : ℝ) • e), ℝ) = n := by
  classical
  let emb : Fin n ↪ E :=
    ⟨fun i ↦ (i : ℝ) • e, fun i j hij ↦ by
      apply Fin.ext
      exact_mod_cast (smul_left_injective ℝ he hij)⟩
  let K : Set E := Set.range emb
  have hcard : Fintype.card K = n :=
    (Fintype.card_congr emb.toEquivRange).symm.trans (Fintype.card_fin n)
  change Module.finrank ℝ C(K, ℝ) = n
  rw [(LinearEquiv.ofBijective (ContinuousMap.coeFnCLM ℝ).toLinearMap
    ContinuousMap.equivFnOfDiscrete.bijective).finrank_eq, Module.finrank_pi, hcard]

private theorem aeval_degreeLT_range_ne_top {X : Type*} [TopologicalSpace X]
    {coordinate : C(X, ℝ)} {n : ℕ}
    (hfinrank : Module.finrank ℝ C(X, ℝ) = n + 1) :
    ((Polynomial.aeval coordinate).toLinearMap.domRestrict (degreeLT ℝ n)).range ≠ ⊤ := by
  intro htop
  have hrank := LinearMap.finrank_range_le
    ((Polynomial.aeval coordinate).toLinearMap.domRestrict (degreeLT ℝ n))
  rw [htop, finrank_top, hfinrank,
    Module.finrank_eq_card_basis (degreeLT.basis ℝ n), Fintype.card_fin] at hrank
  lia

/-- If the activation is polynomial, then its shallow-network space fails to be dense on some
finite (hence compact) set.  No finite-dimensionality assumption on the input space is needed. -/
theorem exists_compact_not_dense_of_isPolynomial [Nontrivial E]
    {σ : C(ℝ, ℝ)} (hσ : Function.IsPolynomial σ) :
    ∃ K : Set E, IsCompact K ∧ ¬ Dense (spaceOn σ K : Set C(K, ℝ)) := by
  obtain ⟨p, hp⟩ := hσ
  obtain ⟨e, he⟩ : ∃ e : E, e ≠ 0 := exists_ne 0
  let emb : Fin (p.natDegree + 2) ↪ E :=
    ⟨fun i ↦ (i : ℝ) • e, fun i j hij ↦ by
      apply Fin.ext
      exact_mod_cast (smul_left_injective ℝ he hij)⟩
  let K : Set E := Set.range emb
  let coordinate : C(K, ℝ) := ⟨fun x ↦ inner ℝ e x / inner ℝ e e, by fun_prop⟩
  let evalDegree : degreeLT ℝ (p.natDegree + 1) →ₗ[ℝ] C(K, ℝ) :=
    (Polynomial.aeval coordinate).toLinearMap.domRestrict (degreeLT ℝ (p.natDegree + 1))
  have hfinrank : Module.finrank ℝ C(K, ℝ) = p.natDegree + 2 :=
    finrank_continuousMap_range_fin_smul he _
  have hproper : evalDegree.range ≠ ⊤ := aeval_degreeLT_range_ne_top hfinrank
  have hspace : (spaceOn σ K : Set C(K, ℝ)) ⊆ evalDegree.range := by
    rw [SetLike.coe_subset_coe, spaceOn]
    apply Submodule.span_le.2
    rintro _ ⟨⟨w, b⟩, rfl⟩
    let q := p.comp (C (inner ℝ w e) * X + C b)
    have hq : q ∈ degreeLT ℝ (p.natDegree + 1) := by
      rw [degreeLT_succ_eq_degreeLE, mem_degreeLE, ← natDegree_le_iff_degree_le]
      calc
        q.natDegree ≤ p.natDegree * (C (inner ℝ w e) * X + C b).natDegree := natDegree_comp_le
        _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ <| natDegree_add_le_of_degree_le
            (by simpa using natDegree_C_mul_X_pow_le (inner ℝ w e) 1) (by simp)
        _ = p.natDegree := Nat.mul_one _
    refine ⟨⟨q, hq⟩, ?_⟩
    ext x
    obtain ⟨i, hi⟩ := x.property
    simp only [evalDegree, LinearMap.domRestrict_apply, AlgHom.toLinearMap_apply,
      Polynomial.aeval_continuousMap_apply, coordinate, ContinuousMap.coe_mk,
      ContinuousMap.restrict_apply, neuron_apply]
    rw [← hp, ← hi]
    have hemb : emb i = (i : ℝ) • e := rfl
    have : inner ℝ e ((i : ℝ) • e) / inner ℝ e e = (i : ℝ) := by
      rw [real_inner_smul_right, div_eq_iff (inner_self_ne_zero.mpr he)]
    rw [hemb, this]
    simp [q, real_inner_smul_right, mul_comm (inner ℝ w e)]
  exact ⟨K, (Set.finite_range emb).isCompact,
    evalDegree.range.not_dense_of_subset_of_finiteDimensional hproper hspace⟩

/-- Density of the network space on every compact set forces the activation not to be a
polynomial, provided the input space is nontrivial. -/
theorem not_isPolynomial_of_dense_spaceOn [Nontrivial E] (σ : C(ℝ, ℝ))
    (hσ : ∀ (K : Set E), IsCompact K → Dense (spaceOn σ K : Set C(K, ℝ))) :
    ¬ Function.IsPolynomial σ := by
  intro hPolynomial
  obtain ⟨K, hK, hnotDense⟩ := exists_compact_not_dense_of_isPolynomial (E := E) hPolynomial
  exact hnotDense (hσ K hK)

end Learning.ShallowNetwork
