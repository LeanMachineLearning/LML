/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import Mathlib.Analysis.Calculus.Gradient.Basic

import LeanMachineLearning.ForMathlib.Analysis.Calculus.Deriv.Slope
import LeanMachineLearning.ForMathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import LeanMachineLearning.ForMathlib.MeasureTheory.Function.L2Space

/-!
# Online to batch conversion

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset
open scoped Gradient ENNReal NNReal RealInnerProductSpace

namespace Learning

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E]
  {mE : MeasurableSpace E} [BorelSpace E]
  {X G : ℕ → Ω → E} {alg : Algorithm E E}
  {ν : ℕ → Kernel E E} [∀ n, IsMarkovKernel (ν n)]
  {f : ℕ → E → ℝ}

-- todo: name
lemma memLp_gradient (h : IsAlgEnvSeq X G alg (obliviousEnv ν) P)
    (h_unbiased : ∀ n x, (ν n x)[id] = ∇ (f n) x)
    (h_memLp : ∀ n, MemLp (G n) 2 P) (n : ℕ) :
    MemLp (fun ω ↦ ∇ (f n) (X n ω)) 2 P := by
  let M n := MeasurableSpace.comap (X n) inferInstance
  have h_lp : MemLp P[G n | M n] 2 P := (h_memLp n).condExp (m := M n)
  have h_ae := h.condExp_feedback_obliviousEnv_ae_eq_integral_id n
      ((h_memLp n).integrable (by simp))
  refine h_lp.ae_eq <| h_ae.trans ?_
  simp [← h_unbiased]

lemma integral_inner_eq_integral_inner_gradient
    (h : IsAlgEnvSeq X G alg (obliviousEnv ν) P)
    (h_unbiased : ∀ n x, (ν n x)[id] = ∇ (f n) x) (h_memLp : ∀ n, MemLp (G n) 2 P)
    (hX_lp : ∀ n, MemLp (X n) 2 P) (y : E) (n : ℕ) :
    P[fun ω ↦ ⟪X n ω - y, G n ω⟫] = P[fun ω ↦ ⟪X n ω - y, ∇ (f n) (X n ω)⟫] := by
  have h_obl : HasCondDistrib (G n) (X n) (ν n) P :=
    h.hasCondDistrib_feedback_obliviousEnv n
  calc P[fun ω ↦ ⟪X n ω - y, G n ω⟫]
  _ = P[fun ω ↦ P[fun ω' ↦ ⟪X n ω' - y, G n ω'⟫ | mE.comap (X n)] ω] := by
    rw [integral_condExp (h.measurable_action _).comap_le]
  _ = P[fun ω ↦ ⟪X n ω - y, P[G n | mE.comap (X n)] ω⟫] := by
    refine integral_congr_ae ?_
    refine condExp_inner_of_stronglyMeasurable_left ?_ ?_ ?_
    · refine StronglyMeasurable.sub ?_ (by fun_prop)
      refine Measurable.stronglyMeasurable ?_
      rw [measurable_iff_comap_le]
    · exact MemLp.integrable_inner ((hX_lp n).sub (memLp_const _)) (h_memLp n)
    · exact (h_memLp n).integrable (by simp)
  _ = P[fun ω ↦ ⟪X n ω - y, (ν n (X n ω))[id]⟫] := by
    refine integral_congr_ae ?_
    filter_upwards [h.condExp_feedback_obliviousEnv_ae_eq_integral_id n
      ((h_memLp n).integrable (by simp))] with ω hω using by rw [hω]
  _ = P[fun ω ↦ ⟪X n ω - y, ∇ (f n) (X n ω)⟫] := by simp_rw [h_unbiased n]

lemma integral_sub_le_integral_inner (hf : ∀ n, ConvexOn ℝ .univ (f n))
    (hdf : ∀ n, Differentiable ℝ (f n))
    (h_unbiased : ∀ n x, (ν n x)[id] = ∇ (f n) x) (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G alg (obliviousEnv ν) P)
    (hX_lp : ∀ n, MemLp (X n) 2 P)
    (h_int : ∀ n, Integrable (fun ω ↦ f n (X n ω)) P) -- todo: discuss this assumption
    (y : E) (n : ℕ) :
    P[fun ω ↦ f n (X n ω) - f n y] ≤ P[fun ω ↦ ⟪X n ω - y, G n ω⟫] := by
  rw [integral_inner_eq_integral_inner_gradient h h_unbiased h_memLp hX_lp y n]
  gcongr
  · exact (h_int n).sub (integrable_const _)
  · refine MemLp.integrable_inner ?_ ?_
    · exact (hX_lp n).sub (memLp_const _)
    · exact memLp_gradient h h_unbiased h_memLp n
  · exact fun ω ↦ (hf n).sub_le_inner_gradient (hdf n).differentiableAt y

lemma integral_sum_sub_le_integral_sum_inner (hf : ∀ n, ConvexOn ℝ .univ (f n))
    (hdf : ∀ n, Differentiable ℝ (f n))
    (h_unbiased : ∀ n x, (ν n x)[id] = ∇ (f n) x) (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G alg (obliviousEnv ν) P)
    (hX_lp : ∀ n, MemLp (X n) 2 P) (h_int : ∀ n, Integrable (fun ω ↦ f n (X n ω)) P)
    (y : E) (n : ℕ) :
    P[fun ω ↦ ∑ i ∈ range n, (f i (X i ω) - f i y)] ≤
      P[fun ω ↦ ∑ i ∈ range n, ⟪X i ω - y, G i ω⟫] := by
  rw [integral_finsetSum, integral_finsetSum]
  rotate_left
  · refine fun i hi ↦ MemLp.integrable_inner ?_ (h_memLp i)
    exact (hX_lp i).sub (memLp_const _)
  · exact fun i hi ↦ (h_int i).sub (integrable_const _)
  refine sum_le_sum fun i hi ↦ ?_
  exact integral_sub_le_integral_inner hf hdf h_unbiased h_memLp h hX_lp h_int y i

lemma integral_apply_avg_sub_le_integral_sum_sub
    {f : E → ℝ} (hf : ConvexOn ℝ .univ f) (hdf : Differentiable ℝ f)
    (h_unbiased : ∀ n x, (ν n x)[id] = ∇ f x) (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G alg (obliviousEnv ν) P)
    (hX_lp : ∀ n, MemLp (X n) 2 P) (h_int : ∀ n, Integrable (fun ω ↦ f (X n ω)) P)
    (y : E) (n : ℕ) (hn : n ≠ 0)
    (h_int_avg : Integrable (fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ range n, X i ω)) P) :
    P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ range n, X i ω) - f y] ≤
      (n : ℝ)⁻¹ * P[fun ω ↦ ∑ i ∈ range n, ⟪X i ω - y, G i ω⟫] := by
  calc P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ range n, X i ω) - f y]
  _ ≤ (n : ℝ)⁻¹ * P[fun ω ↦ ∑ i ∈ range n, (f (X i ω) - f y)] := by
    rw [← integral_const_mul]
    gcongr
    · exact h_int_avg.sub (integrable_const _)
    · refine Integrable.const_mul (integrable_finsetSum _ fun i hi ↦ ?_) _
      exact (h_int i).sub (integrable_const _)
    exact fun ω ↦ hf.apply_avg_sub_le_avg_sub _ y n hn
  _ ≤ (n : ℝ)⁻¹ * P[fun ω ↦ ∑ i ∈ range n, ⟪X i ω - y, G i ω⟫] := by
    grw [integral_sum_sub_le_integral_sum_inner (fun _ ↦ hf) (fun _ ↦ hdf) h_unbiased h_memLp h
      hX_lp h_int y n]

end Learning
