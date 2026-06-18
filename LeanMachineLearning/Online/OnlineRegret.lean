/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import Mathlib.Analysis.Calculus.Gradient.Basic

import LeanMachineLearning.ForMathlib.Analysis.Calculus.Deriv.Slope
import LeanMachineLearning.MeasureTheory.Function.ConditionalExpectation.PullOut
import LeanMachineLearning.MeasureTheory.Function.L2Space

/-!
# Online gradient descent

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset
open scoped Gradient ENNReal NNReal RealInnerProductSpace

namespace Learning

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

section OnlineToBatch

variable {E : Type*}
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
    P[fun ω ↦ ∑ i ∈ Finset.range n, (f i (X i ω) - f i y)] ≤
      P[fun ω ↦ ∑ i ∈ Finset.range n, ⟪X i ω - y, G i ω⟫] := by
  rw [integral_finsetSum, integral_finsetSum]
  rotate_left
  · refine fun i hi ↦ MemLp.integrable_inner ?_ (h_memLp i)
    exact (hX_lp i).sub (memLp_const _)
  · exact fun i hi ↦ (h_int i).sub (integrable_const _)
  refine Finset.sum_le_sum fun i hi ↦ ?_
  exact integral_sub_le_integral_inner hf hdf h_unbiased h_memLp h hX_lp h_int y i

lemma integral_apply_avg_sub_le_integral_sum_sub
    {f : E → ℝ} (hf : ConvexOn ℝ .univ f) (hdf : Differentiable ℝ f)
    (h_unbiased : ∀ n x, (ν n x)[id] = ∇ f x) (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G alg (obliviousEnv ν) P)
    (hX_lp : ∀ n, MemLp (X n) 2 P) (h_int : ∀ n, Integrable (fun ω ↦ f (X n ω)) P)
    (y : E) (n : ℕ) (hn : n ≠ 0)
    (h_int_avg : Integrable (fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)) P) :
    P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) - f y] ≤
      (n : ℝ)⁻¹ * P[fun ω ↦ ∑ i ∈ Finset.range n, ⟪X i ω - y, G i ω⟫] := by
  calc P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) - f y]
  _ ≤ (n : ℝ)⁻¹ * P[fun ω ↦ ∑ i ∈ Finset.range n, (f (X i ω) - f y)] := by
    rw [← integral_const_mul]
    gcongr
    · exact h_int_avg.sub (integrable_const _)
    · refine Integrable.const_mul (integrable_finsetSum _ fun i hi ↦ ?_) _
      exact (h_int i).sub (integrable_const _)
    exact fun ω ↦ hf.todo'3 _ y n hn
  _ ≤ (n : ℝ)⁻¹ * P[fun ω ↦ ∑ i ∈ Finset.range n, ⟪X i ω - y, G i ω⟫] := by
    grw [integral_sum_sub_le_integral_sum_inner (fun _ ↦ hf) (fun _ ↦ hdf) h_unbiased h_memLp h
      hX_lp h_int y n]

end OnlineToBatch

variable {E : Type*} {mE : MeasurableSpace E}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
  {x x₀ : E} {X G : ℕ → Ω → E} {γ : ℕ → ℝ} {η : ℝ}

section Linear

lemma todo'' (x y g : E) (hη : 0 < η) :
    ⟪x - y, g⟫ = (2 * η)⁻¹ * (‖x - y‖ ^ 2 - ‖(x - η • g) - y‖ ^ 2) + (η / 2) * ‖g‖ ^ 2 := by
  have hsub : (x - η • g) - y = (x - y) - η • g := by abel
  rw [hsub, norm_sub_sq_real (x - y) (η • g)]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  field

lemma todo (x y g : ℕ → E) (hγ : ∀ n, 0 < γ n) (n : ℕ) :
    ∑ i ∈ Finset.range n, ⟪x i - y i, g i⟫ ≤
      ∑ i ∈ Finset.range n,
        ((2 * γ i)⁻¹ * (‖x i - y i‖ ^ 2 - ‖(x i - γ i • g i) - y i‖ ^ 2) +
          (γ i / 2) * ‖g i‖ ^ 2) := by
  gcongr with i hi
  rw [todo'' (x i) (y i) (g i) (hγ i)]

lemma todo_sfsq (x g : ℕ → E) (y : E) (hγ : ∀ n, 0 < γ n)
    (hx : ∀ n, x (n + 1) = x n - γ n • g n) (n : ℕ) :
    ∑ i ∈ Finset.range n, ⟪x i - y, g i⟫ ≤
      ∑ i ∈ Finset.range n,
        ((2 * γ i)⁻¹ * (‖x i - y‖ ^ 2 - ‖x (i + 1) - y‖ ^ 2) + (γ i / 2) * ‖g i‖ ^ 2) :=
  (todo x (fun _ ↦ y) g hγ n).trans_eq <| by simp [hx]

section ConstantStep

lemma todo''' (x g : ℕ → E) (y : E)
    (hη : 0 < η) (hx : ∀ n, x (n + 1) = x n - η • g n) (n : ℕ) :
    ∑ i ∈ Finset.range n, ⟪x i - y, g i⟫ ≤
      (2 * η)⁻¹ * (‖x 0 - y‖ ^ 2 - ‖x n - y‖ ^ 2) + (η / 2) * ∑ i ∈ Finset.range n, ‖g i‖ ^ 2 := by
  refine (todo_sfsq x g y (fun _ ↦ hη) hx n).trans_eq ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, Finset.sum_range_sub' (fun i ↦ ‖x i - y‖ ^ 2) n]

lemma lem14dot1 (x g : ℕ → E) (y : E) (η : ℝ)
    (hη : 0 < η) (hx : ∀ n, x (n + 1) = x n - η • g n) (n : ℕ) :
    ∑ i ∈ Finset.range n, ⟪x i - y, g i⟫ ≤
      (2 * η)⁻¹ * ‖x 0 - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, ‖g i‖ ^ 2 := by
  grw [todo''' x g y hη hx n]
  gcongr
  exact sub_le_self _ (sq_nonneg _)

end ConstantStep

end Linear

section OnlineRegret

/-- The regret of a sequence `x : ℕ → E` compared to a point `y : E` in an online learning task
with losses `ℓ : ℕ → E → F`. -/
def onlineRegret {E F : Type*} [AddCommGroup F] (ℓ : ℕ → E → F) (y : E) (x : ℕ → E) (n : ℕ) : F :=
  ∑ i ∈ Finset.range n, (ℓ i (x i) - ℓ i y)

noncomputable def linearizedLoss [CompleteSpace E] (f : ℕ → E → ℝ) (x : ℕ → E) : ℕ → E → ℝ :=
  fun n y ↦ ⟪y, ∇ (f n) (x n)⟫

lemma onlineRegret_le_onlineRegret_linearizedLoss [CompleteSpace E] {f : ℕ → E → ℝ}
    (hf : ∀ n, ConvexOn ℝ .univ (f n)) (hdf : ∀ n, Differentiable ℝ (f n))
    (x : ℕ → E) (y : E) (n : ℕ) :
    onlineRegret f y x n ≤ onlineRegret (linearizedLoss f x) y x n := by
  simp only [onlineRegret, linearizedLoss, ← inner_sub_left]
  gcongr with i hi
  exact (hf i).sub_le_inner_gradient (hdf i).differentiableAt _

lemma apply_avg_sub_le_onlineRegret {f : E → ℝ} (hf : ConvexOn ℝ .univ f)
    (x : ℕ → E) (y : E) (n : ℕ) (hn : n ≠ 0) :
    f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y ≤ (n : ℝ)⁻¹ • onlineRegret (fun _ ↦ f) y x n :=
  hf.todo'3 x y n hn

lemma onlineRegret_gradientStep_le (x g : ℕ → E) (y : E) (η : ℝ)
    (hη : 0 < η) (hx : ∀ n, x (n + 1) = x n - η • g n) (n : ℕ) :
    onlineRegret (fun n x ↦ ⟪x, g n⟫) y x n ≤
      (2 * η)⁻¹ * ‖x 0 - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, ‖g i‖ ^ 2 := by
  simpa [onlineRegret, inner_sub_left] using lem14dot1 x g y η hη hx n

lemma apply_avg_sub_le_onlineRegret_linearizedLoss [CompleteSpace E] {f : E → ℝ}
    (hf : ConvexOn ℝ .univ f) (hdf : Differentiable ℝ f)
    (x : ℕ → E) (y : E) (n : ℕ) (hn : n ≠ 0) :
    f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y ≤
      (n : ℝ)⁻¹ * (onlineRegret (linearizedLoss (fun _ ↦ f) x) y x n) := by
  simpa [onlineRegret, linearizedLoss, ← inner_sub_left] using hf.todo'2 hdf x y n hn

end OnlineRegret

end Learning
