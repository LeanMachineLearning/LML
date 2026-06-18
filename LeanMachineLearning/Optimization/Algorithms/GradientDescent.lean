/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.OnlineRegret
public import LeanMachineLearning.SequentialLearning.Deterministic

import LeanMachineLearning.ForMathlib.Analysis.Calculus.Deriv.Slope
import LeanMachineLearning.MeasureTheory.Function.L2Space

/-!
# Online gradient descent

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset
open scoped Gradient ENNReal NNReal RealInnerProductSpace

namespace Learning

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SecondCountableTopology E] [CompleteSpace E] [BorelSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {x x₀ : E} {X G : ℕ → Ω → E} {γ : ℕ → ℝ} {η : ℝ}
  {f : ℕ → E → ℝ} {hf : ∀ n, Measurable (∇ (f n))}

section Definition

variable {env : Environment E E}

/-- Online gradient descent with step sizes `γ : ℕ → ℝ` and initial point `x₀ : E`,
without projection.

It is an algorithm that chooses actions in `E` and gets feedback in `E` (gradient of the function at
the queried point). -/
noncomputable
def gradientStep (γ : ℕ → ℝ) (x₀ : E) : Algorithm E E :=
  detAlgorithm (fun n hist ↦ (hist ⟨n, by grind⟩).1 - γ n • (hist ⟨n, by grind⟩).2) (by fun_prop) x₀

lemma action_gradientStep_ae_eq (h_seq : IsAlgEnvSeq X G (gradientStep γ x₀) env P) (n : ℕ) :
    X (n + 1) =ᵐ[P] X n - γ n • G n := h_seq.action_detAlgorithm_ae_eq n

lemma action_gradientStep_ae_all_eq (h_seq : IsAlgEnvSeq X G (gradientStep γ x₀) env P) :
    ∀ᵐ ω ∂P, X 0 ω = x₀ ∧ ∀ n, X (n + 1) ω = X n ω - γ n • G n ω :=
  h_seq.action_detAlgorithm_ae_all_eq

lemma action_ae_eq_sub_sum (h_seq : IsAlgEnvSeq X G (gradientStep γ x₀) env P) (n : ℕ) :
    X n =ᵐ[P] fun ω ↦ x₀ - ∑ i ∈ Finset.range n, γ i • G i ω := by
  filter_upwards [h_seq.action_detAlgorithm_ae_all_eq] with ω ⟨hω0, hω⟩
  induction n with
  | zero => simpa
  | succ n ih => rw [hω n, Finset.sum_range_succ, ← sub_sub]; congr

end Definition

namespace GradientStep

variable {gradKernel : ℕ → Kernel E E} [∀ n, IsMarkovKernel (gradKernel n)]

lemma memLp_X (h : IsAlgEnvSeq X G (gradientStep (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (h_memLp : ∀ n, MemLp (G n) 2 P) (n : ℕ) :
    MemLp (X n) 2 P := by
  induction n with
  | zero =>
    have h0 : MemLp (fun _ ↦ x₀) 2 P := memLp_const _
    refine h0.ae_eq ?_
    filter_upwards [action_gradientStep_ae_all_eq h] with ω hω using hω.1.symm
  | succ n hn =>
    have h_sub : MemLp (fun ω ↦ X n ω - η • G n ω) 2 P := hn.sub (MemLp.const_smul (h_memLp n) _)
    refine h_sub.ae_eq ?_
    filter_upwards [action_gradientStep_ae_all_eq h] with ω hω using (hω.2 n).symm

section Linear

lemma integral_sum_inner_le (hη : 0 < η) (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G (gradientStep (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (y : E) (n : ℕ) :
    P[fun ω ↦ ∑ i ∈ Finset.range n, ⟪X i ω - y, G i ω⟫] ≤
      (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
  calc P[fun ω ↦ ∑ i ∈ Finset.range n, ⟪X i ω - y, G i ω⟫]
  _ ≤ ∫ ω, (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, ‖G i ω‖ ^ 2 ∂P := by
    refine integral_mono_ae ?_ ?_ ?_
    · refine integrable_finsetSum _ fun i hi ↦ MemLp.integrable_inner ?_ (h_memLp i)
      exact (memLp_X h h_memLp i).sub (memLp_const _)
    · refine Integrable.add (integrable_const _) (Integrable.const_mul ?_ _)
      exact integrable_finsetSum _ fun i hi ↦ (h_memLp i).integrable_norm_pow (by simp)
    · filter_upwards [action_gradientStep_ae_all_eq h] with ω hω
      refine (lem14dot1 _ _ y η hη hω.2 n).trans_eq ?_
      congr
      exact hω.1
  _ = (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
    rw [integral_add, integral_const_mul, integral_const_mul, integral_finsetSum]
    · simp
    · exact fun i hi ↦ (h_memLp i).integrable_norm_pow (by simp)
    · exact integrable_const _
    · refine Integrable.const_mul ?_ _
      exact integrable_finsetSum _ fun i hi ↦ (h_memLp i).integrable_norm_pow (by simp)

end Linear

lemma integral_sum_sub_le (hf : ∀ n, ConvexOn ℝ .univ (f n)) (hdf : ∀ n, Differentiable ℝ (f n))
    (hη : 0 < η)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x) (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G (gradientStep (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (h_int : ∀ n, Integrable (fun ω ↦ f n (X n ω)) P) (y : E) (n : ℕ) :
    P[fun ω ↦ ∑ i ∈ Finset.range n, (f i (X i ω) - f i y)] ≤
      (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
  calc P[fun ω ↦ ∑ i ∈ Finset.range n, (f i (X i ω) - f i y)]
  _ ≤ P[fun ω ↦ ∑ i ∈ Finset.range n, ⟪X i ω - y, G i ω⟫] :=
    integral_sum_sub_le_integral_sum_inner hf hdf h_unbiased h_memLp h (memLp_X h h_memLp) h_int y n
  _ ≤ (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] :=
    integral_sum_inner_le hη h_memLp h y n

lemma integral_onlineRegret_le
    (hf : ∀ n, ConvexOn ℝ .univ (f n)) (hdf : ∀ n, Differentiable ℝ (f n)) (hη : 0 < η)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x)
    (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G (gradientStep (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (h_int : ∀ n, Integrable (fun ω ↦ f n (X n ω)) P)
    (y : E) (n : ℕ) :
    P[fun ω ↦ onlineRegret f y (X · ω) n] ≤
      (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] :=
  integral_sum_sub_le hf hdf hη h_unbiased h_memLp h h_int y n

lemma integral_apply_avg_le {f : E → ℝ} (hf : ConvexOn ℝ .univ f) (hdf : Differentiable ℝ f)
    (hη : 0 < η)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ f x)
    (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G (gradientStep (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (h_int : ∀ n, Integrable (fun ω ↦ f (X n ω)) P)
    (y : E) (n : ℕ) (hn : n ≠ 0)
    (h_int_avg : Integrable (fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)) P) :
    P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) - f y] ≤
      (2 * η * n)⁻¹ * ‖x₀ - y‖ ^ 2 +
      (η / (2 * n)) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
  calc P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) - f y]
  _ ≤ (n : ℝ)⁻¹ * P[fun ω ↦ ∑ i ∈ Finset.range n, (f (X i ω) - f y)] := by
    rw [← integral_const_mul]
    gcongr
    · exact h_int_avg.sub (integrable_const _)
    · refine Integrable.const_mul (integrable_finsetSum _ fun i hi ↦ ?_) _
      exact (h_int i).sub (integrable_const _)
    exact fun ω ↦ hf.todo'3 _ y n hn
  _ ≤ (2 * η * n)⁻¹ * ‖x₀ - y‖ ^ 2 +
      (η / (2 * n)) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
    grw [integral_sum_sub_le (fun _ ↦ hf) (fun _ ↦ hdf) hη h_unbiased h_memLp h h_int y n]
    refine le_of_eq ?_
    field

theorem integral_apply_avg_const_div_sqrt {f : E → ℝ}
    (hf : ConvexOn ℝ .univ f) (hdf : Differentiable ℝ f)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ f x)
    {D L : ℝ} (hD_pos : 0 < D) (hL_pos : 0 < L)
    {y : E} (hxy_le : ‖x₀ - y‖ ≤ D) (hG_le : ∀ n ω, ‖G n ω‖ ≤ L)
    (h_int : ∀ n, Integrable (fun ω ↦ f (X n ω)) P)
    {n : ℕ} (hn : n ≠ 0)
    (h_int_avg : Integrable (fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)) P)
    (h : IsAlgEnvSeq X G (gradientStep (fun _ ↦ D / (L * √n)) x₀) (obliviousEnv gradKernel) P) :
    P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) - f y] ≤ D * L / √n := by
  let η := D / (L * √n)
  have hG_lp n : MemLp (G n) 2 P := by
    refine MemLp.mono (g := fun _ ↦ L) (memLp_const _)
      (have := h.measurable_feedback; by fun_prop) (ae_of_all _ fun ω ↦ ?_)
    simpa [abs_of_nonneg hL_pos.le] using hG_le n ω
  calc P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) - f y]
  _ ≤ (2 * η * n)⁻¹ * ‖x₀ - y‖ ^ 2 +
      (η / (2 * n)) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
    refine integral_apply_avg_le hf hdf ?_ h_unbiased hG_lp h h_int y n hn h_int_avg
    positivity
  _ ≤ (2 * η * n)⁻¹ * D ^ 2 + (η / 2) * L ^ 2 := by
    gcongr 1
    · gcongr
    · field_simp
      rw [mul_assoc]
      gcongr
      calc ∑ x ∈ range n, ∫ ω, ‖G x ω‖ ^ 2 ∂P
      _ ≤ ∑ x ∈ range n, ∫ ω, L ^ 2 ∂P := by
        gcongr with i hi
        · exact (hG_lp i).integrable_norm_pow (by simp)
        · simp
        intro ω
        simp only
        gcongr
        exact hG_le _ _
      _ = n * L ^ 2 := by simp
  _ = D * L / √n := by
    simp only [mul_inv_rev, inv_div, η]
    field_simp
    rw [Real.sq_sqrt (by positivity)]
    ring

end GradientStep

end Learning
