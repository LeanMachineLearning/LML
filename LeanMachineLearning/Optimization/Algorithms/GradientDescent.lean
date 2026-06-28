/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.OnlineRegret
public import LeanMachineLearning.Online.Projection
public import LeanMachineLearning.SequentialLearning.Deterministic
public import LeanMachineLearning.SequentialLearning.StationaryEnv

import LeanMachineLearning.ForMathlib.Analysis.Calculus.Deriv.Slope
import LeanMachineLearning.ForMathlib.MeasureTheory.Function.L2Space
import LeanMachineLearning.Online.OnlineToBatch

/-!
# Online and stochastic gradient descent

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset
open scoped Gradient ENNReal NNReal RealInnerProductSpace

namespace Learning

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {x x₀ : E} {X G : ℕ → Ω → E} {γ : ℕ → ℝ} {η : ℝ}

section Linear

lemma inner_eq_add (x y g : E) (hη : 0 < η) :
    ⟪x - y, g⟫ = (2 * η)⁻¹ * (‖x - y‖ ^ 2 - ‖(x - η • g) - y‖ ^ 2) + (η / 2) * ‖g‖ ^ 2 := by
  have hsub : (x - η • g) - y = (x - y) - η • g := by abel
  rw [hsub, norm_sub_sq_real (x - y) (η • g)]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  field

lemma inner_le_add_proj [FiniteDimensional ℝ E] {s : Set E} (h_closed : IsClosed s)
    (h_convex : Convex ℝ s) (h_nonempty : s.Nonempty) (x g : E) {y : E} (hy : y ∈ s) (hη : 0 < η) :
    ⟪x - y, g⟫ ≤ (2 * η)⁻¹ * (‖x - y‖ ^ 2 - ‖proj s (x - η • g) - y‖ ^ 2) + (η / 2) * ‖g‖ ^ 2 := by
  rw [inner_eq_add x y g hη]
  gcongr
  rw [← dist_eq_norm, ← dist_eq_norm]
  exact dist_proj_le h_closed h_convex h_nonempty (x - η • g) hy

lemma sum_inner_le_sum' (x y g : ℕ → E) (hγ : ∀ n, 0 < γ n) (n : ℕ) :
    ∑ i ∈ Finset.range n, ⟪x i - y i, g i⟫ ≤
      ∑ i ∈ Finset.range n,
        ((2 * γ i)⁻¹ * (‖x i - y i‖ ^ 2 - ‖(x i - γ i • g i) - y i‖ ^ 2) +
          (γ i / 2) * ‖g i‖ ^ 2) := by
  gcongr with i hi
  rw [inner_eq_add (x i) (y i) (g i) (hγ i)]

lemma sum_inner_le_sum (x g : ℕ → E) (y : E) (hγ : ∀ n, 0 < γ n)
    (hx : ∀ n, x (n + 1) = x n - γ n • g n) (n : ℕ) :
    ∑ i ∈ Finset.range n, ⟪x i - y, g i⟫ ≤
      ∑ i ∈ Finset.range n,
        ((2 * γ i)⁻¹ * (‖x i - y‖ ^ 2 - ‖x (i + 1) - y‖ ^ 2) + (γ i / 2) * ‖g i‖ ^ 2) :=
  (sum_inner_le_sum' x (fun _ ↦ y) g hγ n).trans_eq <| by simp [hx]

section ConstantStep

lemma sum_inner_le_add (x g : ℕ → E) (y : E)
    (hη : 0 < η) (hx : ∀ n, x (n + 1) = x n - η • g n) (n : ℕ) :
    ∑ i ∈ Finset.range n, ⟪x i - y, g i⟫ ≤
      (2 * η)⁻¹ * (‖x 0 - y‖ ^ 2 - ‖x n - y‖ ^ 2) + (η / 2) * ∑ i ∈ Finset.range n, ‖g i‖ ^ 2 := by
  refine (sum_inner_le_sum x g y (fun _ ↦ hη) hx n).trans_eq ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, Finset.sum_range_sub' (fun i ↦ ‖x i - y‖ ^ 2) n]

/-- Lemma 14.1 in Understanding Machine Learning: From Theory to Algorithms. -/
lemma gradient_descent_linear_regret (x g : ℕ → E) (y : E) (η : ℝ)
    (hη : 0 < η) (hx : ∀ n, x (n + 1) = x n - η • g n) (n : ℕ) :
    ∑ i ∈ Finset.range n, ⟪x i - y, g i⟫ ≤
      (2 * η)⁻¹ * ‖x 0 - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, ‖g i‖ ^ 2 := by
  grw [sum_inner_le_add x g y hη hx n]
  gcongr
  exact sub_le_self _ (sq_nonneg _)

end ConstantStep

lemma onlineRegret_gradientStep_le (x g : ℕ → E) (y : E) (η : ℝ)
    (hη : 0 < η) (hx : ∀ n, x (n + 1) = x n - η • g n) (n : ℕ) :
    onlineRegret (fun n x ↦ ⟪x, g n⟫) y x n ≤
      (2 * η)⁻¹ * ‖x 0 - y‖ ^ 2 + (η / 2) * ∑ i ∈ range n, ‖g i‖ ^ 2 := by
  simpa [onlineRegret, inner_sub_left] using gradient_descent_linear_regret x g y η hη hx n

end Linear

variable [SecondCountableTopology E] [CompleteSpace E] [BorelSpace E]
  {f : ℕ → E → ℝ} {hf : ∀ n, Measurable (∇ (f n))}

section Definition

variable {env : Environment E E}

/-- Online gradient descent with step sizes `γ : ℕ → ℝ` and initial point `x₀ : E`,
without projection.

It is an algorithm that chooses actions in `E` and gets feedback in `E` (gradient of the function at
the queried point).
The point `x (n + 1)` is defined as `x (n + 1) = x n - γ n • g n`, where `g n` is the feedback
received at step `n`.
Since the algorithm is expressed as a function of the history `hist : ℕ → Iic n → E × E`,
we write `(hist ⟨n, …⟩).1` for `x n` and `(hist ⟨n, …⟩).2` for `g n`. -/
noncomputable
def gradientStep (γ : ℕ → ℝ) (x₀ : E) : Algorithm E E :=
  let xn := fun (n : ℕ) (hist : Iic n → E × E) ↦ (hist ⟨n, by grind⟩).1
  let gn := fun (n : ℕ) (hist : Iic n → E × E) ↦ (hist ⟨n, by grind⟩).2
  detAlgorithm (fun n hist ↦ xn n hist - γ n • gn n hist) (by fun_prop) x₀

lemma action_gradientStep_ae_eq (h_seq : IsAlgEnvSeq X G (gradientStep γ x₀) env P) (n : ℕ) :
    X (n + 1) =ᵐ[P] X n - γ n • G n := h_seq.action_detAlgorithm_ae_eq n

lemma action_gradientStep_ae_all_eq (h_seq : IsAlgEnvSeq X G (gradientStep γ x₀) env P) :
    ∀ᵐ ω ∂P, X 0 ω = x₀ ∧ ∀ n, X (n + 1) ω = X n ω - γ n • G n ω :=
  h_seq.action_detAlgorithm_ae_all_eq

lemma action_ae_eq_sub_sum (h_seq : IsAlgEnvSeq X G (gradientStep γ x₀) env P) (n : ℕ) :
    X n =ᵐ[P] fun ω ↦ x₀ - ∑ i ∈ range n, γ i • G i ω := by
  filter_upwards [h_seq.action_detAlgorithm_ae_all_eq] with ω ⟨hω0, hω⟩
  induction n with
  | zero => simpa
  | succ n ih => rw [hω n, sum_range_succ, ← sub_sub]; congr

omit [SecondCountableTopology E] [CompleteSpace E] in
lemma measurable_proj [FiniteDimensional ℝ E] {s : Set E}
    (h_closed : IsClosed s) (h_convex : Convex ℝ s) (h_nonempty : s.Nonempty) :
  Measurable (proj s) := (continuous_proj h_closed h_convex h_nonempty).measurable

omit [SecondCountableTopology E] [CompleteSpace E] in
protected
lemma _root_.Measurable.proj [FiniteDimensional ℝ E] {s : Set E}
    (h_closed : IsClosed s) (h_convex : Convex ℝ s) (h_nonempty : s.Nonempty)
    {f : Ω → E} (hf : Measurable f) :
    Measurable (fun ω ↦ proj s (f ω)) :=
  (measurable_proj h_closed h_convex h_nonempty).comp hf

/-- Projected online gradient descent with step sizes `γ : ℕ → ℝ` and initial point `x₀ : E`.

It is an algorithm that chooses actions in `E` and gets feedback in `E` (gradient of the function at
the queried point).
The point `x (n + 1)` is defined as `x (n + 1) = proj s (x n - γ n • g n)`, where `g n` is
the feedback received at step `n` and `proj s` is the projection onto `s`.
Since the algorithm is expressed as a function of the history `hist : ℕ → Iic n → E × E`,
we write `(hist ⟨n, …⟩).1` for `x n` and `(hist ⟨n, …⟩).2` for `g n`. -/
noncomputable
def projGradStep [FiniteDimensional ℝ E] {s : Set E}
    (h_closed : IsClosed s) (h_convex : Convex ℝ s) (h_nonempty : s.Nonempty)
    (γ : ℕ → ℝ) (x₀ : E) : Algorithm E E :=
  let xn := fun (n : ℕ) (hist : Iic n → E × E) ↦ (hist ⟨n, by grind⟩).1
  let gn := fun (n : ℕ) (hist : Iic n → E × E) ↦ (hist ⟨n, by grind⟩).2
  detAlgorithm (fun n hist ↦ proj s (xn n hist - γ n • gn n hist))
    (fun _ ↦ Measurable.proj h_closed h_convex h_nonempty (by fun_prop)) x₀

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
    P[fun ω ↦ ∑ i ∈ range n, ⟪X i ω - y, G i ω⟫] ≤
      (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
  calc P[fun ω ↦ ∑ i ∈ range n, ⟪X i ω - y, G i ω⟫]
  _ ≤ ∫ ω, (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ range n, ‖G i ω‖ ^ 2 ∂P := by
    refine integral_mono_ae ?_ ?_ ?_
    · refine integrable_finsetSum _ fun i hi ↦ MemLp.integrable_inner ?_ (h_memLp i)
      exact (memLp_X h h_memLp i).sub (memLp_const _)
    · refine Integrable.add (integrable_const _) (Integrable.const_mul ?_ _)
      exact integrable_finsetSum _ fun i hi ↦ (h_memLp i).integrable_norm_pow (by simp)
    · filter_upwards [action_gradientStep_ae_all_eq h] with ω hω
      refine (gradient_descent_linear_regret _ _ y η hη hω.2 n).trans_eq ?_
      congr
      exact hω.1
  _ = (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
    rw [integral_add, integral_const_mul, integral_const_mul, integral_finsetSum]
    · simp
    · exact fun i hi ↦ (h_memLp i).integrable_norm_pow (by simp)
    · fun_prop
    · refine Integrable.const_mul ?_ _
      exact integrable_finsetSum _ fun i hi ↦ (h_memLp i).integrable_norm_pow (by simp)

end Linear

lemma integral_sum_sub_le (hf : ∀ n, ConvexOn ℝ .univ (f n)) (hdf : ∀ n, Differentiable ℝ (f n))
    (hη : 0 < η)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x) (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G (gradientStep (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (h_int : ∀ n, Integrable (fun ω ↦ f n (X n ω)) P) (y : E) (n : ℕ) :
    P[fun ω ↦ ∑ i ∈ range n, (f i (X i ω) - f i y)] ≤
      (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
  calc P[fun ω ↦ ∑ i ∈ range n, (f i (X i ω) - f i y)]
  _ ≤ P[fun ω ↦ ∑ i ∈ range n, ⟪X i ω - y, G i ω⟫] :=
    integral_sum_sub_le_integral_sum_inner hf hdf h_unbiased h_memLp h (memLp_X h h_memLp) h_int y n
  _ ≤ (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ range n, P[fun ω ↦ ‖G i ω‖ ^ 2] :=
    integral_sum_inner_le hη h_memLp h y n

lemma integral_onlineRegret_le
    (hf : ∀ n, ConvexOn ℝ .univ (f n)) (hdf : ∀ n, Differentiable ℝ (f n)) (hη : 0 < η)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x)
    (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G (gradientStep (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (h_int : ∀ n, Integrable (fun ω ↦ f n (X n ω)) P)
    (y : E) (n : ℕ) :
    P[fun ω ↦ onlineRegret f y (X · ω) n] ≤
      (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ range n, P[fun ω ↦ ‖G i ω‖ ^ 2] :=
  integral_sum_sub_le hf hdf hη h_unbiased h_memLp h h_int y n

lemma integral_apply_avg_le {f : E → ℝ} (hf : ConvexOn ℝ .univ f) (hdf : Differentiable ℝ f)
    (hη : 0 < η)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ f x)
    (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G (gradientStep (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (h_int : ∀ n, Integrable (fun ω ↦ f (X n ω)) P)
    (y : E) (n : ℕ) (hn : n ≠ 0)
    (h_int_avg : Integrable (fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ range n, X i ω)) P) :
    P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ range n, X i ω) - f y] ≤
      (2 * η * n)⁻¹ * ‖x₀ - y‖ ^ 2 +
      (η / (2 * n)) * ∑ i ∈ range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
  calc P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ range n, X i ω) - f y]
  _ ≤ (n : ℝ)⁻¹ * P[fun ω ↦ ∑ i ∈ range n, (f (X i ω) - f y)] := by
    rw [← integral_const_mul]
    gcongr
    · exact h_int_avg.sub (integrable_const _)
    · refine Integrable.const_mul (integrable_finsetSum _ fun i hi ↦ ?_) _
      exact (h_int i).sub (integrable_const _)
    exact fun ω ↦ hf.apply_avg_sub_le_avg_sub (by simp) y n hn
  _ ≤ (2 * η * n)⁻¹ * ‖x₀ - y‖ ^ 2 +
      (η / (2 * n)) * ∑ i ∈ range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
    grw [integral_sum_sub_le (fun _ ↦ hf) (fun _ ↦ hdf) hη h_unbiased h_memLp h h_int y n]
    refine le_of_eq ?_
    field

theorem integral_apply_avg_le_const_div_sqrt {f : E → ℝ}
    (hf : ConvexOn ℝ .univ f) (hdf : Differentiable ℝ f)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ f x)
    {D L : ℝ} (hD_pos : 0 < D) (hL_pos : 0 < L)
    {y : E} (hxy_le : ‖x₀ - y‖ ≤ D) (hG_le : ∀ n ω, ‖G n ω‖ ≤ L)
    (h_int : ∀ n, Integrable (fun ω ↦ f (X n ω)) P)
    {n : ℕ} (hn : n ≠ 0)
    (h_int_avg : Integrable (fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ range n, X i ω)) P)
    (h : IsAlgEnvSeq X G (gradientStep (fun _ ↦ D / (L * √n)) x₀) (obliviousEnv gradKernel) P) :
    P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ range n, X i ω) - f y] ≤ D * L / √n := by
  let η := D / (L * √n)
  have hG_lp n : MemLp (G n) 2 P := by
    refine MemLp.mono (g := fun _ ↦ L) (memLp_const _)
      (have := h.measurable_feedback; by fun_prop) (ae_of_all _ fun ω ↦ ?_)
    simpa [abs_of_nonneg hL_pos.le] using hG_le n ω
  calc P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ range n, X i ω) - f y]
  _ ≤ (2 * η * n)⁻¹ * ‖x₀ - y‖ ^ 2 +
      (η / (2 * n)) * ∑ i ∈ range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
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
