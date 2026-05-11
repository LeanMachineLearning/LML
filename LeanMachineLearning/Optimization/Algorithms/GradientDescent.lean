/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.MeasureTheory.Function.ConditionalExpectation.PullOut
public import LeanMachineLearning.MeasureTheory.Function.L2Space
public import LeanMachineLearning.SequentialLearning.Deterministic
public import LeanMachineLearning.SequentialLearning.EvaluationEnv
public import Mathlib

/-!
# Online gradient descent

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset
open scoped Gradient ENNReal NNReal RealInnerProductSpace

namespace Learning

variable {E Ω : Type*} {mE : MeasurableSpace E} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
  [MeasurableSub₂ E] {x x₀ : E}
  {g : ℕ → E → E} {hg : ∀ n, Measurable (g n)}
  {env : Environment E E}
  {X G : ℕ → Ω → E} {γ : ℕ → ℝ} {η : ℝ}

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

section Convex

lemma _root_.ConvexOn.fderiv_sub_le_sub {f : E → ℝ} (hf : ConvexOn ℝ .univ f)
    (hfx : DifferentiableAt ℝ f x) (y : E) :
    fderiv ℝ f x (y - x) ≤ f y - f x := by
  have h_convex t (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      f (x + t • (y - x)) ≤ t * f y + (1 - t) * f x := by
    have h1 : x + t • (y - x) = (1 - t) • x + t • y := by module
    have h2 : f ((1 - t) • x + t • y) ≤ (1 - t) • f x + t • f y :=
      hf.2 (Set.mem_univ x) (Set.mem_univ y) (by grind) (by grind) (by simp)
    simp only [smul_eq_mul] at h2
    grind
  have h_path_deriv : HasDerivAt (fun t : ℝ ↦ f (x + t • (y - x)))
      (fderiv ℝ f x (y - x)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ ↦ x + t • (y - x)) (y - x) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (y - x)
    have h2 : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • (y - x)) := by
      simpa using hfx.hasFDerivAt
    exact h2.comp_hasDerivAt _ h1
  refine le_of_tendsto h_path_deriv.tendsto_slope_zero_right (Filter.eventually_of_mem
    (Ioo_mem_nhdsGT_of_mem ⟨le_rfl, zero_lt_one⟩) fun t ht ↦ ?_)
  simp [inv_mul_le_iff₀ ht.1]
  grind

lemma _root_.ConvexOn.add_fderiv_le {f : E → ℝ} (hf : ConvexOn ℝ .univ f)
    (hfx : DifferentiableAt ℝ f x) (y : E) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  suffices fderiv ℝ f x (y - x) ≤ f y - f x by grind
  exact hf.fderiv_sub_le_sub hfx y

lemma _root_.ConvexOn.add_inner_gradient_le [CompleteSpace E] {f : E → ℝ} (hf : ConvexOn ℝ .univ f)
    (hfx : DifferentiableAt ℝ f x) (y : E) :
    f x + ⟪y - x, ∇ f x⟫ ≤ f y := by
  have hfderiv : (fderiv ℝ f x) (y - x) = ⟪y - x, ∇ f x⟫ := by
    simp [gradient, ← InnerProductSpace.toDual_symm_apply, real_inner_comm]
  rw [← hfderiv]
  exact hf.add_fderiv_le hfx y

lemma _root_.ConvexOn.le_add_inner_gradient [CompleteSpace E] {f : E → ℝ} (hf : ConvexOn ℝ .univ f)
    (hfx : DifferentiableAt ℝ f x) (y : E) :
    f x ≤ f y + ⟪x - y, ∇ f x⟫ := by
  have h_add_le := hf.add_inner_gradient_le hfx y
  have h_neg : ⟪x - y, ∇ f x⟫ = -⟪y - x, ∇ f x⟫ := by
    rw [show x - y = -(y - x) by abel, inner_neg_left]
  grind

lemma _root_.ConvexOn.sub_le_inner_gradient [CompleteSpace E] {f : E → ℝ} (hf : ConvexOn ℝ .univ f)
    (hfx : DifferentiableAt ℝ f x) (y : E) :
    f x - f y ≤ ⟪x - y, ∇ f x⟫ := by
  simp only [tsub_le_iff_right]
  rw [add_comm]
  exact hf.le_add_inner_gradient hfx y

lemma todo'3 {f : E → ℝ} (hf : ConvexOn ℝ .univ f)
    (x : ℕ → E) (y : E) (n : ℕ) (hn : n ≠ 0) :
    f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y ≤ (n : ℝ)⁻¹ • ∑ i ∈ range n, (f (x i) - f y) := by
  calc f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y
  _ ≤ (n : ℝ)⁻¹ • ∑ i ∈ range n, f (x i) - f y := by
    simp_rw [smul_sum]
    grw [hf.map_sum_le (fun _ _ ↦ by positivity) (by simp; field) (by simp)]
  _ = (n : ℝ)⁻¹ * ∑ i ∈ range n, (f (x i) - f y) := by
    simp_rw [smul_eq_mul, mul_sum, mul_sub, sum_sub_distrib]
    rw [← sum_mul]
    simp
    field

lemma todo'2 [CompleteSpace E] {f : E → ℝ} (hf : ConvexOn ℝ .univ f) (hdf : Differentiable ℝ f)
    (x : ℕ → E) (y : E) (n : ℕ) (hn : n ≠ 0) :
    f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, ⟪x i - y, ∇ f (x i)⟫ := by
  calc f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y
  _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, (f (x i) - f y) := todo'3 hf x y n hn
  _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, ⟪x i - y, ∇ f (x i)⟫ := by
    gcongr
    exact hf.sub_le_inner_gradient hdf.differentiableAt y

end Convex

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
  todo'3 hf x y n hn

lemma onlineRegret_gradientStep_le (x g : ℕ → E) (y : E) (η : ℝ)
    (hη : 0 < η) (hx : ∀ n, x (n + 1) = x n - η • g n) (n : ℕ) :
    onlineRegret (fun n x ↦ ⟪x, g n⟫) y x n ≤
      (2 * η)⁻¹ * ‖x 0 - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, ‖g i‖ ^ 2 := by
  simpa [onlineRegret, inner_sub_left] using lem14dot1 x g y η hη hx n

end OnlineRegret

variable [SecondCountableTopology E] [CompleteSpace E]
  {f : ℕ → E → ℝ} {hf : ∀ n, Measurable (∇ (f n))}

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

omit [SecondCountableTopology E] in
lemma apply_avg_sub_le_onlineRegret_linearizedLoss {f : E → ℝ}
    (hf : ConvexOn ℝ .univ f) (hdf : Differentiable ℝ f)
    (x : ℕ → E) (y : E) (n : ℕ) (hn : n ≠ 0) :
    f ((n : ℝ)⁻¹ • ∑ i ∈ range n, x i) - f y ≤
      (n : ℝ)⁻¹ * (onlineRegret (linearizedLoss (fun _ ↦ f) x) y x n) := by
  simpa [onlineRegret, linearizedLoss, ← inner_sub_left] using todo'2 hf hdf x y n hn

section Stochastic

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

omit [MeasurableSub₂ E] in
lemma memLp_gradient {alg : Algorithm E E}
    (h : IsAlgEnvSeq X G alg (obliviousEnv gradKernel) P)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x)
    (h_memLp : ∀ n, MemLp (G n) 2 P) (n : ℕ) :
    MemLp (fun ω ↦ ∇ (f n) (X n ω)) 2 P := by
  let M n := MeasurableSpace.comap (X n) inferInstance
  have h_lp : MemLp P[G n | M n] 2 P := (h_memLp n).condExp (m := M n)
  have h_ae := h.condExp_feedback_obliviousEnv_ae_eq_integral_id n
      ((h_memLp n).integrable (by simp))
  refine h_lp.ae_eq <| h_ae.trans ?_
  simp_rw [← h_unbiased]
  rfl

section Linear

lemma qsfqqfqgs'' (hη : 0 < η) (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G (gradientStep (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (y : E) (n : ℕ) :
    P[fun ω ↦ ∑ i ∈ Finset.range n, ⟪X i ω - y, G i ω⟫] ≤
      (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
  calc P[fun ω ↦ ∑ i ∈ Finset.range n, ⟪X i ω - y, G i ω⟫]
  _ ≤ ∫ ω, (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, ‖G i ω‖ ^ 2 ∂P := by
    refine integral_mono_ae ?_ ?_ ?_
    · refine integrable_finset_sum _ fun i hi ↦ MemLp.integrable_inner ?_ (h_memLp i)
      exact (memLp_X h h_memLp i).sub (memLp_const _)
    · refine Integrable.add (integrable_const _) (Integrable.const_mul ?_ _)
      exact integrable_finset_sum _ fun i hi ↦ (h_memLp i).integrable_norm_pow (by simp)
    · filter_upwards [action_gradientStep_ae_all_eq h] with ω hω
      refine (lem14dot1 _ _ y η hη hω.2 n).trans_eq ?_
      congr
      exact hω.1
  _ = (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
    rw [integral_add, integral_const_mul, integral_const_mul, integral_finset_sum]
    · simp
    · exact fun i hi ↦ (h_memLp i).integrable_norm_pow (by simp)
    · exact integrable_const _
    · refine Integrable.const_mul ?_ _
      exact integrable_finset_sum _ fun i hi ↦ (h_memLp i).integrable_norm_pow (by simp)

end Linear

section OnlineToBatch

variable {alg : Algorithm E E}

omit [MeasurableSub₂ E] in
lemma sfdsf (h : IsAlgEnvSeq X G alg (obliviousEnv gradKernel) P)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x) (h_memLp : ∀ n, MemLp (G n) 2 P)
    (hX_lp : ∀ n, MemLp (X n) 2 P) (y : E) (n : ℕ) :
    P[fun ω ↦ ⟪X n ω - y, G n ω⟫] = P[fun ω ↦ ⟪X n ω - y, ∇ (f n) (X n ω)⟫] := by
  let M n := MeasurableSpace.comap (X n) inferInstance
  have h_obl : HasCondDistrib (G n) (X n) (gradKernel n) P :=
    h.hasCondDistrib_feedback_obliviousEnv n
  calc P[fun ω ↦ ⟪X n ω - y, G n ω⟫]
  _ = P[fun ω ↦ P[fun ω' ↦ ⟪X n ω' - y, G n ω'⟫ | M n] ω] := by
    rw [integral_condExp (h.measurable_action _).comap_le]
  _ = P[fun ω ↦ ⟪X n ω - y, P[G n | M n] ω⟫] := by
    refine integral_congr_ae ?_
    refine condExp_inner_of_stronglyMeasurable_left ?_ ?_ ?_
    · refine StronglyMeasurable.sub ?_ (by fun_prop)
      refine Measurable.stronglyMeasurable ?_
      rw [measurable_iff_comap_le]
    · exact MemLp.integrable_inner ((hX_lp n).sub (memLp_const _)) (h_memLp n)
    · exact (h_memLp n).integrable (by simp)
  _ = P[fun ω ↦ ⟪X n ω - y, (gradKernel n (X n ω))[id]⟫] := by
    have h_ae := h.condExp_feedback_obliviousEnv_ae_eq_integral_id n
      ((h_memLp n).integrable (by simp))
    refine integral_congr_ae ?_
    filter_upwards [h_ae] with ω hω using by rw [hω]
  _ = P[fun ω ↦ ⟪X n ω - y, ∇ (f n) (X n ω)⟫] := by simp_rw [h_unbiased n]

omit [MeasurableSub₂ E] in
lemma qfqgs (hf : ∀ n, ConvexOn ℝ .univ (f n)) (hdf : ∀ n, Differentiable ℝ (f n))
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x) (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G alg (obliviousEnv gradKernel) P)
    (hX_lp : ∀ n, MemLp (X n) 2 P)
    (h_int : ∀ n, Integrable (fun ω ↦ f n (X n ω)) P) -- todo: discuss this assumption
    (y : E) (n : ℕ) :
    P[fun ω ↦ f n (X n ω) - f n y] ≤ P[fun ω ↦ ⟪X n ω - y, G n ω⟫] := by
  rw [sfdsf h h_unbiased h_memLp hX_lp y n]
  gcongr
  · exact (h_int n).sub (integrable_const _)
  · refine MemLp.integrable_inner ?_ ?_
    · exact (hX_lp n).sub (memLp_const _)
    · exact memLp_gradient h h_unbiased h_memLp n
  · exact fun ω ↦ (hf n).sub_le_inner_gradient (hdf n).differentiableAt y

omit [MeasurableSub₂ E] in
lemma qsfqqfqgs' (hf : ∀ n, ConvexOn ℝ .univ (f n)) (hdf : ∀ n, Differentiable ℝ (f n))
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x)
    (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G alg (obliviousEnv gradKernel) P)
    (hX_lp : ∀ n, MemLp (X n) 2 P)
    (h_int : ∀ n, Integrable (fun ω ↦ f n (X n ω)) P)
    (y : E) (n : ℕ) :
    P[fun ω ↦ ∑ i ∈ Finset.range n, (f i (X i ω) - f i y)] ≤
      P[fun ω ↦ ∑ i ∈ Finset.range n, ⟪X i ω - y, G i ω⟫] := by
  rw [integral_finset_sum, integral_finset_sum]
  rotate_left
  · refine fun i hi ↦ MemLp.integrable_inner ?_ (h_memLp i)
    exact (hX_lp i).sub (memLp_const _)
  · exact fun i hi ↦ (h_int i).sub (integrable_const _)
  refine Finset.sum_le_sum fun i hi ↦ ?_
  exact qfqgs hf hdf h_unbiased h_memLp h hX_lp h_int y i

omit [MeasurableSub₂ E] in
lemma qsfqqfqgs'''' {f : E → ℝ} (hf : ConvexOn ℝ .univ f) (hdf : Differentiable ℝ f)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ f x)
    (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G alg (obliviousEnv gradKernel) P)
    (hX_lp : ∀ n, MemLp (X n) 2 P)
    (h_int : ∀ n, Integrable (fun ω ↦ f (X n ω)) P)
    (y : E) (n : ℕ) (hn : n ≠ 0)
    (h_int_avg : Integrable (fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)) P) :
    P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) - f y] ≤
      (n : ℝ)⁻¹ * P[fun ω ↦ ∑ i ∈ Finset.range n, ⟪X i ω - y, G i ω⟫] := by
  calc P[fun ω ↦ f ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) - f y]
  _ ≤ (n : ℝ)⁻¹ * P[fun ω ↦ ∑ i ∈ Finset.range n, (f (X i ω) - f y)] := by
    rw [← integral_const_mul]
    gcongr
    · exact h_int_avg.sub (integrable_const _)
    · refine Integrable.const_mul (integrable_finset_sum _ fun i hi ↦ ?_) _
      exact (h_int i).sub (integrable_const _)
    exact fun ω ↦ todo'3 hf _ y n hn
  _ ≤ (n : ℝ)⁻¹ * P[fun ω ↦ ∑ i ∈ Finset.range n, ⟪X i ω - y, G i ω⟫] := by
    grw [qsfqqfqgs' (fun _ ↦ hf) (fun _ ↦ hdf) h_unbiased h_memLp h hX_lp h_int y n]

end OnlineToBatch

lemma qsfqqfqgs (hf : ∀ n, ConvexOn ℝ .univ (f n)) (hdf : ∀ n, Differentiable ℝ (f n)) (hη : 0 < η)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x)
    (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G (gradientStep (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (h_int : ∀ n, Integrable (fun ω ↦ f n (X n ω)) P)
    (y : E) (n : ℕ) :
    P[fun ω ↦ ∑ i ∈ Finset.range n, (f i (X i ω) - f i y)] ≤
      (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
  calc P[fun ω ↦ ∑ i ∈ Finset.range n, (f i (X i ω) - f i y)]
  _ ≤ P[fun ω ↦ ∑ i ∈ Finset.range n, ⟪X i ω - y, G i ω⟫] :=
    qsfqqfqgs' hf hdf h_unbiased h_memLp h (memLp_X h h_memLp) h_int y n
  _ ≤ (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] :=
    qsfqqfqgs'' hη h_memLp h y n

lemma integral_onlineRegret_le
    (hf : ∀ n, ConvexOn ℝ .univ (f n)) (hdf : ∀ n, Differentiable ℝ (f n)) (hη : 0 < η)
    (h_unbiased : ∀ n x, (gradKernel n x)[id] = ∇ (f n) x)
    (h_memLp : ∀ n, MemLp (G n) 2 P)
    (h : IsAlgEnvSeq X G (gradientStep (fun _ ↦ η) x₀) (obliviousEnv gradKernel) P)
    (h_int : ∀ n, Integrable (fun ω ↦ f n (X n ω)) P)
    (y : E) (n : ℕ) :
    P[fun ω ↦ onlineRegret f y (X · ω) n] ≤
      (2 * η)⁻¹ * ‖x₀ - y‖ ^ 2 + (η / 2) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] :=
  qsfqqfqgs hf hdf hη h_unbiased h_memLp h h_int y n

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
    · refine Integrable.const_mul (integrable_finset_sum _ fun i hi ↦ ?_) _
      exact (h_int i).sub (integrable_const _)
    exact fun ω ↦ todo'3 hf _ y n hn
  _ ≤ (2 * η * n)⁻¹ * ‖x₀ - y‖ ^ 2 +
      (η / (2 * n)) * ∑ i ∈ Finset.range n, P[fun ω ↦ ‖G i ω‖ ^ 2] := by
    grw [qsfqqfqgs (fun _ ↦ hf) (fun _ ↦ hdf) hη h_unbiased h_memLp h h_int y n]
    refine le_of_eq ?_
    field

end Stochastic

end Learning
