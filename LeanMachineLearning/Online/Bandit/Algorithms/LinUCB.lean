/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Fawad Haider
-/
module

public import LeanMachineLearning.Online.Bandit.SumRewards
public import LeanMachineLearning.SequentialLearning.Deterministic
public import LeanMachineLearning.MeasureTheory.Constructions.BorelSpace.MeasurableArgMax
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# LinUCB for finite-action linear bandits
Chapter 19 of *Bandit Algorithms*:
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset Learning

open scoped ENNReal NNReal Matrix

namespace Bandits

variable {K d : ℕ}

section Algorithm

namespace LinUCB

/-- Feature vectors for finite-dimensional linear bandits. -/
abbrev Feature (d : ℕ) := Fin d → ℝ

/-- Squared Euclidean norm of a finite-action feature vector, written as the dot product
`x_aᵀ x_a`. -/
def featureSqNorm (x : Fin K → Feature d) (a : Fin K) : ℝ :=
  dotProduct (x a) (x a)

/-- The squared feature norm is nonnegative. -/
lemma featureSqNorm_nonneg (x : Fin K → Feature d) (a : Fin K) :
    0 ≤ featureSqNorm x a := by
  rw [featureSqNorm, dotProduct]
  exact sum_nonneg fun i _ ↦ mul_self_nonneg (x a i)

/-- History-level regularized design matrix for LinUCB. -/
noncomputable def designMatrix' (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) (h : Iic n → Fin K × ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  reg • 1 + ∑ s : Iic n, Matrix.vecMulVec (x (h s).1) (x (h s).1)

/-- History-level response vector for LinUCB. -/
noncomputable def responseVector' (x : Fin K → Feature d)
    (n : ℕ) (h : Iic n → Fin K × ℝ) : Feature d :=
  ∑ s : Iic n, (h s).2 • x (h s).1

/-- History-level regularized least-squares estimate. -/
noncomputable def thetaHat' (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) (h : Iic n → Fin K × ℝ) : Feature d :=
  Matrix.mulVec (designMatrix' reg x n h)⁻¹ (responseVector' x n h)

/-- History-level estimated reward of an arm. -/
noncomputable def estimatedReward' (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) (h : Iic n → Fin K × ℝ) (a : Fin K) : ℝ :=
  dotProduct (thetaHat' reg x n h) (x a)

/-- History-level quadratic form underlying the LinUCB confidence width. -/
noncomputable def widthQuadraticForm' (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) (h : Iic n → Fin K × ℝ) (a : Fin K) : ℝ :=
  dotProduct (x a) (Matrix.mulVec (designMatrix' reg x n h)⁻¹ (x a))

/-- History-level elliptical confidence width of an arm. -/
noncomputable def width' (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) (h : Iic n → Fin K × ℝ) (a : Fin K) : ℝ :=
  √(widthQuadraticForm' reg x n h a)

/-- Squaring the history-level LinUCB width recovers its quadratic form, provided that quadratic
form is nonnegative. -/
lemma width'_sq_eq_quadratic_form (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) (h : Iic n → Fin K × ℝ) (a : Fin K)
    (h_nonneg : 0 ≤ widthQuadraticForm' reg x n h a) :
    width' reg x n h a ^ 2 = widthQuadraticForm' reg x n h a := by
  simp [width', Real.sq_sqrt h_nonneg]

/-- LinUCB optimistic index of an arm.

The parameter `β` is a confidence-radius schedule. Since `h : Iic n → Fin K × ℝ`
contains the observations through time `n`, this index is used to choose the arm
at time `n + 1`, and we evaluate the schedule at `n + 2`
-/
noncomputable def index' (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d)
    (n : ℕ) (h : Iic n → Fin K × ℝ) (a : Fin K) : ℝ :=
  estimatedReward' reg x n h a + √(β (n + 2)) * width' reg x n h a

open Classical in
/-- Arm pulled by finite-action LinUCB at time `n + 1`. -/
noncomputable def nextArm (hK : 0 < K) (reg : ℝ) (β : ℕ → ℝ)
    (x : Fin K → Feature d)
    (n : ℕ) (h : Iic n → Fin K × ℝ) : Fin K :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  measurableArgmax (fun h a ↦ index' reg β x n h a) h

@[fun_prop]
lemma measurable_nextArm (hK : 0 < K) (reg : ℝ) (β : ℕ → ℝ)
    (x : Fin K → Feature d)
    (h_index : ∀ n a, Measurable (fun h ↦ index' reg β x n h a))
    (n : ℕ) :
    Measurable (nextArm hK reg β x n) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact measurable_measurableArgmax fun a ↦ h_index n a

end LinUCB

/-- The finite-action LinUCB algorithm. -/
noncomputable def linUCBAlgorithm (hK : 0 < K) (reg : ℝ) (β : ℕ → ℝ)
    (x : Fin K → LinUCB.Feature d)
    (h_index : ∀ n a, Measurable (fun h ↦ LinUCB.index' reg β x n h a)) :
    Algorithm (Fin K) ℝ :=
  detAlgorithm (LinUCB.nextArm hK reg β x) (by fun_prop) ⟨0, hK⟩

end Algorithm

namespace LinUCB

variable {hK : 0 < K} {reg : ℝ} {β : ℕ → ℝ} {x : Fin K → Feature d}
  {h_index : ∀ n a, Measurable (fun h ↦ index' reg β x n h a)}
  {ν : Kernel (Fin K) ℝ} [IsMarkovKernel ν]
  {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
  {n : ℕ} {ω : Ω}

section AlgorithmBehavior

/-- The process-level design matrix built from actions up to time `n` excluded. -/
noncomputable def designMatrix (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  reg • 1 + ∑ s ∈ range n, Matrix.vecMulVec (x (A s ω)) (x (A s ω))

/-- The initial design matrix before any actions are included. -/
lemma designMatrix_zero (reg : ℝ) (x : Fin K → Feature d) (ω : Ω) :
    designMatrix A reg x 0 ω = reg • 1 := by
  simp [designMatrix]

/-- The design matrix update after observing one additional action. -/
lemma designMatrix_succ (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) :
    designMatrix A reg x (n + 1) ω =
      designMatrix A reg x n ω + Matrix.vecMulVec (x (A n ω)) (x (A n ω)) := by
  simp [designMatrix, sum_range_succ, add_assoc]

/-- With nonnegative regularization, the process-level design matrix is positive semidefinite. -/
lemma designMatrix_posSemidef (hreg_nonneg : 0 ≤ reg) :
    (designMatrix A reg x n ω).PosSemidef := by
  unfold designMatrix
  apply Matrix.PosSemidef.add
  · exact Matrix.PosSemidef.smul Matrix.PosSemidef.one hreg_nonneg
  · refine Matrix.posSemidef_sum (s := range n) ?_
    intro t _
    simpa using Matrix.posSemidef_vecMulVec_self_star (x (A t ω))

/-- Positive regularization makes the process-level design matrix positive definite. -/
lemma designMatrix_posDef (hreg_pos : 0 < reg) :
    (designMatrix A reg x n ω).PosDef := by
  unfold designMatrix
  apply Matrix.PosDef.add_posSemidef
  · exact Matrix.PosDef.smul Matrix.PosDef.one hreg_pos
  · refine Matrix.posSemidef_sum (s := range n) ?_
    intro t _
    simpa using Matrix.posSemidef_vecMulVec_self_star (x (A t ω))

/-- Trace of the process-level regularized design matrix. -/
noncomputable def designTrace (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  Matrix.trace (designMatrix A reg x n ω)

/-- Before any observations, the design trace is the trace of `reg • I_d`, namely `reg * d`. -/
lemma designTrace_zero (reg : ℝ) (x : Fin K → Feature d) (ω : Ω) :
    designTrace A reg x 0 ω = reg * (d : ℝ) := by
  simp [designTrace, designMatrix_zero]

/-- Updating the design matrix by `x_a x_aᵀ` increases the trace by `x_aᵀ x_a`. -/
lemma designTrace_succ (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) :
    designTrace A reg x (n + 1) ω =
      designTrace A reg x n ω + featureSqNorm x (A n ω) := by
  simp [designTrace, designMatrix_succ, featureSqNorm, Matrix.trace_vecMulVec]

/-- Closed form for the design trace: initial regularization trace plus accumulated squared
feature norms. -/
lemma designTrace_eq_reg_mul_dim_add_sum_featureSqNorm
    (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) :
    designTrace A reg x n ω =
      reg * (d : ℝ) + ∑ t ∈ range n, featureSqNorm x (A t ω) := by
  simp [designTrace, designMatrix, featureSqNorm, Matrix.trace_vecMulVec]

/-- With nonnegative regularization, the design trace is nonnegative. -/
lemma designTrace_nonneg (hreg_nonneg : 0 ≤ reg) :
    0 ≤ designTrace A reg x n ω := by
  rw [designTrace_eq_reg_mul_dim_add_sum_featureSqNorm]
  exact add_nonneg
    (mul_nonneg hreg_nonneg (Nat.cast_nonneg d))
    (sum_nonneg fun t _ ↦ featureSqNorm_nonneg x (A t ω))

/-- If every selected feature vector has squared norm at most `L2`, then the trace of the design
matrix is at most `reg * d + n * L2`. -/
lemma designTrace_le_reg_mul_dim_add_nat_mul_featureSqNorm_bound
    (L2 : ℝ)
    (hL2 : ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ L2) :
    designTrace A reg x n ω ≤ reg * (d : ℝ) + (n : ℝ) * L2 := by
  rw [designTrace_eq_reg_mul_dim_add_sum_featureSqNorm]
  gcongr
  calc
    (∑ t ∈ range n, featureSqNorm x (A t ω)) ≤ ∑ _t ∈ range n, L2 := by
      exact sum_le_sum fun t ht ↦ hL2 t ht
    _ = (n : ℝ) * L2 := by
      simp [nsmul_eq_mul]

omit [IsProbabilityMeasure P] in
/-- Almost surely, bounded selected feature norms give the corresponding deterministic trace
budget `reg * d + n * L2`. -/
lemma designTrace_ae_le_reg_mul_dim_add_nat_mul_featureSqNorm_bound
    (L2 : ℝ)
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ L2) :
    ∀ᵐ ω ∂P, designTrace A reg x n ω ≤ reg * (d : ℝ) + (n : ℝ) * L2 := by
  filter_upwards [hL2] with ω hL2ω
  exact designTrace_le_reg_mul_dim_add_nat_mul_featureSqNorm_bound (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) L2 hL2ω

/-- The process-level reward-feature vector built from history up to time `n` excluded. -/
noncomputable def responseVector (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : Feature d :=
  ∑ s ∈ range n, R s ω • x (A s ω)

/-- The initial response vector before any rewards are included. -/
lemma responseVector_zero (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (x : Fin K → Feature d) (ω : Ω) :
    responseVector A R x 0 ω = 0 := by
  simp [responseVector]

/-- The response-vector update after observing one additional reward. -/
lemma responseVector_succ (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) :
    responseVector A R x (n + 1) ω =
      responseVector A R x n ω + R n ω • x (A n ω) := by
  simp [responseVector, sum_range_succ]

/-- The process-level regularized least-squares estimate. -/
noncomputable def thetaHat (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : Feature d :=
  Matrix.mulVec (designMatrix A reg x n ω)⁻¹ (responseVector A R x n ω)

/-- The initial least-squares estimate is zero because no reward-feature observations have been
included yet. -/
lemma thetaHat_zero (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (ω : Ω) :
    thetaHat A R reg x 0 ω = 0 := by
  simp [thetaHat, responseVector_zero]

/-- The process-level estimated linear reward. -/
noncomputable def estimatedReward (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (a : Fin K) (n : ℕ) (ω : Ω) : ℝ :=
  dotProduct (thetaHat A R reg x n ω) (x a)

/-- The initial estimated reward is zero for every arm. -/
lemma estimatedReward_zero (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (a : Fin K) (ω : Ω) :
    estimatedReward A R reg x a 0 ω = 0 := by
  simp [estimatedReward, thetaHat_zero]

/-- The quadratic form `x_aᵀ V_n⁻¹ x_a` underlying the LinUCB confidence width. -/
noncomputable def widthQuadraticForm (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (a : Fin K) (n : ℕ) (ω : Ω) : ℝ :=
  dotProduct (x a) (Matrix.mulVec (designMatrix A reg x n ω)⁻¹ (x a))

/-- The initial width quadratic form is induced by the inverse regularized identity. -/
lemma widthQuadraticForm_zero (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (a : Fin K) (ω : Ω) :
    widthQuadraticForm A reg x a 0 ω =
      dotProduct (x a) (Matrix.mulVec (reg • 1)⁻¹ (x a)) := by
  simp [widthQuadraticForm, designMatrix_zero]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Nonnegative regularization makes every LinUCB width quadratic form nonnegative.

The reason is purely matrix-theoretic: `V_n` is positive semidefinite, the nonsingular inverse of a
positive semidefinite matrix is positive semidefinite in mathlib, and every quadratic form induced
by a positive semidefinite matrix is nonnegative. -/
lemma widthQuadraticForm_nonneg_of_reg_nonneg
    (hreg_nonneg : 0 ≤ reg) (a : Fin K) :
    0 ≤ widthQuadraticForm A reg x a n ω := by
  simpa [widthQuadraticForm] using
    ((designMatrix_posSemidef (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
      hreg_nonneg).inv.dotProduct_mulVec_nonneg (x a))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, nonnegative regularization gives nonnegative selected quadratic width forms
through any finite horizon. -/
lemma widthQuadraticForm_ae_nonneg_of_reg_nonneg
    (hreg_nonneg : 0 ≤ reg) :
    ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω := by
  exact Filter.Eventually.of_forall fun ω t _ht ↦
    widthQuadraticForm_nonneg_of_reg_nonneg (A := A) (reg := reg) (x := x)
      (n := t) (ω := ω) hreg_nonneg (A t ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Positive-time version of `widthQuadraticForm_ae_nonneg_of_reg_nonneg`, matching the side
condition shape used by the regret/width-sum bridge lemmas. -/
lemma widthQuadraticForm_ae_pos_time_nonneg_of_reg_nonneg
    (hreg_nonneg : 0 ≤ reg) :
    ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω := by
  filter_upwards [widthQuadraticForm_ae_nonneg_of_reg_nonneg (A := A) (reg := reg)
    (x := x) (n := n) (P := P) hreg_nonneg] with ω h_nonnegω
  intro t ht _ht0
  exact h_nonnegω t ht

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The matrix comparison needed to turn bounded feature vectors into the positive-time LinUCB
width cap.

Mathematically, this says `x_aᵀ V_t⁻¹ x_a ≤ ‖x_a‖² / reg`. A later matrix-order proof should
derive it from `reg > 0` and `V_t = reg I + ∑ x_s x_sᵀ`. Keeping it as a named property makes the
remaining linear-algebra obligation precise and reusable. -/
def WidthQuadraticFormLeFeatureSqNormDivReg
    (A : ℕ → Ω → Fin K) (reg : ℝ) (x : Fin K → Feature d) : Prop :=
  ∀ (a : Fin K) (n : ℕ) (ω : Ω),
    widthQuadraticForm A reg x a n ω ≤ featureSqNorm x a / reg

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If `x_aᵀ V_n⁻¹ x_a ≤ ‖x_a‖² / reg` and the squared feature norm is at most `reg`, then the
quadratic form is at most one. -/
lemma widthQuadraticForm_le_one_of_featureSqNorm_le_reg
    (a : Fin K)
    (h_width : WidthQuadraticFormLeFeatureSqNormDivReg A reg x)
    (hreg_pos : 0 < reg)
    (h_feature_le : featureSqNorm x a ≤ reg) :
    widthQuadraticForm A reg x a n ω ≤ 1 := by
  refine (h_width a n ω).trans ?_
  rwa [div_le_one hreg_pos]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost-sure positive-time width cap from the matrix comparison and an almost-sure
`featureSqNorm ≤ reg` bound along the selected actions. -/
lemma widthQuadraticForm_ae_le_one_of_featureSqNorm_ae_le_reg
    (h_width : WidthQuadraticFormLeFeatureSqNormDivReg A reg x)
    (hreg_pos : 0 < reg)
    (h_feature_le : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ reg) :
    ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1 := by
  filter_upwards [h_feature_le] with ω h_feature_leω
  intro t ht _ht0
  exact widthQuadraticForm_le_one_of_featureSqNorm_le_reg
    (A := A) (reg := reg) (x := x) (n := t) (ω := ω) (A t ω) h_width hreg_pos
    (h_feature_leω t ht)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost-sure positive-time width cap from the matrix comparison and a selected-feature budget
`featureSqNorm ≤ L2`, when `L2 ≤ reg`. -/
lemma widthQuadraticForm_ae_le_one_of_featureSqNorm_ae_le
    (h_width : WidthQuadraticFormLeFeatureSqNormDivReg A reg x)
    (hreg_pos : 0 < reg) {L2 : ℝ}
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ L2)
    (hL2_le_reg : L2 ≤ reg) :
    ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1 := by
  refine widthQuadraticForm_ae_le_one_of_featureSqNorm_ae_le_reg
    (A := A) (reg := reg) (x := x) (n := n) (P := P) h_width hreg_pos ?_
  filter_upwards [hL2] with ω hL2ω
  intro t ht
  exact (hL2ω t ht).trans hL2_le_reg

/-- The process-level elliptical confidence width. -/
noncomputable def width (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (a : Fin K) (n : ℕ) (ω : Ω) : ℝ :=
  √(widthQuadraticForm A reg x a n ω)

/-- The initial width is the quadratic form induced by the inverse regularized identity. -/
lemma width_zero (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (a : Fin K) (ω : Ω) :
    width A reg x a 0 ω =
      √(dotProduct (x a) (Matrix.mulVec (reg • 1)⁻¹ (x a))) := by
  simp [width, widthQuadraticForm_zero]

/-- Squaring the LinUCB width recovers the quadratic form inside the square root, provided that
quadratic form is nonnegative. -/
lemma width_sq_eq_quadratic_form (a : Fin K)
    (h_nonneg : 0 ≤ widthQuadraticForm A reg x a n ω) :
    width A reg x a n ω ^ 2 = widthQuadraticForm A reg x a n ω := by
  simp [width, Real.sq_sqrt h_nonneg]

/-- The accumulated squared LinUCB widths over positive times before horizon `n`. -/
noncomputable def widthSqSum (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ range n, (if t = 0 then 0 else width A reg x (A t ω) t ω) ^ 2

/-- No positive-time widths are accumulated at horizon zero. -/
lemma widthSqSum_zero (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (ω : Ω) :
    widthSqSum A reg x 0 ω = 0 := by
  simp [widthSqSum]

/-- Advancing the horizon adds the next positive-time squared width term. -/
lemma widthSqSum_succ (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) :
    widthSqSum A reg x (n + 1) ω =
      widthSqSum A reg x n ω +
        (if n = 0 then 0 else width A reg x (A n ω) n ω) ^ 2 := by
  simp [widthSqSum, sum_range_succ]

/-- At positive times, advancing the horizon adds the selected arm's squared width. -/
lemma widthSqSum_succ_of_ne_zero (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) (hn : n ≠ 0) :
    widthSqSum A reg x (n + 1) ω =
      widthSqSum A reg x n ω + width A reg x (A n ω) n ω ^ 2 := by
  simp [widthSqSum_succ, hn]

/-- The accumulated quadratic forms corresponding to the positive-time LinUCB widths. -/
noncomputable def quadraticWidthSum (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ range n,
    if t = 0 then 0 else widthQuadraticForm A reg x (A t ω) t ω

/-- No positive-time quadratic width forms are accumulated at horizon zero. -/
lemma quadraticWidthSum_zero (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (ω : Ω) :
    quadraticWidthSum A reg x 0 ω = 0 := by
  simp [quadraticWidthSum]

/-- Advancing the horizon adds the next positive-time quadratic width form. -/
lemma quadraticWidthSum_succ (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) :
    quadraticWidthSum A reg x (n + 1) ω =
      quadraticWidthSum A reg x n ω +
        if n = 0 then 0 else widthQuadraticForm A reg x (A n ω) n ω := by
  simp [quadraticWidthSum, sum_range_succ]

/-- At positive times, advancing the horizon adds the selected arm's quadratic width form. -/
lemma quadraticWidthSum_succ_of_ne_zero (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) (hn : n ≠ 0) :
    quadraticWidthSum A reg x (n + 1) ω =
      quadraticWidthSum A reg x n ω + widthQuadraticForm A reg x (A n ω) n ω := by
  simp [quadraticWidthSum_succ, hn]

/-- The accumulated capped quadratic forms corresponding to the positive-time LinUCB widths. -/
noncomputable def cappedQuadraticWidthSum (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ range n,
    if t = 0 then 0 else min 1 (widthQuadraticForm A reg x (A t ω) t ω)

/-- No positive-time capped quadratic width forms are accumulated at horizon zero. -/
lemma cappedQuadraticWidthSum_zero (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (ω : Ω) :
    cappedQuadraticWidthSum A reg x 0 ω = 0 := by
  simp [cappedQuadraticWidthSum]

/-- Advancing the horizon adds the next positive-time capped quadratic width form. -/
lemma cappedQuadraticWidthSum_succ (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) :
    cappedQuadraticWidthSum A reg x (n + 1) ω =
      cappedQuadraticWidthSum A reg x n ω +
        if n = 0 then 0 else min 1 (widthQuadraticForm A reg x (A n ω) n ω) := by
  simp [cappedQuadraticWidthSum, sum_range_succ]

/-- At positive times, advancing the horizon adds the selected arm's capped quadratic width form. -/
lemma cappedQuadraticWidthSum_succ_of_ne_zero (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) (hn : n ≠ 0) :
    cappedQuadraticWidthSum A reg x (n + 1) ω =
      cappedQuadraticWidthSum A reg x n ω + min 1 (widthQuadraticForm A reg x (A n ω) n ω) := by
  simp [cappedQuadraticWidthSum_succ, hn]

/-- If every positive-time process-level quadratic width form is at most `1`, then the uncapped
and capped process-level quadratic-width accumulators agree. -/
lemma quadraticWidthSum_eq_cappedQuadraticWidthSum
    (h_le_one : ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1) :
    quadraticWidthSum A reg x n ω = cappedQuadraticWidthSum A reg x n ω := by
  rw [quadraticWidthSum, cappedQuadraticWidthSum]
  refine sum_congr rfl ?_
  intro t ht
  by_cases ht0 : t = 0
  · simp [ht0]
  · rw [if_neg ht0, if_neg ht0]
    exact (min_eq_right (h_le_one t ht ht0)).symm

/-- If the squared-width and quadratic-form accumulators agree through a positive time and the
next quadratic form is nonnegative, then they still agree after adding the next term. -/
lemma widthSqSum_eq_quadraticWidthSum_succ_of_ne_zero (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) (hn : n ≠ 0)
    (h_eq : widthSqSum A reg x n ω = quadraticWidthSum A reg x n ω)
    (h_nonneg : 0 ≤ widthQuadraticForm A reg x (A n ω) n ω) :
    widthSqSum A reg x (n + 1) ω = quadraticWidthSum A reg x (n + 1) ω := by
  rw [widthSqSum_succ_of_ne_zero (A := A) (reg := reg) (x := x) (n := n) (ω := ω) hn,
    quadraticWidthSum_succ_of_ne_zero (A := A) (reg := reg) (x := x) (n := n)
      (ω := ω) hn, h_eq]
  rw [width_sq_eq_quadratic_form (A := A) (reg := reg) (x := x) (a := A n ω)
    (n := n) (ω := ω) h_nonneg]

/-- The accumulated squared widths equal the accumulated quadratic forms, provided each positive
time quadratic form is nonnegative. -/
lemma widthSqSum_eq_sum_quadratic_form
    (h_nonneg : ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω) :
    widthSqSum A reg x n ω = quadraticWidthSum A reg x n ω := by
  rw [widthSqSum, quadraticWidthSum]
  refine sum_congr rfl ?_
  intro t ht
  by_cases ht0 : t = 0
  · simp [ht0]
  · rw [if_neg ht0]
    rw [if_neg ht0]
    exact width_sq_eq_quadratic_form (A := A) (reg := reg) (x := x) (a := A t ω)
      (n := t) (ω := ω) (h_nonneg t ht ht0)

/-- A quadratic-form sum bound implies the corresponding bound on `widthSqSum`. This is the shape
expected from a later elliptical-potential argument. -/
lemma widthSqSum_le_of_sum_quadratic_form_le {W : ℝ}
    (h_nonneg : ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_quad_le : quadraticWidthSum A reg x n ω ≤ W) :
    widthSqSum A reg x n ω ≤ W := by
  rw [widthSqSum_eq_sum_quadratic_form (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω) h_nonneg]
  exact h_quad_le

/-- A capped process-level quadratic-form sum bound implies the corresponding bound on
`widthSqSum`, provided the positive-time process-level quadratic forms are nonnegative and at most
`1`. -/
lemma widthSqSum_le_of_capped_quadratic_width_sum_le {W : ℝ}
    (h_nonneg : ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (h_capped_le : cappedQuadraticWidthSum A reg x n ω ≤ W) :
    widthSqSum A reg x n ω ≤ W := by
  rw [widthSqSum_eq_sum_quadratic_form (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω) h_nonneg]
  rw [quadraticWidthSum_eq_cappedQuadraticWidthSum (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω) h_le_one]
  exact h_capped_le

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, a capped process-level quadratic-form sum bound implies the corresponding bound
on `widthSqSum`, provided the positive-time process-level quadratic forms are almost surely
nonnegative and at most `1`. -/
lemma widthSqSum_ae_le_of_capped_quadratic_width_sum_ae_le {W : ℝ}
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (h_capped_le : ∀ᵐ ω ∂P, cappedQuadraticWidthSum A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P, widthSqSum A reg x n ω ≤ W := by
  filter_upwards [h_nonneg, h_le_one, h_capped_le] with
    ω h_nonnegω h_le_oneω h_capped_leω
  exact widthSqSum_le_of_capped_quadratic_width_sum_le (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω) h_nonnegω h_le_oneω h_capped_leω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Determinant of the process-level LinUCB design matrix. -/
noncomputable def designDet (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  Matrix.det (designMatrix A reg x n ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The initial design determinant is the determinant of the regularized identity. -/
lemma designDet_zero (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (ω : Ω) :
    designDet A reg x 0 ω = Matrix.det (reg • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  simp [designDet, designMatrix_zero]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The initial design determinant is `reg ^ d`. -/
lemma designDet_zero_eq_reg_pow (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (ω : Ω) :
    designDet A reg x 0 ω = reg ^ d := by
  rw [designDet_zero]
  simp

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A nonzero regularization parameter gives a nonzero initial design determinant. -/
lemma designDet_zero_ne_zero_of_reg_ne_zero (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (ω : Ω) (hreg : reg ≠ 0) :
    designDet A reg x 0 ω ≠ 0 := by
  rw [designDet_zero_eq_reg_pow]
  exact pow_ne_zero d hreg

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Positive regularization makes every process-level design determinant nonzero. -/
lemma designDet_ne_zero_of_reg_pos (hreg_pos : 0 < reg) :
    designDet A reg x n ω ≠ 0 := by
  have hunit : IsUnit (designMatrix A reg x n ω) :=
    (designMatrix_posDef (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
      hreg_pos).isUnit
  have hdet_unit : IsUnit (designMatrix A reg x n ω).det :=
    (Matrix.isUnit_iff_isUnit_det (A := designMatrix A reg x n ω)).mp hunit
  exact hdet_unit.ne_zero

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, positive regularization makes all design determinants in a finite horizon
nonzero. -/
lemma designDet_ae_ne_zero_of_reg_pos (hreg_pos : 0 < reg) :
    ∀ᵐ ω ∂P, ∀ t, t ∈ range n → designDet A reg x t ω ≠ 0 := by
  exact Filter.Eventually.of_forall fun ω t _ht ↦
    designDet_ne_zero_of_reg_pos (A := A) (reg := reg) (x := x) (n := t) (ω := ω)
      hreg_pos

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Determinant ratio `det(V_n) / det(V_0)` for the process-level design matrices. -/
noncomputable def designDetRatio (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  designDet A reg x n ω / designDet A reg x 0 ω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- At horizon zero, the determinant ratio is `1` when the initial design determinant is nonzero. -/
lemma designDetRatio_zero (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (ω : Ω) (hdet : designDet A reg x 0 ω ≠ 0) :
    designDetRatio A reg x 0 ω = 1 := by
  simp [designDetRatio, hdet]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- At horizon zero, the determinant ratio is positive when the initial design determinant is
nonzero. -/
lemma designDetRatio_zero_pos (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (ω : Ω) (hdet : designDet A reg x 0 ω ≠ 0) :
    0 < designDetRatio A reg x 0 ω := by
  rw [designDetRatio_zero (A := A) (reg := reg) (x := x) (ω := ω) hdet]
  norm_num

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- One-step determinant ratio `det(V_{n+1}) / det(V_n)` for the process-level design matrices.

This is the determinant-ratio target used by the matrix-determinant part of the elliptical
potential lemma. -/
noncomputable def designDetStepRatio (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  designDet A reg x (n + 1) ω / designDet A reg x n ω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The scalar determinant appearing in the rank-one determinant update is the quadratic form
`uᵀ M u`. -/
lemma det_one_add_replicateRow_mul_matrix_mul_replicateCol
    (M : Matrix (Fin d) (Fin d) ℝ) (u : Feature d) :
    (1 + Matrix.replicateRow Unit u * M * Matrix.replicateCol Unit u).det =
      1 + dotProduct u (Matrix.mulVec M u) := by
  have hsum :
      (∑ j, (∑ i, u i * M i j) * u j) =
        ∑ i, u i * ∑ j, M i j * u j := by
    calc
      (∑ j, (∑ i, u i * M i j) * u j)
          = ∑ j, ∑ i, (u i * M i j) * u j := by
              simp [Finset.sum_mul]
      _ = ∑ i, ∑ j, (u i * M i j) * u j := by
              rw [Finset.sum_comm]
      _ = ∑ i, u i * ∑ j, M i j * u j := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
  rw [Matrix.det_unique]
  simpa [Matrix.mul_apply, Matrix.replicateRow, Matrix.replicateCol, Matrix.mulVec,
    dotProduct] using hsum

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Process-level matrix determinant update for the LinUCB design matrix.

If `V_n` has nonzero determinant, then the rank-one update
`V_{n+1} = V_n + x_{A_n} x_{A_n}ᵀ` satisfies
`det(V_{n+1}) = det(V_n) * (1 + x_{A_n}ᵀ V_n⁻¹ x_{A_n})`. -/
lemma designDet_succ_eq_mul_one_add_widthQuadraticForm
    (hdet : designDet A reg x n ω ≠ 0) :
    designDet A reg x (n + 1) ω =
      designDet A reg x n ω * (1 + widthQuadraticForm A reg x (A n ω) n ω) := by
  have hM : IsUnit (designMatrix A reg x n ω).det := by
    simpa [designDet] using (isUnit_iff_ne_zero.mpr hdet)
  calc
    designDet A reg x (n + 1) ω =
        (designMatrix A reg x n ω +
          Matrix.vecMulVec (x (A n ω)) (x (A n ω))).det := by
        simp [designDet, designMatrix_succ]
    _ = (designMatrix A reg x n ω +
        Matrix.replicateCol Unit (x (A n ω)) * Matrix.replicateRow Unit (x (A n ω))).det := by
        rw [Matrix.vecMulVec_eq Unit]
    _ = (designMatrix A reg x n ω).det *
        (1 + Matrix.replicateRow Unit (x (A n ω)) *
          (designMatrix A reg x n ω)⁻¹ * Matrix.replicateCol Unit (x (A n ω))).det := by
        exact Matrix.det_add_replicateCol_mul_replicateRow (A := designMatrix A reg x n ω)
          (ι := Unit) hM (x (A n ω)) (x (A n ω))
    _ = designDet A reg x n ω * (1 + widthQuadraticForm A reg x (A n ω) n ω) := by
        rw [designDet]
        congr 1
        exact det_one_add_replicateRow_mul_matrix_mul_replicateCol
          (M := (designMatrix A reg x n ω)⁻¹) (u := x (A n ω))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If `det(V_n)` is nonzero and the selected quadratic form is nonnegative, then
`det(V_{n+1})` is nonzero. -/
lemma designDet_succ_ne_zero_of_widthQuadraticForm_nonneg
    (hdet : designDet A reg x n ω ≠ 0)
    (h_nonneg : 0 ≤ widthQuadraticForm A reg x (A n ω) n ω) :
    designDet A reg x (n + 1) ω ≠ 0 := by
  rw [designDet_succ_eq_mul_one_add_widthQuadraticForm (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω) hdet]
  exact mul_ne_zero hdet (ne_of_gt (by linarith))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Starting from a nonzero initial determinant, nonnegative selected quadratic forms preserve
nonzero design determinants up to any fixed time. -/
lemma designDet_ne_zero_of_initial_and_widthQuadraticForm_nonneg_lt
    (m : ℕ) (hdet0 : designDet A reg x 0 ω ≠ 0)
    (h_nonneg : ∀ t, t < m → 0 ≤ widthQuadraticForm A reg x (A t ω) t ω) :
    designDet A reg x m ω ≠ 0 := by
  induction m with
  | zero => exact hdet0
  | succ m ih =>
      exact designDet_succ_ne_zero_of_widthQuadraticForm_nonneg (A := A) (reg := reg)
        (x := x) (n := m) (ω := ω)
        (ih fun t ht ↦ h_nonneg t (Nat.lt_trans ht (Nat.lt_succ_self m)))
        (h_nonneg m (Nat.lt_succ_self m))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Starting from a nonzero initial determinant, nonnegative selected quadratic forms imply that
all design determinants through horizon `n` are nonzero. -/
lemma designDet_ne_zero_of_initial_and_widthQuadraticForm_nonneg
    (hdet0 : designDet A reg x 0 ω ≠ 0)
    (h_nonneg : ∀ t, t ∈ range n → 0 ≤ widthQuadraticForm A reg x (A t ω) t ω) :
    ∀ t, t ∈ range (n + 1) → designDet A reg x t ω ≠ 0 := by
  intro t ht
  exact designDet_ne_zero_of_initial_and_widthQuadraticForm_nonneg_lt (A := A) (reg := reg)
    (x := x) (m := t) (ω := ω) hdet0 fun s hs ↦
      h_nonneg s (mem_range.mpr (Nat.lt_of_lt_of_le hs (Nat.le_of_lt_succ (mem_range.mp ht))))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, a nonzero initial determinant and nonnegative selected quadratic forms imply
that all design determinants through horizon `n` are nonzero. -/
lemma designDet_ae_ne_zero_of_initial_and_widthQuadraticForm_ae_nonneg
    (hdet0 : ∀ᵐ ω ∂P, designDet A reg x 0 ω ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω) :
    ∀ᵐ ω ∂P, ∀ t, t ∈ range (n + 1) → designDet A reg x t ω ≠ 0 := by
  filter_upwards [hdet0, h_nonneg] with ω hdet0ω h_nonnegω
  exact designDet_ne_zero_of_initial_and_widthQuadraticForm_nonneg (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) hdet0ω h_nonnegω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If `det(V_n) ≠ 0`, then the one-step determinant ratio is
`1 + x_{A_n}ᵀ V_n⁻¹ x_{A_n}`. -/
lemma designDetStepRatio_eq_one_add_widthQuadraticForm
    (hdet : designDet A reg x n ω ≠ 0) :
    designDetStepRatio A reg x n ω =
      1 + widthQuadraticForm A reg x (A n ω) n ω := by
  simp [designDetStepRatio,
    designDet_succ_eq_mul_one_add_widthQuadraticForm (A := A) (reg := reg) (x := x)
      (n := n) (ω := ω) hdet, hdet]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The cumulative determinant ratio advances by multiplying by the one-step determinant ratio. -/
lemma designDetRatio_succ_eq_mul_one_add_widthQuadraticForm
    (hdet : designDet A reg x n ω ≠ 0) :
    designDetRatio A reg x (n + 1) ω =
      designDetRatio A reg x n ω * (1 + widthQuadraticForm A reg x (A n ω) n ω) := by
  rw [designDetRatio, designDetRatio,
    designDet_succ_eq_mul_one_add_widthQuadraticForm (A := A) (reg := reg) (x := x)
      (n := n) (ω := ω) hdet]
  ring

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Starting from a nonzero initial determinant, nonnegative selected quadratic forms make the
cumulative determinant ratio positive. -/
lemma designDetRatio_pos_of_initial_and_widthQuadraticForm_nonneg
    (hdet0 : designDet A reg x 0 ω ≠ 0)
    (h_nonneg : ∀ t, t ∈ range n → 0 ≤ widthQuadraticForm A reg x (A t ω) t ω) :
    0 < designDetRatio A reg x n ω := by
  induction n with
  | zero =>
      exact designDetRatio_zero_pos (A := A) (reg := reg) (x := x) (ω := ω) hdet0
  | succ n ih =>
      have hdetn : designDet A reg x n ω ≠ 0 :=
        designDet_ne_zero_of_initial_and_widthQuadraticForm_nonneg_lt (A := A) (reg := reg)
          (x := x) (m := n) (ω := ω) hdet0 fun t ht ↦
            h_nonneg t (mem_range.mpr (Nat.lt_trans ht (Nat.lt_succ_self n)))
      rw [designDetRatio_succ_eq_mul_one_add_widthQuadraticForm (A := A) (reg := reg)
        (x := x) (n := n) (ω := ω) hdetn]
      exact mul_pos
        (ih fun t ht ↦ h_nonneg t
          (mem_range.mpr (Nat.lt_trans (mem_range.mp ht) (Nat.lt_succ_self n))))
        (by linarith [h_nonneg n (by simp)])

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, starting from a nonzero initial determinant, nonnegative selected quadratic
forms make the cumulative determinant ratio positive. -/
lemma designDetRatio_ae_pos_of_initial_and_widthQuadraticForm_ae_nonneg
    (hdet0 : ∀ᵐ ω ∂P, designDet A reg x 0 ω ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω) :
    ∀ᵐ ω ∂P, 0 < designDetRatio A reg x n ω := by
  filter_upwards [hdet0, h_nonneg] with ω hdet0ω h_nonnegω
  exact designDetRatio_pos_of_initial_and_widthQuadraticForm_nonneg (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) hdet0ω h_nonnegω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, a nonzero regularization parameter and nonnegative selected quadratic forms make
the cumulative determinant ratio positive. -/
lemma designDetRatio_ae_pos_of_reg_ne_zero_and_widthQuadraticForm_ae_nonneg
    (hreg : reg ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω) :
    ∀ᵐ ω ∂P, 0 < designDetRatio A reg x n ω := by
  refine designDetRatio_ae_pos_of_initial_and_widthQuadraticForm_ae_nonneg (A := A)
    (reg := reg) (x := x) (n := n) (P := P) ?_ h_nonneg
  exact Filter.Eventually.of_forall fun ω ↦
    designDet_zero_ne_zero_of_reg_ne_zero (A := A) (reg := reg) (x := x) (ω := ω) hreg

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Starting from a nonzero initial determinant, the cumulative determinant ratio is the finite
product of the per-round determinant-update factors. -/
lemma designDetRatio_eq_prod_one_add_widthQuadraticForm
    (hdet0 : designDet A reg x 0 ω ≠ 0)
    (h_nonneg : ∀ t, t ∈ range n → 0 ≤ widthQuadraticForm A reg x (A t ω) t ω) :
    designDetRatio A reg x n ω =
      ∏ t ∈ range n, (1 + widthQuadraticForm A reg x (A t ω) t ω) := by
  induction n with
  | zero =>
      rw [designDetRatio_zero (A := A) (reg := reg) (x := x) (ω := ω) hdet0]
      simp
  | succ n ih =>
      have hdetn : designDet A reg x n ω ≠ 0 :=
        designDet_ne_zero_of_initial_and_widthQuadraticForm_nonneg_lt (A := A) (reg := reg)
          (x := x) (m := n) (ω := ω) hdet0 fun t ht ↦
            h_nonneg t (mem_range.mpr (Nat.lt_trans ht (Nat.lt_succ_self n)))
      rw [designDetRatio_succ_eq_mul_one_add_widthQuadraticForm (A := A) (reg := reg)
        (x := x) (n := n) (ω := ω) hdetn]
      rw [ih fun t ht ↦ h_nonneg t
        (mem_range.mpr (Nat.lt_trans (mem_range.mp ht) (Nat.lt_succ_self n)))]
      simp [Finset.prod_range_succ]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If every selected quadratic form is in `[0, 1]`, the cumulative determinant ratio is at most
`2 ^ n`. -/
lemma designDetRatio_le_two_pow_of_initial_and_widthQuadraticForm_le_one
    (hdet0 : designDet A reg x 0 ω ≠ 0)
    (h_nonneg : ∀ t, t ∈ range n → 0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ t, t ∈ range n → widthQuadraticForm A reg x (A t ω) t ω ≤ 1) :
    designDetRatio A reg x n ω ≤ (2 : ℝ) ^ n := by
  rw [designDetRatio_eq_prod_one_add_widthQuadraticForm (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) hdet0 h_nonneg]
  calc
    (∏ t ∈ range n, (1 + widthQuadraticForm A reg x (A t ω) t ω))
        ≤ ∏ _t ∈ range n, (2 : ℝ) := by
          exact Finset.prod_le_prod
            (fun t ht ↦ by linarith [h_nonneg t ht])
            (fun t ht ↦ by linarith [h_le_one t ht])
    _ = (2 : ℝ) ^ n := by
          simp

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, if every selected quadratic form is in `[0, 1]`, the cumulative determinant
ratio is at most `2 ^ n`. -/
lemma designDetRatio_ae_le_two_pow_of_initial_and_widthQuadraticForm_ae_le_one
    (hdet0 : ∀ᵐ ω ∂P, designDet A reg x 0 ω ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1) :
    ∀ᵐ ω ∂P, designDetRatio A reg x n ω ≤ (2 : ℝ) ^ n := by
  filter_upwards [hdet0, h_nonneg, h_le_one] with ω hdet0ω h_nonnegω h_le_oneω
  exact designDetRatio_le_two_pow_of_initial_and_widthQuadraticForm_le_one (A := A)
    (reg := reg) (x := x) (n := n) (ω := ω) hdet0ω h_nonnegω h_le_oneω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, a nonzero regularization parameter and selected quadratic forms in `[0, 1]`
imply the cumulative determinant ratio is at most `2 ^ n`. -/
lemma designDetRatio_ae_le_two_pow_of_reg_ne_zero_and_widthQuadraticForm_ae_le_one
    (hreg : reg ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1) :
    ∀ᵐ ω ∂P, designDetRatio A reg x n ω ≤ (2 : ℝ) ^ n := by
  refine designDetRatio_ae_le_two_pow_of_initial_and_widthQuadraticForm_ae_le_one
    (A := A) (reg := reg) (x := x) (n := n) (P := P) ?_ h_nonneg h_le_one
  exact Filter.Eventually.of_forall fun ω ↦
    designDet_zero_ne_zero_of_reg_ne_zero (A := A) (reg := reg) (x := x) (ω := ω) hreg

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Converts an almost-sure trace bound into the determinant-ratio bound expected from a future
trace/determinant comparison theorem. -/
lemma designDetRatio_ae_le_trace_budget_of_designTrace_ae_le
    (T : ℝ)
    (h_trace_le : ∀ᵐ ω ∂P, designTrace A reg x n ω ≤ T)
    (h_ratio_of_trace : ∀ ω,
      designTrace A reg x n ω ≤ T →
        designDetRatio A reg x n ω ≤ (T / (reg * (d : ℝ))) ^ d) :
    ∀ᵐ ω ∂P, designDetRatio A reg x n ω ≤ (T / (reg * (d : ℝ))) ^ d := by
  filter_upwards [h_trace_le] with ω h_traceω
  exact h_ratio_of_trace ω h_traceω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Bounded selected feature norms give the concrete trace budget
`reg * d + n * L2`; a future trace/determinant comparison then gives the corresponding
determinant-ratio bound. -/
lemma designDetRatio_ae_le_trace_budget_of_featureSqNorm_bound
    (L2 : ℝ)
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ L2)
    (h_ratio_of_trace : ∀ ω,
      designTrace A reg x n ω ≤ reg * (d : ℝ) + (n : ℝ) * L2 →
        designDetRatio A reg x n ω ≤
          ((reg * (d : ℝ) + (n : ℝ) * L2) / (reg * (d : ℝ))) ^ d) :
    ∀ᵐ ω ∂P,
      designDetRatio A reg x n ω ≤
        ((reg * (d : ℝ) + (n : ℝ) * L2) / (reg * (d : ℝ))) ^ d := by
  exact designDetRatio_ae_le_trace_budget_of_designTrace_ae_le (A := A) (reg := reg)
    (x := x) (n := n) (P := P) (T := reg * (d : ℝ) + (n : ℝ) * L2)
    (designTrace_ae_le_reg_mul_dim_add_nat_mul_featureSqNorm_bound (A := A) (reg := reg)
      (x := x) (n := n) (P := P) L2 hL2)
    h_ratio_of_trace

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A determinant upper bound for `V_n` implies the corresponding determinant-ratio bound, using
`det(V_0) = reg ^ d`. -/
lemma designDetRatio_le_trace_budget_of_designDet_le
    (T : ℝ) (hreg_pos : 0 < reg) (hd : d ≠ 0)
    (hdet_le : designDet A reg x n ω ≤ (T / (d : ℝ)) ^ d) :
    designDetRatio A reg x n ω ≤ (T / (reg * (d : ℝ))) ^ d := by
  rw [designDetRatio, designDet_zero_eq_reg_pow]
  have hreg_pow_nonneg : 0 ≤ reg ^ d := (pow_pos hreg_pos d).le
  have hdiv : designDet A reg x n ω / reg ^ d ≤ (T / (d : ℝ)) ^ d / reg ^ d := by
    exact div_le_div_of_nonneg_right hdet_le hreg_pow_nonneg
  refine hdiv.trans_eq ?_
  rw [← div_pow]
  congr 1
  field_simp [hreg_pos.ne', by exact_mod_cast hd]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, a determinant upper bound for `V_n` implies the corresponding determinant-ratio
bound. -/
lemma designDetRatio_ae_le_trace_budget_of_designDet_ae_le
    (T : ℝ) (hreg_pos : 0 < reg) (hd : d ≠ 0)
    (hdet_le : ∀ᵐ ω ∂P, designDet A reg x n ω ≤ (T / (d : ℝ)) ^ d) :
    ∀ᵐ ω ∂P, designDetRatio A reg x n ω ≤ (T / (reg * (d : ℝ))) ^ d := by
  filter_upwards [hdet_le] with ω hdetω
  exact designDetRatio_le_trace_budget_of_designDet_le (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) T hreg_pos hd hdetω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Converts an almost-sure trace bound plus a future determinant/trace comparison for `det(V_n)`
into the determinant-ratio bound used by the elliptical-potential chain. -/
lemma designDetRatio_ae_le_trace_budget_of_designDet_le_of_designTrace_ae_le
    (T : ℝ) (hreg_pos : 0 < reg) (hd : d ≠ 0)
    (h_trace_le : ∀ᵐ ω ∂P, designTrace A reg x n ω ≤ T)
    (hdet_of_trace : ∀ ω,
      designTrace A reg x n ω ≤ T → designDet A reg x n ω ≤ (T / (d : ℝ)) ^ d) :
    ∀ᵐ ω ∂P, designDetRatio A reg x n ω ≤ (T / (reg * (d : ℝ))) ^ d := by
  refine designDetRatio_ae_le_trace_budget_of_designDet_ae_le (A := A) (reg := reg)
    (x := x) (n := n) (P := P) T hreg_pos hd ?_
  filter_upwards [h_trace_le] with ω h_traceω
  exact hdet_of_trace ω h_traceω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Bounded selected feature norms reduce the determinant-ratio goal to the determinant upper bound
`det(V_n) ≤ ((reg * d + n * L2) / d) ^ d`. -/
lemma designDetRatio_ae_le_trace_budget_of_featureSqNorm_bound_of_designDet_le
    (L2 : ℝ) (hreg_pos : 0 < reg) (hd : d ≠ 0)
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ L2)
    (hdet_of_trace : ∀ ω,
      designTrace A reg x n ω ≤ reg * (d : ℝ) + (n : ℝ) * L2 →
        designDet A reg x n ω ≤
          ((reg * (d : ℝ) + (n : ℝ) * L2) / (d : ℝ)) ^ d) :
    ∀ᵐ ω ∂P,
      designDetRatio A reg x n ω ≤
        ((reg * (d : ℝ) + (n : ℝ) * L2) / (reg * (d : ℝ))) ^ d := by
  exact designDetRatio_ae_le_trace_budget_of_designDet_le_of_designTrace_ae_le (A := A)
    (reg := reg) (x := x) (n := n) (P := P)
    (T := reg * (d : ℝ) + (n : ℝ) * L2) hreg_pos hd
    (designTrace_ae_le_reg_mul_dim_add_nat_mul_featureSqNorm_bound (A := A) (reg := reg)
      (x := x) (n := n) (P := P) L2 hL2)
    hdet_of_trace

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Matrix-level determinant/trace comparison needed for the finite-dimensional
elliptical-potential bound.

For positive semidefinite `d × d` matrices, this is the AM-GM-style inequality
`det(M) ≤ (trace(M) / d) ^ d`. -/
def MatrixDetLeTraceAveragePow (d : ℕ) : Prop :=
  ∀ M : Matrix (Fin d) (Fin d) ℝ, M.PosSemidef → M.det ≤ (M.trace / (d : ℝ)) ^ d

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A matrix-level determinant/trace comparison applies to the LinUCB design matrix because the
design matrix is positive semidefinite. -/
lemma designDet_le_trace_average_pow_of_matrix_det_trace_bound
    (hdet_trace : MatrixDetLeTraceAveragePow d) (hreg_nonneg : 0 ≤ reg) :
    designDet A reg x n ω ≤ (designTrace A reg x n ω / (d : ℝ)) ^ d := by
  simpa [designDet, designTrace] using
    hdet_trace (designMatrix A reg x n ω)
      (designMatrix_posSemidef (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
        hreg_nonneg)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Combining `det(M) ≤ (trace(M)/d)^d` with a trace budget gives the determinant upper bound
`det(V_n) ≤ (T/d)^d`. -/
lemma designDet_le_trace_budget_of_matrix_det_trace_bound
    (hdet_trace : MatrixDetLeTraceAveragePow d) (hreg_nonneg : 0 ≤ reg)
    (hd : d ≠ 0) (T : ℝ) (h_trace_le : designTrace A reg x n ω ≤ T) :
    designDet A reg x n ω ≤ (T / (d : ℝ)) ^ d := by
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hd
  have hbase_nonneg : 0 ≤ designTrace A reg x n ω / (d : ℝ) :=
    div_nonneg (designTrace_nonneg (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
      hreg_nonneg) hd_pos.le
  have hbase_le : designTrace A reg x n ω / (d : ℝ) ≤ T / (d : ℝ) :=
    (div_le_div_iff_of_pos_right hd_pos).mpr h_trace_le
  exact (designDet_le_trace_average_pow_of_matrix_det_trace_bound (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) hdet_trace hreg_nonneg).trans
      (pow_le_pow_left₀ hbase_nonneg hbase_le d)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Bounded selected feature norms and the matrix-level determinant/trace comparison give the
determinant-ratio bound used by the elliptical-potential chain. -/
lemma designDetRatio_ae_le_trace_budget_of_featureSqNorm_bound_of_matrix_det_trace_bound
    (L2 : ℝ) (hreg_pos : 0 < reg) (hd : d ≠ 0)
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ L2)
    (hdet_trace : MatrixDetLeTraceAveragePow d) :
    ∀ᵐ ω ∂P,
      designDetRatio A reg x n ω ≤
        ((reg * (d : ℝ) + (n : ℝ) * L2) / (reg * (d : ℝ))) ^ d := by
  refine designDetRatio_ae_le_trace_budget_of_featureSqNorm_bound_of_designDet_le
    (A := A) (reg := reg) (x := x) (n := n) (P := P) L2 hreg_pos hd hL2 ?_
  intro ω h_traceω
  exact designDet_le_trace_budget_of_matrix_det_trace_bound (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) (T := reg * (d : ℝ) + (n : ℝ) * L2)
    hdet_trace hreg_pos.le hd h_traceω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The log-determinant expression that appears in the elliptical-potential lemma. -/
noncomputable def ellipticalPotential (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  2 * Real.log (designDetRatio A reg x n ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A positive determinant ratio bounded by `D` gives the corresponding log-determinant potential
bound. -/
lemma ellipticalPotential_le_two_mul_log_of_designDetRatio_le {D : ℝ}
    (h_ratio_pos : 0 < designDetRatio A reg x n ω)
    (h_ratio_le : designDetRatio A reg x n ω ≤ D) :
    ellipticalPotential A reg x n ω ≤ 2 * Real.log D := by
  rw [ellipticalPotential]
  exact mul_le_mul_of_nonneg_left (Real.log_le_log h_ratio_pos h_ratio_le) (by norm_num)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, a positive determinant ratio bounded by `D` gives the corresponding
log-determinant potential bound. -/
lemma ellipticalPotential_ae_le_two_mul_log_of_designDetRatio_ae_le {D : ℝ}
    (h_ratio_pos : ∀ᵐ ω ∂P, 0 < designDetRatio A reg x n ω)
    (h_ratio_le : ∀ᵐ ω ∂P, designDetRatio A reg x n ω ≤ D) :
    ∀ᵐ ω ∂P, ellipticalPotential A reg x n ω ≤ 2 * Real.log D := by
  filter_upwards [h_ratio_pos, h_ratio_le] with ω h_ratio_posω h_ratio_leω
  exact ellipticalPotential_le_two_mul_log_of_designDetRatio_le (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) h_ratio_posω h_ratio_leω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- One-step log-determinant potential term based on `det(V_{n+1}) / det(V_n)`.

The future determinant-update proof should naturally establish the capped quadratic-width term is
bounded by this quantity. A separate log/telescoping bridge then connects this one-step quantity to
`ellipticalPotentialIncrement`. -/
noncomputable def ellipticalPotentialStep (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  2 * Real.log (designDetStepRatio A reg x n ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Under determinant nonvanishing, the one-step log-determinant potential is
`2 * log (1 + x_{A_n}ᵀ V_n⁻¹ x_{A_n})`. -/
lemma ellipticalPotentialStep_eq_two_mul_log_one_add_widthQuadraticForm
    (hdet : designDet A reg x n ω ≠ 0) :
    ellipticalPotentialStep A reg x n ω =
      2 * Real.log (1 + widthQuadraticForm A reg x (A n ω) n ω) := by
  simp [ellipticalPotentialStep,
    designDetStepRatio_eq_one_add_widthQuadraticForm (A := A) (reg := reg) (x := x)
      (n := n) (ω := ω) hdet]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Scalar log inequality used in the elliptical-potential proof: for `0 ≤ q ≤ 1`,
`min 1 q ≤ 2 * log (1 + q)`. -/
lemma min_one_le_two_mul_log_one_add_of_nonneg_le_one {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1) :
    min 1 q ≤ 2 * Real.log (1 + q) := by
  have hlog : 2 * q / (q + 2) ≤ Real.log (1 + q) :=
    Real.le_log_one_add_of_nonneg hq_nonneg
  have hq_add_two_pos : 0 < q + 2 := by linarith
  have hq_le_two : q ≤ 2 := by linarith
  have hq_le_log_lower : q ≤ 2 * (2 * q / (q + 2)) := by
    rw [show 2 * (2 * q / (q + 2)) = 4 * q / (q + 2) by ring]
    rw [le_div_iff₀ hq_add_two_pos]
    nlinarith
  rw [min_eq_right hq_le_one]
  exact hq_le_log_lower.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Under determinant nonvanishing and the usual `0 ≤ q ≤ 1` quadratic-form side conditions, the
single capped quadratic-width term is bounded by the one-step log-determinant potential. -/
lemma cappedWidthTerm_le_ellipticalPotentialStep
    (hdet : designDet A reg x n ω ≠ 0)
    (h_nonneg : 0 ≤ widthQuadraticForm A reg x (A n ω) n ω)
    (h_le_one : n ≠ 0 → widthQuadraticForm A reg x (A n ω) n ω ≤ 1) :
    (if n = 0 then 0 else min 1 (widthQuadraticForm A reg x (A n ω) n ω)) ≤
      ellipticalPotentialStep A reg x n ω := by
  by_cases hn : n = 0
  · rw [if_pos hn,
      ellipticalPotentialStep_eq_two_mul_log_one_add_widthQuadraticForm (A := A) (reg := reg)
        (x := x) (n := n) (ω := ω) hdet]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  · rw [if_neg hn,
      ellipticalPotentialStep_eq_two_mul_log_one_add_widthQuadraticForm (A := A) (reg := reg)
        (x := x) (n := n) (ω := ω) hdet]
    exact min_one_le_two_mul_log_one_add_of_nonneg_le_one h_nonneg (h_le_one hn)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, determinant nonvanishing and the standard quadratic-form side conditions imply
the per-step one-step-potential bound required by the elliptical-potential induction shell. -/
lemma cappedWidthTerm_ae_le_ellipticalPotentialStep_of_det_ne_zero
    (hdet : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → designDet A reg x t ω ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1) :
    ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      (if t = 0 then 0 else min 1 (widthQuadraticForm A reg x (A t ω) t ω)) ≤
        ellipticalPotentialStep A reg x t ω := by
  filter_upwards [hdet, h_nonneg, h_le_one] with ω hdetω h_nonnegω h_le_oneω
  intro t ht
  exact cappedWidthTerm_le_ellipticalPotentialStep (A := A) (reg := reg) (x := x)
    (n := t) (ω := ω) (hdetω t ht) (h_nonnegω t ht) (h_le_oneω t ht)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- At horizon zero, the log-determinant potential is zero when the initial design determinant is
nonzero. -/
lemma ellipticalPotential_zero (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (ω : Ω) (hdet : designDet A reg x 0 ω ≠ 0) :
    ellipticalPotential A reg x 0 ω = 0 := by
  simp [ellipticalPotential, designDetRatio_zero (A := A) (reg := reg) (x := x) (ω := ω) hdet]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Base case for the log-determinant elliptical-potential inequality. At horizon zero there are no
positive-time capped quadratic width forms, and the log-determinant potential is zero when the
initial design determinant is nonzero. -/
lemma cappedQuadraticWidthSum_le_ellipticalPotential_zero
    (A : ℕ → Ω → Fin K) (reg : ℝ) (x : Fin K → Feature d) (ω : Ω)
    (hdet : designDet A reg x 0 ω ≠ 0) :
    cappedQuadraticWidthSum A reg x 0 ω ≤ ellipticalPotential A reg x 0 ω := by
  rw [cappedQuadraticWidthSum_zero (A := A) (reg := reg) (x := x) (ω := ω),
    ellipticalPotential_zero (A := A) (reg := reg) (x := x) (ω := ω) hdet]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- One-step increment of the log-determinant elliptical potential. -/
noncomputable def ellipticalPotentialIncrement (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  ellipticalPotential A reg x (n + 1) ω - ellipticalPotential A reg x n ω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The one-step determinant-ratio potential equals the increment of the cumulative
log-determinant potential, provided the relevant design determinants are nonzero. -/
lemma ellipticalPotentialStep_eq_increment
    (hdet0 : designDet A reg x 0 ω ≠ 0)
    (hdetn : designDet A reg x n ω ≠ 0)
    (hdet_succ : designDet A reg x (n + 1) ω ≠ 0) :
    ellipticalPotentialStep A reg x n ω = ellipticalPotentialIncrement A reg x n ω := by
  simp [ellipticalPotentialStep, designDetStepRatio, ellipticalPotentialIncrement,
    ellipticalPotential, designDetRatio, Real.log_div hdet_succ hdetn,
    Real.log_div hdet_succ hdet0, Real.log_div hdetn hdet0]
  ring

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, the one-step determinant-ratio potential equals the increment of the cumulative
log-determinant potential throughout the finite horizon, provided all determinants up to that
horizon are nonzero almost surely. -/
lemma ellipticalPotentialStep_ae_eq_increment_of_det_ne_zero
    (hdet : ∀ᵐ ω ∂P, ∀ t, t ∈ range (n + 1) → designDet A reg x t ω ≠ 0) :
    ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      ellipticalPotentialStep A reg x t ω = ellipticalPotentialIncrement A reg x t ω := by
  filter_upwards [hdet] with ω hdetω
  intro t ht
  exact ellipticalPotentialStep_eq_increment (A := A) (reg := reg) (x := x) (n := t)
    (ω := ω) (hdetω 0 (by simp))
    (hdetω t (mem_range.mpr (Nat.lt_trans (mem_range.mp ht) (Nat.lt_succ_self n))))
    (hdetω (t + 1) (mem_range.mpr (Nat.succ_lt_succ (mem_range.mp ht))))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If the next capped quadratic width term is bounded by the next log-determinant potential
increment, then the cumulative capped-sum/log-det inequality advances by one step. -/
lemma cappedQuadraticWidthSum_succ_le_ellipticalPotential
    (h_prev : cappedQuadraticWidthSum A reg x n ω ≤ ellipticalPotential A reg x n ω)
    (h_step :
      (if n = 0 then 0 else min 1 (widthQuadraticForm A reg x (A n ω) n ω)) ≤
        ellipticalPotentialIncrement A reg x n ω) :
    cappedQuadraticWidthSum A reg x (n + 1) ω ≤ ellipticalPotential A reg x (n + 1) ω := by
  rw [cappedQuadraticWidthSum_succ (A := A) (reg := reg) (x := x) (n := n) (ω := ω)]
  calc
    cappedQuadraticWidthSum A reg x n ω +
        (if n = 0 then 0 else min 1 (widthQuadraticForm A reg x (A n ω) n ω))
      ≤ ellipticalPotential A reg x n ω + ellipticalPotentialIncrement A reg x n ω := by
        exact add_le_add h_prev h_step
    _ = ellipticalPotential A reg x (n + 1) ω := by
        simp [ellipticalPotentialIncrement]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A per-step bound by log-determinant potential increments implies the cumulative
elliptical-potential inequality. This is the induction shell for the future determinant-update
proof. -/
lemma cappedQuadraticWidthSum_le_ellipticalPotential_of_step_le
    (hdet : designDet A reg x 0 ω ≠ 0) :
    (∀ t, t ∈ range n →
      (if t = 0 then 0 else min 1 (widthQuadraticForm A reg x (A t ω) t ω)) ≤
        ellipticalPotentialIncrement A reg x t ω) →
    cappedQuadraticWidthSum A reg x n ω ≤ ellipticalPotential A reg x n ω := by
  induction n with
  | zero =>
      intro _
      exact cappedQuadraticWidthSum_le_ellipticalPotential_zero (A := A) (reg := reg)
        (x := x) (ω := ω) hdet
  | succ n ih =>
      intro h_step
      refine cappedQuadraticWidthSum_succ_le_ellipticalPotential (A := A) (reg := reg)
        (x := x) (n := n) (ω := ω) ?_ ?_
      · exact ih fun t ht ↦ h_step t
          (mem_range.mpr (Nat.lt_trans (mem_range.mp ht) (Nat.lt_succ_self n)))
      · exact h_step n (by simp)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, a per-step bound by log-determinant potential increments implies the cumulative
elliptical-potential inequality. -/
lemma cappedQuadraticWidthSum_ae_le_ellipticalPotential_of_step_ae_le
    (hdet : ∀ᵐ ω ∂P, designDet A reg x 0 ω ≠ 0)
    (h_step : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      (if t = 0 then 0 else min 1 (widthQuadraticForm A reg x (A t ω) t ω)) ≤
        ellipticalPotentialIncrement A reg x t ω) :
    ∀ᵐ ω ∂P, cappedQuadraticWidthSum A reg x n ω ≤ ellipticalPotential A reg x n ω := by
  filter_upwards [hdet, h_step] with ω hdetω h_stepω
  exact cappedQuadraticWidthSum_le_ellipticalPotential_of_step_le (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) hdetω h_stepω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, per-step bounds by the one-step determinant-ratio potential imply the
cumulative capped-sum/log-det inequality, provided the one-step determinant-ratio potential is
bounded by the corresponding cumulative-potential increment.

This separates the future elliptical-potential proof into two local obligations:

* a matrix-determinant update bounding the selected arm's capped quadratic form by
  `ellipticalPotentialStep`;
* a log/telescoping bridge from `ellipticalPotentialStep` to `ellipticalPotentialIncrement`. -/
lemma cappedQuadraticWidthSum_ae_le_ellipticalPotential_of_stepPotential_ae_le
    (hdet : ∀ᵐ ω ∂P, designDet A reg x 0 ω ≠ 0)
    (h_step : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      (if t = 0 then 0 else min 1 (widthQuadraticForm A reg x (A t ω) t ω)) ≤
        ellipticalPotentialStep A reg x t ω)
    (h_step_le_increment : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      ellipticalPotentialStep A reg x t ω ≤ ellipticalPotentialIncrement A reg x t ω) :
    ∀ᵐ ω ∂P, cappedQuadraticWidthSum A reg x n ω ≤ ellipticalPotential A reg x n ω := by
  refine cappedQuadraticWidthSum_ae_le_ellipticalPotential_of_step_ae_le (A := A)
    (reg := reg) (x := x) (n := n) (P := P) hdet ?_
  filter_upwards [h_step, h_step_le_increment] with ω h_stepω h_step_le_incrementω
  intro t ht
  exact (h_stepω t ht).trans (h_step_le_incrementω t ht)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, per-step bounds by the one-step determinant-ratio potential imply the
cumulative capped-sum/log-det inequality when all design determinants up to the horizon are nonzero
almost surely.

Compared with `cappedQuadraticWidthSum_ae_le_ellipticalPotential_of_stepPotential_ae_le`, this
version discharges the log/telescoping bridge automatically from determinant nonvanishing. -/
lemma cappedQuadraticWidthSum_ae_le_ellipticalPotential_of_stepPotential_ae_le_of_det_ne_zero
    (hdet : ∀ᵐ ω ∂P, ∀ t, t ∈ range (n + 1) → designDet A reg x t ω ≠ 0)
    (h_step : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      (if t = 0 then 0 else min 1 (widthQuadraticForm A reg x (A t ω) t ω)) ≤
        ellipticalPotentialStep A reg x t ω) :
    ∀ᵐ ω ∂P, cappedQuadraticWidthSum A reg x n ω ≤ ellipticalPotential A reg x n ω := by
  have hdet0 : ∀ᵐ ω ∂P, designDet A reg x 0 ω ≠ 0 := by
    filter_upwards [hdet] with ω hdetω
    exact hdetω 0 (by simp)
  refine cappedQuadraticWidthSum_ae_le_ellipticalPotential_of_stepPotential_ae_le (A := A)
    (reg := reg) (x := x) (n := n) (P := P) hdet0 h_step ?_
  filter_upwards [ellipticalPotentialStep_ae_eq_increment_of_det_ne_zero (A := A)
    (reg := reg) (x := x) (n := n) (P := P) hdet] with ω h_eq
  intro t ht
  rw [h_eq t ht]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The process-level capped quadratic-width input expected from an elliptical-potential argument.

It packages the three facts needed to turn a capped process-level quadratic-width estimate into the
`widthSqSum` estimate used by the regret chain:

* each positive-time process-level quadratic width form is nonnegative;
* each positive-time process-level quadratic width form is at most `1`;
* their capped process-level accumulated sum is bounded by `W`. -/
def CappedQuadraticWidthBound (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) (W : ℝ) : Prop :=
  (∀ t, t ∈ range n → t ≠ 0 → 0 ≤ widthQuadraticForm A reg x (A t ω) t ω) ∧
    (∀ t, t ∈ range n → t ≠ 0 → widthQuadraticForm A reg x (A t ω) t ω ≤ 1) ∧
      cappedQuadraticWidthSum A reg x n ω ≤ W

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Build the packaged process-level capped quadratic-width input from its component facts. -/
lemma cappedQuadraticWidthBound_of_nonneg_le_one_and_sum_le {W : ℝ}
    (h_nonneg : ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (h_sum_le : cappedQuadraticWidthSum A reg x n ω ≤ W) :
    CappedQuadraticWidthBound A reg x n ω W := by
  exact ⟨h_nonneg, h_le_one, h_sum_le⟩

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Base case for the packaged process-level capped quadratic-width input. At horizon zero, the
nonnegativity and `≤ 1` side conditions are vacuous, and the capped sum is zero. -/
lemma cappedQuadraticWidthBound_zero {W : ℝ} (hW : 0 ≤ W) :
    CappedQuadraticWidthBound A reg x 0 ω W := by
  refine cappedQuadraticWidthBound_of_nonneg_le_one_and_sum_le (A := A) (reg := reg)
    (x := x) (n := 0) (ω := ω) ?_ ?_ ?_
  · intro t ht _
    simp at ht
  · intro t ht _
    simp at ht
  · simpa [cappedQuadraticWidthSum_zero] using hW

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Base case for the packaged process-level capped quadratic-width input when the constant bound
is supplied through the log-determinant potential. -/
lemma cappedQuadraticWidthBound_zero_of_ellipticalPotential_le_bound {W : ℝ}
    (hdet : designDet A reg x 0 ω ≠ 0) (h_potential_le : ellipticalPotential A reg x 0 ω ≤ W) :
    CappedQuadraticWidthBound A reg x 0 ω W := by
  refine cappedQuadraticWidthBound_of_nonneg_le_one_and_sum_le (A := A) (reg := reg)
    (x := x) (n := 0) (ω := ω) ?_ ?_ ?_
  · intro t ht _
    simp at ht
  · intro t ht _
    simp at ht
  · exact (cappedQuadraticWidthSum_le_ellipticalPotential_zero (A := A) (reg := reg)
      (x := x) (ω := ω) hdet).trans h_potential_le

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The packaged process-level capped quadratic-width input is monotone in the numeric bound. -/
lemma cappedQuadraticWidthBound_mono {W W' : ℝ}
    (h_bound : CappedQuadraticWidthBound A reg x n ω W) (hW : W ≤ W') :
    CappedQuadraticWidthBound A reg x n ω W' := by
  exact ⟨h_bound.1, h_bound.2.1, h_bound.2.2.trans hW⟩

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, build the packaged process-level capped quadratic-width input from its component
facts. -/
lemma cappedQuadraticWidthBound_ae_of_nonneg_le_one_and_sum_ae_le {W : ℝ}
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (h_sum_le : ∀ᵐ ω ∂P, cappedQuadraticWidthSum A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P, CappedQuadraticWidthBound A reg x n ω W := by
  filter_upwards [h_nonneg, h_le_one, h_sum_le] with
    ω h_nonnegω h_le_oneω h_sum_leω
  exact cappedQuadraticWidthBound_of_nonneg_le_one_and_sum_le (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) h_nonnegω h_le_oneω h_sum_leω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, the packaged process-level capped quadratic-width input is monotone in the
numeric bound. -/
lemma cappedQuadraticWidthBound_ae_mono {W W' : ℝ}
    (h_bound : ∀ᵐ ω ∂P, CappedQuadraticWidthBound A reg x n ω W) (hW : W ≤ W') :
    ∀ᵐ ω ∂P, CappedQuadraticWidthBound A reg x n ω W' := by
  filter_upwards [h_bound] with ω h_boundω
  exact cappedQuadraticWidthBound_mono (A := A) (reg := reg) (x := x) (n := n)
    (ω := ω) h_boundω hW

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A capped-sum bound by the log-determinant potential, together with a constant bound on that
potential, gives the packaged process-level capped quadratic-width input. -/
lemma cappedQuadraticWidthBound_of_ellipticalPotential_le_bound {W : ℝ}
    (h_nonneg : ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (h_elliptical :
      cappedQuadraticWidthSum A reg x n ω ≤ ellipticalPotential A reg x n ω)
    (h_potential_le : ellipticalPotential A reg x n ω ≤ W) :
    CappedQuadraticWidthBound A reg x n ω W := by
  exact cappedQuadraticWidthBound_of_nonneg_le_one_and_sum_le (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) h_nonneg h_le_one (h_elliptical.trans h_potential_le)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, a capped-sum bound by the log-determinant potential and an almost-sure constant
bound on that potential give the packaged process-level capped quadratic-width input. -/
lemma cappedQuadraticWidthBound_ae_of_ellipticalPotential_ae_le_bound {W : ℝ}
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (h_elliptical : ∀ᵐ ω ∂P,
      cappedQuadraticWidthSum A reg x n ω ≤ ellipticalPotential A reg x n ω)
    (h_potential_le : ∀ᵐ ω ∂P, ellipticalPotential A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P, CappedQuadraticWidthBound A reg x n ω W := by
  filter_upwards [h_nonneg, h_le_one, h_elliptical, h_potential_le] with
    ω h_nonnegω h_le_oneω h_ellipticalω h_potential_leω
  exact cappedQuadraticWidthBound_of_ellipticalPotential_le_bound (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) h_nonnegω h_le_oneω h_ellipticalω h_potential_leω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, per-step bounds by log-determinant potential increments and a final constant
bound on the potential give the packaged process-level capped quadratic-width input. -/
lemma cappedQuadraticWidthBound_ae_of_ellipticalPotential_step_ae_le_bound {W : ℝ}
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (hdet : ∀ᵐ ω ∂P, designDet A reg x 0 ω ≠ 0)
    (h_step : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      (if t = 0 then 0 else min 1 (widthQuadraticForm A reg x (A t ω) t ω)) ≤
        ellipticalPotentialIncrement A reg x t ω)
    (h_potential_le : ∀ᵐ ω ∂P, ellipticalPotential A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P, CappedQuadraticWidthBound A reg x n ω W := by
  exact cappedQuadraticWidthBound_ae_of_ellipticalPotential_ae_le_bound (A := A)
    (reg := reg) (x := x) (n := n) (P := P) (W := W) h_nonneg h_le_one
    (cappedQuadraticWidthSum_ae_le_ellipticalPotential_of_step_ae_le (A := A)
      (reg := reg) (x := x) (n := n) (P := P) hdet h_step)
    h_potential_le

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, one-step determinant-ratio potential bounds, their bridge to cumulative
potential increments, and a final constant bound on the potential give the packaged process-level
capped quadratic-width input.

This is the packaged form of the determinant-update interface: once the true matrix determinant
lemma proves the `h_step` assumption and the log/telescoping algebra proves
`h_step_le_increment`, the existing regret chain can consume the resulting bound. -/
lemma cappedQuadraticWidthBound_ae_of_ellipticalPotential_stepPotential_ae_le_bound {W : ℝ}
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (hdet : ∀ᵐ ω ∂P, designDet A reg x 0 ω ≠ 0)
    (h_step : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      (if t = 0 then 0 else min 1 (widthQuadraticForm A reg x (A t ω) t ω)) ≤
        ellipticalPotentialStep A reg x t ω)
    (h_step_le_increment : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      ellipticalPotentialStep A reg x t ω ≤ ellipticalPotentialIncrement A reg x t ω)
    (h_potential_le : ∀ᵐ ω ∂P, ellipticalPotential A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P, CappedQuadraticWidthBound A reg x n ω W := by
  exact cappedQuadraticWidthBound_ae_of_ellipticalPotential_ae_le_bound (A := A)
    (reg := reg) (x := x) (n := n) (P := P) (W := W) h_nonneg h_le_one
    (cappedQuadraticWidthSum_ae_le_ellipticalPotential_of_stepPotential_ae_le (A := A)
      (reg := reg) (x := x) (n := n) (P := P) hdet h_step h_step_le_increment)
    h_potential_le

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, one-step determinant-ratio potential bounds, determinant nonvanishing up to the
horizon, and a final constant bound on the potential give the packaged process-level capped
quadratic-width input.

This is the determinant-nonvanishing version of the one-step interface: the remaining hard
elliptical-potential work is to prove the one-step matrix inequality and the final
log-determinant bound. -/
lemma cappedQuadraticWidthBound_ae_of_ellipticalPotential_stepPotential_ae_le_bound_of_det_ne_zero
    {W : ℝ}
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (hdet : ∀ᵐ ω ∂P, ∀ t, t ∈ range (n + 1) → designDet A reg x t ω ≠ 0)
    (h_step : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      (if t = 0 then 0 else min 1 (widthQuadraticForm A reg x (A t ω) t ω)) ≤
        ellipticalPotentialStep A reg x t ω)
    (h_potential_le : ∀ᵐ ω ∂P, ellipticalPotential A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P, CappedQuadraticWidthBound A reg x n ω W := by
  exact cappedQuadraticWidthBound_ae_of_ellipticalPotential_ae_le_bound (A := A)
    (reg := reg) (x := x) (n := n) (P := P) (W := W) h_nonneg h_le_one
    (cappedQuadraticWidthSum_ae_le_ellipticalPotential_of_stepPotential_ae_le_of_det_ne_zero
      (A := A) (reg := reg) (x := x) (n := n) (P := P) hdet h_step)
    h_potential_le

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, the determinant-update step, determinant nonvanishing up to the horizon, and a
final constant bound on the log-determinant potential give the packaged capped quadratic-width
input used by the regret chain.

The assumptions now match the concrete obligations left for a full elliptical-potential proof:

* prove all relevant design determinants are nonzero;
* prove selected quadratic forms are nonnegative and at most `1` at positive times;
* prove the final log-determinant potential is at most `W`. -/
lemma cappedQuadraticWidthBound_ae_of_det_update_ellipticalPotential_le_bound {W : ℝ}
    (hdet : ∀ᵐ ω ∂P, ∀ t, t ∈ range (n + 1) → designDet A reg x t ω ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (h_potential_le : ∀ᵐ ω ∂P, ellipticalPotential A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P, CappedQuadraticWidthBound A reg x n ω W := by
  have hdet_range_n : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → designDet A reg x t ω ≠ 0 := by
    filter_upwards [hdet] with ω hdetω
    intro t ht
    exact hdetω t (mem_range.mpr (Nat.lt_trans (mem_range.mp ht) (Nat.lt_succ_self n)))
  have h_nonneg_positive : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω := by
    filter_upwards [h_nonneg] with ω h_nonnegω
    intro t ht _
    exact h_nonnegω t ht
  exact cappedQuadraticWidthBound_ae_of_ellipticalPotential_stepPotential_ae_le_bound_of_det_ne_zero
    (A := A) (reg := reg) (x := x) (n := n) (P := P) (W := W)
    h_nonneg_positive h_le_one hdet
    (cappedWidthTerm_ae_le_ellipticalPotentialStep_of_det_ne_zero (A := A) (reg := reg)
      (x := x) (n := n) (P := P) hdet_range_n h_nonneg h_le_one)
    h_potential_le

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, a nonzero initial determinant, the determinant-update step, and a final constant
bound on the log-determinant potential give the packaged capped quadratic-width input used by the
regret chain.

This removes the need to assume determinant nonvanishing at every time: it is derived inductively
from `det(V_0) ≠ 0` and nonnegative selected quadratic forms. -/
lemma cappedQuadraticWidthBound_ae_of_initial_det_update_ellipticalPotential_le_bound {W : ℝ}
    (hdet0 : ∀ᵐ ω ∂P, designDet A reg x 0 ω ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (h_potential_le : ∀ᵐ ω ∂P, ellipticalPotential A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P, CappedQuadraticWidthBound A reg x n ω W := by
  exact cappedQuadraticWidthBound_ae_of_det_update_ellipticalPotential_le_bound (A := A)
    (reg := reg) (x := x) (n := n) (P := P) (W := W)
    (designDet_ae_ne_zero_of_initial_and_widthQuadraticForm_ae_nonneg (A := A)
      (reg := reg) (x := x) (n := n) (P := P) hdet0 h_nonneg)
    h_nonneg h_le_one h_potential_le

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, a nonzero regularization parameter, the determinant-update step, and a final
constant bound on the log-determinant potential give the packaged capped quadratic-width input used
by the regret chain. -/
lemma cappedQuadraticWidthBound_ae_of_reg_ne_zero_det_update_ellipticalPotential_le_bound {W : ℝ}
    (hreg : reg ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (h_potential_le : ∀ᵐ ω ∂P, ellipticalPotential A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P, CappedQuadraticWidthBound A reg x n ω W := by
  refine cappedQuadraticWidthBound_ae_of_initial_det_update_ellipticalPotential_le_bound
    (A := A) (reg := reg) (x := x) (n := n) (P := P) (W := W) ?_ h_nonneg h_le_one
    h_potential_le
  exact Filter.Eventually.of_forall fun ω ↦
    designDet_zero_ne_zero_of_reg_ne_zero (A := A) (reg := reg) (x := x) (ω := ω) hreg

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Positive regularization discharges the determinant-nonvanishing and quadratic-form
nonnegativity obligations in the log-determinant elliptical-potential chain. -/
lemma cappedQuadraticWidthBound_ae_of_reg_pos_det_update_ellipticalPotential_le_bound {W : ℝ}
    (hreg_pos : 0 < reg)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (h_potential_le : ∀ᵐ ω ∂P, ellipticalPotential A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P, CappedQuadraticWidthBound A reg x n ω W := by
  exact cappedQuadraticWidthBound_ae_of_det_update_ellipticalPotential_le_bound
    (A := A) (reg := reg) (x := x) (n := n) (P := P) (W := W)
    (designDet_ae_ne_zero_of_reg_pos (A := A) (reg := reg) (x := x)
      (n := n + 1) (P := P) hreg_pos)
    (widthQuadraticForm_ae_nonneg_of_reg_nonneg (A := A) (reg := reg) (x := x)
      (n := n) (P := P) hreg_pos.le)
    h_le_one h_potential_le

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, a nonzero initial determinant, nonnegative selected quadratic forms, a
determinant-ratio upper bound, and the determinant-update step give the packaged capped
quadratic-width input used by the regret chain.

This version accepts the determinant-ratio bound directly and converts it into the
`ellipticalPotential ≤ 2 * log D` bound internally. -/
lemma cappedQuadraticWidthBound_ae_of_initial_det_update_designDetRatio_le_bound {D : ℝ}
    (hdet0 : ∀ᵐ ω ∂P, designDet A reg x 0 ω ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (h_ratio_le : ∀ᵐ ω ∂P, designDetRatio A reg x n ω ≤ D) :
    ∀ᵐ ω ∂P, CappedQuadraticWidthBound A reg x n ω (2 * Real.log D) := by
  exact cappedQuadraticWidthBound_ae_of_initial_det_update_ellipticalPotential_le_bound
    (A := A) (reg := reg) (x := x) (n := n) (P := P) (W := 2 * Real.log D)
    hdet0 h_nonneg h_le_one
    (ellipticalPotential_ae_le_two_mul_log_of_designDetRatio_ae_le (A := A)
      (reg := reg) (x := x) (n := n) (P := P)
      (designDetRatio_ae_pos_of_initial_and_widthQuadraticForm_ae_nonneg (A := A)
        (reg := reg) (x := x) (n := n) (P := P) hdet0 h_nonneg)
      h_ratio_le)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, a nonzero regularization parameter, nonnegative selected quadratic forms, a
determinant-ratio upper bound, and the determinant-update step give the packaged capped
quadratic-width input used by the regret chain.

This is the most direct interface for the final determinant-bound part of the finite-action
elliptical-potential argument: after proving `designDetRatio ≤ D`, the theorem supplies the
`CappedQuadraticWidthBound` with bound `2 * log D`. -/
lemma cappedQuadraticWidthBound_ae_of_reg_ne_zero_det_update_designDetRatio_le_bound {D : ℝ}
    (hreg : reg ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (h_ratio_le : ∀ᵐ ω ∂P, designDetRatio A reg x n ω ≤ D) :
    ∀ᵐ ω ∂P, CappedQuadraticWidthBound A reg x n ω (2 * Real.log D) := by
  refine cappedQuadraticWidthBound_ae_of_initial_det_update_designDetRatio_le_bound
    (A := A) (reg := reg) (x := x) (n := n) (P := P) ?_ h_nonneg h_le_one h_ratio_le
  exact Filter.Eventually.of_forall fun ω ↦
    designDet_zero_ne_zero_of_reg_ne_zero (A := A) (reg := reg) (x := x) (ω := ω) hreg

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A simple explicit determinant-ratio bound for the capped quadratic-width input.

If `reg ≠ 0` and every selected quadratic form is almost surely in `[0, 1]`, then the determinant
ratio is at most `2 ^ n`, so the existing determinant-update/elliptical-potential chain gives the
packaged capped-width bound with budget `2 * log (2 ^ n)`. -/
lemma cappedQuadraticWidthBound_ae_of_reg_ne_zero_det_update_two_pow_bound
    (hreg : reg ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1) :
    ∀ᵐ ω ∂P,
      CappedQuadraticWidthBound A reg x n ω (2 * Real.log ((2 : ℝ) ^ n)) := by
  refine cappedQuadraticWidthBound_ae_of_reg_ne_zero_det_update_designDetRatio_le_bound
    (A := A) (reg := reg) (x := x) (n := n) (P := P) (D := (2 : ℝ) ^ n)
    hreg h_nonneg ?_ ?_
  · filter_upwards [h_le_one] with ω h_le_oneω
    exact fun t ht _ ↦ h_le_oneω t ht
  · exact designDetRatio_ae_le_two_pow_of_reg_ne_zero_and_widthQuadraticForm_ae_le_one
      (A := A) (reg := reg) (x := x) (n := n) (P := P) hreg h_nonneg h_le_one

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Trace-budget interface for the determinant part of the finite-action elliptical-potential
argument.

The future spectral/AM-GM determinant theorem should prove the hypothesis
`designDetRatio ≤ (T / (reg * d)) ^ d`, where `T` is an upper bound on `trace(V_n)`. This theorem
then feeds that determinant-ratio bound into the already-proved determinant-update and
elliptical-potential chain. -/
lemma cappedQuadraticWidthBound_ae_of_reg_ne_zero_det_update_trace_budget_bound
    (hreg : reg ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (T : ℝ)
    (h_ratio_le : ∀ᵐ ω ∂P,
      designDetRatio A reg x n ω ≤ (T / (reg * (d : ℝ))) ^ d) :
    ∀ᵐ ω ∂P,
      CappedQuadraticWidthBound A reg x n ω
        (2 * Real.log ((T / (reg * (d : ℝ))) ^ d)) := by
  exact cappedQuadraticWidthBound_ae_of_reg_ne_zero_det_update_designDetRatio_le_bound
    (A := A) (reg := reg) (x := x) (n := n) (P := P)
    (D := (T / (reg * (d : ℝ))) ^ d) hreg h_nonneg h_le_one h_ratio_le

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Feature-norm-budget interface for the determinant part of the finite-action
elliptical-potential argument.

If selected feature vectors have squared norm at most `L2`, then `trace(V_n) ≤ reg * d + n * L2`.
Given a future deterministic trace/determinant comparison that turns this trace budget into the
determinant-ratio bound, this theorem supplies the packaged capped-width input with the explicit
budget `2 * log (((reg * d + n * L2) / (reg * d)) ^ d)`. -/
lemma cappedQuadraticWidthBound_ae_of_reg_ne_zero_det_update_featureSqNorm_budget_bound
    (hreg : reg ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (L2 : ℝ)
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ L2)
    (h_ratio_of_trace : ∀ ω,
      designTrace A reg x n ω ≤ reg * (d : ℝ) + (n : ℝ) * L2 →
        designDetRatio A reg x n ω ≤
          ((reg * (d : ℝ) + (n : ℝ) * L2) / (reg * (d : ℝ))) ^ d) :
    ∀ᵐ ω ∂P,
      CappedQuadraticWidthBound A reg x n ω
        (2 * Real.log (((reg * (d : ℝ) + (n : ℝ) * L2) / (reg * (d : ℝ))) ^ d)) := by
  exact cappedQuadraticWidthBound_ae_of_reg_ne_zero_det_update_trace_budget_bound
    (A := A) (reg := reg) (x := x) (n := n) (P := P)
    (T := reg * (d : ℝ) + (n : ℝ) * L2) hreg h_nonneg h_le_one
    (designDetRatio_ae_le_trace_budget_of_featureSqNorm_bound (A := A) (reg := reg)
      (x := x) (n := n) (P := P) L2 hL2 h_ratio_of_trace)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The explicit feature-norm determinant budget can be rewritten in the common
`d * log(1 + n L² / (reg d))` form. -/
lemma featureSqNorm_budget_log_eq_dim_mul_log_one_add
    (L2 : ℝ) (hden : reg * (d : ℝ) ≠ 0) :
    2 * Real.log (((reg * (d : ℝ) + (n : ℝ) * L2) / (reg * (d : ℝ))) ^ d) =
      2 * (d : ℝ) * Real.log (1 + (n : ℝ) * L2 / (reg * (d : ℝ))) := by
  have hbase :
      (reg * (d : ℝ) + (n : ℝ) * L2) / (reg * (d : ℝ)) =
        1 + (n : ℝ) * L2 / (reg * (d : ℝ)) := by
    exact same_add_div hden
  rw [Real.log_pow, hbase]
  ring

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Feature-norm-budget interface with the log term rewritten in the standard
`2 * d * log(1 + n L² / (reg d))` shape. -/
lemma cappedQuadraticWidthBound_ae_of_reg_ne_zero_det_update_featureSqNorm_budget_bound'
    (hreg : reg ≠ 0) (hd : d ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (L2 : ℝ)
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ L2)
    (h_ratio_of_trace : ∀ ω,
      designTrace A reg x n ω ≤ reg * (d : ℝ) + (n : ℝ) * L2 →
        designDetRatio A reg x n ω ≤
          ((reg * (d : ℝ) + (n : ℝ) * L2) / (reg * (d : ℝ))) ^ d) :
    ∀ᵐ ω ∂P,
      CappedQuadraticWidthBound A reg x n ω
        (2 * (d : ℝ) * Real.log (1 + (n : ℝ) * L2 / (reg * (d : ℝ)))) := by
  have hden : reg * (d : ℝ) ≠ 0 := by
    exact mul_ne_zero hreg (by exact_mod_cast hd)
  rw [← featureSqNorm_budget_log_eq_dim_mul_log_one_add (reg := reg) (n := n) L2 hden]
  exact cappedQuadraticWidthBound_ae_of_reg_ne_zero_det_update_featureSqNorm_budget_bound
    (A := A) (reg := reg) (x := x) (n := n) (P := P) hreg h_nonneg h_le_one L2 hL2
    h_ratio_of_trace

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Feature-norm-budget interface with the determinant/trace comparison stated as a determinant
upper bound for `V_n`, rather than directly as a determinant-ratio bound. -/
lemma cappedQuadraticWidthBound_ae_of_reg_pos_det_update_featureSqNorm_budget_bound_of_designDet_le
    (hreg_pos : 0 < reg) (hd : d ≠ 0)
    (h_width_le_feature : WidthQuadraticFormLeFeatureSqNormDivReg A reg x)
    (L2 : ℝ)
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ L2)
    (hL2_le_reg : L2 ≤ reg)
    (hdet_of_trace : ∀ ω,
      designTrace A reg x n ω ≤ reg * (d : ℝ) + (n : ℝ) * L2 →
        designDet A reg x n ω ≤
          ((reg * (d : ℝ) + (n : ℝ) * L2) / (d : ℝ)) ^ d) :
    ∀ᵐ ω ∂P,
      CappedQuadraticWidthBound A reg x n ω
        (2 * (d : ℝ) * Real.log (1 + (n : ℝ) * L2 / (reg * (d : ℝ)))) := by
  refine cappedQuadraticWidthBound_ae_of_reg_ne_zero_det_update_featureSqNorm_budget_bound'
    (A := A) (reg := reg) (x := x) (n := n) (P := P) hreg_pos.ne' hd
    (widthQuadraticForm_ae_nonneg_of_reg_nonneg (A := A) (reg := reg) (x := x)
      (n := n) (P := P) hreg_pos.le)
    (widthQuadraticForm_ae_le_one_of_featureSqNorm_ae_le (A := A) (reg := reg)
      (x := x) (n := n) (P := P) h_width_le_feature hreg_pos hL2 hL2_le_reg)
    L2 hL2 ?_
  intro ω h_traceω
  exact designDetRatio_le_trace_budget_of_designDet_le (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) (T := reg * (d : ℝ) + (n : ℝ) * L2) hreg_pos hd
    (hdet_of_trace ω h_traceω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Feature-norm-budget interface where the remaining matrix-analysis input is the reusable
positive-semidefinite determinant/trace comparison `det(M) ≤ (trace(M) / d) ^ d`. -/
lemma cappedQuadraticWidthBound_ae_of_matrix_det_trace_bound
    (hreg_pos : 0 < reg) (hd : d ≠ 0)
    (h_width_le_feature : WidthQuadraticFormLeFeatureSqNormDivReg A reg x)
    (L2 : ℝ)
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ L2)
    (hL2_le_reg : L2 ≤ reg)
    (hdet_trace : MatrixDetLeTraceAveragePow d) :
    ∀ᵐ ω ∂P,
      CappedQuadraticWidthBound A reg x n ω
        (2 * (d : ℝ) * Real.log (1 + (n : ℝ) * L2 / (reg * (d : ℝ)))) := by
  refine
    cappedQuadraticWidthBound_ae_of_reg_pos_det_update_featureSqNorm_budget_bound_of_designDet_le
    (A := A) (reg := reg) (x := x) (n := n) (P := P) hreg_pos hd
    h_width_le_feature L2 hL2 hL2_le_reg ?_
  intro ω h_traceω
  exact designDet_le_trace_budget_of_matrix_det_trace_bound (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) hdet_trace hreg_pos.le hd
    (reg * (d : ℝ) + (n : ℝ) * L2) h_traceω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The packaged process-level capped quadratic-width input implies the `widthSqSum` bound consumed
by the regret chain. -/
lemma widthSqSum_le_of_capped_quadratic_width_bound {W : ℝ}
    (h_bound : CappedQuadraticWidthBound A reg x n ω W) :
    widthSqSum A reg x n ω ≤ W := by
  exact widthSqSum_le_of_capped_quadratic_width_sum_le (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω) h_bound.1 h_bound.2.1 h_bound.2.2

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, the packaged process-level capped quadratic-width input implies the `widthSqSum`
bound consumed by the regret chain. -/
lemma widthSqSum_ae_le_of_capped_quadratic_width_bound_ae {W : ℝ}
    (h_bound : ∀ᵐ ω ∂P, CappedQuadraticWidthBound A reg x n ω W) :
    ∀ᵐ ω ∂P, widthSqSum A reg x n ω ≤ W := by
  filter_upwards [h_bound] with ω h_boundω
  exact widthSqSum_le_of_capped_quadratic_width_bound (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω) (W := W) h_boundω

/-- The process-level LinUCB optimistic index. -/
noncomputable def index (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d) (a : Fin K)
    (n : ℕ) (ω : Ω) : ℝ :=
  estimatedReward A R reg x a n ω + √(β (n + 1)) * width A reg x a n ω

/-- At time zero, the LinUCB index is only the confidence bonus because the estimated reward is
zero. -/
lemma index_zero (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d) (a : Fin K) (ω : Ω) :
    index A R reg β x a 0 ω = √(β 1) * width A reg x a 0 ω := by
  simp [index, estimatedReward_zero]

/-- At time zero, the LinUCB index is the confidence schedule times the initial quadratic-form
width. -/
lemma index_zero_eq_initial_quadratic_form (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d) (a : Fin K) (ω : Ω) :
    index A R reg β x a 0 ω =
      √(β 1) * √(dotProduct (x a) (Matrix.mulVec (reg • 1)⁻¹ (x a))) := by
  simp [index_zero, width_zero]

lemma designMatrix_eq_designMatrix' (reg : ℝ) (x : Fin K → Feature d) (n : ℕ)
    (ω : Ω) (hn : n ≠ 0) :
    designMatrix A reg x n ω =
      designMatrix' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n =>
    simp only [designMatrix, designMatrix', IsAlgEnvSeq.hist]
    rw [Nat.range_succ_eq_Iic]
    exact congrArg (fun S ↦ reg • 1 + S) <|
      (Finset.sum_coe_sort (Iic n)
        (fun s ↦ Matrix.vecMulVec (x (A s ω)) (x (A s ω)))).symm

lemma responseVector_eq_responseVector' (x : Fin K → Feature d)
    (n : ℕ) (ω : Ω) (hn : n ≠ 0) :
    responseVector A R x n ω = responseVector' x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n =>
    simp only [responseVector, responseVector', IsAlgEnvSeq.hist]
    rw [Nat.range_succ_eq_Iic]
    exact (Finset.sum_coe_sort (Iic n) (fun s ↦ R s ω • x (A s ω))).symm

lemma thetaHat_eq_thetaHat' (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) (ω : Ω) (hn : n ≠ 0) :
    thetaHat A R reg x n ω = thetaHat' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) := by
  simp [thetaHat, thetaHat', designMatrix_eq_designMatrix' (A := A) (R := R) reg x n ω hn,
    responseVector_eq_responseVector' (A := A) (R := R) x n ω hn]

lemma estimatedReward_eq_estimatedReward' (reg : ℝ) (x : Fin K → Feature d)
    (a : Fin K) (n : ℕ) (ω : Ω) (hn : n ≠ 0) :
    estimatedReward A R reg x a n ω =
      estimatedReward' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) a := by
  simp [estimatedReward, estimatedReward', thetaHat_eq_thetaHat' (A := A) (R := R) reg x n ω hn]

lemma widthQuadraticForm_eq_widthQuadraticForm' (reg : ℝ) (x : Fin K → Feature d)
    (a : Fin K) (n : ℕ) (ω : Ω) (hn : n ≠ 0) :
    widthQuadraticForm A reg x a n ω =
      widthQuadraticForm' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) a := by
  simp [widthQuadraticForm, widthQuadraticForm',
    designMatrix_eq_designMatrix' (A := A) (R := R) reg x n ω hn]

/-- At positive process times, nonnegativity of the process-level width quadratic form is
equivalent to nonnegativity of the matching history-level width quadratic form. -/
lemma widthQuadraticForm_nonneg_iff_widthQuadraticForm' (reg : ℝ) (x : Fin K → Feature d)
    (a : Fin K) (n : ℕ) (ω : Ω) (hn : n ≠ 0) :
    0 ≤ widthQuadraticForm A reg x a n ω ↔
      0 ≤ widthQuadraticForm' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) a := by
  rw [widthQuadraticForm_eq_widthQuadraticForm' (A := A) (R := R) reg x a n ω hn]

/-- At positive process times, the process-level quadratic width form is at most `1` iff the
matching history-level quadratic width form is at most `1`. -/
lemma widthQuadraticForm_le_one_iff_widthQuadraticForm' (reg : ℝ) (x : Fin K → Feature d)
    (a : Fin K) (n : ℕ) (ω : Ω) (hn : n ≠ 0) :
    widthQuadraticForm A reg x a n ω ≤ 1 ↔
      widthQuadraticForm' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) a ≤ 1 := by
  rw [widthQuadraticForm_eq_widthQuadraticForm' (A := A) (R := R) reg x a n ω hn]

/-- The all-positive-times process-level nonnegativity assumption is equivalent to the matching
history-level nonnegativity assumption. -/
lemma widthQuadraticForm_all_nonneg_iff_history (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) (ω : Ω) :
    (∀ t, t ∈ range n → t ≠ 0 → 0 ≤ widthQuadraticForm A reg x (A t ω) t ω) ↔
      ∀ t, t ∈ range n → t ≠ 0 →
        0 ≤ widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω) := by
  constructor
  · intro h t ht ht0
    exact (widthQuadraticForm_nonneg_iff_widthQuadraticForm' (A := A) (R := R) reg x
      (A t ω) t ω ht0).1 (h t ht ht0)
  · intro h t ht ht0
    exact (widthQuadraticForm_nonneg_iff_widthQuadraticForm' (A := A) (R := R) reg x
      (A t ω) t ω ht0).2 (h t ht ht0)

/-- The all-positive-times process-level `≤ 1` assumption is equivalent to the matching
history-level `≤ 1` assumption. -/
lemma widthQuadraticForm_all_le_one_iff_history (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) (ω : Ω) :
    (∀ t, t ∈ range n → t ≠ 0 → widthQuadraticForm A reg x (A t ω) t ω ≤ 1) ↔
      ∀ t, t ∈ range n → t ≠ 0 →
        widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω) ≤ 1 := by
  constructor
  · intro h t ht ht0
    exact (widthQuadraticForm_le_one_iff_widthQuadraticForm' (A := A) (R := R) reg x
      (A t ω) t ω ht0).1 (h t ht ht0)
  · intro h t ht ht0
    exact (widthQuadraticForm_le_one_iff_widthQuadraticForm' (A := A) (R := R) reg x
      (A t ω) t ω ht0).2 (h t ht ht0)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, process-level all-positive-times nonnegativity is equivalent to the matching
history-level nonnegativity assumption. -/
lemma widthQuadraticForm_ae_all_nonneg_iff_history (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) :
    (∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω) ↔
      ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
        0 ≤ widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω) := by
  constructor
  · intro h
    filter_upwards [h] with ω hω
    exact (widthQuadraticForm_all_nonneg_iff_history (A := A) (R := R) reg x n ω).1 hω
  · intro h
    filter_upwards [h] with ω hω
    exact (widthQuadraticForm_all_nonneg_iff_history (A := A) (R := R) reg x n ω).2 hω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, the process-level all-positive-times `≤ 1` assumption is equivalent to the
matching history-level `≤ 1` assumption. -/
lemma widthQuadraticForm_ae_all_le_one_iff_history (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) :
    (∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1) ↔
      ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
        widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω) ≤ 1 := by
  constructor
  · intro h
    filter_upwards [h] with ω hω
    exact (widthQuadraticForm_all_le_one_iff_history (A := A) (R := R) reg x n ω).1 hω
  · intro h
    filter_upwards [h] with ω hω
    exact (widthQuadraticForm_all_le_one_iff_history (A := A) (R := R) reg x n ω).2 hω

lemma width_eq_width' (reg : ℝ) (x : Fin K → Feature d)
    (a : Fin K) (n : ℕ) (ω : Ω) (hn : n ≠ 0) :
    width A reg x a n ω = width' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) a := by
  simp [width, width', widthQuadraticForm_eq_widthQuadraticForm' (A := A) (R := R) reg x a n
    ω hn]

/-- At positive process times, squaring the process-level width recovers the matching history-level
quadratic form when that history-level quadratic form is nonnegative. -/
lemma width_sq_eq_widthQuadraticForm' (reg : ℝ) (x : Fin K → Feature d)
    (a : Fin K) (n : ℕ) (ω : Ω) (hn : n ≠ 0)
    (h_nonneg :
      0 ≤ widthQuadraticForm' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) a) :
    width A reg x a n ω ^ 2 =
      widthQuadraticForm' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) a := by
  rw [width_eq_width' (A := A) (R := R) reg x a n ω hn]
  exact width'_sq_eq_quadratic_form reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) a
    h_nonneg

/-- At positive process times, advancing `widthSqSum` adds the matching history-level quadratic
form when that history-level quadratic form is nonnegative. -/
lemma widthSqSum_succ_eq_add_widthQuadraticForm' (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) (ω : Ω) (hn : n ≠ 0)
    (h_nonneg :
      0 ≤ widthQuadraticForm' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) (A n ω)) :
    widthSqSum A reg x (n + 1) ω =
      widthSqSum A reg x n ω +
        widthQuadraticForm' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) (A n ω) := by
  rw [widthSqSum_succ_of_ne_zero (A := A) (reg := reg) (x := x) (n := n) (ω := ω) hn]
  rw [width_sq_eq_widthQuadraticForm' (A := A) (R := R) reg x (A n ω) n ω hn h_nonneg]

/-- At positive process times, advancing `quadraticWidthSum` adds the matching history-level
quadratic form. -/
lemma quadraticWidthSum_succ_eq_add_widthQuadraticForm' (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) (ω : Ω) (hn : n ≠ 0) :
    quadraticWidthSum A reg x (n + 1) ω =
      quadraticWidthSum A reg x n ω +
        widthQuadraticForm' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) (A n ω) := by
  rw [quadraticWidthSum_succ_of_ne_zero (A := A) (reg := reg) (x := x) (n := n)
    (ω := ω) hn]
  rw [widthQuadraticForm_eq_widthQuadraticForm' (A := A) (R := R) reg x (A n ω) n ω hn]

/-- The history-level quadratic-form accumulator aligned with process times.

The term at process time `t = 0` is set to zero, matching the convention used by `widthSqSum` and
`quadraticWidthSum`. At positive process time `t`, the history available to LinUCB is
`IsAlgEnvSeq.hist A R (t - 1) ω`. -/
noncomputable def historyQuadraticWidthSum (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ range n,
    if t = 0 then 0 else
      widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω)

/-- No positive-time history-level quadratic width forms are accumulated at horizon zero. -/
lemma historyQuadraticWidthSum_zero (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (ω : Ω) :
    historyQuadraticWidthSum A R reg x 0 ω = 0 := by
  simp [historyQuadraticWidthSum]

/-- Advancing the horizon adds the next positive-time history-level quadratic width form. -/
lemma historyQuadraticWidthSum_succ (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) :
    historyQuadraticWidthSum A R reg x (n + 1) ω =
      historyQuadraticWidthSum A R reg x n ω +
        if n = 0 then 0 else
          widthQuadraticForm' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) (A n ω) := by
  simp [historyQuadraticWidthSum, sum_range_succ]

/-- At positive process times, advancing the history-level quadratic accumulator adds the selected
arm's history-level quadratic width form. -/
lemma historyQuadraticWidthSum_succ_of_ne_zero (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) (hn : n ≠ 0) :
    historyQuadraticWidthSum A R reg x (n + 1) ω =
      historyQuadraticWidthSum A R reg x n ω +
        widthQuadraticForm' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) (A n ω) := by
  simp [historyQuadraticWidthSum_succ, hn]

/-- The capped history-level quadratic-form accumulator aligned with process times.

This is the accumulator shape that commonly appears in elliptical-potential statements:
each positive-time quadratic width form is capped at `1`. -/
noncomputable def historyCappedQuadraticWidthSum (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ range n,
    if t = 0 then 0 else
      min 1 (widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω))

/-- No positive-time capped history-level quadratic width forms are accumulated at horizon zero. -/
lemma historyCappedQuadraticWidthSum_zero (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (ω : Ω) :
    historyCappedQuadraticWidthSum A R reg x 0 ω = 0 := by
  simp [historyCappedQuadraticWidthSum]

/-- Advancing the horizon adds the next positive-time capped history-level quadratic width form. -/
lemma historyCappedQuadraticWidthSum_succ (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) :
    historyCappedQuadraticWidthSum A R reg x (n + 1) ω =
      historyCappedQuadraticWidthSum A R reg x n ω +
        if n = 0 then 0 else
          min 1
            (widthQuadraticForm' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) (A n ω)) := by
  simp [historyCappedQuadraticWidthSum, sum_range_succ]

/-- At positive process times, advancing the capped history-level quadratic accumulator adds the
selected arm's capped history-level quadratic width form. -/
lemma historyCappedQuadraticWidthSum_succ_of_ne_zero
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) (hn : n ≠ 0) :
    historyCappedQuadraticWidthSum A R reg x (n + 1) ω =
      historyCappedQuadraticWidthSum A R reg x n ω +
        min 1
          (widthQuadraticForm' reg x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) (A n ω)) := by
  simp [historyCappedQuadraticWidthSum_succ, hn]

/-- The process-level capped quadratic-width accumulator equals the history-level capped
accumulator aligned with the same process times. -/
lemma cappedQuadraticWidthSum_eq_historyCappedQuadraticWidthSum (reg : ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) :
    cappedQuadraticWidthSum A reg x n ω =
      historyCappedQuadraticWidthSum A R reg x n ω := by
  rw [cappedQuadraticWidthSum, historyCappedQuadraticWidthSum]
  refine sum_congr rfl ?_
  intro t ht
  by_cases ht0 : t = 0
  · simp [ht0]
  · rw [if_neg ht0, if_neg ht0]
    exact congrArg (fun q : ℝ ↦ min 1 q)
      (widthQuadraticForm_eq_widthQuadraticForm' (A := A) (R := R) reg x (A t ω) t ω ht0)

/-- A process-level capped quadratic-width sum bound is equivalent to the matching history-level
capped quadratic-width sum bound. -/
lemma cappedQuadraticWidthSum_le_iff_historyCappedQuadraticWidthSum_le
    (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) (W : ℝ) :
    cappedQuadraticWidthSum A reg x n ω ≤ W ↔
      historyCappedQuadraticWidthSum A R reg x n ω ≤ W := by
  rw [cappedQuadraticWidthSum_eq_historyCappedQuadraticWidthSum (A := A) (R := R)
    reg x n ω]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, a process-level capped quadratic-width sum bound is equivalent to the matching
history-level capped quadratic-width sum bound. -/
lemma cappedQuadraticWidthSum_ae_le_iff_historyCappedQuadraticWidthSum_ae_le
    (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (W : ℝ) :
    (∀ᵐ ω ∂P, cappedQuadraticWidthSum A reg x n ω ≤ W) ↔
      ∀ᵐ ω ∂P, historyCappedQuadraticWidthSum A R reg x n ω ≤ W := by
  constructor
  · intro h
    filter_upwards [h] with ω hω
    exact (cappedQuadraticWidthSum_le_iff_historyCappedQuadraticWidthSum_le
      (A := A) (R := R) reg x n ω W).1 hω
  · intro h
    filter_upwards [h] with ω hω
    exact (cappedQuadraticWidthSum_le_iff_historyCappedQuadraticWidthSum_le
      (A := A) (R := R) reg x n ω W).2 hω

/-- If every positive-time history-level quadratic width form is at most `1`, then the uncapped and
capped history-level accumulators agree. -/
lemma historyQuadraticWidthSum_eq_historyCappedQuadraticWidthSum
    (h_le_one : ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω) ≤ 1) :
    historyQuadraticWidthSum A R reg x n ω =
      historyCappedQuadraticWidthSum A R reg x n ω := by
  rw [historyQuadraticWidthSum, historyCappedQuadraticWidthSum]
  refine sum_congr rfl ?_
  intro t ht
  by_cases ht0 : t = 0
  · simp [ht0]
  · rw [if_neg ht0, if_neg ht0]
    exact (min_eq_right (h_le_one t ht ht0)).symm

/-- The process-level quadratic-width accumulator equals the history-level accumulator aligned with
the same process times. -/
lemma quadraticWidthSum_eq_historyQuadraticWidthSum (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) (ω : Ω) :
    quadraticWidthSum A reg x n ω = historyQuadraticWidthSum A R reg x n ω := by
  rw [quadraticWidthSum, historyQuadraticWidthSum]
  refine sum_congr rfl ?_
  intro t ht
  by_cases ht0 : t = 0
  · simp [ht0]
  · rw [if_neg ht0, if_neg ht0]
    exact widthQuadraticForm_eq_widthQuadraticForm' (A := A) (R := R) reg x (A t ω) t ω ht0

/-- The squared-width accumulator equals the history-level quadratic-form accumulator whenever the
positive-time history-level quadratic forms are nonnegative. -/
lemma widthSqSum_eq_historyQuadraticWidthSum
    (h_nonneg : ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω)) :
    widthSqSum A reg x n ω = historyQuadraticWidthSum A R reg x n ω := by
  have h_process_nonneg : ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω := by
    intro t ht ht0
    exact (widthQuadraticForm_nonneg_iff_widthQuadraticForm' (A := A) (R := R) reg x
      (A t ω) t ω ht0).2 (h_nonneg t ht ht0)
  rw [widthSqSum_eq_sum_quadratic_form (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω) h_process_nonneg]
  exact quadraticWidthSum_eq_historyQuadraticWidthSum (A := A) (R := R) reg x n ω

/-- A bound on the history-level quadratic-form accumulator implies the corresponding bound on
`widthSqSum`, provided the positive-time history-level quadratic forms are nonnegative. -/
lemma widthSqSum_le_of_history_quadratic_width_sum_le {W : ℝ}
    (h_nonneg : ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω))
    (h_hist_le : historyQuadraticWidthSum A R reg x n ω ≤ W) :
    widthSqSum A reg x n ω ≤ W := by
  rw [widthSqSum_eq_historyQuadraticWidthSum (A := A) (R := R) (reg := reg) (x := x)
    (n := n) (ω := ω) h_nonneg]
  exact h_hist_le

omit [IsProbabilityMeasure P] in
/-- Almost surely, a history-level quadratic-form bound gives the `widthSqSum` bound consumed by
the regret chain. -/
lemma widthSqSum_ae_le_of_history_quadratic_width_sum_ae_le {W : ℝ}
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω))
    (h_hist_le : ∀ᵐ ω ∂P, historyQuadraticWidthSum A R reg x n ω ≤ W) :
    ∀ᵐ ω ∂P, widthSqSum A reg x n ω ≤ W := by
  filter_upwards [h_nonneg, h_hist_le] with ω h_nonnegω h_hist_leω
  exact widthSqSum_le_of_history_quadratic_width_sum_le (A := A) (R := R) (reg := reg)
    (x := x) (n := n) (ω := ω) h_nonnegω h_hist_leω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The pointwise input expected from a future elliptical-potential argument.

It packages the two facts needed to turn a history-level quadratic-width estimate into the
`widthSqSum` estimate used by the regret chain:

* each positive-time quadratic width form is nonnegative;
* their history-level accumulated sum is bounded by `W`. -/
def HistoryQuadraticWidthBound (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) (W : ℝ) : Prop :=
  (∀ t, t ∈ range n → t ≠ 0 →
    0 ≤ widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω)) ∧
    historyQuadraticWidthSum A R reg x n ω ≤ W

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Build the packaged history-level quadratic-width input from its two component facts. -/
lemma historyQuadraticWidthBound_of_nonneg_and_sum_le {W : ℝ}
    (h_nonneg : ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω))
    (h_sum_le : historyQuadraticWidthSum A R reg x n ω ≤ W) :
    HistoryQuadraticWidthBound A R reg x n ω W := by
  exact ⟨h_nonneg, h_sum_le⟩

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The packaged history-level quadratic-width input is monotone in the numeric bound. -/
lemma historyQuadraticWidthBound_mono {W W' : ℝ}
    (h_bound : HistoryQuadraticWidthBound A R reg x n ω W) (hW : W ≤ W') :
    HistoryQuadraticWidthBound A R reg x n ω W' := by
  exact ⟨h_bound.1, h_bound.2.trans hW⟩

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, build the packaged history-level quadratic-width input from its two component
facts. -/
lemma historyQuadraticWidthBound_ae_of_nonneg_and_sum_ae_le {W : ℝ}
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω))
    (h_sum_le : ∀ᵐ ω ∂P, historyQuadraticWidthSum A R reg x n ω ≤ W) :
    ∀ᵐ ω ∂P, HistoryQuadraticWidthBound A R reg x n ω W := by
  filter_upwards [h_nonneg, h_sum_le] with ω h_nonnegω h_sum_leω
  exact historyQuadraticWidthBound_of_nonneg_and_sum_le (A := A) (R := R)
    (reg := reg) (x := x) (n := n) (ω := ω) h_nonnegω h_sum_leω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, the packaged history-level quadratic-width input is monotone in the numeric
bound. -/
lemma historyQuadraticWidthBound_ae_mono {W W' : ℝ}
    (h_bound : ∀ᵐ ω ∂P, HistoryQuadraticWidthBound A R reg x n ω W) (hW : W ≤ W') :
    ∀ᵐ ω ∂P, HistoryQuadraticWidthBound A R reg x n ω W' := by
  filter_upwards [h_bound] with ω h_boundω
  exact historyQuadraticWidthBound_mono (A := A) (R := R) (reg := reg) (x := x)
    (n := n) (ω := ω) h_boundω hW

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A capped quadratic-width sum bound gives the packaged history-level input whenever every
positive-time quadratic width form is nonnegative and at most `1`. -/
lemma historyQuadraticWidthBound_of_capped_sum_le {W : ℝ}
    (h_nonneg : ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω))
    (h_le_one : ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω) ≤ 1)
    (h_capped_le : historyCappedQuadraticWidthSum A R reg x n ω ≤ W) :
    HistoryQuadraticWidthBound A R reg x n ω W := by
  refine historyQuadraticWidthBound_of_nonneg_and_sum_le (A := A) (R := R)
    (reg := reg) (x := x) (n := n) (ω := ω) h_nonneg ?_
  rw [historyQuadraticWidthSum_eq_historyCappedQuadraticWidthSum (A := A) (R := R)
    (reg := reg) (x := x) (n := n) (ω := ω) h_le_one]
  exact h_capped_le

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, a capped quadratic-width sum bound gives the packaged history-level input
whenever every positive-time quadratic width form is almost surely nonnegative and at most `1`. -/
lemma historyQuadraticWidthBound_ae_of_capped_sum_ae_le {W : ℝ}
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω))
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω) ≤ 1)
    (h_capped_le : ∀ᵐ ω ∂P, historyCappedQuadraticWidthSum A R reg x n ω ≤ W) :
    ∀ᵐ ω ∂P, HistoryQuadraticWidthBound A R reg x n ω W := by
  filter_upwards [h_nonneg, h_le_one, h_capped_le] with
    ω h_nonnegω h_le_oneω h_capped_leω
  exact historyQuadraticWidthBound_of_capped_sum_le (A := A) (R := R) (reg := reg)
    (x := x) (n := n) (ω := ω) h_nonnegω h_le_oneω h_capped_leω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The packaged history-level quadratic-width input implies the `widthSqSum` bound consumed by the
regret chain. -/
lemma widthSqSum_le_of_history_quadratic_width_bound {W : ℝ}
    (h_bound : HistoryQuadraticWidthBound A R reg x n ω W) :
    widthSqSum A reg x n ω ≤ W := by
  exact widthSqSum_le_of_history_quadratic_width_sum_le (A := A) (R := R) (reg := reg)
    (x := x) (n := n) (ω := ω) h_bound.1 h_bound.2

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, the packaged history-level quadratic-width input implies the `widthSqSum` bound
consumed by the regret chain. -/
lemma widthSqSum_ae_le_of_history_quadratic_width_bound_ae {W : ℝ}
    (h_bound : ∀ᵐ ω ∂P, HistoryQuadraticWidthBound A R reg x n ω W) :
    ∀ᵐ ω ∂P, widthSqSum A reg x n ω ≤ W := by
  filter_upwards [h_bound] with ω h_boundω
  exact widthSqSum_le_of_history_quadratic_width_bound (A := A) (R := R) (reg := reg)
    (x := x) (n := n) (ω := ω) (W := W) h_boundω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A capped history-level quadratic-width sum bound implies the `widthSqSum` bound consumed by
the regret chain, provided the positive-time quadratic width forms are nonnegative and at most
`1`. -/
lemma widthSqSum_le_of_capped_history_quadratic_width_sum_le {W : ℝ}
    (h_nonneg : ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω))
    (h_le_one : ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω) ≤ 1)
    (h_capped_le : historyCappedQuadraticWidthSum A R reg x n ω ≤ W) :
    widthSqSum A reg x n ω ≤ W := by
  exact widthSqSum_le_of_history_quadratic_width_bound (A := A) (R := R) (reg := reg)
    (x := x) (n := n) (ω := ω) (W := W)
    (historyQuadraticWidthBound_of_capped_sum_le (A := A) (R := R) (reg := reg)
      (x := x) (n := n) (ω := ω) h_nonneg h_le_one h_capped_le)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Almost surely, a capped history-level quadratic-width sum bound implies the `widthSqSum` bound
consumed by the regret chain, provided the positive-time quadratic width forms are almost surely
nonnegative and at most `1`. -/
lemma widthSqSum_ae_le_of_capped_history_quadratic_width_sum_ae_le {W : ℝ}
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω))
    (h_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω) ≤ 1)
    (h_capped_le : ∀ᵐ ω ∂P, historyCappedQuadraticWidthSum A R reg x n ω ≤ W) :
    ∀ᵐ ω ∂P, widthSqSum A reg x n ω ≤ W := by
  exact widthSqSum_ae_le_of_history_quadratic_width_bound_ae (A := A) (R := R)
    (reg := reg) (x := x) (n := n) (P := P) (W := W)
    (historyQuadraticWidthBound_ae_of_capped_sum_ae_le (A := A) (R := R)
      (reg := reg) (x := x) (n := n) (P := P) (W := W) h_nonneg h_le_one
      h_capped_le)

lemma index_eq_index' (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d)
    (a : Fin K) (n : ℕ) (ω : Ω) (hn : n ≠ 0) :
    index A R reg β x a n ω =
      index' reg β x (n - 1) (IsAlgEnvSeq.hist A R (n - 1) ω) a := by
  have htime : n + 1 = n - 1 + 2 := by grind
  simp [index, index', estimatedReward_eq_estimatedReward' (A := A) (R := R) reg x a n ω hn,
    width_eq_width' (A := A) (R := R) reg x a n ω hn, htime]

/-- The action at time `n + 1` is the finite-action LinUCB argmax for the observed history. -/
lemma arm_ae_eq_linUCBNextArm [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (n : ℕ) :
    A (n + 1) =ᵐ[P]
      fun ω ↦ nextArm hK reg β x n (IsAlgEnvSeq.hist A R n ω) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact h.action_detAlgorithm_ae_eq n

/-- Almost surely, every positive-time action is the finite-action LinUCB argmax. -/
lemma arm_ae_all_eq [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P) :
    ∀ᵐ ω ∂P,
      ∀ n, A (n + 1) ω =
        nextArm hK reg β x n (IsAlgEnvSeq.hist A R n ω) := by
  simp_rw [ae_all_iff]
  exact fun n ↦ arm_ae_eq_linUCBNextArm h n

/-- Finite-action LinUCB chooses an arm maximizing the LinUCB index. -/
lemma index_le_index_arm [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (a : Fin K) (hn : n ≠ 0) :
    ∀ᵐ ω ∂P, index A R reg β x a n ω ≤ index A R reg β x (A n ω) n ω := by
  filter_upwards [arm_ae_eq_linUCBNextArm h (n - 1)] with ω h_arm
  have hn_succ : n - 1 + 1 = n := by grind
  simp only [hn_succ] at h_arm
  rw [index_eq_index' (A := A) (R := R) reg β x a n ω hn,
    index_eq_index' (A := A) (R := R) reg β x (A n ω) n ω hn]
  rw [h_arm]
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact isMaxOn_measurableArgmax (fun h a ↦ index' reg β x (n - 1) h a)
    (IsAlgEnvSeq.hist A R (n - 1) ω) a

/-- Almost surely, the selected arm maximizes the LinUCB index at every positive time. -/
lemma forall_index_le_index_arm [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (a : Fin K) :
    ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      index A R reg β x a n ω ≤ index A R reg β x (A n ω) n ω := by
  simp_rw [ae_all_iff]
  exact fun n hn ↦ index_le_index_arm h a hn

end AlgorithmBehavior

omit [IsMarkovKernel ν] in
/-- If the LinUCB confidence inequalities hold for a comparator arm and the selected arm, and the
selected arm has maximal LinUCB index, then instantaneous regret is controlled by the selected
arm's LinUCB width. -/
lemma mean_sub_mean_arm_le_two_mul_width (a : Fin K)
    (h_best : (ν a)[id] ≤ index A R reg β x a n ω)
    (h_arm : estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (h_le : index A R reg β x a n ω ≤ index A R reg β x (A n ω) n ω) :
    (ν a)[id] - (ν (A n ω))[id] ≤
      2 * (√(β (n + 1)) * width A reg x (A n ω) n ω) := by
  rw [sub_le_iff_le_add']
  calc
    (ν a)[id] ≤ index A R reg β x a n ω := h_best
    _ ≤ index A R reg β x (A n ω) n ω := h_le
    _ ≤ (ν (A n ω))[id] +
        2 * (√(β (n + 1)) * width A reg x (A n ω) n ω) := by
      rw [index, two_mul, ← add_assoc]
      gcongr
      rwa [sub_le_iff_le_add] at h_arm

omit [IsMarkovKernel ν] in
/-- The gap of the selected arm is bounded by twice its LinUCB bonus whenever the usual confidence
inequalities hold and the selected arm has maximal LinUCB index. -/
lemma gap_arm_le_two_mul_width [Nonempty (Fin K)]
    (h_best : (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (h_le : index A R reg β x (bestArm ν) n ω ≤
      index A R reg β x (A n ω) n ω) :
    gap ν (A n ω) ≤ 2 * (√(β (n + 1)) * width A reg x (A n ω) n ω) := by
  rw [gap_eq_bestArm_sub]
  exact mean_sub_mean_arm_le_two_mul_width (A := A) (R := R) (reg := reg) (β := β) (x := x)
    (ν := ν) (a := bestArm ν) h_best h_arm h_le

/-- Almost surely, the selected arm's gap is bounded by twice its LinUCB bonus whenever the usual
confidence inequalities hold almost surely. -/
lemma gap_arm_ae_le_two_mul_width [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (hn : n ≠ 0)
    (h_best : ∀ᵐ ω ∂P, (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id]) :
    ∀ᵐ ω ∂P,
      gap ν (A n ω) ≤ 2 * (√(β (n + 1)) * width A reg x (A n ω) n ω) := by
  filter_upwards [h_best, h_arm, index_le_index_arm h (bestArm ν) hn] with
    ω h_bestω h_armω h_leω
  exact gap_arm_le_two_mul_width (A := A) (R := R) (reg := reg) (β := β) (x := x)
    (ν := ν) h_bestω h_armω h_leω

/-- Almost surely, the selected arm's gap is bounded by twice its LinUCB bonus at every positive
time whenever the usual confidence inequalities hold almost surely at every positive time. -/
lemma forall_gap_arm_le_two_mul_width [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id]) :
    ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      gap ν (A n ω) ≤ 2 * (√(β (n + 1)) * width A reg x (A n ω) n ω) := by
  filter_upwards [h_best, h_arm, forall_index_le_index_arm h (bestArm ν)] with
    ω h_bestω h_armω h_leω
  intro n hn
  exact gap_arm_le_two_mul_width (A := A) (R := R) (reg := reg) (β := β) (x := x)
    (ν := ν) (n := n) (ω := ω) (h_bestω n hn) (h_armω n hn) (h_leω n hn)

omit [IsMarkovKernel ν] in
/-- If every realized gap up to horizon `n` is bounded pointwise, then regret up to `n` is bounded
by the corresponding sum of pointwise bounds. -/
lemma regret_le_sum_of_gap_bound (B : ℕ → ℝ)
    (hB : ∀ t, t ∈ range n → gap ν (A t ω) ≤ B t) :
    regret ν A n ω ≤ ∑ t ∈ range n, B t := by
  rw [regret_eq_sum_gap]
  exact sum_le_sum hB

omit [IsMarkovKernel ν] in
/-- A pathwise cumulative-regret bound obtained by summing the positive-time LinUCB width bound.

The time-zero gap is left unchanged because the current LinUCB max-index theorem applies only at
positive times. -/
lemma regret_le_sum_width_of_forall_gap_le
    (h_gap : ∀ t, t ∈ range n → t ≠ 0 →
      gap ν (A t ω) ≤ 2 * (√(β (t + 1)) * width A reg x (A t ω) t ω)) :
    regret ν A n ω ≤
      ∑ t ∈ range n,
        if t = 0 then gap ν (A 0 ω)
        else 2 * (√(β (t + 1)) * width A reg x (A t ω) t ω) := by
  refine regret_le_sum_of_gap_bound (A := A) (ν := ν) (n := n) (ω := ω)
    (B := fun t ↦
      if t = 0 then gap ν (A 0 ω)
      else 2 * (√(β (t + 1)) * width A reg x (A t ω) t ω)) ?_
  intro t ht
  by_cases ht0 : t = 0
  · simp [ht0]
  · simpa [ht0] using h_gap t ht ht0

omit [IsMarkovKernel ν] in
/-- Cauchy-Schwarz bound for the positive-time LinUCB bonus sum. -/
lemma sum_positive_bonus_le_two_mul_sqrt_sum_sq :
    (∑ t ∈ range n,
      if t = 0 then 0
      else 2 * (√(β (t + 1)) * width A reg x (A t ω) t ω)) ≤
      2 * (√(∑ t ∈ range n, (if t = 0 then 0 else √(β (t + 1))) ^ 2) *
        √(∑ t ∈ range n, (if t = 0 then 0 else width A reg x (A t ω) t ω) ^ 2)) := by
  calc
    (∑ t ∈ range n,
      if t = 0 then 0
      else 2 * (√(β (t + 1)) * width A reg x (A t ω) t ω))
        = 2 * ∑ t ∈ range n,
          (if t = 0 then 0 else √(β (t + 1))) *
            (if t = 0 then 0 else width A reg x (A t ω) t ω) := by
          rw [mul_sum]
          refine sum_congr rfl ?_
          intro t ht
          by_cases ht0 : t = 0
          · simp [ht0]
          · simp [ht0]
    _ ≤ 2 * (√(∑ t ∈ range n, (if t = 0 then 0 else √(β (t + 1))) ^ 2) *
        √(∑ t ∈ range n, (if t = 0 then 0 else width A reg x (A t ω) t ω) ^ 2)) := by
      gcongr
      exact Real.sum_mul_le_sqrt_mul_sqrt (range n)
        (fun t ↦ if t = 0 then 0 else √(β (t + 1)))
        (fun t ↦ if t = 0 then 0 else width A reg x (A t ω) t ω)

/-- The squared beta factor in the Cauchy-Schwarz bound simplifies when the confidence schedule is
nonnegative. -/
lemma sum_sqrt_beta_sq_eq (hβ : ∀ t, 0 ≤ β (t + 1)) :
    (∑ t ∈ range n, if t = 0 then 0 else √(β (t + 1)) ^ 2) =
      ∑ t ∈ range n, if t = 0 then 0 else β (t + 1) := by
  refine sum_congr rfl ?_
  intro t ht
  by_cases ht0 : t = 0
  · simp [ht0]
  · simp [ht0, Real.sq_sqrt (hβ t)]

/-- Almost surely, the cumulative regret is bounded by the sum of LinUCB width terms whenever the
usual confidence inequalities hold almost surely at every positive time. -/
lemma regret_ae_le_sum_width [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id]) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        ∑ t ∈ range n,
          if t = 0 then gap ν (A 0 ω)
          else 2 * (√(β (t + 1)) * width A reg x (A t ω) t ω) := by
  filter_upwards [forall_gap_arm_le_two_mul_width h h_best h_arm] with ω h_gapω
  exact regret_le_sum_width_of_forall_gap_le (A := A) (reg := reg) (β := β)
    (x := x) (ν := ν) (n := n) (ω := ω) fun t ht ht0 ↦ h_gapω t ht0

/-- Almost surely, cumulative regret is bounded by the initial gap plus a Cauchy-Schwarz bound on
the positive-time LinUCB width terms. -/
lemma regret_ae_le_initial_add_cauchy [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id]) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        (∑ t ∈ range n, if t = 0 then gap ν (A 0 ω) else 0) +
          2 * (√(∑ t ∈ range n, (if t = 0 then 0 else √(β (t + 1))) ^ 2) *
            √(∑ t ∈ range n, (if t = 0 then 0 else width A reg x (A t ω) t ω) ^ 2)) := by
  filter_upwards [regret_ae_le_sum_width h h_best h_arm] with ω h_regret
  refine h_regret.trans ?_
  have hsplit :
      (∑ t ∈ range n,
        if t = 0 then gap ν (A 0 ω)
        else 2 * (√(β (t + 1)) * width A reg x (A t ω) t ω)) =
        (∑ t ∈ range n, if t = 0 then gap ν (A 0 ω) else 0) +
          ∑ t ∈ range n,
            if t = 0 then 0
            else 2 * (√(β (t + 1)) * width A reg x (A t ω) t ω) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl ?_
    intro t ht
    by_cases ht0 : t = 0
    · simp [ht0]
    · simp [ht0]
  rw [hsplit]
  exact add_le_add_right (sum_positive_bonus_le_two_mul_sqrt_sum_sq (A := A)
    (reg := reg) (β := β) (x := x) (n := n) (ω := ω)) _

/-- Almost surely, cumulative regret is bounded by the initial gap plus a Cauchy-Schwarz bound whose
beta factor has been simplified using nonnegativity of the confidence schedule. -/
lemma regret_ae_le_initial_add_cauchy_simplified [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (hβ : ∀ t, 0 ≤ β (t + 1)) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        (∑ t ∈ range n, if t = 0 then gap ν (A 0 ω) else 0) +
          2 * (√(∑ t ∈ range n, if t = 0 then 0 else β (t + 1)) *
            √(∑ t ∈ range n, (if t = 0 then 0 else width A reg x (A t ω) t ω) ^ 2)) := by
  filter_upwards [regret_ae_le_initial_add_cauchy (A := A) (R := R) (reg := reg) (β := β)
    (x := x) (ν := ν) (n := n) h h_best h_arm] with ω h_regret
  simpa [sum_sqrt_beta_sq_eq (β := β) (n := n) hβ] using h_regret

omit [IsMarkovKernel ν] in
/-- If the squared LinUCB widths are bounded by `W`, then the Cauchy-Schwarz regret bound can use
`√W` in place of the square root of the realized squared-width sum. -/
lemma regret_le_initial_add_cauchy_of_width_sq_le (W : ℝ)
    (h_regret :
      regret ν A n ω ≤
        (∑ t ∈ range n, if t = 0 then gap ν (A 0 ω) else 0) +
          2 * (√(∑ t ∈ range n, if t = 0 then 0 else β (t + 1)) *
            √(∑ t ∈ range n, (if t = 0 then 0 else width A reg x (A t ω) t ω) ^ 2)))
    (hW : widthSqSum A reg x n ω ≤ W)
    :
    regret ν A n ω ≤
      (∑ t ∈ range n, if t = 0 then gap ν (A 0 ω) else 0) +
        2 * (√(∑ t ∈ range n, if t = 0 then 0 else β (t + 1)) * √W) := by
  rw [widthSqSum] at hW
  refine h_regret.trans ?_
  gcongr

/-- Almost surely, cumulative regret is bounded by the initial gap plus
`2 * √(sum beta terms) * √W` whenever the squared LinUCB widths are almost surely bounded by `W`.

This is the interface expected from a future elliptical-potential bound. -/
lemma regret_ae_le_initial_add_sqrt_width_bound [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (hβ : ∀ t, 0 ≤ β (t + 1)) (W : ℝ)
    (hW : ∀ᵐ ω ∂P, widthSqSum A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        (∑ t ∈ range n, if t = 0 then gap ν (A 0 ω) else 0) +
          2 * (√(∑ t ∈ range n, if t = 0 then 0 else β (t + 1)) * √W) := by
  filter_upwards [regret_ae_le_initial_add_cauchy_simplified (A := A) (R := R)
    (reg := reg) (β := β) (x := x) (ν := ν) (n := n) h h_best h_arm hβ, hW] with
    ω h_regret hWω
  exact regret_le_initial_add_cauchy_of_width_sq_le (A := A) (reg := reg) (β := β)
    (x := x) (ν := ν) (n := n) (ω := ω) W h_regret hWω

omit [IsMarkovKernel ν] in
/-- If the beta sum is bounded by `B`, then the regret bound can use `√B` in place of the square
root of the beta sum. -/
lemma regret_le_initial_add_sqrt_bounds_of_beta_sum_le (B W : ℝ)
    (h_regret :
      regret ν A n ω ≤
        (∑ t ∈ range n, if t = 0 then gap ν (A 0 ω) else 0) +
          2 * (√(∑ t ∈ range n, if t = 0 then 0 else β (t + 1)) * √W))
    (hB : (∑ t ∈ range n, if t = 0 then 0 else β (t + 1)) ≤ B)
    :
    regret ν A n ω ≤
      (∑ t ∈ range n, if t = 0 then gap ν (A 0 ω) else 0) + 2 * (√B * √W) := by
  refine h_regret.trans ?_
  gcongr

/-- Almost surely, cumulative regret is bounded by the initial gap plus
`2 * √B * √W` whenever the beta sum is bounded by `B` and the squared LinUCB widths are almost
surely bounded by `W`. -/
lemma regret_ae_le_initial_add_sqrt_bounds [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (hβ : ∀ t, 0 ≤ β (t + 1)) (B W : ℝ)
    (hB : (∑ t ∈ range n, if t = 0 then 0 else β (t + 1)) ≤ B)
    (hW : ∀ᵐ ω ∂P, widthSqSum A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        (∑ t ∈ range n, if t = 0 then gap ν (A 0 ω) else 0) + 2 * (√B * √W) := by
  filter_upwards [regret_ae_le_initial_add_sqrt_width_bound (A := A) (R := R)
    (reg := reg) (β := β) (x := x) (ν := ν) (n := n) h h_best h_arm hβ W hW
    ] with ω h_regret
  exact regret_le_initial_add_sqrt_bounds_of_beta_sum_le (A := A) (β := β) (ν := ν)
    (n := n) (ω := ω) B W h_regret hB

/-- If the confidence-radius schedule is nonnegative and monotone, the positive-time beta sum is
bounded by the horizon times the terminal beta value. -/
lemma beta_sum_le_nat_mul_of_monotone
    (hβ_mono : Monotone β) (hβ : ∀ t, 0 ≤ β (t + 1)) :
    (∑ t ∈ range n, if t = 0 then 0 else β (t + 1)) ≤ (n : ℝ) * β n := by
  calc
    (∑ t ∈ range n, if t = 0 then 0 else β (t + 1))
      ≤ ∑ _t ∈ range n, β n := by
        refine sum_le_sum ?_
        intro t ht
        by_cases ht0 : t = 0
        · rw [if_pos ht0]
          have hn_pos : 0 < n := by
            simpa [ht0] using mem_range.mp ht
          have hn_beta : 0 ≤ β n := by
            have htime : n - 1 + 1 = n := by grind
            simpa [htime] using hβ (n - 1)
          exact hn_beta
        · rw [if_neg ht0]
          exact hβ_mono (Nat.succ_le_iff.mpr (mem_range.mp ht))
    _ = (n : ℝ) * β n := by
      simp [sum_const, nsmul_eq_mul]

omit [IsMarkovKernel ν] in
/-- The initial-gap sum is just the time-zero gap when the horizon is positive, and zero when the
horizon is zero. -/
lemma initial_gap_sum_eq :
    (∑ t ∈ range n, if t = 0 then gap ν (A 0 ω) else 0) =
      if n = 0 then 0 else gap ν (A 0 ω) := by
  cases n <;> simp

/-- Almost surely, cumulative regret is bounded by the initial gap plus
`2 * √(n * β n) * √W` whenever the squared LinUCB widths are almost surely bounded by `W` and `β`
is nonnegative and monotone. -/
lemma regret_ae_le_initial_add_sqrt_nat_mul_beta_width_bound [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (hβ : ∀ t, 0 ≤ β (t + 1)) (hβ_mono : Monotone β) (W : ℝ)
    (hW : ∀ᵐ ω ∂P, widthSqSum A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        (∑ t ∈ range n, if t = 0 then gap ν (A 0 ω) else 0) +
          2 * (√((n : ℝ) * β n) * √W) := by
  exact regret_ae_le_initial_add_sqrt_bounds (A := A) (R := R) (reg := reg) (β := β)
    (x := x) (ν := ν) (n := n) h h_best h_arm hβ ((n : ℝ) * β n) W
    (beta_sum_le_nat_mul_of_monotone (β := β) (n := n) hβ_mono hβ) hW

/-- Almost surely, cumulative regret is bounded by the simplified initial-gap term plus
`2 * √(n * β n) * √W` whenever the squared LinUCB widths are almost surely bounded by `W` and `β`
is nonnegative and monotone. -/
lemma regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_width_bound [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (hβ : ∀ t, 0 ≤ β (t + 1)) (hβ_mono : Monotone β) (W : ℝ)
    (hW : ∀ᵐ ω ∂P, widthSqSum A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        (if n = 0 then 0 else gap ν (A 0 ω)) + 2 * (√((n : ℝ) * β n) * √W) := by
  filter_upwards [regret_ae_le_initial_add_sqrt_nat_mul_beta_width_bound (A := A) (R := R)
    (reg := reg) (β := β) (x := x) (ν := ν) (n := n) h h_best h_arm hβ hβ_mono W hW
    ] with ω h_regret
  simpa [initial_gap_sum_eq (A := A) (ν := ν) (n := n) (ω := ω)] using h_regret

/-- Almost surely, cumulative regret is bounded by the simplified initial-gap term plus
`2 * √(n * β n) * √W` whenever a history-level quadratic-form bound supplies the future
elliptical-potential input. -/
lemma regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_history_quadratic_bound [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (hβ : ∀ t, 0 ≤ β (t + 1)) (hβ_mono : Monotone β) (W : ℝ)
    (h_quad_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω))
    (hW : ∀ᵐ ω ∂P, historyQuadraticWidthSum A R reg x n ω ≤ W) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        (if n = 0 then 0 else gap ν (A 0 ω)) + 2 * (√((n : ℝ) * β n) * √W) := by
  exact regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_width_bound (A := A) (R := R)
    (reg := reg) (β := β) (x := x) (ν := ν) (n := n) h h_best h_arm hβ hβ_mono W
    (widthSqSum_ae_le_of_history_quadratic_width_sum_ae_le (A := A) (R := R)
      (reg := reg) (x := x) (n := n) (P := P) (W := W) h_quad_nonneg hW)

/-- Almost surely, cumulative regret is bounded by the simplified initial-gap term plus
`2 * √(n * β n) * √W` whenever the packaged history-level quadratic-width input holds almost
surely.

This is the theorem a future elliptical-potential lemma should feed into directly. -/
lemma regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_history_quadratic_width_bound
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (hβ : ∀ t, 0 ≤ β (t + 1)) (hβ_mono : Monotone β) (W : ℝ)
    (h_bound : ∀ᵐ ω ∂P, HistoryQuadraticWidthBound A R reg x n ω W) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        (if n = 0 then 0 else gap ν (A 0 ω)) + 2 * (√((n : ℝ) * β n) * √W) := by
  exact regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_width_bound (A := A) (R := R)
    (reg := reg) (β := β) (x := x) (ν := ν) (n := n) h h_best h_arm hβ hβ_mono W
    (widthSqSum_ae_le_of_history_quadratic_width_bound_ae (A := A) (R := R)
      (reg := reg) (x := x) (n := n) (P := P) (W := W) h_bound)

/-- Almost surely, cumulative regret is bounded by the simplified initial-gap term plus
`2 * √(n * β n) * √W` whenever a capped history-level quadratic-width sum bound holds almost
surely and every positive-time quadratic width form is almost surely nonnegative and at most `1`.

This is the direct interface for the common capped form of the elliptical-potential lemma. -/
lemma regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_capped_history_quadratic_bound
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (hβ : ∀ t, 0 ≤ β (t + 1)) (hβ_mono : Monotone β) (W : ℝ)
    (h_quad_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω))
    (h_quad_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm' reg x (t - 1) (IsAlgEnvSeq.hist A R (t - 1) ω) (A t ω) ≤ 1)
    (hW : ∀ᵐ ω ∂P, historyCappedQuadraticWidthSum A R reg x n ω ≤ W) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        (if n = 0 then 0 else gap ν (A 0 ω)) + 2 * (√((n : ℝ) * β n) * √W) := by
  exact regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_width_bound (A := A) (R := R)
    (reg := reg) (β := β) (x := x) (ν := ν) (n := n) h h_best h_arm hβ hβ_mono W
    (widthSqSum_ae_le_of_capped_history_quadratic_width_sum_ae_le (A := A) (R := R)
      (reg := reg) (x := x) (n := n) (P := P) (W := W) h_quad_nonneg h_quad_le_one hW)

/-- Almost surely, cumulative regret is bounded by the simplified initial-gap term plus
`2 * √(n * β n) * √W` whenever a capped process-level quadratic-width sum bound holds almost
surely and every positive-time process-level quadratic width form is almost surely nonnegative and
at most `1`.

This is the direct interface for an elliptical-potential lemma stated using the process-level design
matrices `designMatrix A reg x t ω`. -/
lemma regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_capped_quadratic_bound
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (hβ : ∀ t, 0 ≤ β (t + 1)) (hβ_mono : Monotone β) (W : ℝ)
    (h_quad_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω)
    (h_quad_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (hW : ∀ᵐ ω ∂P, cappedQuadraticWidthSum A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        (if n = 0 then 0 else gap ν (A 0 ω)) + 2 * (√((n : ℝ) * β n) * √W) := by
  exact regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_width_bound (A := A) (R := R)
    (reg := reg) (β := β) (x := x) (ν := ν) (n := n) h h_best h_arm hβ hβ_mono W
    (widthSqSum_ae_le_of_capped_quadratic_width_sum_ae_le (A := A) (reg := reg)
      (x := x) (n := n) (P := P) (W := W) h_quad_nonneg h_quad_le_one hW)

/-- Almost surely, cumulative regret is bounded by the simplified initial-gap term plus
`2 * √(n * β n) * √W` whenever the packaged process-level capped quadratic-width input holds
almost surely.

This is the compact theorem a process-level elliptical-potential lemma should feed into directly. -/
lemma regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_capped_quadratic_width_bound
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (hβ : ∀ t, 0 ≤ β (t + 1)) (hβ_mono : Monotone β) (W : ℝ)
    (h_bound : ∀ᵐ ω ∂P, CappedQuadraticWidthBound A reg x n ω W) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        (if n = 0 then 0 else gap ν (A 0 ω)) + 2 * (√((n : ℝ) * β n) * √W) := by
  exact regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_width_bound (A := A) (R := R)
    (reg := reg) (β := β) (x := x) (ν := ν) (n := n) h h_best h_arm hβ hβ_mono W
    (widthSqSum_ae_le_of_capped_quadratic_width_bound_ae (A := A) (reg := reg)
      (x := x) (n := n) (P := P) (W := W) h_bound)

/-- Almost surely, cumulative regret is bounded by the simplified initial-gap term plus the
feature-budget elliptical-potential term
`2 * √(n * β n) * √(2 * d * log(1 + n L² / (reg d)))`.

The remaining matrix-analysis inputs are isolated as named hypotheses: `h_width_le_feature` should
come from the inverse-design comparison `xᵀV⁻¹x ≤ ‖x‖² / reg`, and `h_ratio_of_trace` should come
from a determinant/trace comparison proving that the trace budget implies the displayed
determinant-ratio bound. -/
lemma regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_featureSqNorm_budget_bound
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (hβ : ∀ t, 0 ≤ β (t + 1)) (hβ_mono : Monotone β)
    (hreg_pos : 0 < reg) (hd : d ≠ 0)
    (h_width_le_feature : WidthQuadraticFormLeFeatureSqNormDivReg A reg x)
    (L2 : ℝ)
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ L2)
    (hL2_le_reg : L2 ≤ reg)
    (h_ratio_of_trace : ∀ ω,
      designTrace A reg x n ω ≤ reg * (d : ℝ) + (n : ℝ) * L2 →
        designDetRatio A reg x n ω ≤
          ((reg * (d : ℝ) + (n : ℝ) * L2) / (reg * (d : ℝ))) ^ d) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        (if n = 0 then 0 else gap ν (A 0 ω)) +
          2 * (√((n : ℝ) * β n) *
            √(2 * (d : ℝ) * Real.log (1 + (n : ℝ) * L2 / (reg * (d : ℝ))))) := by
  exact regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_capped_quadratic_width_bound
    (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := n) h h_best
    h_arm hβ hβ_mono
    (2 * (d : ℝ) * Real.log (1 + (n : ℝ) * L2 / (reg * (d : ℝ))))
    (cappedQuadraticWidthBound_ae_of_reg_ne_zero_det_update_featureSqNorm_budget_bound'
      (A := A) (reg := reg) (x := x) (n := n) (P := P) hreg_pos.ne' hd
      (widthQuadraticForm_ae_nonneg_of_reg_nonneg (A := A) (reg := reg) (x := x)
        (n := n) (P := P) hreg_pos.le)
      (widthQuadraticForm_ae_le_one_of_featureSqNorm_ae_le (A := A) (reg := reg)
        (x := x) (n := n) (P := P) h_width_le_feature hreg_pos hL2 hL2_le_reg)
      L2 hL2 h_ratio_of_trace)

/-- Almost surely, cumulative regret is bounded by the feature-budget elliptical-potential term
when the determinant/trace input is stated as the determinant upper bound
`det(V_n) ≤ ((reg * d + n * L²) / d) ^ d`. -/
lemma regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_featureSqNorm_budget_bound_of_designDet_le
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (hβ : ∀ t, 0 ≤ β (t + 1)) (hβ_mono : Monotone β)
    (hreg_pos : 0 < reg) (hd : d ≠ 0)
    (h_width_le_feature : WidthQuadraticFormLeFeatureSqNormDivReg A reg x)
    (L2 : ℝ)
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ L2)
    (hL2_le_reg : L2 ≤ reg)
    (hdet_of_trace : ∀ ω,
      designTrace A reg x n ω ≤ reg * (d : ℝ) + (n : ℝ) * L2 →
        designDet A reg x n ω ≤
          ((reg * (d : ℝ) + (n : ℝ) * L2) / (d : ℝ)) ^ d) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        (if n = 0 then 0 else gap ν (A 0 ω)) +
          2 * (√((n : ℝ) * β n) *
            √(2 * (d : ℝ) * Real.log (1 + (n : ℝ) * L2 / (reg * (d : ℝ))))) := by
  exact regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_capped_quadratic_width_bound
    (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := n) h h_best
    h_arm hβ hβ_mono
    (2 * (d : ℝ) * Real.log (1 + (n : ℝ) * L2 / (reg * (d : ℝ))))
    (cappedQuadraticWidthBound_ae_of_reg_pos_det_update_featureSqNorm_budget_bound_of_designDet_le
      (A := A) (reg := reg) (x := x) (n := n) (P := P) hreg_pos hd
      h_width_le_feature L2 hL2 hL2_le_reg hdet_of_trace)

/-- Almost surely, cumulative regret is bounded by the feature-budget elliptical-potential term
when the determinant/trace input is the reusable PSD matrix determinant/trace comparison
`det(M) ≤ (trace(M) / d) ^ d`. -/
lemma regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_of_matrix_det_trace_bound
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (hβ : ∀ t, 0 ≤ β (t + 1)) (hβ_mono : Monotone β)
    (hreg_pos : 0 < reg) (hd : d ≠ 0)
    (h_width_le_feature : WidthQuadraticFormLeFeatureSqNormDivReg A reg x)
    (L2 : ℝ)
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ L2)
    (hL2_le_reg : L2 ≤ reg)
    (hdet_trace : MatrixDetLeTraceAveragePow d) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        (if n = 0 then 0 else gap ν (A 0 ω)) +
          2 * (√((n : ℝ) * β n) *
            √(2 * (d : ℝ) * Real.log (1 + (n : ℝ) * L2 / (reg * (d : ℝ))))) := by
  exact regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_capped_quadratic_width_bound
    (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := n) h h_best
    h_arm hβ hβ_mono
    (2 * (d : ℝ) * Real.log (1 + (n : ℝ) * L2 / (reg * (d : ℝ))))
    (cappedQuadraticWidthBound_ae_of_matrix_det_trace_bound
      (A := A) (reg := reg) (x := x) (n := n) (P := P) hreg_pos hd
      h_width_le_feature L2 hL2 hL2_le_reg hdet_trace)

/-- Almost surely, cumulative regret is bounded by the simplified initial-gap term plus
`2 * √(n * β n) * √W` whenever positive regularization, the positive-time width cap, and the final
log-determinant potential bound hold.

The capped-sum/log-determinant part of the elliptical-potential argument is now proved internally:
positive regularization gives determinant nonvanishing and nonnegative quadratic forms, while
`h_quad_le_one` supplies the cap needed for `min 1 q ≤ 2 * log (1 + q)`. -/
lemma regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_of_ellipticalPotential_bound
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x h_index) (stationaryEnv ν) P)
    (h_best : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) n ω)
    (h_arm : ∀ᵐ ω ∂P, ∀ n, n ≠ 0 →
      estimatedReward A R reg x (A n ω) n ω -
        √(β (n + 1)) * width A reg x (A n ω) n ω ≤ (ν (A n ω))[id])
    (hβ : ∀ t, 0 ≤ β (t + 1)) (hβ_mono : Monotone β) (W : ℝ)
    (hreg_pos : 0 < reg)
    (h_quad_le_one : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      widthQuadraticForm A reg x (A t ω) t ω ≤ 1)
    (h_potential_le : ∀ᵐ ω ∂P, ellipticalPotential A reg x n ω ≤ W) :
    ∀ᵐ ω ∂P,
      regret ν A n ω ≤
        (if n = 0 then 0 else gap ν (A 0 ω)) + 2 * (√((n : ℝ) * β n) * √W) := by
  exact regret_ae_le_initial_gap_add_sqrt_nat_mul_beta_capped_quadratic_width_bound
    (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := n) h h_best
    h_arm hβ hβ_mono W
    (cappedQuadraticWidthBound_ae_of_reg_pos_det_update_ellipticalPotential_le_bound
      (A := A) (reg := reg) (x := x) (n := n) (P := P) (W := W) hreg_pos
      h_quad_le_one h_potential_le)

end LinUCB

end Bandits
