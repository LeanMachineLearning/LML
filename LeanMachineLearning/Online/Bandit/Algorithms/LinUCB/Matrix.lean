/-
Copyright (c) 2026 Fawad Haider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Fawad Haider
-/
module

public import LeanMachineLearning.Online.Bandit.Algorithms.LinUCB.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# LinUCB for finite-action linear bandits
Chapter 19 of *Bandit Algorithms*:
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset Learning

open scoped ENNReal NNReal Matrix MatrixOrder

namespace Bandits

variable {K d : ℕ}

namespace LinUCB

variable {hK : 0 < K} {reg : ℝ} {β : ℕ → ℝ} {x : Fin K → Feature d}
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

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The design matrix dominates its regularization part: after subtracting `reg • I`, what remains
is the sum of observed rank-one feature matrices, hence positive semidefinite. -/
lemma designMatrix_sub_reg_smul_one_posSemidef :
    (designMatrix A reg x n ω - reg • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
  have hsum :
      (∑ s ∈ range n, Matrix.vecMulVec (x (A s ω)) (x (A s ω))).PosSemidef := by
    refine Matrix.posSemidef_sum (s := range n) ?_
    intro t _
    simpa using Matrix.posSemidef_vecMulVec_self_star (x (A t ω))
  simpa [designMatrix, add_sub_cancel_left] using hsum

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Matrix-order form of `designMatrix_sub_reg_smul_one_posSemidef`: `reg • I ≤ V_n`. -/
lemma reg_smul_one_le_designMatrix :
    reg • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ designMatrix A reg x n ω := by
  rw [Matrix.le_iff]
  exact designMatrix_sub_reg_smul_one_posSemidef (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Matrix order is preserved by evaluating the quadratic form against a fixed feature vector. -/
lemma dotProduct_mulVec_le_of_matrix_le {M N : Matrix (Fin d) (Fin d) ℝ}
    (hMN : M ≤ N) (u : Feature d) :
    dotProduct u (M *ᵥ u) ≤ dotProduct u (N *ᵥ u) := by
  have h_nonneg : 0 ≤ dotProduct u ((N - M) *ᵥ u) := by
    simpa using (Matrix.le_iff.mp hMN).dotProduct_mulVec_nonneg u
  rw [Matrix.sub_mulVec, dotProduct_sub] at h_nonneg
  exact sub_nonneg.mp h_nonneg

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The inverse of the regularized identity is the reciprocal-scaled identity. -/
lemma reg_smul_one_inv (hreg : reg ≠ 0) :
    (reg • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ =
      reg⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  rw [Matrix.inv_eq_left_inv]
  simp [smul_smul, hreg]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The quadratic form induced by `(reg • I)⁻¹` is the squared norm divided by `reg`. -/
lemma dotProduct_reg_smul_one_inv_mulVec (hreg : reg ≠ 0) (u : Feature d) :
    dotProduct u (((reg • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹) *ᵥ u) =
      dotProduct u u / reg := by
  rw [reg_smul_one_inv (reg := reg) (d := d) hreg]
  simp [Matrix.smul_mulVec, div_eq_inv_mul, mul_comm]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Arm-specific form of `dotProduct_reg_smul_one_inv_mulVec`. -/
lemma dotProduct_reg_smul_one_inv_mulVec_eq_featureSqNorm_div
    (hreg : reg ≠ 0) (a : Fin K) :
    dotProduct (x a) (((reg • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹) *ᵥ (x a)) =
      featureSqNorm x a / reg := by
  simpa [featureSqNorm] using
    dotProduct_reg_smul_one_inv_mulVec (reg := reg) (d := d) hreg (x a)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Reusable matrix-analysis theorem needed for the LinUCB width comparison.

It states the usual inverse anti-monotonicity of positive-definite matrices in the PSD order:
if `M` is positive definite and `M ≤ N`, then inversion reverses the order. -/
def MatrixInvAntiMonoOnPosDef (d : ℕ) : Prop :=
  ∀ M N : Matrix (Fin d) (Fin d) ℝ, M.PosDef → M ≤ N → N⁻¹ ≤ M⁻¹

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Inversion reverses the PSD order on positive-definite real matrices.

The proof uses the standard Schur-complement argument. From `M ≤ N`, the difference `N - M` is
positive semidefinite, hence `N` is positive definite. The block matrix
`[N, I; I, M⁻¹]` is positive semidefinite because its lower-right Schur complement is `N - M`.
Taking the upper-left Schur complement of the same block matrix gives `M⁻¹ - N⁻¹ ≥ 0`, which is
exactly `N⁻¹ ≤ M⁻¹`. -/
lemma MatrixInvAntiMonoOnPosDef.of_posDef : MatrixInvAntiMonoOnPosDef d := by
  intro M N hM hMN
  have hDiff : (N - M).PosSemidef := by
    simpa using (Matrix.le_iff.mp hMN)
  have hN : N.PosDef := by
    have hadd := hM.add_posSemidef hDiff
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hadd
  have hMdet : IsUnit M.det := by
    exact Matrix.isUnit_iff_isUnit_det (A := M) |>.mp hM.isUnit
  have hNdet : IsUnit N.det := by
    exact Matrix.isUnit_iff_isUnit_det (A := N) |>.mp hN.isUnit
  letI : Invertible M := Matrix.invertibleOfIsUnitDet M hMdet
  letI : Invertible N := Matrix.invertibleOfIsUnitDet N hNdet
  have h_block :
      (Matrix.fromBlocks N (1 : Matrix (Fin d) (Fin d) ℝ)
        ((1 : Matrix (Fin d) (Fin d) ℝ)ᴴ) M⁻¹).PosSemidef := by
    exact (Matrix.PosDef.fromBlocks₂₂ (A := N)
      (B := (1 : Matrix (Fin d) (Fin d) ℝ)) (D := M⁻¹) hM.inv).mpr
      (by simpa [Matrix.inv_inv_of_invertible, Matrix.mul_assoc] using hDiff)
  have h_schur :
      (M⁻¹ - (1 : Matrix (Fin d) (Fin d) ℝ)ᴴ * N⁻¹ *
        (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
    exact (Matrix.PosDef.fromBlocks₁₁ (A := N) (B := (1 : Matrix (Fin d) (Fin d) ℝ))
      (D := M⁻¹) hN).mp h_block
  rw [Matrix.le_iff]
  simpa [Matrix.mul_assoc] using h_schur

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The inverse-design comparison used in the finite-action LinUCB regret route.

Mathematically, this should follow from `reg • I ≤ V_t` and positive regularization: inversion
reverses the positive-definite matrix order, so `V_t⁻¹ ≤ (reg • I)⁻¹`. -/
def DesignMatrixInvLeRegInv
    (A : ℕ → Ω → Fin K) (reg : ℝ) (x : Fin K → Feature d) : Prop :=
  ∀ (n : ℕ) (ω : Ω),
    (designMatrix A reg x n ω)⁻¹ ≤ (reg • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Projection lemma for the named inverse-order obligation. -/
lemma DesignMatrixInvLeRegInv.apply
    (h_inv : DesignMatrixInvLeRegInv A reg x) (n : ℕ) (ω : Ω) :
    (designMatrix A reg x n ω)⁻¹ ≤ (reg • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ :=
  h_inv n ω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Positive regularization gives the LinUCB-specific inverse-design comparison. -/
lemma DesignMatrixInvLeRegInv.of_reg_pos
    (hreg_pos : 0 < reg) :
    DesignMatrixInvLeRegInv A reg x := by
  intro n ω
  exact MatrixInvAntiMonoOnPosDef.of_posDef (reg • (1 : Matrix (Fin d) (Fin d) ℝ))
    (designMatrix A reg x n ω)
    (Matrix.PosDef.smul Matrix.PosDef.one hreg_pos)
    (reg_smul_one_le_designMatrix (A := A) (reg := reg) (x := x) (n := n) (ω := ω))

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

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A uniform finite-action feature bound implies the selected-action feature bound through any
finite horizon. -/
lemma featureSqNorm_ae_le_of_featureSqNormBound
    (L2 : ℝ) (hL2 : FeatureSqNormBound x L2) :
    ∀ᵐ ω ∂P, ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ L2 :=
  Filter.Eventually.of_forall fun ω t _ht ↦ hL2 (A t ω)

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

Mathematically, this says `x_aᵀ V_t⁻¹ x_a ≤ ‖x_a‖² / reg`. Positive regularization proves it
because `reg I ≤ V_t` and positive-definite matrix inversion reverses the PSD order. -/
def WidthQuadraticFormLeFeatureSqNormDivReg
    (A : ℕ → Ω → Fin K) (reg : ℝ) (x : Fin K → Feature d) : Prop :=
  ∀ (a : Fin K) (n : ℕ) (ω : Ω),
    widthQuadraticForm A reg x a n ω ≤ featureSqNorm x a / reg

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If the inverse design matrix is bounded by the inverse regularized identity, then the LinUCB
quadratic width is bounded by `featureSqNorm / reg` for one arm, time, and sample point. -/
lemma widthQuadraticForm_le_featureSqNorm_div_reg_of_inv_le
    (a : Fin K)
    (h_inv : (designMatrix A reg x n ω)⁻¹ ≤
      (reg • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹)
    (hreg : reg ≠ 0) :
    widthQuadraticForm A reg x a n ω ≤ featureSqNorm x a / reg := by
  calc
    widthQuadraticForm A reg x a n ω =
        dotProduct (x a) (((designMatrix A reg x n ω)⁻¹) *ᵥ (x a)) := rfl
    _ ≤ dotProduct (x a)
        (((reg • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹) *ᵥ (x a)) :=
        dotProduct_mulVec_le_of_matrix_le h_inv (x a)
    _ = featureSqNorm x a / reg :=
        dotProduct_reg_smul_one_inv_mulVec_eq_featureSqNorm_div
          (reg := reg) (x := x) hreg a

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A pointwise inverse-order comparison for all times and sample points gives the reusable
`WidthQuadraticFormLeFeatureSqNormDivReg` property consumed by the regret route. -/
lemma WidthQuadraticFormLeFeatureSqNormDivReg.of_inv_le
    (hreg : reg ≠ 0)
    (h_inv : DesignMatrixInvLeRegInv A reg x) :
    WidthQuadraticFormLeFeatureSqNormDivReg A reg x := by
  intro a n ω
  exact widthQuadraticForm_le_featureSqNorm_div_reg_of_inv_le
    (A := A) (reg := reg) (x := x) (n := n) (ω := ω) a
    (h_inv.apply n ω) hreg

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Positive regularization bounds LinUCB quadratic widths by the squared feature norm divided by
the regularization. -/
lemma WidthQuadraticFormLeFeatureSqNormDivReg.of_reg_pos
    (hreg_pos : 0 < reg) :
    WidthQuadraticFormLeFeatureSqNormDivReg A reg x :=
  WidthQuadraticFormLeFeatureSqNormDivReg.of_inv_le (A := A) (reg := reg) (x := x)
    hreg_pos.ne' (DesignMatrixInvLeRegInv.of_reg_pos (A := A) (reg := reg) (x := x)
      hreg_pos)

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
  refine Finset.sum_congr rfl ?_
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
/-- Positive regularization makes every process-level design determinant positive. -/
lemma designDet_pos_of_reg_pos (hreg_pos : 0 < reg) :
    0 < designDet A reg x n ω := by
  unfold designDet
  exact (designMatrix_posDef (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
    hreg_pos).det_pos

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Positive regularization makes every process-level design determinant nonzero. -/
lemma designDet_ne_zero_of_reg_pos (hreg_pos : 0 < reg) :
    designDet A reg x n ω ≠ 0 := by
  exact (designDet_pos_of_reg_pos (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
    hreg_pos).ne'

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
/-- The process-level determinant ratio is `det(Vₙ) / reg ^ d`. -/
lemma designDetRatio_eq_div_reg_pow :
    designDetRatio A reg x n ω = designDet A reg x n ω / reg ^ d := by
  rw [designDetRatio, designDet_zero_eq_reg_pow]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If the process-level design matrix is diagonal, its determinant is the product of its diagonal
entries. -/
lemma designDet_eq_prod_of_designMatrix_eq_diagonal {diag : Fin d → ℝ}
    (hdiag : designMatrix A reg x n ω = Matrix.diagonal diag) :
    designDet A reg x n ω = ∏ i, diag i := by
  unfold designDet
  rw [hdiag, Matrix.det_diagonal]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If positive regularization makes the design matrix positive definite and that matrix is
diagonal, then every diagonal entry is positive. -/
lemma diagonal_pos_of_designMatrix_eq_diagonal {diag : Fin d → ℝ}
    (hreg_pos : 0 < reg)
    (hdiag : designMatrix A reg x n ω = Matrix.diagonal diag) :
    ∀ i, 0 < diag i := by
  have hpos : (Matrix.diagonal diag).PosDef := by
    simpa [hdiag] using
      designMatrix_posDef (A := A) (reg := reg) (x := x) (n := n) (ω := ω) hreg_pos
  exact Matrix.posDef_diagonal_iff.mp hpos

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Diagonal-design form of the determinant ratio. -/
lemma designDetRatio_eq_prod_div_reg_pow_of_designMatrix_eq_diagonal {diag : Fin d → ℝ}
    (hdiag : designMatrix A reg x n ω = Matrix.diagonal diag) :
    designDetRatio A reg x n ω = (∏ i, diag i) / reg ^ d := by
  rw [designDetRatio_eq_div_reg_pow,
    designDet_eq_prod_of_designMatrix_eq_diagonal (A := A) (reg := reg) (x := x)
      (n := n) (ω := ω) hdiag]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Eigenvalues of the positive-definite process-level LinUCB design matrix.

The positive regularization proof is part of the definition because the matrix spectral API exposes
eigenvalues through a Hermitian proof. -/
noncomputable def designEigenvalues (hreg_pos : 0 < reg) : Fin d → ℝ :=
  (designMatrix_posDef (A := A) (reg := reg) (x := x) (n := n) (ω := ω) hreg_pos).1.eigenvalues

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Positive regularization makes every design-matrix eigenvalue positive. -/
lemma designEigenvalues_pos (hreg_pos : 0 < reg) (i : Fin d) :
    0 < designEigenvalues (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
      hreg_pos i := by
  unfold designEigenvalues
  exact (designMatrix_posDef (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
    hreg_pos).eigenvalues_pos i

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The design determinant is the product of the positive design-matrix eigenvalues. -/
lemma designDet_eq_prod_designEigenvalues (hreg_pos : 0 < reg) :
    designDet A reg x n ω =
      ∏ i, designEigenvalues (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
        hreg_pos i := by
  unfold designDet designEigenvalues
  exact (designMatrix_posDef (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
    hreg_pos).1.det_eq_prod_eigenvalues

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The design determinant ratio is the product of the positive design-matrix eigenvalues divided
by the initial determinant `reg ^ d`. -/
lemma designDetRatio_eq_prod_designEigenvalues_div_reg_pow (hreg_pos : 0 < reg) :
    designDetRatio A reg x n ω =
      (∏ i, designEigenvalues (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
        hreg_pos i) / reg ^ d := by
  rw [designDetRatio_eq_div_reg_pow,
    designDet_eq_prod_designEigenvalues (A := A) (reg := reg) (x := x)
      (n := n) (ω := ω) hreg_pos]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The eigenvector unitary that diagonalizes the positive-definite process-level design matrix. -/
noncomputable def designEigenvectorUnitary (hreg_pos : 0 < reg) :
    Matrix.unitaryGroup (Fin d) ℝ :=
  (designMatrix_posDef (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
    hreg_pos).1.eigenvectorUnitary

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The design eigenvector unitary diagonalizes the process-level design matrix, with diagonal
entries equal to `designEigenvalues`. -/
lemma designEigenvectorUnitary_diagonalizes (hreg_pos : 0 < reg) :
    star (designEigenvectorUnitary (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
        hreg_pos : Matrix (Fin d) (Fin d) ℝ) * designMatrix A reg x n ω *
      (designEigenvectorUnitary (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
        hreg_pos : Matrix (Fin d) (Fin d) ℝ) =
    Matrix.diagonal (designEigenvalues (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
      hreg_pos) := by
  let hM := designMatrix_posDef (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
    hreg_pos
  change star (hM.1.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *
      designMatrix A reg x n ω * (hM.1.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) =
    Matrix.diagonal hM.1.eigenvalues
  simpa using hM.1.conjStarAlgAut_star_eigenvectorUnitary

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Orthogonal/unitary change-of-coordinates preserves the corresponding quadratic form.

This is the finite-dimensional linear-algebra part of diagonalizing the Gaussian kernel: the
quadratic form for `M` in the original coordinates equals the quadratic form for
`star U * M * U` in the `star U` coordinates. -/
lemma unitary_conj_quadraticForm_eq
    (M : Matrix (Fin d) (Fin d) ℝ) (U : Matrix.unitaryGroup (Fin d) ℝ)
    (lambda : Feature d) :
    dotProduct ((star (U : Matrix (Fin d) (Fin d) ℝ)) *ᵥ lambda)
      (Matrix.mulVec ((star (U : Matrix (Fin d) (Fin d) ℝ)) * M *
          (U : Matrix (Fin d) (Fin d) ℝ))
        ((star (U : Matrix (Fin d) (Fin d) ℝ)) *ᵥ lambda)) =
    dotProduct lambda (Matrix.mulVec M lambda) := by
  let Umat : Matrix (Fin d) (Fin d) ℝ := U
  have hstar_left : Umat * star Umat = 1 := by
    change (U : Matrix (Fin d) (Fin d) ℝ) *
        star (U : Matrix (Fin d) (Fin d) ℝ) = 1
    exact Unitary.coe_mul_star_self U
  have hy : star Umat *ᵥ lambda = Matrix.vecMul lambda Umat := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    simpa [Umat] using (Matrix.mulVec_transpose (U : Matrix (Fin d) (Fin d) ℝ) lambda)
  have hcancel_left : Umat * (star Umat * M * Umat) = M * Umat := by
    rw [Matrix.mul_assoc (star Umat) M Umat]
    rw [← Matrix.mul_assoc Umat (star Umat) (M * Umat)]
    rw [hstar_left, Matrix.one_mul]
  have hcancel_right : (M * Umat) * star Umat = M := by
    rw [Matrix.mul_assoc M Umat (star Umat)]
    rw [hstar_left, Matrix.mul_one]
  change dotProduct (star Umat *ᵥ lambda)
      (Matrix.mulVec (star Umat * M * Umat) (star Umat *ᵥ lambda)) =
    dotProduct lambda (Matrix.mulVec M lambda)
  calc
    dotProduct (star Umat *ᵥ lambda)
        (Matrix.mulVec (star Umat * M * Umat) (star Umat *ᵥ lambda))
        = dotProduct (Matrix.vecMul lambda Umat)
            (Matrix.mulVec (star Umat * M * Umat) (star Umat *ᵥ lambda)) := by
          rw [hy]
    _ = Matrix.vecMul (Matrix.vecMul lambda Umat) (star Umat * M * Umat) ⬝ᵥ
          (star Umat *ᵥ lambda) := by
          rw [Matrix.dotProduct_mulVec]
    _ = Matrix.vecMul lambda (Umat * (star Umat * M * Umat)) ⬝ᵥ
          (star Umat *ᵥ lambda) := by
          rw [Matrix.vecMul_vecMul]
    _ = Matrix.vecMul lambda (M * Umat) ⬝ᵥ (star Umat *ᵥ lambda) := by
          rw [hcancel_left]
    _ = Matrix.vecMul (Matrix.vecMul lambda (M * Umat)) (star Umat) ⬝ᵥ lambda := by
          rw [Matrix.dotProduct_mulVec]
    _ = Matrix.vecMul lambda ((M * Umat) * star Umat) ⬝ᵥ lambda := by
          rw [Matrix.vecMul_vecMul]
    _ = Matrix.vecMul lambda M ⬝ᵥ lambda := by
          rw [hcancel_right]
    _ = dotProduct lambda (Matrix.mulVec M lambda) := by
          rw [Matrix.dotProduct_mulVec]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The process-level design quadratic form becomes the diagonal eigenvalue quadratic form after
applying the design eigenvector coordinates. -/
lemma designQuadraticForm_eq_eigenvectorUnitary_diagonal
    (hreg_pos : 0 < reg) (lambda : Feature d) :
    dotProduct lambda (Matrix.mulVec (designMatrix A reg x n ω) lambda) =
      dotProduct
        ((star (designEigenvectorUnitary (A := A) (reg := reg) (x := x) (n := n)
          (ω := ω) hreg_pos : Matrix (Fin d) (Fin d) ℝ)) *ᵥ lambda)
        (Matrix.mulVec
          (Matrix.diagonal
            (designEigenvalues (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
              hreg_pos))
          ((star (designEigenvectorUnitary (A := A) (reg := reg) (x := x) (n := n)
            (ω := ω) hreg_pos : Matrix (Fin d) (Fin d) ℝ)) *ᵥ lambda)) := by
  rw [← designEigenvectorUnitary_diagonalizes (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω) hreg_pos]
  exact (unitary_conj_quadraticForm_eq (d := d) (designMatrix A reg x n ω)
    (designEigenvectorUnitary (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
      hreg_pos) lambda).symm

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The adjoint of a real unitary matrix has determinant with absolute value one. -/
lemma abs_det_star_unitary
    (U : Matrix.unitaryGroup (Fin d) ℝ) :
    |(star (U : Matrix (Fin d) (Fin d) ℝ)).det| = 1 := by
  rw [← abs_one, abs_eq_iff_mul_self_eq]
  have hunit := Matrix.det_of_mem_unitary
    (A := star (U : Matrix (Fin d) (Fin d) ℝ))
    (SetLike.coe_mem (star U : Matrix.unitaryGroup (Fin d) ℝ))
  simpa [sq, mul_comm] using hunit.1

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Multiplication by the adjoint of a real unitary matrix preserves Lebesgue volume on feature
coordinates.

This is the measure-theoretic piece needed for the spectral reduction of the anisotropic Gaussian
integral: after diagonalizing the design matrix by a unitary eigenvector matrix, the corresponding
coordinate change has determinant of absolute value `1`, so Haar/Lebesgue volume is unchanged. -/
lemma unitary_star_mulVec_measurePreserving
    (U : Matrix.unitaryGroup (Fin d) ℝ) :
    MeasurePreserving
    (fun lambda : Feature d =>
        star (U : Matrix (Fin d) (Fin d) ℝ) *ᵥ lambda)
      volume volume := by
  let L : Feature d →ₗ[ℝ] Feature d :=
    Matrix.toLin' (star (U : Matrix (Fin d) (Fin d) ℝ))
  have h_abs_det :
      |(star (U : Matrix (Fin d) (Fin d) ℝ)).det| = 1 :=
    abs_det_star_unitary U
  have hdet_ne : LinearMap.det L ≠ 0 := by
    simpa [L, LinearMap.det_toLin'] using
      (Matrix.UnitaryGroup.det_isUnit (star U)).ne_zero
  refine ⟨L.continuous_of_finiteDimensional.measurable, ?_⟩
  change Measure.map L volume = volume
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) hdet_ne]
  have hscale : ENNReal.ofReal |(LinearMap.det L)⁻¹| = 1 := by
    dsimp [L]
    rw [LinearMap.det_toLin', abs_inv, h_abs_det]
    norm_num
  rw [hscale, one_smul]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The adjoint action of a real unitary matrix as a volume-preserving measurable equivalence on
feature coordinates. -/
noncomputable def unitaryStarMulVecMeasurableEquiv
    (U : Matrix.unitaryGroup (Fin d) ℝ) : Feature d ≃ᵐ Feature d where
  toFun lambda := star (U : Matrix (Fin d) (Fin d) ℝ) *ᵥ lambda
  invFun lambda := (U : Matrix (Fin d) (Fin d) ℝ) *ᵥ lambda
  left_inv lambda := by
    change (U : Matrix (Fin d) (Fin d) ℝ) *ᵥ
      (star (U : Matrix (Fin d) (Fin d) ℝ) *ᵥ lambda) = lambda
    have hunit :
        (U : Matrix (Fin d) (Fin d) ℝ) *
          star (U : Matrix (Fin d) (Fin d) ℝ) = 1 := by
      exact Unitary.coe_mul_star_self U
    rw [Matrix.mulVec_mulVec, hunit, Matrix.one_mulVec]
  right_inv lambda := by
    change star (U : Matrix (Fin d) (Fin d) ℝ) *ᵥ
      ((U : Matrix (Fin d) (Fin d) ℝ) *ᵥ lambda) = lambda
    have hunit :
        star (U : Matrix (Fin d) (Fin d) ℝ) *
          (U : Matrix (Fin d) (Fin d) ℝ) = 1 := by
      exact Unitary.coe_star_mul_self U
    rw [Matrix.mulVec_mulVec, hunit, Matrix.one_mulVec]
  measurable_toFun := (unitary_star_mulVec_measurePreserving U).measurable
  measurable_invFun := by
    change Measurable fun lambda : Feature d =>
      (U : Matrix (Fin d) (Fin d) ℝ) *ᵥ lambda
    simpa using (unitary_star_mulVec_measurePreserving (star U)).measurable

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The unitary adjoint measurable equivalence preserves Lebesgue volume. -/
lemma unitaryStarMulVecMeasurableEquiv_measurePreserving
    (U : Matrix.unitaryGroup (Fin d) ℝ) :
    MeasurePreserving (unitaryStarMulVecMeasurableEquiv U) volume volume := by
  change MeasurePreserving
    (fun lambda : Feature d => star (U : Matrix (Fin d) (Fin d) ℝ) *ᵥ lambda)
    volume volume
  exact unitary_star_mulVec_measurePreserving U

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
/-- Positive regularization makes every realized determinant ratio positive. -/
lemma designDetRatio_pos_of_reg_pos (hreg_pos : 0 < reg) :
    0 < designDetRatio A reg x n ω := by
  rw [designDetRatio_eq_div_reg_pow]
  exact div_pos
    (designDet_pos_of_reg_pos (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
      hreg_pos)
    (pow_pos hreg_pos d)

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
/-- Converts an almost-sure trace bound into the determinant-ratio bound supplied by a
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
`reg * d + n * L2`; a trace/determinant comparison then gives the corresponding
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
/-- Converts an almost-sure trace bound plus a determinant/trace comparison for `det(V_n)`
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
/-- Scalar AM-GM in the form used for PSD matrix eigenvalues:
the product of nonnegative entries is bounded by the arithmetic mean to the `card` power. -/
lemma prod_le_average_pow_of_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (∏ i, z i) ≤ ((∑ i, z i) / (Fintype.card ι : ℝ)) ^ Fintype.card ι := by
  classical
  have hN_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hweights_pos : 0 < ∑ i : ι, (1 : ℝ) := by
    simpa using hN_pos
  have h_amgm := Real.geom_mean_le_arith_mean (s := Finset.univ)
      (w := fun _ : ι ↦ (1 : ℝ)) (z := z)
      (by intro i hi; norm_num) hweights_pos (by intro i hi; exact hz i)
  have h_amgm' :
      (∏ i : ι, z i) ^ ((Fintype.card ι : ℝ)⁻¹) ≤
        (∑ i : ι, z i) / (Fintype.card ι : ℝ) := by
    simpa using h_amgm
  have hprod_nonneg : 0 ≤ ∏ i : ι, z i := by
    exact Finset.prod_nonneg fun i _ ↦ hz i
  have hraise := Real.rpow_le_rpow (Real.rpow_nonneg hprod_nonneg _) h_amgm' hN_pos.le
  have hleft :
      ((∏ i : ι, z i) ^ ((Fintype.card ι : ℝ)⁻¹)) ^ (Fintype.card ι : ℝ) =
        ∏ i : ι, z i := by
    rw [← Real.rpow_mul hprod_nonneg]
    rw [inv_mul_cancel₀ hN_pos.ne']
    simp
  have hright :
      ((∑ i : ι, z i) / (Fintype.card ι : ℝ)) ^ (Fintype.card ι : ℝ) =
        ((∑ i : ι, z i) / (Fintype.card ι : ℝ)) ^ Fintype.card ι := by
    rw [Real.rpow_natCast]
  simpa [hleft, hright] using hraise

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- PSD matrix determinant/trace comparison from AM-GM over eigenvalues:
`det(M) ≤ (trace(M) / d) ^ d`. -/
lemma matrixDetLeTraceAveragePow : MatrixDetLeTraceAveragePow d := by
  intro M hM
  by_cases hd : d = 0
  · subst d
    simp
  · haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
    rw [hM.1.det_eq_prod_eigenvalues, hM.1.trace_eq_sum_eigenvalues]
    simpa using prod_le_average_pow_of_nonneg
      (z := fun i : Fin d ↦ hM.1.eigenvalues i)
      (fun i ↦ hM.eigenvalues_nonneg i)

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
/-- The deterministic determinant-ratio trace budget used in the textbook LinUCB bound:
`(1 + n L² / (λ d))^d`. -/
noncomputable def textbookDesignDetRatioTraceBound
    (d : ℕ) (reg L2 : ℝ) (n : ℕ) : ℝ :=
  (1 + (n : ℝ) * L2 / (reg * (d : ℝ))) ^ d

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The textbook determinant-ratio trace budget is the same as the trace-average expression
produced by the determinant/trace comparison. -/
lemma textbookDesignDetRatioTraceBound_eq_trace_budget
    (L2 : ℝ) (hreg_pos : 0 < reg) (hd : d ≠ 0) :
    textbookDesignDetRatioTraceBound d reg L2 n =
      ((reg * (d : ℝ) + (n : ℝ) * L2) / (reg * (d : ℝ))) ^ d := by
  unfold textbookDesignDetRatioTraceBound
  congr 1
  have hden : reg * (d : ℝ) ≠ 0 := by
    exact mul_ne_zero hreg_pos.ne' (by exact_mod_cast hd)
  field_simp [hden]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The trace-budget determinant-ratio bound is monotone in the horizon when `L2 ≥ 0`. -/
lemma trace_budget_ratio_pow_le_textbookDesignDetRatioTraceBound
    (L2 : ℝ) (hreg_pos : 0 < reg) (hd : d ≠ 0) (hL2_nonneg : 0 ≤ L2)
    {t n : ℕ} (ht : t ≤ n) :
    ((reg * (d : ℝ) + (t : ℝ) * L2) / (reg * (d : ℝ))) ^ d ≤
      textbookDesignDetRatioTraceBound d reg L2 n := by
  have hden_pos : 0 < reg * (d : ℝ) := by
    exact mul_pos hreg_pos (by exact_mod_cast Nat.pos_of_ne_zero hd)
  have ht_real : (t : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast ht
  have hnum_nonneg : 0 ≤ reg * (d : ℝ) + (t : ℝ) * L2 :=
    add_nonneg hden_pos.le (mul_nonneg (Nat.cast_nonneg t) hL2_nonneg)
  have hbase_le :
      (reg * (d : ℝ) + (t : ℝ) * L2) / (reg * (d : ℝ)) ≤
        (reg * (d : ℝ) + (n : ℝ) * L2) / (reg * (d : ℝ)) := by
    refine (div_le_div_iff_of_pos_right hden_pos).mpr ?_
    nlinarith
  calc
    ((reg * (d : ℝ) + (t : ℝ) * L2) / (reg * (d : ℝ))) ^ d
        ≤ ((reg * (d : ℝ) + (n : ℝ) * L2) / (reg * (d : ℝ))) ^ d :=
          pow_le_pow_left₀ (div_nonneg hnum_nonneg hden_pos.le) hbase_le d
    _ = textbookDesignDetRatioTraceBound d reg L2 n :=
          (textbookDesignDetRatioTraceBound_eq_trace_budget (reg := reg) (d := d)
            (n := n) L2 hreg_pos hd).symm

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Bounded finite-action features and the matrix determinant/trace comparison bound every
intermediate determinant ratio by the terminal textbook trace budget. -/
lemma designDetRatio_ae_all_le_textbookTraceBound_of_featureSqNorm_bound
    [Nonempty (Fin K)]
    (L2 : ℝ) (hreg_pos : 0 < reg) (hd : d ≠ 0)
    (hL2 : FeatureSqNormBound x L2)
    (hdet_trace : MatrixDetLeTraceAveragePow d) :
    ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      designDetRatio A reg x t ω ≤ textbookDesignDetRatioTraceBound d reg L2 n := by
  have hL2_nonneg : 0 ≤ L2 := hL2.nonneg
  have h_all :
      ∀ᵐ ω ∂P, ∀ t,
        designDetRatio A reg x t ω ≤
          ((reg * (d : ℝ) + (t : ℝ) * L2) / (reg * (d : ℝ))) ^ d := by
    simp_rw [ae_all_iff]
    intro t
    exact designDetRatio_ae_le_trace_budget_of_featureSqNorm_bound_of_matrix_det_trace_bound
      (A := A) (reg := reg) (x := x) (n := t) (P := P)
      L2 hreg_pos hd
      (featureSqNorm_ae_le_of_featureSqNormBound (A := A) (x := x) (n := t)
        (P := P) L2 hL2)
      hdet_trace
  filter_upwards [h_all] with ω h_allω t ht
  exact (h_allω t).trans
    (trace_budget_ratio_pow_le_textbookDesignDetRatioTraceBound (reg := reg) (d := d)
      L2 hreg_pos hd hL2_nonneg (le_of_lt (mem_range.mp ht)))

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

The determinant-update lemmas below establish that the capped quadratic-width term is bounded by
this quantity. A separate log/telescoping bridge then connects this one-step quantity to
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
/-- Scalar log inequality used in the textbook elliptical-potential proof: for `0 ≤ q`,
`min 1 q ≤ 2 * log (1 + q)`. -/
lemma min_one_le_two_mul_log_one_add_of_nonneg {q : ℝ}
    (hq_nonneg : 0 ≤ q) :
    min 1 q ≤ 2 * Real.log (1 + q) := by
  by_cases hq_le_one : q ≤ 1
  · exact min_one_le_two_mul_log_one_add_of_nonneg_le_one hq_nonneg hq_le_one
  · have hq_one : 1 ≤ q := by linarith
    have hlog : 2 * q / (q + 2) ≤ Real.log (1 + q) :=
      Real.le_log_one_add_of_nonneg hq_nonneg
    have hq_add_two_pos : 0 < q + 2 := by linarith
    have hone_le_log_lower : 1 ≤ 2 * (2 * q / (q + 2)) := by
      rw [show 2 * (2 * q / (q + 2)) = 4 * q / (q + 2) by ring]
      rw [le_div_iff₀ hq_add_two_pos]
      nlinarith
    rw [min_eq_left hq_one]
    exact hone_le_log_lower.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))

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
/-- Under determinant nonvanishing and nonnegativity of the selected quadratic form, the single
capped quadratic-width term is bounded by the one-step log-determinant potential. This is the
textbook form; no separate `q ≤ 1` assumption is needed because the term is already capped. -/
lemma cappedWidthTerm_le_ellipticalPotentialStep_of_nonneg
    (hdet : designDet A reg x n ω ≠ 0)
    (h_nonneg : 0 ≤ widthQuadraticForm A reg x (A n ω) n ω) :
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
    exact min_one_le_two_mul_log_one_add_of_nonneg h_nonneg

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
/-- Almost surely, determinant nonvanishing and nonnegative selected quadratic forms imply the
per-step one-step-potential bound for the capped quadratic-width term. -/
lemma cappedWidthTerm_ae_le_ellipticalPotentialStep_of_det_ne_zero_of_nonneg
    (hdet : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → designDet A reg x t ω ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω) :
    ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      (if t = 0 then 0 else min 1 (widthQuadraticForm A reg x (A t ω) t ω)) ≤
        ellipticalPotentialStep A reg x t ω := by
  filter_upwards [hdet, h_nonneg] with ω hdetω h_nonnegω
  intro t ht
  exact cappedWidthTerm_le_ellipticalPotentialStep_of_nonneg (A := A) (reg := reg)
    (x := x) (n := t) (ω := ω) (hdetω t ht) (h_nonnegω t ht)

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
elliptical-potential inequality. This is the induction shell for the determinant-update proof. -/
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

This separates the elliptical-potential proof into two local obligations:

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
/-- Almost surely, determinant nonvanishing and nonnegative selected quadratic forms imply the
capped-sum/log-determinant elliptical-potential bound.

This is the capped form used in the textbook proof of LinUCB: the quadratic forms do not need to
be bounded by `1`, because the accumulated quantity is `min 1 q_t`. -/
lemma cappedQuadraticWidthSum_ae_le_ellipticalPotential_of_det_ne_zero_and_nonneg
    (hdet : ∀ᵐ ω ∂P, ∀ t, t ∈ range (n + 1) → designDet A reg x t ω ≠ 0)
    (h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω) :
    ∀ᵐ ω ∂P, cappedQuadraticWidthSum A reg x n ω ≤ ellipticalPotential A reg x n ω := by
  have hdet_range_n : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → designDet A reg x t ω ≠ 0 := by
    filter_upwards [hdet] with ω hdetω
    intro t ht
    exact hdetω t (mem_range.mpr (Nat.lt_trans (mem_range.mp ht) (Nat.lt_succ_self n)))
  exact cappedQuadraticWidthSum_ae_le_ellipticalPotential_of_stepPotential_ae_le_of_det_ne_zero
    (A := A) (reg := reg) (x := x) (n := n) (P := P) hdet
    (cappedWidthTerm_ae_le_ellipticalPotentialStep_of_det_ne_zero_of_nonneg
      (A := A) (reg := reg) (x := x) (n := n) (P := P) hdet_range_n h_nonneg)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Positive regularization discharges determinant nonvanishing and nonnegativity, yielding the
capped-sum/log-determinant elliptical-potential bound directly. -/
lemma cappedQuadraticWidthSum_ae_le_ellipticalPotential_of_reg_pos
    (hreg_pos : 0 < reg) :
    ∀ᵐ ω ∂P, cappedQuadraticWidthSum A reg x n ω ≤ ellipticalPotential A reg x n ω := by
  exact cappedQuadraticWidthSum_ae_le_ellipticalPotential_of_det_ne_zero_and_nonneg
    (A := A) (reg := reg) (x := x) (n := n) (P := P)
    (designDet_ae_ne_zero_of_reg_pos (A := A) (reg := reg) (x := x)
      (n := n + 1) (P := P) hreg_pos)
    (widthQuadraticForm_ae_nonneg_of_reg_nonneg (A := A) (reg := reg) (x := x)
      (n := n) (P := P) hreg_pos.le)

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

This is the determinant-nonvanishing version of the one-step interface: it isolates the one-step
matrix inequality from the final log-determinant bound. -/
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

Given a determinant-ratio bound `designDetRatio ≤ (T / (reg * d)) ^ d`, where `T` is an upper bound
on `trace(V_n)`, this theorem feeds that determinant-ratio bound into the determinant-update and
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
Given a deterministic trace/determinant comparison that turns this trace budget into the
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
/-- Textbook capped elliptical-potential budget from bounded selected feature norms and the
matrix-level determinant/trace comparison.

Unlike `cappedQuadraticWidthBound_ae_of_matrix_det_trace_bound`, this theorem bounds the capped
quadratic-width sum directly and does not assume the individual quadratic forms are at most `1`. -/
lemma cappedQuadraticWidthSum_ae_le_featureSqNorm_budget_of_matrix_det_trace_bound
    (hreg_pos : 0 < reg) (hd : d ≠ 0)
    (L2 : ℝ)
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → featureSqNorm x (A t ω) ≤ L2)
    (hdet_trace : MatrixDetLeTraceAveragePow d) :
    ∀ᵐ ω ∂P,
      cappedQuadraticWidthSum A reg x n ω ≤
        2 * (d : ℝ) * Real.log (1 + (n : ℝ) * L2 / (reg * (d : ℝ))) := by
  have hden : reg * (d : ℝ) ≠ 0 := by
    exact mul_ne_zero hreg_pos.ne' (by exact_mod_cast hd)
  rw [← featureSqNorm_budget_log_eq_dim_mul_log_one_add (reg := reg) (n := n) L2 hden]
  have h_nonneg : ∀ᵐ ω ∂P, ∀ t, t ∈ range n →
      0 ≤ widthQuadraticForm A reg x (A t ω) t ω :=
    widthQuadraticForm_ae_nonneg_of_reg_nonneg (A := A) (reg := reg) (x := x)
      (n := n) (P := P) hreg_pos.le
  have h_potential_le : ∀ᵐ ω ∂P,
      ellipticalPotential A reg x n ω ≤
        2 * Real.log (((reg * (d : ℝ) + (n : ℝ) * L2) / (reg * (d : ℝ))) ^ d) := by
    exact ellipticalPotential_ae_le_two_mul_log_of_designDetRatio_ae_le (A := A)
      (reg := reg) (x := x) (n := n) (P := P)
      (designDetRatio_ae_pos_of_reg_ne_zero_and_widthQuadraticForm_ae_nonneg
        (A := A) (reg := reg) (x := x) (n := n) (P := P) hreg_pos.ne' h_nonneg)
      (designDetRatio_ae_le_trace_budget_of_featureSqNorm_bound_of_matrix_det_trace_bound
        (A := A) (reg := reg) (x := x) (n := n) (P := P) L2 hreg_pos hd hL2
        hdet_trace)
  filter_upwards [cappedQuadraticWidthSum_ae_le_ellipticalPotential_of_reg_pos
    (A := A) (reg := reg) (x := x) (n := n) (P := P) hreg_pos, h_potential_le] with
    ω h_capped_le h_potentialω
  exact h_capped_le.trans h_potentialω

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
      (x := x) (n := n) (P := P)
      (WidthQuadraticFormLeFeatureSqNormDivReg.of_reg_pos (A := A) (reg := reg)
        (x := x) hreg_pos)
      hreg_pos hL2 hL2_le_reg)
    L2 hL2 ?_
  intro ω h_traceω
  exact designDetRatio_le_trace_budget_of_designDet_le (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) (T := reg * (d : ℝ) + (n : ℝ) * L2) hreg_pos hd
    (hdet_of_trace ω h_traceω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Feature-norm-budget interface consuming the reusable positive-semidefinite determinant/trace
comparison `det(M) ≤ (trace(M) / d) ^ d`. -/
lemma cappedQuadraticWidthBound_ae_of_matrix_det_trace_bound
    (hreg_pos : 0 < reg) (hd : d ≠ 0)
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
    L2 hL2 hL2_le_reg ?_
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

/-- The finite-action LinUCB process starts from the deterministic default arm. -/
lemma arm_zero [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P) :
    A 0 =ᵐ[P] fun _ ↦ ⟨0, hK⟩ := by
  exact h.action_zero_detAlgorithm

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- In zero feature dimension, every least-squares reward estimate is zero. -/
lemma estimatedReward_eq_zero_of_dim_eq_zero (hd : d = 0) (a : Fin K) :
    estimatedReward A R reg x a n ω = 0 := by
  subst d
  simp [estimatedReward, dotProduct]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- In zero feature dimension, every LinUCB quadratic width form is zero. -/
lemma widthQuadraticForm_eq_zero_of_dim_eq_zero (hd : d = 0) (a : Fin K) :
    widthQuadraticForm A reg x a n ω = 0 := by
  subst d
  simp [widthQuadraticForm, dotProduct]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- In zero feature dimension, every LinUCB width is zero. -/
lemma width_eq_zero_of_dim_eq_zero (hd : d = 0) (a : Fin K) :
    width A reg x a n ω = 0 := by
  simp [width, widthQuadraticForm_eq_zero_of_dim_eq_zero (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) hd a]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- In zero feature dimension, every LinUCB index is zero. -/
lemma index_eq_zero_of_dim_eq_zero (hd : d = 0) (a : Fin K) :
    index A R reg β x a n ω = 0 := by
  simp [index, estimatedReward_eq_zero_of_dim_eq_zero (A := A) (R := R)
    (reg := reg) (x := x) (n := n) (ω := ω) hd a,
    width_eq_zero_of_dim_eq_zero (A := A) (reg := reg) (x := x) (n := n)
      (ω := ω) hd a]

end AlgorithmBehavior

end LinUCB

end Bandits
