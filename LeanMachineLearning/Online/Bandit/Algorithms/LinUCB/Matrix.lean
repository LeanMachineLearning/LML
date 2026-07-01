/-
Copyright (c) 2026 OpenAI, Fawad Haider. All rights reserved.
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
/-- Hermitian matrices induce symmetric coordinate bilinear forms on feature vectors. -/
lemma dotProduct_mulVec_comm_of_isHermitian {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.IsHermitian) (u v : Feature d) :
    dotProduct u (M *ᵥ v) = dotProduct v (M *ᵥ u) := by
  have hMT : Mᵀ = M := by
    simpa using hM.eq
  rw [Matrix.dotProduct_mulVec]
  have huM : u ᵥ* M = M *ᵥ u := by
    calc
      u ᵥ* M = u ᵥ* Mᵀ := by rw [hMT]
      _ = M *ᵥ u := Matrix.vecMul_transpose M u
  rw [huM, dotProduct_comm]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Expansion of a Hermitian matrix quadratic form around a difference. -/
lemma dotProduct_sub_mulVec_sub_eq {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.IsHermitian) (u v : Feature d) :
    dotProduct (u - v) (M *ᵥ (u - v)) =
      dotProduct u (M *ᵥ u) - 2 * dotProduct u (M *ᵥ v) +
        dotProduct v (M *ᵥ v) := by
  rw [Matrix.mulVec_sub, dotProduct_sub]
  simp only [WithLp.ofLp_sub]
  rw [sub_dotProduct, sub_dotProduct]
  rw [dotProduct_mulVec_comm_of_isHermitian hM v u]
  ring

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Triangle inequality for the norm induced by a positive-definite matrix. -/
lemma dotProduct_sub_mulVec_sub_le_sqrt_add_sqrt_sq {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) (u v : Feature d) :
    dotProduct (u - v) (M *ᵥ (u - v)) ≤
      (√(dotProduct u (M *ᵥ u)) + √(dotProduct v (M *ᵥ v))) ^ 2 := by
  let uf : Fin d → ℝ := u
  let vf : Fin d → ℝ := v
  letI : SeminormedAddCommGroup (Fin d → ℝ) :=
    Matrix.toSeminormedAddCommGroup M hM.posSemidef
  letI : InnerProductSpace ℝ (Fin d → ℝ) :=
    Matrix.toInnerProductSpace M hM.posSemidef
  have hq_sub :
      dotProduct (u - v) (M *ᵥ (u - v)) = inner ℝ (uf - vf) (uf - vf) := by
    change (u - v).ofLp ⬝ᵥ M *ᵥ (u - v).ofLp = inner ℝ (uf - vf) (uf - vf)
    simp only [WithLp.ofLp_sub]
    change (uf - vf) ⬝ᵥ M *ᵥ (uf - vf) = (M *ᵥ (uf - vf)) ⬝ᵥ (uf - vf)
    rw [dotProduct_comm]
  have hq_u : dotProduct u (M *ᵥ u) = inner ℝ uf uf := by
    change uf ⬝ᵥ M *ᵥ uf = (M *ᵥ uf) ⬝ᵥ uf
    rw [dotProduct_comm]
  have hq_v : dotProduct v (M *ᵥ v) = inner ℝ vf vf := by
    change vf ⬝ᵥ M *ᵥ vf = (M *ᵥ vf) ⬝ᵥ vf
    rw [dotProduct_comm]
  have h_cross_sq := real_inner_mul_inner_self_le uf vf
  have h_cross_sq_pow :
      (inner ℝ uf vf) ^ 2 ≤ inner ℝ uf uf * inner ℝ vf vf := by
    simpa [pow_two] using h_cross_sq
  have h_cross_abs :
      |inner ℝ uf vf| ≤ √(inner ℝ uf uf * inner ℝ vf vf) :=
    Real.abs_le_sqrt h_cross_sq_pow
  have h_sqrt_mul :
      √(inner ℝ uf uf * inner ℝ vf vf) =
        √(inner ℝ uf uf) * √(inner ℝ vf vf) :=
    Real.sqrt_mul (real_inner_self_nonneg (x := uf)) (inner ℝ vf vf)
  have h_sqrt_u_mul :
      √(inner ℝ uf uf) * √(inner ℝ uf uf) = inner ℝ uf uf := by
    rw [← sq, Real.sq_sqrt (real_inner_self_nonneg (x := uf))]
  have h_sqrt_v_mul :
      √(inner ℝ vf vf) * √(inner ℝ vf vf) = inner ℝ vf vf := by
    rw [← sq, Real.sq_sqrt (real_inner_self_nonneg (x := vf))]
  have h_neg_cross :
      - inner ℝ uf vf ≤ √(inner ℝ uf uf) * √(inner ℝ vf vf) := by
    exact (neg_le_abs (inner ℝ uf vf)).trans (h_cross_abs.trans_eq h_sqrt_mul)
  have h_cross_comm : inner ℝ vf uf = inner ℝ uf vf := by
    rw [real_inner_comm]
  calc
    dotProduct (u - v) (M *ᵥ (u - v))
        = inner ℝ (uf - vf) (uf - vf) := hq_sub
    _ = inner ℝ uf uf - inner ℝ uf vf - inner ℝ vf uf + inner ℝ vf vf := by
          rw [inner_sub_sub_self]
    _ = inner ℝ uf uf + inner ℝ vf vf - 2 * inner ℝ uf vf := by
          rw [h_cross_comm]
          ring
    _ ≤ inner ℝ uf uf + inner ℝ vf vf +
          2 * (√(inner ℝ uf uf) * √(inner ℝ vf vf)) := by
          nlinarith [h_neg_cross]
    _ = (√(inner ℝ uf uf) + √(inner ℝ vf vf)) ^ 2 := by
          nlinarith [h_sqrt_u_mul, h_sqrt_v_mul]
    _ = (√(dotProduct u (M *ᵥ u)) + √(dotProduct v (M *ᵥ v))) ^ 2 := by
          rw [hq_u, hq_v]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Matrix Cauchy-Schwarz with an inverse-design factor. -/
lemma abs_dotProduct_le_sqrt_mul_sqrt_inv_mulVec {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) (hMdet : IsUnit M.det) (u v : Feature d) :
    |dotProduct u v| ≤
      √(dotProduct u (M *ᵥ u)) * √(dotProduct v (M⁻¹ *ᵥ v)) := by
  let uf : Fin d → ℝ := u
  let y : Fin d → ℝ := M⁻¹ *ᵥ v
  letI : SeminormedAddCommGroup (Fin d → ℝ) :=
    Matrix.toSeminormedAddCommGroup M hM.posSemidef
  letI : InnerProductSpace ℝ (Fin d → ℝ) :=
    Matrix.toInnerProductSpace M hM.posSemidef
  have hMy : M *ᵥ y = v := by
    simp [y, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hMdet]
  have h_inner_uy :
      inner ℝ uf y = dotProduct u v := by
    change (M *ᵥ y) ⬝ᵥ uf = dotProduct u v
    rw [hMy, dotProduct_comm]
  have h_inner_uu :
      inner ℝ uf uf = dotProduct u (M *ᵥ u) := by
    change (M *ᵥ uf) ⬝ᵥ uf = dotProduct u (M *ᵥ u)
    rw [dotProduct_comm]
  have h_inner_yy :
      inner ℝ y y = dotProduct v (M⁻¹ *ᵥ v) := by
    change (M *ᵥ y) ⬝ᵥ y = dotProduct v (M⁻¹ *ᵥ v)
    rw [hMy]
  have hsq := real_inner_mul_inner_self_le uf y
  rw [h_inner_uy, h_inner_uu, h_inner_yy] at hsq
  have hsq' :
      dotProduct u v ^ 2 ≤ dotProduct u (M *ᵥ u) * dotProduct v (M⁻¹ *ᵥ v) := by
    simpa [pow_two] using hsq
  have h_abs := Real.abs_le_sqrt hsq'
  calc
    |dotProduct u v|
        ≤ √(dotProduct u (M *ᵥ u) * dotProduct v (M⁻¹ *ᵥ v)) := h_abs
    _ = √(dotProduct u (M *ᵥ u)) * √(dotProduct v (M⁻¹ *ᵥ v)) := by
        rw [Real.sqrt_mul (by simpa using hM.posSemidef.dotProduct_mulVec_nonneg u)]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Multiplying a wrapped inverse matrix-vector product by the original nonsingular matrix recovers
the original feature vector in coordinates. -/
lemma mulVec_matrixMulFeature_nonsing_inv (M : Matrix (Fin d) (Fin d) ℝ)
    (hMdet : IsUnit M.det) (v : Feature d) :
    Matrix.mulVec M (matrixMulFeature M⁻¹ v) = v := by
  rw [mulVec_matrixMulFeature, Matrix.mul_nonsing_inv _ hMdet]
  simp

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The inverse of the regularized identity is the reciprocal-scaled identity. -/
lemma reg_smul_one_inv (hreg : reg ≠ 0) :
    (reg • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ =
      reg⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  rw [Matrix.inv_eq_left_inv]
  simp [smul_smul, hreg]

/-- Matrix inverse anti-monotonicity on positive-definite matrices. -/
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

/-- Closed form for the design trace: initial regularization trace plus accumulated squared
feature norms. -/
lemma designTrace_eq_reg_mul_dim_add_sum_featureSqNorm
    (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) :
    designTrace A reg x n ω =
      reg * (d : ℝ) + ∑ t ∈ range n, ‖x (A t ω)‖ ^ 2 := by
  simp [designTrace, designMatrix, Matrix.trace_vecMulVec, dotProduct_self_eq_norm_sq]

/-- With nonnegative regularization, the design trace is nonnegative. -/
lemma designTrace_nonneg (hreg_nonneg : 0 ≤ reg) :
    0 ≤ designTrace A reg x n ω := by
  rw [designTrace_eq_reg_mul_dim_add_sum_featureSqNorm]
  exact add_nonneg
    (mul_nonneg hreg_nonneg (Nat.cast_nonneg d))
    (sum_nonneg fun t _ ↦ sq_nonneg ‖x (A t ω)‖)

/-- If every selected feature vector has squared norm at most `L2`, then the trace of the design
matrix is at most `reg * d + n * L2`. -/
lemma designTrace_le_reg_mul_dim_add_nat_mul_featureSqNorm_bound
    (L2 : ℝ)
    (hL2 : ∀ t, t ∈ range n → ‖x (A t ω)‖ ^ 2 ≤ L2) :
    designTrace A reg x n ω ≤ reg * (d : ℝ) + (n : ℝ) * L2 := by
  rw [designTrace_eq_reg_mul_dim_add_sum_featureSqNorm]
  gcongr
  calc
    (∑ t ∈ range n, ‖x (A t ω)‖ ^ 2) ≤ ∑ _t ∈ range n, L2 := by
      exact sum_le_sum fun t ht ↦ hL2 t ht
    _ = (n : ℝ) * L2 := by
      simp [nsmul_eq_mul]

omit [IsProbabilityMeasure P] in
/-- Almost surely, bounded selected feature norms give the corresponding deterministic trace
budget `reg * d + n * L2`. -/
lemma designTrace_ae_le_reg_mul_dim_add_nat_mul_featureSqNorm_bound
    (L2 : ℝ)
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → ‖x (A t ω)‖ ^ 2 ≤ L2) :
    ∀ᵐ ω ∂P, designTrace A reg x n ω ≤ reg * (d : ℝ) + (n : ℝ) * L2 := by
  filter_upwards [hL2] with ω hL2ω
  exact designTrace_le_reg_mul_dim_add_nat_mul_featureSqNorm_bound (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) L2 hL2ω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A uniform finite-action feature bound implies the selected-action feature bound through any
finite horizon. -/
lemma featureSqNorm_ae_le_of_featureSqNormBound
    (L2 : ℝ) (hL2 : FeatureSqNormBound x L2) :
    ∀ᵐ ω ∂P, ∀ t, t ∈ range n → ‖x (A t ω)‖ ^ 2 ≤ L2 :=
  Filter.Eventually.of_forall fun ω t _ht ↦ hL2 (A t ω)

/-- The process-level reward-feature vector built from history up to time `n` excluded. -/
noncomputable def responseVector (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : Feature d :=
  ∑ s ∈ range n, R s ω • x (A s ω)

/-- Process-level regularized least-squares parameter estimate. -/
noncomputable def thetaHat (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : Feature d :=
  matrixMulFeature (designMatrix A reg x n ω)⁻¹ (responseVector A R x n ω)

/-- Process-level estimated mean reward for an arm. -/
noncomputable def estimatedReward (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (a : Fin K) (n : ℕ) (ω : Ω) : ℝ :=
  dotProduct (thetaHat A R reg x n ω) (x a)

/-- Quadratic form inside the LinUCB confidence width. -/
noncomputable def widthQuadraticForm (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (a : Fin K) (n : ℕ) (ω : Ω) : ℝ :=
  dotProduct (x a) (Matrix.mulVec (designMatrix A reg x n ω)⁻¹ (x a))

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

/-- LinUCB elliptical confidence width for an arm. -/
noncomputable def width (A : ℕ → Ω → Fin K) (reg : ℝ)
    (x : Fin K → Feature d) (a : Fin K) (n : ℕ) (ω : Ω) : ℝ :=
  √(widthQuadraticForm A reg x a n ω)

/-- Positive-time sum of capped quadratic width forms. -/
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
    simpa [Umat, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.mulVec_transpose (U : Matrix (Fin d) (Fin d) ℝ) lambda)
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
        matrixMulFeature (star (U : Matrix (Fin d) (Fin d) ℝ)) lambda)
      volume volume := by
  let L : Feature d →ₗ[ℝ] Feature d :=
    Matrix.toLpLin 2 2 (star (U : Matrix (Fin d) (Fin d) ℝ))
  have h_abs_det :
      |(star (U : Matrix (Fin d) (Fin d) ℝ)).det| = 1 :=
    abs_det_star_unitary U
  have hdet_ne : LinearMap.det L ≠ 0 := by
    simpa [L, LinearMap.det_toLpLin] using
      (Matrix.UnitaryGroup.det_isUnit (star U)).ne_zero
  refine ⟨L.continuous_of_finiteDimensional.measurable, ?_⟩
  change Measure.map L volume = volume
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) hdet_ne]
  have hscale : ENNReal.ofReal |(LinearMap.det L)⁻¹| = 1 := by
    dsimp [L]
    rw [LinearMap.det_toLpLin, abs_inv, h_abs_det]
    norm_num
  rw [hscale, one_smul]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The adjoint action of a real unitary matrix as a volume-preserving measurable equivalence on
feature coordinates. -/
noncomputable def unitaryStarMulVecMeasurableEquiv
    (U : Matrix.unitaryGroup (Fin d) ℝ) : Feature d ≃ᵐ Feature d where
  toFun lambda := matrixMulFeature (star (U : Matrix (Fin d) (Fin d) ℝ)) lambda
  invFun lambda := matrixMulFeature (U : Matrix (Fin d) (Fin d) ℝ) lambda
  left_inv lambda := by
    have hunit :
        (U : Matrix (Fin d) (Fin d) ℝ) *
          star (U : Matrix (Fin d) (Fin d) ℝ) = 1 := by
      exact Unitary.coe_mul_star_self U
    ext i
    simp [matrixMulFeature, Matrix.mulVec_mulVec, hunit]
  right_inv lambda := by
    have hunit :
        star (U : Matrix (Fin d) (Fin d) ℝ) *
          (U : Matrix (Fin d) (Fin d) ℝ) = 1 := by
      exact Unitary.coe_star_mul_self U
    ext i
    simp [matrixMulFeature, Matrix.mulVec_mulVec, hunit]
  measurable_toFun := (unitary_star_mulVec_measurePreserving U).measurable
  measurable_invFun := by
    change Measurable fun lambda : Feature d =>
      matrixMulFeature (U : Matrix (Fin d) (Fin d) ℝ) lambda
    simpa using (unitary_star_mulVec_measurePreserving (star U)).measurable

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The unitary adjoint measurable equivalence preserves Lebesgue volume. -/
lemma unitaryStarMulVecMeasurableEquiv_measurePreserving
    (U : Matrix.unitaryGroup (Fin d) ℝ) :
    MeasurePreserving (unitaryStarMulVecMeasurableEquiv U) volume volume := by
  change MeasurePreserving
    (fun lambda : Feature d =>
      matrixMulFeature (star (U : Matrix (Fin d) (Fin d) ℝ)) lambda)
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
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → ‖x (A t ω)‖ ^ 2 ≤ L2)
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
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → ‖x (A t ω)‖ ^ 2 ≤ L2)
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
    (hL2 : ∀ᵐ ω ∂P, ∀ t, t ∈ range n → ‖x (A t ω)‖ ^ 2 ≤ L2)
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

/-- The process-level LinUCB optimistic index. -/
noncomputable def index (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d) (a : Fin K)
    (n : ℕ) (ω : Ω) : ℝ :=
  estimatedReward A R reg x a n ω + √(β (n + 1)) * width A reg x a n ω

lemma arm_zero
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
