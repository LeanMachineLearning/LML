/-
Copyright (c) 2026 Fawad Haider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Fawad Haider
-/
module

public import LeanMachineLearning.Online.Bandit.SumRewards
public import LeanMachineLearning.SequentialLearning.Deterministic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Probability.Martingale.OptionalStopping

/-!
# LinUCB for finite-action linear bandits
Chapter 19 of *Bandit Algorithms*:
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset Learning

open scoped ENNReal NNReal Matrix MatrixOrder

namespace Bandits

variable {K d : ℕ}

section Algorithm

namespace LinUCB

/-- Feature vectors for finite-dimensional linear bandits.

We use mathlib's Euclidean space model so that LinUCB's feature vectors carry the standard
inner-product and norm structure of `ℝ^d`. Coordinate formulas remain available through the
coercion `Feature d → (Fin d → ℝ)`, which is useful for the matrix identities below. -/
abbrev Feature (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- View a coordinate matrix-vector product as a Euclidean feature vector. -/
noncomputable def matrixMulFeature (M : Matrix (Fin d) (Fin d) ℝ) (v : Feature d) :
    Feature d :=
  WithLp.toLp 2 (Matrix.mulVec M v)

lemma mulVec_matrixMulFeature (M N : Matrix (Fin d) (Fin d) ℝ) (v : Feature d) :
    Matrix.mulVec M (matrixMulFeature N v) = Matrix.mulVec (M * N) v := by
  ext i
  simp [matrixMulFeature, Matrix.mulVec_mulVec]

/-- The coordinate dot product of a feature vector with itself is its squared Euclidean norm. -/
lemma dotProduct_self_eq_norm_sq (u : Feature d) :
    dotProduct u u = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp [dotProduct, inner]

/-- The squared Euclidean norm of an arbitrary feature vector is nonnegative. -/
lemma dotProduct_self_nonneg (u : Feature d) :
    0 ≤ dotProduct u u := by
  rw [dotProduct]
  exact sum_nonneg fun i _ ↦ mul_self_nonneg (u i)

/-- Euclidean Cauchy-Schwarz for the finite-dimensional `Feature d` dot product. -/
lemma abs_dotProduct_le_sqrt_mul_sqrt (u v : Feature d) :
    |dotProduct u v| ≤ √(dotProduct u u) * √(dotProduct v v) := by
  have hpos :
      dotProduct u v ≤ √(dotProduct u u) * √(dotProduct v v) := by
    simpa [dotProduct, pow_two] using
      (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin d)) u v)
  have hneg :
      -dotProduct u v ≤ √(dotProduct u u) * √(dotProduct v v) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin d))
      (fun i : Fin d ↦ -u i) v
    simpa [dotProduct, pow_two, Finset.sum_neg_distrib] using h
  exact abs_le.mpr ⟨by linarith, hpos⟩

/-- Cauchy-Schwarz with external squared-norm bounds. -/
lemma abs_dotProduct_le_sqrt_mul_sqrt_of_sq_norm_le
    (u v : Feature d) {U V : ℝ}
    (hu : dotProduct u u ≤ U) (hv : dotProduct v v ≤ V) :
    |dotProduct u v| ≤ √U * √V := by
  refine (abs_dotProduct_le_sqrt_mul_sqrt u v).trans ?_
  exact mul_le_mul (Real.sqrt_le_sqrt hu) (Real.sqrt_le_sqrt hv)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Uniform squared feature-norm bound for finite-action LinUCB.

This is the finite-action version of the textbook assumption `‖x‖₂ ≤ L`, written here in squared
form as `‖x_a‖₂² ≤ L2` for every action. -/
def FeatureSqNormBound (x : Fin K → Feature d) (L2 : ℝ) : Prop :=
  ∀ a, ‖x a‖ ^ 2 ≤ L2

/-- A uniform squared feature-norm bound is nonnegative whenever the finite action set is
nonempty. -/
lemma FeatureSqNormBound.nonneg [Nonempty (Fin K)]
    {x : Fin K → Feature d} {L2 : ℝ} (hL2 : FeatureSqNormBound x L2) :
    0 ≤ L2 := by
  classical
  exact (sq_nonneg ‖x (Classical.arbitrary (Fin K))‖).trans
    (hL2 (Classical.arbitrary (Fin K)))

lemma exists_abs_dotProduct_feature_bound (x : Fin K → Feature d) (v : Feature d) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ a, |dotProduct v (x a)| ≤ Q := by
  refine ⟨∑ a, |dotProduct v (x a)|, ?_, ?_⟩
  · exact sum_nonneg fun a _ha ↦ abs_nonneg _
  · intro a
    exact Finset.single_le_sum
      (fun b _hb ↦ abs_nonneg (dotProduct v (x b))) (Finset.mem_univ a)

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
  matrixMulFeature (designMatrix' reg x n h)⁻¹ (responseVector' x n h)

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

/-- History-level LinUCB optimistic index for a candidate arm. -/
noncomputable def index' (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d)
    (n : ℕ) (h : Iic n → Fin K × ℝ) (a : Fin K) : ℝ :=
  estimatedReward' reg x n h a + √(β (n + 2)) * width' reg x n h a

lemma measurable_designMatrix'_apply (reg : ℝ) (x : Fin K → Feature d) (n : ℕ)
    (i j : Fin d) :
    Measurable (fun h ↦ designMatrix' reg x n h i j) := by
  unfold designMatrix'
  change Measurable fun h : Iic n → Fin K × ℝ ↦
    (reg • (1 : Matrix (Fin d) (Fin d) ℝ)) i j +
      (∑ s : Iic n, Matrix.vecMulVec (x (h s).1) (x (h s).1)) i j
  refine Measurable.const_add ?_ _
  rw [show (fun h : Iic n → Fin K × ℝ ↦
      (∑ s : Iic n, Matrix.vecMulVec (x (h s).1) (x (h s).1)) i j) =
        fun h ↦ ∑ s : Iic n, x (h s).1 i * x (h s).1 j by
    funext h
    simp [Matrix.sum_apply, Matrix.vecMulVec]]
  fun_prop

@[fun_prop]
lemma measurable_responseVector'_apply (x : Fin K → Feature d) (n : ℕ) (i : Fin d) :
    Measurable (fun h ↦ responseVector' x n h i) := by
  unfold responseVector'
  fun_prop

lemma measurable_matrix_det_apply {α : Type*} {mα : MeasurableSpace α}
    (M : α → Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ i j, Measurable fun a ↦ M a i j) :
    Measurable fun a ↦ (M a).det := by
  simp_rw [Matrix.det_apply']
  fun_prop

lemma measurable_matrix_adjugate_apply {α : Type*} {mα : MeasurableSpace α}
    (M : α → Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ i j, Measurable fun a ↦ M a i j) (i j : Fin d) :
    Measurable fun a ↦ (M a).adjugate i j := by
  simp_rw [Matrix.adjugate_apply]
  refine measurable_matrix_det_apply (fun a ↦ (M a).updateRow j (Pi.single i 1)) ?_
  intro k l
  by_cases hkj : k = j
  · subst k
    simp [Matrix.updateRow_self]
  · simpa [Matrix.updateRow_ne hkj] using hM k l

lemma measurable_matrix_inv_apply {α : Type*} {mα : MeasurableSpace α}
    (M : α → Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ i j, Measurable fun a ↦ M a i j) (i j : Fin d) :
    Measurable fun a ↦ (M a)⁻¹ i j := by
  simp_rw [Matrix.inv_def]
  change Measurable fun a ↦ Ring.inverse (M a).det * (M a).adjugate i j
  simpa [Ring.inverse_eq_inv] using
    (measurable_matrix_det_apply M hM).inv.mul (measurable_matrix_adjugate_apply M hM i j)

@[fun_prop]
lemma measurable_thetaHat'_apply (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (i : Fin d) :
    Measurable (fun h ↦ thetaHat' reg x n h i) := by
  unfold thetaHat'
  change Measurable fun h ↦
    ∑ j, (designMatrix' reg x n h)⁻¹ i j * responseVector' x n h j
  refine Finset.measurable_sum _ fun j _ ↦ ?_
  exact (measurable_matrix_inv_apply (fun h ↦ designMatrix' reg x n h)
    (measurable_designMatrix'_apply reg x n) i j).mul
    (measurable_responseVector'_apply x n j)

@[fun_prop]
lemma measurable_estimatedReward' (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) (a : Fin K) :
    Measurable (fun h ↦ estimatedReward' reg x n h a) := by
  unfold estimatedReward'
  change Measurable fun h ↦ ∑ i, thetaHat' reg x n h i * x a i
  fun_prop

@[fun_prop]
lemma measurable_widthQuadraticForm' (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) (a : Fin K) :
    Measurable (fun h ↦ widthQuadraticForm' reg x n h a) := by
  unfold widthQuadraticForm'
  change Measurable fun h ↦
    ∑ i, x a i * (∑ j, (designMatrix' reg x n h)⁻¹ i j * x a j)
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun j _ ↦ ?_
  exact (measurable_matrix_inv_apply (fun h ↦ designMatrix' reg x n h)
    (measurable_designMatrix'_apply reg x n) i j).mul measurable_const

@[fun_prop]
lemma measurable_width' (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (a : Fin K) :
    Measurable (fun h ↦ width' reg x n h a) := by
  unfold width'
  fun_prop

@[fun_prop]
lemma measurable_index' (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d)
    (n : ℕ) (a : Fin K) :
    Measurable (fun h ↦ index' reg β x n h a) := by
  unfold index'
  fun_prop

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
    (n : ℕ) :
    Measurable (nextArm hK reg β x n) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact measurable_measurableArgmax fun a ↦ measurable_index' reg β x n a

end LinUCB

/-- The finite-action LinUCB algorithm. -/
noncomputable def linUCBAlgorithm (hK : 0 < K) (reg : ℝ) (β : ℕ → ℝ)
    (x : Fin K → LinUCB.Feature d) :
    Algorithm (Fin K) ℝ :=
  detAlgorithm (LinUCB.nextArm hK reg β x) (by fun_prop) ⟨0, hK⟩

end Algorithm

end Bandits
