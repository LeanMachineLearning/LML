/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Fawad Haider
-/
module

public import LeanMachineLearning.Online.Bandit.SumRewards
public import LeanMachineLearning.SequentialLearning.Deterministic
public import LeanMachineLearning.MeasureTheory.Constructions.BorelSpace.MeasurableArgMax
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

end LinUCB

end Bandits
