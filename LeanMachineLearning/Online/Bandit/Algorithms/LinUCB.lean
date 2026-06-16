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

end LinUCB

end Bandits
