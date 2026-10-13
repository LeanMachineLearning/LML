/-
Copyright (c) 2026 OpenAI, Fawad Haider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Fawad Haider
-/
module

public import LeanMachineLearning.Online.Bandit.Algorithms.LinUCB.ConcentrationCore
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# LinUCB Textbook Mixture Event

Textbook determinant-ratio self-normalized event, Gaussian-mixture statistic,
stopping-time machinery, and deterministic bridge to the textbook noise event.
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

omit [IsMarkovKernel ν] in
/-- Horizon-local textbook self-normalized centered-noise event.

At every positive time in the horizon, the centered reward-feature vector is controlled in the
inverse-design norm by the determinant-ratio radius from the textbook self-normalized inequality.
This is the direct target for the missing Gaussian-mixture/determinant concentration theorem. -/
def LinUCBTextbookSelfNormalizedNoiseEventUpTo
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (δ : ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) (ω : Ω) : Prop :=
  ∀ t, t ∈ range n → t ≠ 0 →
    centeredNoiseQuadraticForm A R ν reg x t ω ≤
      textbookSelfNormalizedNoiseBound σ2 δ (designDetRatio A reg x t ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Gaussian-mixture statistic for the textbook self-normalized LinUCB proof.

After integrating the fixed-direction exponential process over a Gaussian direction, the textbook
argument obtains a nonnegative process of this shape:
`exp(‖S_t‖²_{V_t⁻¹} / (2 σ²)) / sqrt(det(V_t) / det(reg I))`.
The missing vector concentration theorem should prove that this statistic is at most `1 / δ` with
probability at least `1 - δ`. The deterministic lemmas below turn that mixture-statistic bound into
`LinUCBTextbookSelfNormalizedNoiseEventUpTo`. -/
noncomputable def textbookSelfNormalizedMixtureStatistic
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (centeredNoiseQuadraticForm A R ν reg x n ω / (2 * (σ2 : ℝ))) /
    √(designDetRatio A reg x n ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Horizon-local mixture-statistic event corresponding to the textbook Gaussian-mixture proof. -/
def LinUCBTextbookMixtureBoundEventUpTo
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (δ : ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) (ω : Ω) : Prop :=
  ∀ t, t ∈ range n → t ≠ 0 →
    textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω ≤ 1 / δ

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The textbook Gaussian-mixture statistic is pointwise nonnegative. -/
lemma textbookSelfNormalizedMixtureStatistic_nonneg
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν n ω := by
  unfold textbookSelfNormalizedMixtureStatistic
  exact div_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Process-level design-matrix entries are measurable when the action process is measurable. -/
lemma measurable_designMatrix_apply
    (hA : ∀ t, Measurable (A t)) (reg : ℝ) (x : Fin K → Feature d)
    (n : ℕ) (i j : Fin d) :
    Measurable fun ω ↦ designMatrix A reg x n ω i j := by
  unfold designMatrix
  change Measurable fun ω ↦
    (reg • (1 : Matrix (Fin d) (Fin d) ℝ)) i j +
      (∑ s ∈ range n, Matrix.vecMulVec (x (A s ω)) (x (A s ω))) i j
  refine Measurable.const_add ?_ _
  rw [show (fun ω ↦
      (∑ s ∈ range n, Matrix.vecMulVec (x (A s ω)) (x (A s ω))) i j) =
        fun ω ↦ ∑ s ∈ range n, x (A s ω) i * x (A s ω) j by
    funext ω
    simp [Matrix.sum_apply, Matrix.vecMulVec]]
  refine Finset.measurable_sum (range n) fun s _hs ↦ ?_
  have hxi : Measurable fun ω ↦ x (A s ω) i :=
    (measurable_of_countable fun a : Fin K ↦ x a i).comp (hA s)
  have hxj : Measurable fun ω ↦ x (A s ω) j :=
    (measurable_of_countable fun a : Fin K ↦ x a j).comp (hA s)
  exact hxi.mul hxj

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Process-level response-vector coordinates are measurable when actions and rewards are
measurable. -/
lemma measurable_responseVector_apply
    (hA : ∀ t, Measurable (A t)) (hR : ∀ t, Measurable (R t))
    (x : Fin K → Feature d) (n : ℕ) (i : Fin d) :
    Measurable fun ω ↦ responseVector A R x n ω i := by
  unfold responseVector
  have hsum : Measurable fun ω ↦ ∑ s ∈ range n, R s ω * x (A s ω) i := by
    refine Finset.measurable_sum (range n) fun s _hs ↦ ?_
    have hxi : Measurable fun ω ↦ x (A s ω) i :=
      (measurable_of_countable fun a : Fin K ↦ x a i).comp (hA s)
    exact (hR s).mul hxi
  simpa [Finset.sum_apply, smul_eq_mul] using hsum

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Process-level mean-response coordinates are measurable when the action process is measurable. -/
lemma measurable_meanResponseVector_apply
    (hA : ∀ t, Measurable (A t)) (ν : Kernel (Fin K) ℝ)
    (x : Fin K → Feature d) (n : ℕ) (i : Fin d) :
    Measurable fun ω ↦ meanResponseVector A ν x n ω i := by
  unfold meanResponseVector
  have hsum : Measurable fun ω ↦ ∑ s ∈ range n, (ν (A s ω))[id] * x (A s ω) i := by
    refine Finset.measurable_sum (range n) fun s _hs ↦ ?_
    have hmean : Measurable fun ω ↦ (ν (A s ω))[id] :=
      (measurable_rewardMean ν).comp (hA s)
    have hxi : Measurable fun ω ↦ x (A s ω) i :=
      (measurable_of_countable fun a : Fin K ↦ x a i).comp (hA s)
    exact hmean.mul hxi
  simpa [Finset.sum_apply, smul_eq_mul] using hsum

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Process-level centered-response coordinates are measurable when actions and rewards are
measurable. -/
lemma measurable_centeredResponseVector_apply
    (hA : ∀ t, Measurable (A t)) (hR : ∀ t, Measurable (R t))
    (ν : Kernel (Fin K) ℝ) (x : Fin K → Feature d) (n : ℕ) (i : Fin d) :
    Measurable fun ω ↦ centeredResponseVector A R ν x n ω i := by
  unfold centeredResponseVector
  exact (measurable_responseVector_apply (A := A) (R := R) hA hR x n i).sub
    (measurable_meanResponseVector_apply (A := A) hA ν x n i)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The centered-noise inverse-design quadratic form is measurable when actions and rewards are
measurable. -/
lemma measurable_centeredNoiseQuadraticForm
    (hA : ∀ t, Measurable (A t)) (hR : ∀ t, Measurable (R t))
    (ν : Kernel (Fin K) ℝ) (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) :
    Measurable fun ω ↦ centeredNoiseQuadraticForm A R ν reg x n ω := by
  unfold centeredNoiseQuadraticForm
  change Measurable fun ω ↦
    ∑ i, centeredResponseVector A R ν x n ω i *
      (∑ j, (designMatrix A reg x n ω)⁻¹ i j *
        centeredResponseVector A R ν x n ω j)
  refine Finset.measurable_sum univ fun i _hi ↦ ?_
  refine (measurable_centeredResponseVector_apply (A := A) (R := R) hA hR ν x n i).mul ?_
  refine Finset.measurable_sum univ fun j _hj ↦ ?_
  exact (measurable_matrix_inv_apply (fun ω ↦ designMatrix A reg x n ω)
    (measurable_designMatrix_apply (A := A) hA reg x n) i j).mul
    (measurable_centeredResponseVector_apply (A := A) (R := R) hA hR ν x n j)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The process-level design determinant is measurable when the action process is measurable. -/
lemma measurable_designDet
    (hA : ∀ t, Measurable (A t)) (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) :
    Measurable fun ω ↦ designDet A reg x n ω := by
  unfold designDet
  exact measurable_matrix_det_apply (fun ω ↦ designMatrix A reg x n ω)
    (measurable_designMatrix_apply (A := A) hA reg x n)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The process-level design determinant ratio is measurable when the action process is
measurable. -/
lemma measurable_designDetRatio
    (hA : ∀ t, Measurable (A t)) (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) :
    Measurable fun ω ↦ designDetRatio A reg x n ω := by
  unfold designDetRatio
  exact (measurable_designDet (A := A) hA reg x n).div
    (measurable_designDet (A := A) hA reg x 0)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The textbook Gaussian-mixture statistic is measurable when actions and rewards are
measurable. -/
lemma measurable_textbookSelfNormalizedMixtureStatistic
    (hA : ∀ t, Measurable (A t)) (hR : ∀ t, Measurable (R t))
    (reg : ℝ) (σ2 : ℝ≥0) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) :
    Measurable fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν n ω := by
  unfold textbookSelfNormalizedMixtureStatistic
  exact (Real.measurable_exp.comp
    ((measurable_centeredNoiseQuadraticForm (A := A) (R := R) hA hR ν reg x n).div_const
      (2 * (σ2 : ℝ)))).div
    ((measurable_designDetRatio (A := A) hA reg x n).sqrt)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Localized version of `measurable_designMatrix_apply`: the design matrix at horizon `n` only
uses actions with indices in `range n`. -/
lemma measurable_designMatrix_apply_of_mem_range
    {m : MeasurableSpace Ω}
    (hA : ∀ t, t ∈ range n → Measurable[m] (A t)) (reg : ℝ)
    (x : Fin K → Feature d) (i j : Fin d) :
    Measurable[m] fun ω ↦ designMatrix A reg x n ω i j := by
  unfold designMatrix
  change Measurable[m] fun ω ↦
    (reg • (1 : Matrix (Fin d) (Fin d) ℝ)) i j +
      (∑ s ∈ range n, Matrix.vecMulVec (x (A s ω)) (x (A s ω))) i j
  refine Measurable.const_add ?_ _
  rw [show (fun ω ↦
      (∑ s ∈ range n, Matrix.vecMulVec (x (A s ω)) (x (A s ω))) i j) =
        fun ω ↦ ∑ s ∈ range n, x (A s ω) i * x (A s ω) j by
    funext ω
    simp [Matrix.sum_apply, Matrix.vecMulVec]]
  refine Finset.measurable_sum (range n) fun s hs ↦ ?_
  have hxi : Measurable[m] fun ω ↦ x (A s ω) i :=
    (measurable_of_countable fun a : Fin K ↦ x a i).comp (hA s hs)
  have hxj : Measurable[m] fun ω ↦ x (A s ω) j :=
    (measurable_of_countable fun a : Fin K ↦ x a j).comp (hA s hs)
  exact hxi.mul hxj

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Localized version of `measurable_responseVector_apply`: the response vector at horizon `n`
only uses action/reward pairs with indices in `range n`. -/
lemma measurable_responseVector_apply_of_mem_range
    {m : MeasurableSpace Ω}
    (hA : ∀ t, t ∈ range n → Measurable[m] (A t))
    (hR : ∀ t, t ∈ range n → Measurable[m] (R t))
    (x : Fin K → Feature d) (i : Fin d) :
    Measurable[m] fun ω ↦ responseVector A R x n ω i := by
  unfold responseVector
  have hsum : Measurable[m] fun ω ↦ ∑ s ∈ range n, R s ω * x (A s ω) i := by
    refine Finset.measurable_sum (range n) fun s hs ↦ ?_
    have hxi : Measurable[m] fun ω ↦ x (A s ω) i :=
      (measurable_of_countable fun a : Fin K ↦ x a i).comp (hA s hs)
    exact (hR s hs).mul hxi
  simpa [Finset.sum_apply, smul_eq_mul] using hsum

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Localized version of `measurable_meanResponseVector_apply`: the mean-response vector at
horizon `n` only uses actions with indices in `range n`. -/
lemma measurable_meanResponseVector_apply_of_mem_range
    {m : MeasurableSpace Ω}
    (hA : ∀ t, t ∈ range n → Measurable[m] (A t)) (ν : Kernel (Fin K) ℝ)
    (x : Fin K → Feature d) (i : Fin d) :
    Measurable[m] fun ω ↦ meanResponseVector A ν x n ω i := by
  unfold meanResponseVector
  have hsum : Measurable[m] fun ω ↦ ∑ s ∈ range n, (ν (A s ω))[id] * x (A s ω) i := by
    refine Finset.measurable_sum (range n) fun s hs ↦ ?_
    have hmean : Measurable[m] fun ω ↦ (ν (A s ω))[id] :=
      (measurable_rewardMean ν).comp (hA s hs)
    have hxi : Measurable[m] fun ω ↦ x (A s ω) i :=
      (measurable_of_countable fun a : Fin K ↦ x a i).comp (hA s hs)
    exact hmean.mul hxi
  simpa [Finset.sum_apply, smul_eq_mul] using hsum

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Localized version of `measurable_centeredResponseVector_apply`. -/
lemma measurable_centeredResponseVector_apply_of_mem_range
    {m : MeasurableSpace Ω}
    (hA : ∀ t, t ∈ range n → Measurable[m] (A t))
    (hR : ∀ t, t ∈ range n → Measurable[m] (R t))
    (ν : Kernel (Fin K) ℝ) (x : Fin K → Feature d) (i : Fin d) :
    Measurable[m] fun ω ↦ centeredResponseVector A R ν x n ω i := by
  unfold centeredResponseVector
  exact (measurable_responseVector_apply_of_mem_range (A := A) (R := R) hA hR x i).sub
    (measurable_meanResponseVector_apply_of_mem_range (A := A) hA ν x i)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Localized version of `measurable_centeredNoiseQuadraticForm`. -/
lemma measurable_centeredNoiseQuadraticForm_of_mem_range
    {m : MeasurableSpace Ω}
    (hA : ∀ t, t ∈ range n → Measurable[m] (A t))
    (hR : ∀ t, t ∈ range n → Measurable[m] (R t))
    (ν : Kernel (Fin K) ℝ) (reg : ℝ) (x : Fin K → Feature d) :
    Measurable[m] fun ω ↦ centeredNoiseQuadraticForm A R ν reg x n ω := by
  unfold centeredNoiseQuadraticForm
  change Measurable[m] fun ω ↦
    ∑ i, centeredResponseVector A R ν x n ω i *
      (∑ j, (designMatrix A reg x n ω)⁻¹ i j *
        centeredResponseVector A R ν x n ω j)
  refine Finset.measurable_sum univ fun i _hi ↦ ?_
  refine (measurable_centeredResponseVector_apply_of_mem_range
    (A := A) (R := R) hA hR ν x i).mul ?_
  refine Finset.measurable_sum univ fun j _hj ↦ ?_
  exact (measurable_matrix_inv_apply (fun ω ↦ designMatrix A reg x n ω)
    (measurable_designMatrix_apply_of_mem_range (A := A) hA reg x) i j).mul
    (measurable_centeredResponseVector_apply_of_mem_range
      (A := A) (R := R) hA hR ν x j)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Localized version of `measurable_designDet`. -/
lemma measurable_designDet_of_mem_range
    {m : MeasurableSpace Ω}
    (hA : ∀ t, t ∈ range n → Measurable[m] (A t)) (reg : ℝ)
    (x : Fin K → Feature d) :
    Measurable[m] fun ω ↦ designDet A reg x n ω := by
  unfold designDet
  exact measurable_matrix_det_apply (fun ω ↦ designMatrix A reg x n ω)
    (measurable_designMatrix_apply_of_mem_range (A := A) hA reg x)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Localized version of `measurable_designDetRatio`. -/
lemma measurable_designDetRatio_of_mem_range
    {m : MeasurableSpace Ω}
    (hA : ∀ t, t ∈ range n → Measurable[m] (A t)) (reg : ℝ)
    (x : Fin K → Feature d) :
    Measurable[m] fun ω ↦ designDetRatio A reg x n ω := by
  unfold designDetRatio
  have hA0 : ∀ t, t ∈ range 0 → Measurable[m] (A t) := by
    intro t ht
    simp at ht
  exact (measurable_designDet_of_mem_range (A := A) hA reg x).div
    (measurable_designDet_of_mem_range (A := A) hA0 reg x)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Localized version of `measurable_textbookSelfNormalizedMixtureStatistic`. -/
lemma measurable_textbookSelfNormalizedMixtureStatistic_of_mem_range
    {m : MeasurableSpace Ω}
    (hA : ∀ t, t ∈ range n → Measurable[m] (A t))
    (hR : ∀ t, t ∈ range n → Measurable[m] (R t))
    (reg : ℝ) (σ2 : ℝ≥0) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) :
    Measurable[m] fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν n ω := by
  unfold textbookSelfNormalizedMixtureStatistic
  exact (Real.measurable_exp.comp
    ((measurable_centeredNoiseQuadraticForm_of_mem_range
      (A := A) (R := R) hA hR ν reg x).div_const
        (2 * (σ2 : ℝ)))).div
    ((measurable_designDetRatio_of_mem_range (A := A) hA reg x).sqrt)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The textbook mixture statistic is adapted to the repository's action filtration.

At time `n = 0`, the statistic is deterministic. At positive time `n`, it is a measurable
function of the history through `n - 1`, hence of `filtrationAction n`, which additionally contains
the already selected action at time `n`. -/
lemma stronglyMeasurable_textbookSelfNormalizedMixtureStatistic_filtrationAction
    (hA : ∀ t, Measurable (A t)) (hR : ∀ t, Measurable (R t))
    (reg : ℝ) (σ2 : ℝ≥0) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) :
    StronglyMeasurable[IsAlgEnvSeq.filtrationAction hA hR n]
      (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν n ω) := by
  by_cases hn : n = 0
  · subst n
    exact stronglyMeasurable_const' fun ω₁ ω₂ ↦ by
      simp [textbookSelfNormalizedMixtureStatistic, centeredNoiseQuadraticForm,
        centeredResponseVector_zero (A := A) (R := R) (ν := ν) (x := x),
        designDetRatio, designDet, designMatrix_zero]
  · have hleft :
        IsAlgEnvSeq.filtration hA hR (n - 1) ≤
          IsAlgEnvSeq.filtrationAction hA hR n := by
      simp [IsAlgEnvSeq.filtrationAction, hn]
    have hA_before : ∀ t, t ∈ range n →
        Measurable[IsAlgEnvSeq.filtrationAction hA hR n] (A t) := by
      intro t ht
      have ht_le : t ≤ n - 1 := Nat.le_pred_of_lt (mem_range.mp ht)
      have ht_meas :
          Measurable[IsAlgEnvSeq.filtration hA hR (n - 1)] (A t) :=
        (IsAlgEnvSeq.adapted_action hA hR t).mono
          ((IsAlgEnvSeq.filtration hA hR).mono ht_le) le_rfl
      exact ht_meas.mono hleft le_rfl
    have hR_before : ∀ t, t ∈ range n →
        Measurable[IsAlgEnvSeq.filtrationAction hA hR n] (R t) := by
      intro t ht
      have ht_le : t ≤ n - 1 := Nat.le_pred_of_lt (mem_range.mp ht)
      have ht_meas :
          Measurable[IsAlgEnvSeq.filtration hA hR (n - 1)] (R t) :=
        (IsAlgEnvSeq.adapted_feedback hA hR t).mono
          ((IsAlgEnvSeq.filtration hA hR).mono ht_le) le_rfl
      exact ht_meas.mono hleft le_rfl
    exact (measurable_textbookSelfNormalizedMixtureStatistic_of_mem_range
      (A := A) (R := R) (n := n) hA_before hR_before reg σ2 x ν).stronglyMeasurable

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Process-level adaptedness of the textbook Gaussian-mixture statistic. -/
lemma stronglyAdapted_textbookSelfNormalizedMixtureStatistic_filtrationAction
    (hA : ∀ t, Measurable (A t)) (hR : ∀ t, Measurable (R t))
    (reg : ℝ) (σ2 : ℝ≥0) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) :
    StronglyAdapted (IsAlgEnvSeq.filtrationAction hA hR)
      (fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω) := by
  intro n
  exact stronglyMeasurable_textbookSelfNormalizedMixtureStatistic_filtrationAction
    (A := A) (R := R) hA hR reg σ2 x ν n

omit [IsMarkovKernel ν] in
/-- Assemble the textbook Gaussian-mixture statistic as a `Supermartingale` from the two remaining
analytic obligations.

The adaptedness field is proved by
`stronglyAdapted_textbookSelfNormalizedMixtureStatistic_filtrationAction`. Therefore a future
method-of-mixtures proof only has to supply:

* integrability of the closed-form determinant-ratio statistic at every time, and
* the one-step conditional expectation inequality.

This mirrors the UCB proof-template style: first prove a process is adapted/integrable and has
one-step conditional decrease, then let `supermartingale_nat` produce the full multi-time
supermartingale statement. -/
lemma supermartingale_textbookSelfNormalizedMixtureStatistic_filtrationAction_of_condExp_succ_le
    (hA : ∀ t, Measurable (A t)) (hR : ∀ t, Measurable (R t))
    (reg : ℝ) (σ2 : ℝ≥0) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ)
    (h_int : ∀ i,
      Integrable (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω) P)
    (h_cond : ∀ i,
      P[fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν (i + 1) ω |
          IsAlgEnvSeq.filtrationAction hA hR i] ≤ᵐ[P]
        fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω) :
    Supermartingale
      (fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω)
      (IsAlgEnvSeq.filtrationAction hA hR) P := by
  exact supermartingale_nat
    (𝒢 := IsAlgEnvSeq.filtrationAction hA hR)
    (hadp := stronglyAdapted_textbookSelfNormalizedMixtureStatistic_filtrationAction
      (A := A) (R := R) hA hR reg σ2 x ν)
    h_int h_cond

omit [IsMarkovKernel ν] in
/-- Assemble the textbook Gaussian-mixture statistic as a `Supermartingale` from one-step
set-integral decrease.

This is often the most convenient interface for the remaining method-of-mixtures proof. After
Fubini/Tonelli turns the stopped Gaussian integral into iterated integrals, the natural statement is
that every event in the current action filtration has no larger next-time mixture integral than
current-time mixture integral. Mathlib's `supermartingale_of_setIntegral_succ_le` then supplies the
conditional-expectation supermartingale fields. -/
lemma supermartingale_textbookSelfNormalizedMixtureStatistic_filtrationAction_of_setIntegral_succ_le
    (hA : ∀ t, Measurable (A t)) (hR : ∀ t, Measurable (R t))
    (reg : ℝ) (σ2 : ℝ≥0) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ)
    (h_int : ∀ i,
      Integrable (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω) P)
    (h_set : ∀ i, ∀ s : Set Ω,
      MeasurableSet[IsAlgEnvSeq.filtrationAction hA hR i] s →
        (∫ ω in s, textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν (i + 1) ω ∂P) ≤
          ∫ ω in s, textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω ∂P) :
    Supermartingale
      (fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω)
      (IsAlgEnvSeq.filtrationAction hA hR) P := by
  exact supermartingale_of_setIntegral_succ_le
    (𝒢 := IsAlgEnvSeq.filtrationAction hA hR)
    (hadp := stronglyAdapted_textbookSelfNormalizedMixtureStatistic_filtrationAction
      (A := A) (R := R) hA hR reg σ2 x ν)
    h_int h_set

/-- Assemble the textbook Gaussian-mixture statistic from fixed-direction exponential
supermartingales plus a set-integral mixture identity.

This is the bridge from the scalar concentration core to the future determinant-ratio
self-normalized theorem. The scalar input is already proved by
`supermartingale_exp_centeredResponseDirectionalExponent`. The remaining Gaussian-mixture work is
concentrated in two analytic hypotheses:

* integrability of the direction-indexed set integrals, and
* the set-integral identity saying that the closed-form textbook statistic equals the integral of
  the fixed-direction exponential process over the direction measure.

Once those are available, the supermartingale proof is pure monotonicity: apply the
fixed-direction supermartingale set-integral inequality for each direction and integrate over
directions. -/
lemma supermartingale_textbookSelfNormalizedMixtureStatistic_filtrationAction_of_directionalMixture
    [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (μlambda : Measure (Feature d))
    (h_int_stat : ∀ i,
      Integrable (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω) P)
    (h_inner_int : ∀ i, ∀ s : Set Ω, MeasurableSet s →
      Integrable
        (fun lambda ↦
          ∫ ω in s,
            Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda) ∂P)
        μlambda)
    (h_mix_set : ∀ i, ∀ s : Set Ω, MeasurableSet s →
      (∫ ω in s, textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω ∂P) =
        ∫ lambda,
          (∫ ω in s,
            Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda) ∂P)
          ∂μlambda) :
    Supermartingale
      (fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω)
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) P := by
  let ℱ := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback
  refine
    supermartingale_textbookSelfNormalizedMixtureStatistic_filtrationAction_of_setIntegral_succ_le
      (A := A) (R := R) (reg := reg) (σ2 := σ2) (x := x) (ν := ν) (P := P)
      h.measurable_action h.measurable_feedback h_int_stat ?_
  intro i s hs
  have hs_base : MeasurableSet s := ℱ.le i s hs
  have h_pointwise :
      (fun lambda ↦
        ∫ ω in s,
          Real.exp
            (centeredResponseDirectionalExponent A R ν reg σ2 x (i + 1) ω lambda) ∂P)
        ≤ᵐ[μlambda]
      fun lambda ↦
        ∫ ω in s,
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda) ∂P :=
    Filter.Eventually.of_forall fun lambda ↦ by
      exact
        (supermartingale_exp_centeredResponseDirectionalExponent
          (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
          h hν lambda).setIntegral_le (Nat.le_succ i) hs
  calc
    (∫ ω in s, textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν (i + 1) ω ∂P)
        =
          ∫ lambda,
            (∫ ω in s,
              Real.exp
                (centeredResponseDirectionalExponent A R ν reg σ2 x (i + 1) ω lambda) ∂P)
            ∂μlambda := h_mix_set (i + 1) s hs_base
    _ ≤
          ∫ lambda,
            (∫ ω in s,
              Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda) ∂P)
            ∂μlambda :=
        integral_mono_ae (h_inner_int (i + 1) s hs_base) (h_inner_int i s hs_base)
          h_pointwise
    _ =
        ∫ ω in s, textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω ∂P :=
        (h_mix_set i s hs_base).symm

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Turn the pointwise Gaussian-mixture identity into the set-integral identity used by the
supermartingale assembler.

The textbook method-of-mixtures proof first identifies the determinant-ratio statistic pointwise as
a Gaussian integral over fixed-direction exponential processes. The supermartingale proof above is
phrased in terms of set integrals because conditional-expectation inequalities are easiest to
assemble from inequalities on every event in the current filtration. This lemma is the deterministic
bridge between those two interfaces: `setIntegral_congr_ae` moves the pointwise identity under
`∫ ω in s`, and `h_fubini` is the remaining Tonelli/Fubini swap. -/
lemma textbookSelfNormalizedMixtureStatistic_setIntegral_eq_integral_of_ae_eq_integral
    {σ2 : ℝ≥0} (μlambda : Measure (Feature d))
    (h_pointwise : ∀ i,
      (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω) =ᵐ[P]
        fun ω ↦
          ∫ lambda,
            Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda)
          ∂μlambda)
    (h_fubini : ∀ i, ∀ s : Set Ω, MeasurableSet s →
      (∫ ω in s,
        (∫ lambda,
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda)
        ∂μlambda) ∂P) =
        ∫ lambda,
          (∫ ω in s,
            Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda) ∂P)
          ∂μlambda) :
    ∀ i, ∀ s : Set Ω, MeasurableSet s →
      (∫ ω in s, textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω ∂P) =
        ∫ lambda,
          (∫ ω in s,
            Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda) ∂P)
          ∂μlambda := by
  intro i s hs
  calc
    (∫ ω in s, textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω ∂P)
        =
      ∫ ω in s,
        (∫ lambda,
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda)
        ∂μlambda) ∂P := by
        exact setIntegral_congr_ae hs ((h_pointwise i).mono fun _ hω _ ↦ hω)
    _ =
        ∫ lambda,
          (∫ ω in s,
            Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda) ∂P)
          ∂μlambda := h_fubini i s hs

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Normalizing constant of the isotropic Gaussian direction prior used in the textbook
method-of-mixtures proof.

For positive `reg` and `σ2`, this is `(σ² reg / (2π))^(d/2)`. The `max 0` makes the expression a
total nonnegative density normalizer even before those side conditions are available. It is kept as
a named expression so the remaining Gaussian-integral theorem can talk about a concrete density
rather than an abstract direction measure. -/
noncomputable def gaussianDirectionNormalizer (d : ℕ) (reg : ℝ) (σ2 : ℝ≥0) : ℝ :=
  Real.rpow (max 0 ((σ2 : ℝ) * reg / (2 * Real.pi))) ((d : ℝ) / 2)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Under the positive regularization/noise-variance assumptions of the textbook theorem, the
total normalizer is exactly the usual Gaussian normalizer `(σ² reg / (2π))^(d/2)`. -/
lemma gaussianDirectionNormalizer_eq_of_pos
    {σ2 : ℝ≥0}
    (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ)) :
    gaussianDirectionNormalizer d reg σ2 =
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) := by
  unfold gaussianDirectionNormalizer
  rw [max_eq_right]
  exact div_nonneg (mul_nonneg hσ2_pos.le hreg_pos.le) (by positivity)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Density of the isotropic Gaussian direction prior from the textbook method of mixtures.

This is the density of `N(0, (σ² reg)⁻¹ I)` with respect to Lebesgue measure on
`Feature d = Fin d → ℝ`, written in the coordinates used throughout this file. -/
noncomputable def gaussianDirectionDensity (d : ℕ) (reg : ℝ) (σ2 : ℝ≥0)
    (lambda : Feature d) : ℝ :=
  gaussianDirectionNormalizer d reg σ2 *
    Real.exp (-(((σ2 : ℝ) * reg * dotProduct lambda lambda) / 2))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Under the positive assumptions used by the textbook theorem, the concrete direction density is
the usual isotropic Gaussian density from the method-of-mixtures proof. -/
lemma gaussianDirectionDensity_eq_of_pos
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ))
    (lambda : Feature d) :
    gaussianDirectionDensity d reg σ2 lambda =
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        Real.exp (-(((σ2 : ℝ) * reg * dotProduct lambda lambda) / 2)) := by
  simp [gaussianDirectionDensity, gaussianDirectionNormalizer_eq_of_pos
    (d := d) (reg := reg) hreg_pos hσ2_pos]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The isotropic Gaussian exponential factor splits into a product of one-dimensional factors.

This is the algebraic step needed before applying product-volume Gaussian integral lemmas to the
concrete direction prior. -/
lemma gaussianDirectionExp_eq_prod (a : ℝ) (lambda : Feature d) :
    Real.exp (-(a * dotProduct lambda lambda / 2)) =
      ∏ i, Real.exp (-(a * (lambda i) ^ 2 / 2)) := by
  have hsum :
      -(a * dotProduct lambda lambda / 2) =
        ∑ i : Fin d, -(a * (lambda i) ^ 2 / 2) := by
    simp [dotProduct, pow_two, div_eq_mul_inv, Finset.mul_sum, mul_assoc, mul_comm]
  rw [hsum, Real.exp_sum]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Product form of the concrete Gaussian direction density. -/
lemma gaussianDirectionDensity_eq_normalizer_mul_prod
    (d : ℕ) (reg : ℝ) (σ2 : ℝ≥0) (lambda : Feature d) :
    gaussianDirectionDensity d reg σ2 lambda =
      gaussianDirectionNormalizer d reg σ2 *
        ∏ i, Real.exp (-(((σ2 : ℝ) * reg * (lambda i) ^ 2) / 2)) := by
  unfold gaussianDirectionDensity
  rw [gaussianDirectionExp_eq_prod]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Under the positive assumptions of the textbook theorem, the concrete Gaussian prior density is
the textbook normalizer times a product of one-dimensional Gaussian exponential factors. -/
lemma gaussianDirectionDensity_eq_rpow_mul_prod_of_pos
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ))
    (lambda : Feature d) :
    gaussianDirectionDensity d reg σ2 lambda =
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        ∏ i, Real.exp (-(((σ2 : ℝ) * reg * (lambda i) ^ 2) / 2)) := by
  rw [gaussianDirectionDensity_eq_normalizer_mul_prod,
    gaussianDirectionNormalizer_eq_of_pos (d := d) (reg := reg) hreg_pos hσ2_pos]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The product of one-dimensional Gaussian exponential factors in the concrete direction prior is
integrable under the positive regularization/noise-variance assumptions. -/
lemma integrable_gaussianDirectionExp_prod_of_pos
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ)) :
    Integrable
      (fun lambda : Feature d ↦
        ∏ i, Real.exp (-(((σ2 : ℝ) * reg * (lambda i) ^ 2) / 2))) := by
  apply Integrable.fintype_prod
    (f := fun _ (z : ℝ) ↦ Real.exp (-(((σ2 : ℝ) * reg * z ^ 2) / 2)))
  intro _i
  have hb : 0 < ((σ2 : ℝ) * reg) / 2 := div_pos (mul_pos hσ2_pos hreg_pos) two_pos
  convert integrable_exp_neg_mul_sq hb using 1 with z
  ring_nf

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Coordinate-wise weighted Gaussian exponential products are integrable when every coordinate
weight is positive.

This is the analytic core of the diagonal case of the anisotropic Gaussian integral. The full
positive-definite theorem should reduce to this statement after diagonalizing the design matrix. -/
lemma integrable_weightedGaussianExp_prod_of_pos
    (a : Fin d → ℝ) (ha : ∀ i, 0 < a i) :
    Integrable (fun lambda : Feature d ↦
      ∏ i, Real.exp (-(a i * (lambda i) ^ 2))) := by
  apply Integrable.fintype_prod
    (f := fun i (z : ℝ) ↦ Real.exp (-(a i * z ^ 2)))
  intro i
  convert integrable_exp_neg_mul_sq (ha i) using 1 with z
  ring_nf

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Integral of a coordinate-wise weighted Gaussian exponential product.

This is the diagonal-matrix counterpart of the remaining anisotropic Gaussian integral. It packages
the Fubini/product part separately from the later determinant algebra and orthogonal
change-of-variables arguments. -/
lemma integral_weightedGaussianExp_prod (a : Fin d → ℝ) :
    (∫ lambda : Feature d,
      ∏ i, Real.exp (-(a i * (lambda i) ^ 2))) =
        ∏ i, Real.sqrt (Real.pi / a i) := by
  have h_one : ∀ i,
      (∫ z : ℝ, Real.exp (-(a i * z ^ 2))) = Real.sqrt (Real.pi / a i) := by
    intro i
    convert integral_gaussian (a i) using 1 with z
    ring_nf
  rw [integral_fintype_prod_volume_eq_prod
    (f := fun i (z : ℝ) ↦ Real.exp (-(a i * z ^ 2)))]
  simp [h_one]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Quadratic form of a diagonal matrix in feature coordinates. -/
lemma dotProduct_mulVec_diagonal (diag : Fin d → ℝ) (lambda : Feature d) :
    dotProduct lambda (Matrix.mulVec (Matrix.diagonal diag) lambda) =
      ∑ i, diag i * (lambda i) ^ 2 := by
  simp [dotProduct, Matrix.mulVec, Matrix.diagonal, pow_two, mul_comm, mul_left_comm]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Exponential of a diagonal quadratic form factors into one-dimensional Gaussian terms. -/
lemma diagonalGaussianExp_eq_prod (a : ℝ) (diag : Fin d → ℝ) (lambda : Feature d) :
    Real.exp (-(a * dotProduct lambda (Matrix.mulVec (Matrix.diagonal diag) lambda))) =
      ∏ i, Real.exp (-((a * diag i) * (lambda i) ^ 2)) := by
  have hsum :
      -(a * dotProduct lambda (Matrix.mulVec (Matrix.diagonal diag) lambda)) =
        ∑ i : Fin d, -((a * diag i) * (lambda i) ^ 2) := by
    simp [dotProduct, Matrix.mulVec, Matrix.diagonal, pow_two, Finset.mul_sum,
      mul_comm, mul_left_comm]
  rw [hsum, Real.exp_sum]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Diagonal-matrix version of the anisotropic Gaussian integral.

The remaining full positive-definite Gaussian integral should reduce to this theorem after
orthogonally diagonalizing the design matrix and proving the coordinate change preserves volume. -/
lemma integral_diagonalGaussianExp (a : ℝ) (diag : Fin d → ℝ) :
    (∫ lambda : Feature d,
      Real.exp (-(a * dotProduct lambda (Matrix.mulVec (Matrix.diagonal diag) lambda)))) =
        ∏ i, Real.sqrt (Real.pi / (a * diag i)) := by
  calc
    (∫ lambda : Feature d,
      Real.exp (-(a * dotProduct lambda (Matrix.mulVec (Matrix.diagonal diag) lambda))))
        = ∫ lambda : Feature d,
            ∏ i, Real.exp (-((a * diag i) * (lambda i) ^ 2)) := by
          exact integral_congr_ae <| ae_of_all _ fun lambda ↦
            diagonalGaussianExp_eq_prod (d := d) a diag lambda
    _ = ∏ i, Real.sqrt (Real.pi / (a * diag i)) := by
          rw [integral_weightedGaussianExp_prod (d := d) (fun i ↦ a * diag i)]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Normalized diagonal Gaussian integral scalar algebra.

This is the determinant-normalization part of the diagonal anisotropic integral. The left side is
the Gaussian-prior normalizer times the diagonal Gaussian integral; the right side is the inverse
square root of the diagonal determinant ratio. -/
lemma normalized_diagonalGaussianIntegral_eq_inv_sqrt_prod_div_reg_pow
    {sig : ℝ} (hreg_pos : 0 < reg) (hsig_pos : 0 < sig)
    (diag : Fin d → ℝ) (hdiag_pos : ∀ i, 0 < diag i) :
    Real.rpow (sig * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        (∏ i, Real.sqrt (Real.pi / ((sig / 2) * diag i))) =
      1 / Real.sqrt ((∏ i, diag i) / reg ^ d) := by
  have hsig_ne : sig ≠ 0 := hsig_pos.ne'
  have hprod_pos : 0 < ∏ i, diag i := by
    exact Finset.prod_pos fun i _hi ↦ hdiag_pos i
  have hreg_pow_pos : 0 < reg ^ d := pow_pos hreg_pos d
  have hratio_pos : 0 < (∏ i, diag i) / reg ^ d := div_pos hprod_pos hreg_pow_pos
  have ha_pos : 0 < sig * reg / (2 * Real.pi) := by positivity
  have hprod_ratio :
      (∏ i : Fin d, Real.pi / ((sig / 2) * diag i)) =
        (2 * Real.pi / sig) ^ d / ∏ i, diag i := by
    calc
      (∏ i : Fin d, Real.pi / ((sig / 2) * diag i)) =
          ∏ i : Fin d, (2 * Real.pi / sig) / diag i := by
          apply Finset.prod_congr rfl
          intro i _hi
          field_simp [hsig_ne]
      _ = (2 * Real.pi / sig) ^ d / ∏ i, diag i := by
          simp [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.prod_inv_distrib]
  have hprod_sqrt_sq :
      (∏ i, Real.sqrt (Real.pi / ((sig / 2) * diag i))) ^ 2 =
        (2 * Real.pi / sig) ^ d / ∏ i, diag i := by
    rw [sq, ← Finset.prod_mul_distrib]
    calc
      (∏ x : Fin d,
          (√(Real.pi / (sig / 2 * diag x)) * √(Real.pi / (sig / 2 * diag x)))) =
          ∏ i : Fin d, Real.pi / ((sig / 2) * diag i) := by
          apply Finset.prod_congr rfl
          intro i _hi
          rw [Real.mul_self_sqrt]
          exact (div_pos Real.pi_pos (mul_pos (div_pos hsig_pos two_pos) (hdiag_pos i))).le
      _ = (2 * Real.pi / sig) ^ d / ∏ i, diag i := hprod_ratio
  have hrpow_sq :
      (Real.rpow (sig * reg / (2 * Real.pi)) ((d : ℝ) / 2)) ^ 2 =
        (sig * reg / (2 * Real.pi)) ^ d := by
    rw [sq]
    rw [show
        Real.rpow (sig * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
          Real.rpow (sig * reg / (2 * Real.pi)) ((d : ℝ) / 2) =
            Real.rpow (sig * reg / (2 * Real.pi))
              (((d : ℝ) / 2) + ((d : ℝ) / 2)) from
        (Real.rpow_add ha_pos ((d : ℝ) / 2) ((d : ℝ) / 2)).symm]
    have hsum : ((d : ℝ) / 2) + ((d : ℝ) / 2) = (d : ℝ) := by
      ring
    rw [hsum]
    exact Real.rpow_natCast (sig * reg / (2 * Real.pi)) d
  have hright_sq :
      (1 / Real.sqrt ((∏ i, diag i) / reg ^ d)) ^ 2 = reg ^ d / ∏ i, diag i := by
    rw [div_pow, one_pow, Real.sq_sqrt hratio_pos.le]
    field_simp [hreg_pow_pos.ne', hprod_pos.ne']
  have hleft_nonneg :
      0 ≤ Real.rpow (sig * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
          (∏ i, Real.sqrt (Real.pi / ((sig / 2) * diag i))) :=
    mul_nonneg (Real.rpow_nonneg ha_pos.le _)
      (Finset.prod_nonneg fun i _hi ↦ Real.sqrt_nonneg _)
  have hright_nonneg : 0 ≤ 1 / Real.sqrt ((∏ i, diag i) / reg ^ d) :=
    div_nonneg zero_le_one (Real.sqrt_nonneg _)
  refine (sq_eq_sq₀ hleft_nonneg hright_nonneg).mp ?_
  rw [mul_pow, hrpow_sq, hprod_sqrt_sq, hright_sq]
  calc
    (sig * reg / (2 * Real.pi)) ^ d * ((2 * Real.pi / sig) ^ d / ∏ i, diag i)
        = ((sig * reg / (2 * Real.pi)) ^ d * (2 * Real.pi / sig) ^ d) /
            ∏ i, diag i := by
          ring
    _ = ((sig * reg / (2 * Real.pi)) * (2 * Real.pi / sig)) ^ d / ∏ i, diag i := by
          rw [← mul_pow]
    _ = reg ^ d / ∏ i, diag i := by
          have hmul : (sig * reg / (2 * Real.pi)) * (2 * Real.pi / sig) = reg := by
            field_simp [hsig_ne, Real.pi_ne_zero]
          rw [hmul]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The concrete Gaussian direction density is integrable under the positive assumptions of the
textbook theorem. -/
lemma integrable_gaussianDirectionDensity_of_pos
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ)) :
    Integrable (fun lambda : Feature d ↦ gaussianDirectionDensity d reg σ2 lambda) := by
  refine ((integrable_gaussianDirectionExp_prod_of_pos (d := d) (reg := reg)
    hreg_pos hσ2_pos).const_mul
      (Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2))).congr ?_
  exact ae_of_all _ fun lambda ↦ (gaussianDirectionDensity_eq_rpow_mul_prod_of_pos
    (d := d) (reg := reg) hreg_pos hσ2_pos lambda).symm

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Integral of the product of one-dimensional Gaussian exponential factors appearing in the
concrete direction prior. -/
lemma integral_gaussianDirectionExp_prod
    (d : ℕ) (reg : ℝ) (σ2 : ℝ≥0) :
    (∫ lambda : Feature d,
      ∏ i, Real.exp (-(((σ2 : ℝ) * reg * (lambda i) ^ 2) / 2))) =
        (Real.sqrt (Real.pi / (((σ2 : ℝ) * reg) / 2))) ^ d := by
  have h_one :
      (∫ z : ℝ, Real.exp (-(((σ2 : ℝ) * reg * z ^ 2) / 2))) =
        Real.sqrt (Real.pi / (((σ2 : ℝ) * reg) / 2)) := by
    convert integral_gaussian (((σ2 : ℝ) * reg) / 2) using 1 with z
    ring_nf
  rw [integral_fintype_prod_volume_eq_pow (ι := Fin d)
    (f := fun z : ℝ ↦ Real.exp (-(((σ2 : ℝ) * reg * z ^ 2) / 2)))]
  simp [h_one]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Integral of the concrete Gaussian direction density, before simplifying the scalar normalizer.

The remaining normalization algebra is to show the displayed scalar is `1`. -/
lemma integral_gaussianDirectionDensity_eq_of_pos
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ)) :
    (∫ lambda : Feature d, gaussianDirectionDensity d reg σ2 lambda) =
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        (Real.sqrt (Real.pi / (((σ2 : ℝ) * reg) / 2))) ^ d := by
  calc
    (∫ lambda : Feature d, gaussianDirectionDensity d reg σ2 lambda)
        =
      ∫ lambda : Feature d,
        Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
          ∏ i, Real.exp (-(((σ2 : ℝ) * reg * (lambda i) ^ 2) / 2)) := by
        exact integral_congr_ae <| ae_of_all _ fun lambda ↦
          gaussianDirectionDensity_eq_rpow_mul_prod_of_pos
            (d := d) (reg := reg) hreg_pos hσ2_pos lambda
    _ =
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        (∫ lambda : Feature d,
          ∏ i, Real.exp (-(((σ2 : ℝ) * reg * (lambda i) ^ 2) / 2))) := by
        rw [integral_const_mul]
    _ =
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        (Real.sqrt (Real.pi / (((σ2 : ℝ) * reg) / 2))) ^ d := by
        rw [integral_gaussianDirectionExp_prod d reg σ2]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The concrete Gaussian direction density is normalized under the positive assumptions of the
textbook theorem. -/
lemma integral_gaussianDirectionDensity_eq_one_of_pos
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ)) :
    (∫ lambda : Feature d, gaussianDirectionDensity d reg σ2 lambda) = 1 := by
  let a : ℝ := ((σ2 : ℝ) * reg) / (2 * Real.pi)
  have ha_pos : 0 < a := by
    positivity
  have hbase :
      Real.pi / (((σ2 : ℝ) * reg) / 2) = a⁻¹ := by
    subst a
    field_simp [hσ2_pos.ne', hreg_pos.ne', Real.pi_ne_zero]
  have hsqrt :
      Real.sqrt (Real.pi / (((σ2 : ℝ) * reg) / 2)) =
        a ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, hbase, Real.inv_rpow ha_pos.le]
    rw [← Real.rpow_neg ha_pos.le]
    ring_nf
  have hpow :
      (Real.sqrt (Real.pi / (((σ2 : ℝ) * reg) / 2))) ^ d =
        a ^ ((-(1 : ℝ) / 2) * (d : ℝ)) := by
    rw [hsqrt, ← Real.rpow_natCast, ← Real.rpow_mul ha_pos.le]
  have hscalar :
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
          (Real.sqrt (Real.pi / (((σ2 : ℝ) * reg) / 2))) ^ d =
        1 := by
    change a ^ ((d : ℝ) / 2) *
          (Real.sqrt (Real.pi / (((σ2 : ℝ) * reg) / 2))) ^ d =
        1
    rw [hpow]
    calc
      a ^ ((d : ℝ) / 2) * a ^ ((-(1 : ℝ) / 2) * (d : ℝ))
          = a ^ (((d : ℝ) / 2) + ((-(1 : ℝ) / 2) * (d : ℝ))) := by
            rw [Real.rpow_add ha_pos]
      _ = 1 := by
        have hexp : ((d : ℝ) / 2) + ((-(1 : ℝ) / 2) * (d : ℝ)) = 0 := by
          ring
        rw [hexp, Real.rpow_zero]
  rw [integral_gaussianDirectionDensity_eq_of_pos (d := d) (reg := reg)
    hreg_pos hσ2_pos]
  exact hscalar

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Concrete Gaussian direction measure used by the textbook method of mixtures. -/
noncomputable def gaussianDirectionMeasure (d : ℕ) (reg : ℝ) (σ2 : ℝ≥0) :
    Measure (Feature d) :=
  volume.withDensity fun lambda ↦ ENNReal.ofReal (gaussianDirectionDensity d reg σ2 lambda)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The concrete Gaussian direction measure has total mass one under the positive assumptions of
the textbook theorem. -/
lemma gaussianDirectionMeasure_univ_eq_one_of_pos
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ)) :
    gaussianDirectionMeasure d reg σ2 Set.univ = 1 := by
  have hlintegral :
      (∫⁻ lambda : Feature d,
        ENNReal.ofReal (gaussianDirectionDensity d reg σ2 lambda) ∂volume) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_gaussianDirectionDensity_of_pos (d := d) (reg := reg)
        hreg_pos hσ2_pos)
      (ae_of_all _ fun lambda ↦ by
        unfold gaussianDirectionDensity gaussianDirectionNormalizer
        exact mul_nonneg
          (Real.rpow_nonneg (le_max_left 0 ((σ2 : ℝ) * reg / (2 * Real.pi))) _)
          (Real.exp_nonneg _))]
    rw [integral_gaussianDirectionDensity_eq_one_of_pos (d := d) (reg := reg)
      hreg_pos hσ2_pos]
    norm_num
  unfold gaussianDirectionMeasure
  rw [withDensity_apply _ MeasurableSet.univ]
  simpa using hlintegral

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The concrete Gaussian direction measure is a probability measure under the positive assumptions
of the textbook theorem. -/
lemma isProbabilityMeasure_gaussianDirectionMeasure_of_pos
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ)) :
    IsProbabilityMeasure (gaussianDirectionMeasure d reg σ2) where
  measure_univ := gaussianDirectionMeasure_univ_eq_one_of_pos
    (d := d) (reg := reg) hreg_pos hσ2_pos

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The concrete Gaussian direction measure is finite under the positive assumptions of the
textbook theorem. -/
lemma isFiniteMeasure_gaussianDirectionMeasure_of_pos
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ)) :
    IsFiniteMeasure (gaussianDirectionMeasure d reg σ2) := by
  have : IsProbabilityMeasure (gaussianDirectionMeasure d reg σ2) :=
    isProbabilityMeasure_gaussianDirectionMeasure_of_pos
      (d := d) (reg := reg) hreg_pos hσ2_pos
  infer_instance

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
instance instSFinite_gaussianDirectionMeasure (d : ℕ) (reg : ℝ) (σ2 : ℝ≥0) :
    SFinite (gaussianDirectionMeasure d reg σ2) := by
  unfold gaussianDirectionMeasure
  infer_instance

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The concrete Gaussian direction density is nonnegative. -/
lemma gaussianDirectionDensity_nonneg (d : ℕ) (reg : ℝ) (σ2 : ℝ≥0)
    (lambda : Feature d) :
    0 ≤ gaussianDirectionDensity d reg σ2 lambda := by
  unfold gaussianDirectionDensity gaussianDirectionNormalizer
  exact mul_nonneg (Real.rpow_nonneg (le_max_left 0 ((σ2 : ℝ) * reg / (2 * Real.pi))) _)
    (le_of_lt (Real.exp_pos _))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The concrete Gaussian direction density is measurable. -/
lemma measurable_gaussianDirectionDensity (d : ℕ) (reg : ℝ) (σ2 : ℝ≥0) :
    Measurable fun lambda : Feature d ↦ gaussianDirectionDensity d reg σ2 lambda := by
  unfold gaussianDirectionDensity gaussianDirectionNormalizer
  fun_prop

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Integrating against the concrete Gaussian direction measure is the same as integrating the
integrand multiplied by the Gaussian prior density against Lebesgue measure.

This is the measure-theoretic bridge needed before applying the completed-square algebra. The
remaining hard theorem is the actual positive-definite Gaussian integral of the right-hand side. -/
lemma integral_gaussianDirectionMeasure_eq_integral_density_mul
    (d : ℕ) (reg : ℝ) (σ2 : ℝ≥0) (g : Feature d → ℝ) :
    (∫ lambda, g lambda ∂gaussianDirectionMeasure d reg σ2) =
      ∫ lambda, gaussianDirectionDensity d reg σ2 lambda * g lambda := by
  unfold gaussianDirectionMeasure
  rw [integral_withDensity_eq_integral_toReal_smul]
  · congr 1
    ext lambda
    simp [gaussianDirectionDensity_nonneg]
  · exact (measurable_gaussianDirectionDensity d reg σ2).ennreal_ofReal
  · exact ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The unshifted positive-definite Gaussian kernel whose integral gives the determinant
normalizer in the textbook method-of-mixtures proof. -/
noncomputable def anisotropicGaussianKernel
    (A : ℕ → Ω → Fin K) (reg : ℝ) (σ2 : ℝ≥0) (x : Fin K → Feature d)
    (n : ℕ) (ω : Ω) (lambda : Feature d) : ℝ :=
  Real.exp
    (-(((σ2 : ℝ) / 2) *
      dotProduct lambda (Matrix.mulVec (designMatrix A reg x n ω) lambda)))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If the design matrix is diagonal, the anisotropic kernel is the corresponding diagonal
Gaussian exponential. -/
lemma anisotropicGaussianKernel_eq_diagonalGaussianExp_of_designMatrix_eq_diagonal
    {diag : Fin d → ℝ} (hdiag : designMatrix A reg x n ω = Matrix.diagonal diag)
    (σ2 : ℝ≥0) (lambda : Feature d) :
    anisotropicGaussianKernel A reg σ2 x n ω lambda =
      Real.exp
        (-(((σ2 : ℝ) / 2) *
          dotProduct lambda (Matrix.mulVec (Matrix.diagonal diag) lambda))) := by
  unfold anisotropicGaussianKernel
  rw [hdiag]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Diagonal-design version of the unshifted anisotropic Gaussian integral.

This is the exact integral bridge used after the spectral step rewrites the positive-definite
design matrix in orthonormal coordinates as a diagonal matrix. -/
lemma integral_anisotropicGaussianKernel_of_designMatrix_eq_diagonal
    {diag : Fin d → ℝ} (hdiag : designMatrix A reg x n ω = Matrix.diagonal diag)
    (σ2 : ℝ≥0) :
    (∫ lambda, anisotropicGaussianKernel A reg σ2 x n ω lambda) =
      ∏ i, Real.sqrt (Real.pi / (((σ2 : ℝ) / 2) * diag i)) := by
  calc
    (∫ lambda, anisotropicGaussianKernel A reg σ2 x n ω lambda)
        =
      ∫ lambda : Feature d,
        Real.exp
          (-(((σ2 : ℝ) / 2) *
            dotProduct lambda (Matrix.mulVec (Matrix.diagonal diag) lambda))) := by
        exact integral_congr_ae <| ae_of_all _ fun lambda ↦
          anisotropicGaussianKernel_eq_diagonalGaussianExp_of_designMatrix_eq_diagonal
            (A := A) (reg := reg) (x := x) (n := n) (ω := ω) hdiag σ2 lambda
    _ = ∏ i, Real.sqrt (Real.pi / (((σ2 : ℝ) / 2) * diag i)) := by
        rw [integral_diagonalGaussianExp (d := d) ((σ2 : ℝ) / 2) diag]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Diagonal-design determinant-normalized form of the unshifted anisotropic Gaussian integral.

This is the diagonal version of the positive-definite Gaussian determinant computation. The
orthogonal diagonalization bridge below reduces the general design matrix to this statement. -/
lemma anisotropicKernelIntegral_eq_inv_sqrt_designDetRatio_of_designMatrix_eq_diagonal
    {diag : Fin d → ℝ} (hreg_pos : 0 < reg) {σ2 : ℝ≥0}
    (hσ2_pos : 0 < (σ2 : ℝ))
    (hdiag : designMatrix A reg x n ω = Matrix.diagonal diag) :
    Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        (∫ lambda, anisotropicGaussianKernel A reg σ2 x n ω lambda) =
      1 / √(designDetRatio A reg x n ω) := by
  have hdiag_pos : ∀ i, 0 < diag i :=
    diagonal_pos_of_designMatrix_eq_diagonal (A := A) (reg := reg) (x := x)
      (n := n) (ω := ω) hreg_pos hdiag
  rw [integral_anisotropicGaussianKernel_of_designMatrix_eq_diagonal
    (A := A) (reg := reg) (x := x) (n := n) (ω := ω) hdiag σ2]
  rw [designDetRatio_eq_prod_div_reg_pow_of_designMatrix_eq_diagonal
    (A := A) (reg := reg) (x := x) (n := n) (ω := ω) hdiag]
  exact normalized_diagonalGaussianIntegral_eq_inv_sqrt_prod_div_reg_pow
    (d := d) (reg := reg) hreg_pos hσ2_pos diag hdiag_pos

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Abstract volume-preserving diagonalization bridge for the anisotropic Gaussian integral.

This is the measure-theoretic part of the spectral-theorem step. If a measurable equivalence `e`
preserves Lebesgue volume and rewrites the design-matrix quadratic form as a diagonal quadratic
form in the transformed coordinates, then the anisotropic integral is the corresponding diagonal
Gaussian integral. -/
lemma integral_anisotropicGaussianKernel_eq_diagonal_of_measurePreserving
    (e : Feature d ≃ᵐ Feature d) (he : MeasurePreserving e volume volume)
    {diag : Fin d → ℝ}
    (hquad : ∀ lambda : Feature d,
      dotProduct lambda (Matrix.mulVec (designMatrix A reg x n ω) lambda) =
        dotProduct (e lambda) (Matrix.mulVec (Matrix.diagonal diag) (e lambda)))
    (σ2 : ℝ≥0) :
    (∫ lambda, anisotropicGaussianKernel A reg σ2 x n ω lambda) =
      ∫ lambda : Feature d,
        Real.exp
          (-(((σ2 : ℝ) / 2) *
            dotProduct lambda (Matrix.mulVec (Matrix.diagonal diag) lambda))) := by
  calc
    (∫ lambda, anisotropicGaussianKernel A reg σ2 x n ω lambda)
        = ∫ lambda : Feature d,
            Real.exp
              (-(((σ2 : ℝ) / 2) *
                dotProduct (e lambda) (Matrix.mulVec (Matrix.diagonal diag) (e lambda)))) := by
          exact integral_congr_ae <| ae_of_all _ fun lambda ↦ by
            unfold anisotropicGaussianKernel
            rw [hquad lambda]
    _ = ∫ lambda : Feature d,
          Real.exp
            (-(((σ2 : ℝ) / 2) *
              dotProduct lambda (Matrix.mulVec (Matrix.diagonal diag) lambda))) := by
          exact he.integral_comp' (f := e)
            (fun lambda : Feature d ↦
              Real.exp
                (-(((σ2 : ℝ) / 2) *
                  dotProduct lambda (Matrix.mulVec (Matrix.diagonal diag) lambda))))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Product form of the abstract volume-preserving diagonalization bridge. -/
lemma integral_anisotropicGaussianKernel_of_measurePreserving_diagonalization
    (e : Feature d ≃ᵐ Feature d) (he : MeasurePreserving e volume volume)
    {diag : Fin d → ℝ}
    (hquad : ∀ lambda : Feature d,
      dotProduct lambda (Matrix.mulVec (designMatrix A reg x n ω) lambda) =
        dotProduct (e lambda) (Matrix.mulVec (Matrix.diagonal diag) (e lambda)))
    (σ2 : ℝ≥0) :
    (∫ lambda, anisotropicGaussianKernel A reg σ2 x n ω lambda) =
      ∏ i, Real.sqrt (Real.pi / (((σ2 : ℝ) / 2) * diag i)) := by
  rw [integral_anisotropicGaussianKernel_eq_diagonal_of_measurePreserving
    (A := A) (reg := reg) (x := x) (n := n) (ω := ω) e he hquad σ2]
  rw [integral_diagonalGaussianExp (d := d) ((σ2 : ℝ) / 2) diag]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Determinant-normalized form of the abstract volume-preserving diagonalization bridge.

The design-eigenvalue specialization below provides `e`, `diag`, the quadratic-form identity, the
determinant-ratio identity, and positivity of the diagonal entries for the positive-definite design
matrix. -/
lemma anisotropicKernelIntegral_eq_inv_sqrt_designDetRatio_of_measurePreserving_diagonalization
    (e : Feature d ≃ᵐ Feature d) (he : MeasurePreserving e volume volume)
    {diag : Fin d → ℝ} (hreg_pos : 0 < reg) {σ2 : ℝ≥0}
    (hσ2_pos : 0 < (σ2 : ℝ))
    (hquad : ∀ lambda : Feature d,
      dotProduct lambda (Matrix.mulVec (designMatrix A reg x n ω) lambda) =
        dotProduct (e lambda) (Matrix.mulVec (Matrix.diagonal diag) (e lambda)))
    (hdetRatio : designDetRatio A reg x n ω = (∏ i, diag i) / reg ^ d)
    (hdiag_pos : ∀ i, 0 < diag i) :
    Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        (∫ lambda, anisotropicGaussianKernel A reg σ2 x n ω lambda) =
      1 / √(designDetRatio A reg x n ω) := by
  rw [integral_anisotropicGaussianKernel_of_measurePreserving_diagonalization
    (A := A) (reg := reg) (x := x) (n := n) (ω := ω) e he hquad σ2]
  rw [hdetRatio]
  exact normalized_diagonalGaussianIntegral_eq_inv_sqrt_prod_div_reg_pow
    (d := d) (reg := reg) hreg_pos hσ2_pos diag hdiag_pos

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Determinant-normalized diagonalization bridge specialized to the design-matrix eigenvalues.

After this lemma, the concrete design-eigenvector specialization only has to supply the
volume-preserving coordinate change and the quadratic-form identity. Positivity of the diagonal
terms and the determinant-ratio identity are discharged by the positive-definite design-matrix
eigenvalue facts. -/
lemma anisotropicKernelIntegral_eq_inv_sqrt_designDetRatio_of_measurePreserving_designEigenvalues
    (e : Feature d ≃ᵐ Feature d) (he : MeasurePreserving e volume volume)
    (hreg_pos : 0 < reg) {σ2 : ℝ≥0} (hσ2_pos : 0 < (σ2 : ℝ))
    (hquad : ∀ lambda : Feature d,
      dotProduct lambda (Matrix.mulVec (designMatrix A reg x n ω) lambda) =
        dotProduct (e lambda)
          (Matrix.mulVec
            (Matrix.diagonal
              (designEigenvalues (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
                hreg_pos))
            (e lambda))) :
    Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        (∫ lambda, anisotropicGaussianKernel A reg σ2 x n ω lambda) =
      1 / √(designDetRatio A reg x n ω) := by
  exact anisotropicKernelIntegral_eq_inv_sqrt_designDetRatio_of_measurePreserving_diagonalization
    (A := A) (reg := reg) (x := x) (n := n) (ω := ω) e he hreg_pos hσ2_pos hquad
    (designDetRatio_eq_prod_designEigenvalues_div_reg_pow
      (A := A) (reg := reg) (x := x) (n := n) (ω := ω) hreg_pos)
    (designEigenvalues_pos (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
      hreg_pos)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Determinant-normalized diagonalization bridge for a measurable equivalence whose underlying
function is the design eigenvector coordinate map.

This isolates the two facts needed for the concrete spectral step: the coordinate map is the
adjoint eigenvector map, and that map preserves volume. The next lemma supplies those facts using
`unitaryStarMulVecMeasurableEquiv` and
`unitaryStarMulVecMeasurableEquiv_measurePreserving`. -/
lemma anisotropicKernelIntegral_eq_inv_sqrt_designDetRatio_of_measurePreserving_designEigenvectorMap
    (e : Feature d ≃ᵐ Feature d) (he : MeasurePreserving e volume volume)
    (hreg_pos : 0 < reg) {σ2 : ℝ≥0} (hσ2_pos : 0 < (σ2 : ℝ))
    (he_apply : ∀ lambda : Feature d,
      e lambda =
        (star (designEigenvectorUnitary (A := A) (reg := reg) (x := x) (n := n)
          (ω := ω) hreg_pos : Matrix (Fin d) (Fin d) ℝ)) *ᵥ lambda) :
    Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        (∫ lambda, anisotropicGaussianKernel A reg σ2 x n ω lambda) =
      1 / √(designDetRatio A reg x n ω) := by
  refine anisotropicKernelIntegral_eq_inv_sqrt_designDetRatio_of_measurePreserving_designEigenvalues
    (A := A) (reg := reg) (x := x) (n := n) (ω := ω) e he hreg_pos hσ2_pos ?_
  intro lambda
  rw [he_apply lambda]
  exact designQuadraticForm_eq_eigenvectorUnitary_diagonal (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω) hreg_pos lambda

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Determinant-normalized anisotropic Gaussian integral for the positive-definite LinUCB design
matrix.

This is the concrete spectral version of the previous abstract bridge: the measurable equivalence
is the adjoint eigenvector coordinate map of the design matrix, and
`unitaryStarMulVecMeasurableEquiv_measurePreserving` proves that this coordinate change preserves
Lebesgue volume. -/
lemma anisotropicKernelIntegral_eq_inv_sqrt_designDetRatio_of_designEigenvectors
    (hreg_pos : 0 < reg) {σ2 : ℝ≥0} (hσ2_pos : 0 < (σ2 : ℝ)) :
    Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        (∫ lambda, anisotropicGaussianKernel A reg σ2 x n ω lambda) =
      1 / √(designDetRatio A reg x n ω) := by
  let U :=
    designEigenvectorUnitary (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
      hreg_pos
  refine
    anisotropicKernelIntegral_eq_inv_sqrt_designDetRatio_of_measurePreserving_designEigenvectorMap
    (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
    (e := unitaryStarMulVecMeasurableEquiv U)
    (he := unitaryStarMulVecMeasurableEquiv_measurePreserving U)
    hreg_pos hσ2_pos ?_
  intro lambda
  rfl

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- At time zero, the anisotropic kernel is the isotropic Gaussian factor from the concrete
Gaussian direction prior, because `V₀ = reg • I`. -/
lemma anisotropicGaussianKernel_zero (σ2 : ℝ≥0) (lambda : Feature d) :
    anisotropicGaussianKernel A reg σ2 x 0 ω lambda =
      Real.exp (-(((σ2 : ℝ) * reg * dotProduct lambda lambda) / 2)) := by
  unfold anisotropicGaussianKernel
  rw [designMatrix_zero]
  simp [Matrix.smul_mulVec]
  ring_nf

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- At time zero, the centered directional exponent is zero.

There are no observed rewards at time zero, so the centered response vector vanishes. The design
matrix contribution also cancels because `V₀ = reg • I`, leaving the exponential integrand equal
to the constant `1`. -/
lemma centeredResponseDirectionalExponent_zero (σ2 : ℝ≥0) (lambda : Feature d) :
    centeredResponseDirectionalExponent A R ν reg σ2 x 0 ω lambda = 0 := by
  unfold centeredResponseDirectionalExponent
  rw [centeredResponseVector_zero, designMatrix_zero]
  simp [Matrix.smul_mulVec]

omit [IsMarkovKernel ν] in
/-- The product-integrability condition in the Gaussian-prior input is automatic at time zero.

After `centeredResponseDirectionalExponent_zero`, the integrand is the constant `1`. The ambient
product measure is finite because `P` is a probability measure and the concrete Gaussian direction
measure is finite when `reg > 0` and `σ² > 0`. -/
lemma integrable_exp_centeredResponseDirectionalExponent_zero_gaussianDirectionMeasure
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ)) :
    Integrable
      (Function.uncurry fun ω lambda ↦
        Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x 0 ω lambda))
      (P.prod (gaussianDirectionMeasure d reg σ2)) := by
  haveI : IsFiniteMeasure (gaussianDirectionMeasure d reg σ2) :=
    isFiniteMeasure_gaussianDirectionMeasure_of_pos
      (d := d) (reg := reg) hreg_pos hσ2_pos
  refine (integrable_const (α := Ω × Feature d)
    (μ := P.prod (gaussianDirectionMeasure d reg σ2)) (c := (1 : ℝ))).congr ?_
  exact Filter.Eventually.of_forall fun p ↦ by
    rcases p with ⟨ω, lambda⟩
    simp [Function.uncurry,
      centeredResponseDirectionalExponent_zero (A := A) (R := R) (ν := ν)
        (reg := reg) (x := x) (ω := ω) σ2 lambda]

/-- Joint measurability of the centered directional exponent over sample paths and Gaussian
directions. -/
lemma measurable_centeredResponseDirectionalExponent_prod
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    (σ2 : ℝ≥0) (i : ℕ) :
    Measurable fun p : Ω × Feature d ↦
      centeredResponseDirectionalExponent A R ν reg σ2 x i p.1 p.2 := by
  have h_lambda : ∀ j : Fin d, Measurable fun p : Ω × Feature d ↦ p.2 j := by
    intro j
    exact (measurable_pi_apply j).comp measurable_snd
  have h_centered : ∀ j : Fin d,
      Measurable fun p : Ω × Feature d ↦ centeredResponseVector A R ν x i p.1 j := by
    intro j
    exact (measurable_centeredResponseVector_apply (A := A) (R := R)
      h.measurable_action h.measurable_feedback ν x i j).comp measurable_fst
  have h_design : ∀ j k : Fin d,
      Measurable fun p : Ω × Feature d ↦ designMatrix A reg x i p.1 j k := by
    intro j k
    exact (measurable_designMatrix_apply (A := A) h.measurable_action reg x i j k).comp
      measurable_fst
  have h_dot_centered : Measurable fun p : Ω × Feature d ↦
      dotProduct p.2 (centeredResponseVector A R ν x i p.1) := by
    simp_rw [dotProduct]
    exact Finset.measurable_sum univ fun j _hj ↦ (h_lambda j).mul (h_centered j)
  have h_dot_design : Measurable fun p : Ω × Feature d ↦
      dotProduct p.2 (Matrix.mulVec (designMatrix A reg x i p.1) p.2) := by
    simp_rw [dotProduct, Matrix.mulVec]
    refine Finset.measurable_sum univ fun j _hj ↦ ?_
    refine (h_lambda j).mul ?_
    exact Finset.measurable_sum univ fun k _hk ↦ (h_design j k).mul (h_lambda k)
  have h_dot_lambda : Measurable fun p : Ω × Feature d ↦ dotProduct p.2 p.2 := by
    simp_rw [dotProduct]
    exact Finset.measurable_sum univ fun j _hj ↦ (h_lambda j).mul (h_lambda j)
  have h_exponent : Measurable fun p : Ω × Feature d ↦
      centeredResponseDirectionalExponent A R ν reg σ2 x i p.1 p.2 := by
    unfold centeredResponseDirectionalExponent
    exact h_dot_centered.sub
      (((measurable_const.mul
        (h_dot_design.sub (measurable_const.mul h_dot_lambda))).div_const 2))
  exact h_exponent

/-- Joint measurability of the fixed-direction exponential integrand over sample paths and
Gaussian directions. -/
lemma aestronglyMeasurable_exp_centeredResponseDirectionalExponent_prod
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    (σ2 : ℝ≥0) (i : ℕ) :
    AEStronglyMeasurable
      (Function.uncurry fun ω lambda ↦
        Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
      (P.prod (gaussianDirectionMeasure d reg σ2)) := by
  exact (Real.measurable_exp.comp
    (measurable_centeredResponseDirectionalExponent_prod
      (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (P := P)
      h σ2 i)).aestronglyMeasurable

/-- Product-integrability of the fixed-direction exponential process under the concrete Gaussian
direction measure.

For each fixed direction `λ`, the scalar exponential process has expectation at most `1`. Since the
Gaussian direction measure is finite under `reg > 0` and `σ² > 0`, Fubini's product-integrability
criterion gives integrability over `Ω × Feature d`. -/
lemma integrable_exp_centeredResponseDirectionalExponent_gaussianDirectionMeasure
    [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ)) (i : ℕ) :
    Integrable
      (Function.uncurry fun ω lambda ↦
        Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
      (P.prod (gaussianDirectionMeasure d reg σ2)) := by
  haveI : IsFiniteMeasure (gaussianDirectionMeasure d reg σ2) :=
    isFiniteMeasure_gaussianDirectionMeasure_of_pos
      (d := d) (reg := reg) hreg_pos hσ2_pos
  let μlambda := gaussianDirectionMeasure d reg σ2
  let f : Ω × Feature d → ℝ :=
    Function.uncurry fun ω lambda ↦
      Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda)
  have hf_aesm : AEStronglyMeasurable f (P.prod μlambda) := by
    simpa [f, μlambda] using
      aestronglyMeasurable_exp_centeredResponseDirectionalExponent_prod
        (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (P := P)
        h σ2 i
  rw [integrable_prod_iff' hf_aesm]
  constructor
  · exact Filter.Eventually.of_forall fun lambda ↦
      integrable_exp_centeredResponseDirectionalExponent
        (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := i)
        h hν lambda
  · refine Integrable.mono' (integrable_const (α := Feature d) (μ := μlambda) (c := (1 : ℝ)))
      ?_ ?_
    · simpa [f] using hf_aesm.norm.prod_swap.integral_prod_right'
    · exact Filter.Eventually.of_forall fun lambda ↦ by
        have h_inner_nonneg : 0 ≤ ∫ ω, ‖f (ω, lambda)‖ ∂P :=
          integral_nonneg fun _ ↦ norm_nonneg _
        rw [Real.norm_of_nonneg h_inner_nonneg]
        calc
          (∫ ω, ‖f (ω, lambda)‖ ∂P)
              =
            ∫ ω,
              Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda) ∂P := by
              exact integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ by
                simp [f, Real.norm_of_nonneg (Real.exp_nonneg _)]
          _ ≤ 1 :=
              integral_exp_centeredResponseDirectionalExponent_le_one
                (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
                (n := i) h hν lambda

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The time-zero anisotropic Gaussian integral is the product one-dimensional Gaussian integral.

This proves the base case of the remaining determinant-integral theorem: before any observations,
the design matrix is the regularized identity, so no diagonalization or Jacobian argument is
needed. -/
lemma integral_anisotropicGaussianKernel_zero (σ2 : ℝ≥0) :
    (∫ lambda, anisotropicGaussianKernel A reg σ2 x 0 ω lambda) =
      (Real.sqrt (Real.pi / (((σ2 : ℝ) * reg) / 2))) ^ d := by
  calc
    (∫ lambda, anisotropicGaussianKernel A reg σ2 x 0 ω lambda)
        = ∫ lambda : Feature d,
          Real.exp (-(((σ2 : ℝ) * reg * dotProduct lambda lambda) / 2)) := by
          exact integral_congr_ae <| ae_of_all _ fun lambda ↦
            anisotropicGaussianKernel_zero (A := A) (reg := reg) (x := x)
              (ω := ω) σ2 lambda
    _ = ∫ lambda : Feature d,
          ∏ i, Real.exp (-(((σ2 : ℝ) * reg * (lambda i) ^ 2) / 2)) := by
          exact integral_congr_ae <| ae_of_all _ fun lambda ↦ by
            simpa [mul_assoc] using gaussianDirectionExp_eq_prod (d := d)
              ((σ2 : ℝ) * reg) lambda
    _ = (Real.sqrt (Real.pi / (((σ2 : ℝ) * reg) / 2))) ^ d := by
          rw [integral_gaussianDirectionExp_prod d reg σ2]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The normalized unshifted Gaussian determinant-integral identity holds at time zero.

At `n = 0`, `designDetRatio = 1`, so the statement follows from the Gaussian direction-density
normalization already proved for the isotropic prior. -/
lemma anisotropicKernelIntegral_zero_eq_inv_sqrt_designDetRatio
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ)) :
    Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        (∫ lambda, anisotropicGaussianKernel A reg σ2 x 0 ω lambda) =
      1 / √(designDetRatio A reg x 0 ω) := by
  have hscalar_eq := integral_gaussianDirectionDensity_eq_of_pos (d := d) (reg := reg)
    hreg_pos hσ2_pos
  have hscalar_one := integral_gaussianDirectionDensity_eq_one_of_pos (d := d) (reg := reg)
    hreg_pos hσ2_pos
  rw [hscalar_eq] at hscalar_one
  have hratio : designDetRatio A reg x 0 ω = 1 :=
    designDetRatio_zero (A := A) (reg := reg) (x := x) (ω := ω)
      (designDet_zero_ne_zero_of_reg_ne_zero (A := A) (reg := reg) (x := x) (ω := ω)
        hreg_pos.ne')
  rw [integral_anisotropicGaussianKernel_zero (A := A) (reg := reg) (x := x)
    (ω := ω) σ2]
  rw [hratio]
  simpa using hscalar_one

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Center of the translated Gaussian kernel appearing after completing the square. -/
noncomputable def completedSquareGaussianCenter
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (ν : Kernel (Fin K) ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) :
    Feature d :=
  (σ2 : ℝ)⁻¹ •
    Matrix.mulVec (designMatrix A reg x n ω)⁻¹ (centeredResponseVector A R ν x n ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The translated Gaussian kernel obtained after completing the square in the textbook
method-of-mixtures proof.

For fixed history `ω`, this is the only remaining `lambda`-dependent factor after multiplying the
fixed-direction exponential supermartingale by the concrete Gaussian prior density. The missing
multivariate Gaussian integral theorem should integrate this kernel and produce the determinant
normalizer. -/
noncomputable def completedSquareGaussianKernel
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (ν : Kernel (Fin K) ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (x : Fin K → Feature d)
    (n : ℕ) (ω : Ω) (lambda : Feature d) : ℝ :=
  anisotropicGaussianKernel A reg σ2 x n ω
    (lambda - completedSquareGaussianCenter A R ν reg σ2 x n ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Translation invariance removes the completed-square shift from the remaining Gaussian integral.

After this lemma, the hard analytic theorem no longer involves the random center of the Gaussian
kernel. It only has to evaluate the unshifted positive-definite Gaussian integral. -/
lemma integral_completedSquareGaussianKernel_eq_integral_anisotropicGaussianKernel
    (σ2 : ℝ≥0) :
    (∫ lambda, completedSquareGaussianKernel A R ν reg σ2 x n ω lambda) =
      ∫ lambda, anisotropicGaussianKernel A reg σ2 x n ω lambda := by
  unfold completedSquareGaussianKernel
  exact MeasureTheory.integral_sub_right_eq_self
    (μ := volume)
    (f := fun lambda : Feature d ↦ anisotropicGaussianKernel A reg σ2 x n ω lambda)
    (completedSquareGaussianCenter A R ν reg σ2 x n ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Pointwise completed-square form of the concrete Gaussian-prior integrand.

This is the algebraic bridge immediately before the missing translated Gaussian determinant
integral: the left side is the integrand in `TextbookGaussianPriorInput.pointwiseVolume`; the right
side separates the textbook normalizer, the self-normalized noise factor, and the translated
Gaussian kernel. -/
lemma gaussianPriorIntegrand_eq_completedSquare_of_pos
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ))
    (lambda : Feature d) :
    gaussianDirectionDensity d reg σ2 lambda *
        Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda) =
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        (Real.exp (centeredNoiseQuadraticForm A R ν reg x n ω / (2 * (σ2 : ℝ))) *
          completedSquareGaussianKernel A R ν reg σ2 x n ω lambda) := by
  rw [gaussianDirectionDensity_eq_of_pos (d := d) (reg := reg) hreg_pos hσ2_pos lambda]
  calc
    (Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
          Real.exp (-(((σ2 : ℝ) * reg * dotProduct lambda lambda) / 2))) *
        Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda)
        =
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        (Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda) *
          Real.exp (-(((σ2 : ℝ) * reg * dotProduct lambda lambda) / 2))) := by
        ring
    _ =
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        (Real.exp (centeredNoiseQuadraticForm A R ν reg x n ω / (2 * (σ2 : ℝ))) *
          completedSquareGaussianKernel A R ν reg σ2 x n ω lambda) := by
        rw [exp_centeredResponseDirectionalExponent_mul_exp_neg_priorPenalty_eq_completedSquare
          (A := A) (R := R) (ν := ν) (reg := reg) (x := x) (n := n) (ω := ω)
          σ2 lambda hreg_pos hσ2_pos.ne']
        rfl

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Integral form of the completed-square bridge for the concrete Gaussian prior.

The remaining analytic step is now isolated to the final integral of
`completedSquareGaussianKernel`, which should evaluate to the inverse determinant normalizer. -/
lemma integral_gaussianPriorIntegrand_eq_completedSquare_of_pos
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ)) :
    (∫ lambda,
      gaussianDirectionDensity d reg σ2 lambda *
        Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda)) =
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        Real.exp (centeredNoiseQuadraticForm A R ν reg x n ω / (2 * (σ2 : ℝ))) *
          ∫ lambda, completedSquareGaussianKernel A R ν reg σ2 x n ω lambda := by
  calc
    (∫ lambda,
      gaussianDirectionDensity d reg σ2 lambda *
        Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda))
        =
      ∫ lambda,
        Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
          (Real.exp (centeredNoiseQuadraticForm A R ν reg x n ω / (2 * (σ2 : ℝ))) *
            completedSquareGaussianKernel A R ν reg σ2 x n ω lambda) := by
        exact integral_congr_ae <| ae_of_all _ fun lambda ↦
          gaussianPriorIntegrand_eq_completedSquare_of_pos
            (A := A) (R := R) (ν := ν) (reg := reg) (x := x) (n := n) (ω := ω)
            hreg_pos hσ2_pos lambda
    _ =
      (Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
          Real.exp (centeredNoiseQuadraticForm A R ν reg x n ω / (2 * (σ2 : ℝ)))) *
        ∫ lambda, completedSquareGaussianKernel A R ν reg σ2 x n ω lambda := by
        rw [← integral_const_mul]
        congr 1
        ext lambda
        ring
    _ =
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        Real.exp (centeredNoiseQuadraticForm A R ν reg x n ω / (2 * (σ2 : ℝ))) *
          ∫ lambda, completedSquareGaussianKernel A R ν reg σ2 x n ω lambda := by
        ring

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Pointwise Gaussian-prior identity from the remaining translated-kernel determinant integral.

The hypothesis is exactly the scalar determinant-normalizer evaluation left after the completed
square: the Gaussian prior normalizer times the translated kernel integral must equal
`1 / sqrt(detRatio)`. Under that hypothesis, the concrete Gaussian-prior integral is the textbook
mixture statistic. -/
lemma textbookMixtureStatistic_eq_gaussianPriorIntegral_of_kernel_integral
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ))
    (h_kernel :
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
          (∫ lambda, completedSquareGaussianKernel A R ν reg σ2 x n ω lambda) =
        1 / √(designDetRatio A reg x n ω)) :
    textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν n ω =
      ∫ lambda,
        gaussianDirectionDensity d reg σ2 lambda *
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda) := by
  rw [integral_gaussianPriorIntegrand_eq_completedSquare_of_pos
    (A := A) (R := R) (ν := ν) (reg := reg) (x := x) (n := n) (ω := ω)
    hreg_pos hσ2_pos]
  unfold textbookSelfNormalizedMixtureStatistic
  calc
    Real.exp (centeredNoiseQuadraticForm A R ν reg x n ω / (2 * (σ2 : ℝ))) /
        √(designDetRatio A reg x n ω)
        =
      Real.exp (centeredNoiseQuadraticForm A R ν reg x n ω / (2 * (σ2 : ℝ))) *
        (1 / √(designDetRatio A reg x n ω)) := by
        ring
    _ =
      Real.exp (centeredNoiseQuadraticForm A R ν reg x n ω / (2 * (σ2 : ℝ))) *
        (Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
          ∫ lambda, completedSquareGaussianKernel A R ν reg σ2 x n ω lambda) := by
        rw [h_kernel]
    _ =
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
        Real.exp (centeredNoiseQuadraticForm A R ν reg x n ω / (2 * (σ2 : ℝ))) *
          ∫ lambda, completedSquareGaussianKernel A R ν reg σ2 x n ω lambda := by
        ring

/-- The remaining analytic input expected from the textbook Gaussian method of mixtures.

For a concrete Gaussian direction measure `μlambda`, the missing multivariate Gaussian theorem
should prove this predicate. The first field is the pointwise determinant-ratio mixture identity;
the second field is the global product-integrability needed by Fubini and optional-stopping
bookkeeping. Everything after this predicate is already deterministic/probabilistic plumbing. -/
structure TextbookGaussianMixtureInput
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (ν : Kernel (Fin K) ℝ) (reg : ℝ) (σ2 : ℝ≥0)
    (x : Fin K → Feature d) (P : Measure Ω)
    (μlambda : Measure (Feature d)) : Prop where
  pointwise : ∀ i,
    (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω) =ᵐ[P]
      fun ω ↦
        ∫ lambda,
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda)
        ∂μlambda
  globalProdIntegrable : ∀ i,
    Integrable
      (Function.uncurry fun ω lambda ↦
        Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
      (P.prod μlambda)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Concrete-prior form of the remaining textbook Gaussian-mixture input.

Unlike `TextbookGaussianMixtureInput`, this no longer quantifies over an arbitrary direction
measure. The pointwise field asks for exactly the Gaussian integral identity obtained after
multiplying the fixed-direction exponential process by the isotropic Gaussian prior density. -/
structure TextbookGaussianPriorInput
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (ν : Kernel (Fin K) ℝ) (reg : ℝ) (σ2 : ℝ≥0)
    (x : Fin K → Feature d) (P : Measure Ω) : Prop where
  pointwiseVolume : ∀ i,
    (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω) =ᵐ[P]
      fun ω ↦
        ∫ lambda,
          gaussianDirectionDensity d reg σ2 lambda *
            Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda)
  globalProdIntegrable : ∀ i,
    Integrable
      (Function.uncurry fun ω lambda ↦
        Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
      (P.prod (gaussianDirectionMeasure d reg σ2))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Build the concrete Gaussian-prior input from the remaining translated-kernel determinant
integral.

This is the narrowed interface for the missing analytic theorem. Instead of asking for the original
pointwise Gaussian-prior integral identity, it asks for the post-completion scalar identity
`normalizer * ∫ completedSquareGaussianKernel = 1 / sqrt(detRatio)` at each time. -/
lemma textbookGaussianPriorInput_of_kernelIntegral
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ))
    (h_kernel : ∀ i, ∀ᵐ ω ∂P,
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
          (∫ lambda, completedSquareGaussianKernel A R ν reg σ2 x i ω lambda) =
        1 / √(designDetRatio A reg x i ω))
    (h_prod : ∀ i,
      Integrable
        (Function.uncurry fun ω lambda ↦
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
        (P.prod (gaussianDirectionMeasure d reg σ2))) :
    TextbookGaussianPriorInput A R ν reg σ2 x P where
  pointwiseVolume := by
    intro i
    filter_upwards [h_kernel i] with ω hω
    exact textbookMixtureStatistic_eq_gaussianPriorIntegral_of_kernel_integral
      (A := A) (R := R) (ν := ν) (reg := reg) (x := x) (n := i) (ω := ω)
      hreg_pos hσ2_pos hω
  globalProdIntegrable := h_prod

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Build the concrete Gaussian-prior input from the unshifted anisotropic Gaussian determinant
integral.

This is one step closer to the textbook theorem than `textbookGaussianPriorInput_of_kernelIntegral`:
the random completed-square shift has already been removed by translation invariance of Lebesgue
measure. The remaining pointwise obligation is the standard positive-definite Gaussian integral. -/
lemma textbookGaussianPriorInput_of_anisotropicKernelIntegral
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ))
    (h_kernel : ∀ i, ∀ᵐ ω ∂P,
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
          (∫ lambda, anisotropicGaussianKernel A reg σ2 x i ω lambda) =
        1 / √(designDetRatio A reg x i ω))
    (h_prod : ∀ i,
      Integrable
        (Function.uncurry fun ω lambda ↦
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
        (P.prod (gaussianDirectionMeasure d reg σ2))) :
    TextbookGaussianPriorInput A R ν reg σ2 x P :=
  textbookGaussianPriorInput_of_kernelIntegral
    (A := A) (R := R) (ν := ν) (reg := reg) (x := x) (P := P)
    hreg_pos hσ2_pos
    (fun i ↦ by
      filter_upwards [h_kernel i] with ω hω
      rw [integral_completedSquareGaussianKernel_eq_integral_anisotropicGaussianKernel
        (A := A) (R := R) (ν := ν) (reg := reg) (x := x) (n := i) (ω := ω)
        σ2]
      exact hω)
    h_prod

omit [IsMarkovKernel ν] in
/-- Build the concrete Gaussian-prior input when the unshifted anisotropic determinant integral is
proved only for positive times.

The time-zero determinant-integral identity is proved by
`anisotropicKernelIntegral_zero_eq_inv_sqrt_designDetRatio`, and the time-zero product-integrability
case is just integrability of the constant `1` under a finite product measure. Future analytic work
only has to handle the nonzero design matrices generated after at least one update. -/
lemma textbookGaussianPriorInput_of_anisotropicKernelIntegral_posTime
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ))
    (h_kernel_pos : ∀ i, i ≠ 0 → ∀ᵐ ω ∂P,
      Real.rpow ((σ2 : ℝ) * reg / (2 * Real.pi)) ((d : ℝ) / 2) *
          (∫ lambda, anisotropicGaussianKernel A reg σ2 x i ω lambda) =
        1 / √(designDetRatio A reg x i ω))
    (h_prod_pos : ∀ i, i ≠ 0 →
      Integrable
        (Function.uncurry fun ω lambda ↦
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
        (P.prod (gaussianDirectionMeasure d reg σ2))) :
    TextbookGaussianPriorInput A R ν reg σ2 x P :=
  textbookGaussianPriorInput_of_anisotropicKernelIntegral
    (A := A) (R := R) (ν := ν) (reg := reg) (x := x) (P := P)
    hreg_pos hσ2_pos
    (fun i ↦ by
      by_cases hi : i = 0
      · subst i
        exact Filter.Eventually.of_forall fun ω ↦
          anisotropicKernelIntegral_zero_eq_inv_sqrt_designDetRatio
            (A := A) (reg := reg) (x := x) (ω := ω) hreg_pos hσ2_pos
      · exact h_kernel_pos i hi)
    (fun i ↦ by
      by_cases hi : i = 0
      · subst i
        exact integrable_exp_centeredResponseDirectionalExponent_zero_gaussianDirectionMeasure
          (A := A) (R := R) (ν := ν) (reg := reg) (x := x) (P := P)
          hreg_pos hσ2_pos
      · exact h_prod_pos i hi)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Build the concrete Gaussian-prior input from the spectral determinant integral.

The anisotropic Gaussian determinant identity is now supplied by
`anisotropicKernelIntegral_eq_inv_sqrt_designDetRatio_of_designEigenvectors`, so the only remaining
analytic input is product-integrability of the fixed-direction exponential process under the
concrete Gaussian direction measure. -/
lemma textbookGaussianPriorInput_of_designEigenvectorIntegral
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ))
    (h_prod : ∀ i,
      Integrable
        (Function.uncurry fun ω lambda ↦
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
        (P.prod (gaussianDirectionMeasure d reg σ2))) :
    TextbookGaussianPriorInput A R ν reg σ2 x P :=
  textbookGaussianPriorInput_of_anisotropicKernelIntegral
    (A := A) (R := R) (ν := ν) (reg := reg) (x := x) (P := P)
    hreg_pos hσ2_pos
    (fun i ↦ Filter.Eventually.of_forall fun ω ↦
      anisotropicKernelIntegral_eq_inv_sqrt_designDetRatio_of_designEigenvectors
        (A := A) (reg := reg) (x := x) (n := i) (ω := ω) hreg_pos hσ2_pos)
    h_prod

omit [IsMarkovKernel ν] in
/-- Positive-time integrability interface for the concrete Gaussian-prior input.

Time zero is handled by the existing constant-integrability lemma. For all positive times, future
work only has to prove product-integrability of the fixed-direction exponential process; the
spectral determinant integral is already discharged for every time. -/
lemma textbookGaussianPriorInput_of_designEigenvectorIntegral_posTime
    {σ2 : ℝ≥0} (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ))
    (h_prod_pos : ∀ i, i ≠ 0 →
      Integrable
        (Function.uncurry fun ω lambda ↦
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
        (P.prod (gaussianDirectionMeasure d reg σ2))) :
    TextbookGaussianPriorInput A R ν reg σ2 x P :=
  textbookGaussianPriorInput_of_designEigenvectorIntegral
    (A := A) (R := R) (ν := ν) (reg := reg) (x := x) (P := P)
    hreg_pos hσ2_pos
    (fun i ↦ by
      by_cases hi : i = 0
      · subst i
        exact integrable_exp_centeredResponseDirectionalExponent_zero_gaussianDirectionMeasure
          (A := A) (R := R) (ν := ν) (reg := reg) (x := x) (P := P)
          hreg_pos hσ2_pos
      · exact h_prod_pos i hi)

/-- Concrete Gaussian-prior input from the fixed-direction exponential supermartingale and the
spectral determinant integral.

This discharges both analytic hypotheses previously exposed by
`textbookGaussianPriorInput_of_anisotropicKernelIntegral_posTime`: the determinant integral follows
from unitary diagonalization of the design matrix, and product-integrability follows from the
fixed-direction expectation bound plus finiteness of the Gaussian direction measure. -/
lemma textbookGaussianPriorInput_of_designEigenvectorIntegral_supermartingale
    [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (hreg_pos : 0 < reg) (hσ2_pos : 0 < (σ2 : ℝ)) :
    TextbookGaussianPriorInput A R ν reg σ2 x P :=
  textbookGaussianPriorInput_of_designEigenvectorIntegral
    (A := A) (R := R) (ν := ν) (reg := reg) (x := x) (P := P)
    hreg_pos hσ2_pos
    (fun i ↦
      integrable_exp_centeredResponseDirectionalExponent_gaussianDirectionMeasure
        (A := A) (R := R) (ν := ν) (reg := reg) (β := β) (x := x) (P := P)
        h hν hreg_pos hσ2_pos i)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The concrete Gaussian-prior input implies the abstract mixture input consumed by the existing
supermartingale and regret bridges. -/
lemma TextbookGaussianPriorInput.toMixtureInput
    {σ2 : ℝ≥0}
    (h_prior : TextbookGaussianPriorInput A R ν reg σ2 x P) :
    TextbookGaussianMixtureInput A R ν reg σ2 x P (gaussianDirectionMeasure d reg σ2) where
  pointwise := by
    intro i
    filter_upwards [h_prior.pointwiseVolume i] with ω hω
    rw [hω]
    exact (integral_gaussianDirectionMeasure_eq_integral_density_mul d reg σ2
      (fun lambda ↦
        Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))).symm
  globalProdIntegrable := h_prior.globalProdIntegrable

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Product-integrability implies integrability of the closed-form textbook mixture statistic once
the pointwise Gaussian-mixture identity is known.

This is a standard Fubini bookkeeping step: product-integrability gives integrability of the
direction-integral as a function of the sample path, and the pointwise identity transfers that
integrability to the determinant-ratio statistic. -/
lemma textbookMixtureStatistic_integrable_of_pointwise_prod_integrable
    {σ2 : ℝ≥0} (μlambda : Measure (Feature d)) [SFinite μlambda]
    (h_pointwise : ∀ i,
      (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω) =ᵐ[P]
        fun ω ↦
          ∫ lambda,
            Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda)
          ∂μlambda)
    (h_prod_int : ∀ i, ∀ s : Set Ω, MeasurableSet s →
      Integrable
        (Function.uncurry fun ω lambda ↦
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
        ((P.restrict s).prod μlambda)) :
    ∀ i,
      Integrable (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω) P := by
  intro i
  have h_integral :
      Integrable
        (fun ω ↦
          ∫ lambda,
            Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda)
          ∂μlambda) P := by
    simpa using (h_prod_int i Set.univ MeasurableSet.univ).integral_prod_left
  exact h_integral.congr (h_pointwise i).symm

omit [IsMarkovKernel ν] in
/-- Product-integrability gives the integrability of the direction-indexed set integrals needed
for monotonicity of the integrated fixed-direction supermartingales. -/
lemma directionalMixture_inner_integrable_of_prod_integrable
    {σ2 : ℝ≥0} (μlambda : Measure (Feature d)) [SFinite μlambda]
    (h_prod_int : ∀ i, ∀ s : Set Ω, MeasurableSet s →
      Integrable
        (Function.uncurry fun ω lambda ↦
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
        ((P.restrict s).prod μlambda)) :
    ∀ i, ∀ s : Set Ω, MeasurableSet s →
      Integrable
        (fun lambda ↦
          ∫ ω in s,
            Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda) ∂P)
        μlambda := by
  intro i s hs
  simpa using (h_prod_int i s hs).integral_prod_right

omit [IsMarkovKernel ν] in
/-- Product-integrability supplies the Fubini/Tonelli swap used to turn the pointwise
Gaussian-mixture identity into the set-integral identity. -/
lemma directionalMixture_fubini_of_prod_integrable
    {σ2 : ℝ≥0} (μlambda : Measure (Feature d)) [SFinite μlambda]
    (h_prod_int : ∀ i, ∀ s : Set Ω, MeasurableSet s →
      Integrable
        (Function.uncurry fun ω lambda ↦
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
        ((P.restrict s).prod μlambda)) :
    ∀ i, ∀ s : Set Ω, MeasurableSet s →
      (∫ ω in s,
        (∫ lambda,
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda)
        ∂μlambda) ∂P) =
        ∫ lambda,
          (∫ ω in s,
            Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda) ∂P)
          ∂μlambda := by
  intro i s hs
  simpa using
    (integral_integral_swap
      (μ := P.restrict s) (ν := μlambda)
      (f := fun ω lambda ↦
        Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
      (h_prod_int i s hs))

omit [IsMarkovKernel ν] in
/-- Global product-integrability implies the restricted product-integrability needed on every
filtration event.

This removes a quantifier-heavy assumption from later theorem statements. The reason is purely
measure-theoretic: `(P.restrict s).prod μlambda` is the restriction of `P.prod μlambda` to
`s ×ˢ univ`, hence it is bounded by `P.prod μlambda`; integrability is monotone under smaller
measures. -/
lemma directionalMixture_prod_integrable_of_global_prod_integrable
    {σ2 : ℝ≥0} (μlambda : Measure (Feature d)) [SFinite μlambda]
    (h_prod_int : ∀ i,
      Integrable
        (Function.uncurry fun ω lambda ↦
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
        (P.prod μlambda)) :
    ∀ i, ∀ s : Set Ω,
      Integrable
        (Function.uncurry fun ω lambda ↦
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
        ((P.restrict s).prod μlambda) := by
  intro i s
  refine (h_prod_int i).mono_measure ?_
  rw [Measure.restrict_prod_eq_prod_univ]
  exact Measure.restrict_le_self

/-- Assemble the textbook Gaussian-mixture statistic from fixed-direction exponential
supermartingales plus the pointwise Gaussian-mixture identity.

Compared with
`supermartingale_textbookSelfNormalizedMixtureStatistic_filtrationAction_of_directionalMixture`,
this exposes the obligations in the order used by the textbook proof: first prove the pointwise
Gaussian integral formula for the determinant-ratio statistic, then justify the Fubini/Tonelli swap
needed to integrate that identity over arbitrary filtration events. -/
lemma supermartingale_textbookMixtureStatistic_of_directionalMixture_pointwise
    [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (μlambda : Measure (Feature d))
    (h_int_stat : ∀ i,
      Integrable (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω) P)
    (h_inner_int : ∀ i, ∀ s : Set Ω, MeasurableSet s →
      Integrable
        (fun lambda ↦
          ∫ ω in s,
            Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda) ∂P)
        μlambda)
    (h_pointwise : ∀ i,
      (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω) =ᵐ[P]
        fun ω ↦
          ∫ lambda,
            Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda)
          ∂μlambda)
    (h_fubini : ∀ i, ∀ s : Set Ω, MeasurableSet s →
      (∫ ω in s,
        (∫ lambda,
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda)
        ∂μlambda) ∂P) =
        ∫ lambda,
          (∫ ω in s,
            Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda) ∂P)
          ∂μlambda) :
    Supermartingale
      (fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω)
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) P := by
  exact
    supermartingale_textbookSelfNormalizedMixtureStatistic_filtrationAction_of_directionalMixture
      (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
      h hν μlambda h_int_stat h_inner_int
      (textbookSelfNormalizedMixtureStatistic_setIntegral_eq_integral_of_ae_eq_integral
        (A := A) (R := R) (reg := reg) (σ2 := σ2) (x := x) (ν := ν) (P := P)
        μlambda h_pointwise h_fubini)

/-- Assemble the textbook Gaussian-mixture statistic from fixed-direction exponential
supermartingales plus the pointwise Gaussian-mixture identity and product-integrability.

This is the closest current interface to the textbook method-of-mixtures proof: after proving the
pointwise Gaussian integral formula, the remaining measure-theoretic input is a single
product-integrability condition strong enough to provide both Fubini and the integrability fields
required by the supermartingale API. -/
lemma supermartingale_textbookMixtureStatistic_of_directionalMixture_prod_integrable
    [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (μlambda : Measure (Feature d)) [SFinite μlambda]
    (h_pointwise : ∀ i,
      (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν i ω) =ᵐ[P]
        fun ω ↦
          ∫ lambda,
            Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda)
          ∂μlambda)
    (h_prod_int : ∀ i, ∀ s : Set Ω, MeasurableSet s →
      Integrable
        (Function.uncurry fun ω lambda ↦
          Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x i ω lambda))
        ((P.restrict s).prod μlambda)) :
    Supermartingale
      (fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω)
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) P := by
  exact supermartingale_textbookMixtureStatistic_of_directionalMixture_pointwise
    (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
    h hν μlambda
    (textbookMixtureStatistic_integrable_of_pointwise_prod_integrable
      (A := A) (R := R) (reg := reg) (σ2 := σ2) (x := x) (ν := ν) (P := P)
      μlambda h_pointwise h_prod_int)
    (directionalMixture_inner_integrable_of_prod_integrable
      (A := A) (R := R) (reg := reg) (σ2 := σ2) (x := x) (ν := ν) (P := P)
      μlambda h_prod_int)
    h_pointwise
    (directionalMixture_fubini_of_prod_integrable
      (A := A) (R := R) (reg := reg) (σ2 := σ2) (x := x) (ν := ν) (P := P)
      μlambda h_prod_int)

/-- Assemble the textbook Gaussian-mixture statistic from fixed-direction exponential
supermartingales plus pointwise Gaussian mixture and global product-integrability.

This is the lightest current version of
`supermartingale_textbookMixtureStatistic_of_directionalMixture_prod_integrable`: the caller only
has to supply the named analytic Gaussian-mixture input. -/
lemma supermartingale_textbookMixtureStatistic_of_directionalMixture_global_prod_integrable
    [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (μlambda : Measure (Feature d)) [SFinite μlambda]
    (h_mix : TextbookGaussianMixtureInput A R ν reg σ2 x P μlambda) :
    Supermartingale
      (fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω)
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) P := by
  exact supermartingale_textbookMixtureStatistic_of_directionalMixture_prod_integrable
    (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
    h hν μlambda h_mix.pointwise
    (fun i s _hs ↦
      directionalMixture_prod_integrable_of_global_prod_integrable
        (A := A) (R := R) (reg := reg) (σ2 := σ2) (x := x) (ν := ν) (P := P)
        μlambda h_mix.globalProdIntegrable i s)

/-- Assemble the textbook Gaussian-mixture statistic from the concrete Gaussian-prior input.

This is the supermartingale-layer interface closest to the textbook method-of-mixtures proof: the
caller supplies the concrete Gaussian-prior identity/integrability package, and the abstract
direction-measure bridge is handled internally. -/
lemma supermartingale_textbookMixtureStatistic_of_textbookGaussianPriorInput
    [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (h_prior : TextbookGaussianPriorInput A R ν reg σ2 x P) :
    Supermartingale
      (fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω)
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) P := by
  exact supermartingale_textbookMixtureStatistic_of_directionalMixture_global_prod_integrable
    (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
    h hν (gaussianDirectionMeasure d reg σ2)
    (TextbookGaussianPriorInput.toMixtureInput (A := A) (R := R) (reg := reg)
      (σ2 := σ2) (x := x) (ν := ν) (P := P) h_prior)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- At time zero, the textbook Gaussian-mixture statistic is one under positive regularization. -/
lemma textbookSelfNormalizedMixtureStatistic_zero_of_reg_pos
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (ω : Ω) (hreg_pos : 0 < reg) :
    textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν 0 ω = 1 := by
  have hdet : designDet A reg x 0 ω ≠ 0 :=
    designDet_zero_ne_zero_of_reg_ne_zero (A := A) (reg := reg) (x := x)
      (ω := ω) hreg_pos.ne'
  simp [textbookSelfNormalizedMixtureStatistic, centeredNoiseQuadraticForm,
    centeredResponseVector_zero (A := A) (R := R) (ν := ν) (x := x) (ω := ω),
    designDetRatio_zero (A := A) (reg := reg) (x := x) (ω := ω) hdet]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Failure of the horizon-local mixture event is exactly a positive-time crossing of the
threshold `1 / δ`. -/
lemma not_LinUCBTextbookMixtureBoundEventUpTo_iff
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (δ : ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) (ω : Ω) :
    ¬ LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω ↔
      ∃ t, t ∈ range n ∧ t ≠ 0 ∧
        1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω := by
  classical
  simp [LinUCBTextbookMixtureBoundEventUpTo, not_le]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Measurability of one fixed-time textbook mixture-statistic crossing event. -/
lemma measurableSet_textbookMixtureStatistic_crossing
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n t : ℕ}
    (hstat :
      Measurable fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω) :
    MeasurableSet {ω | t ∈ range n ∧ t ≠ 0 ∧
      1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω} := by
  by_cases ht : t ∈ range n ∧ t ≠ 0
  · simpa [ht] using (measurableSet_lt measurable_const hstat)
  · have hempty :
        {ω : Ω | t ∈ range n ∧ t ≠ 0 ∧
          1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω} = ∅ := by
      ext ω
      constructor
      · intro hω
        exact False.elim (ht ⟨hω.1, hω.2.1⟩)
      · intro hω
        exact False.elim hω
    rw [hempty]
    exact MeasurableSet.empty

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If every fixed-time mixture statistic in the finite horizon is measurable, then the failure
set of the horizon-local mixture event is measurable. -/
lemma measurableSet_not_LinUCBTextbookMixtureBoundEventUpTo
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ}
    (hstat : ∀ t, t ∈ range n →
      Measurable fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω) :
    MeasurableSet {ω | ¬ LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω} := by
  classical
  let E : ℕ → Set Ω := fun t ↦
    {ω | t ∈ range n ∧ t ≠ 0 ∧
      1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω}
  have hset :
      {ω | ¬ LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω} =
        ⋃ t ∈ (range n : Finset ℕ), E t := by
    ext ω
    constructor
    · intro hfail
      rcases (not_LinUCBTextbookMixtureBoundEventUpTo_iff
        (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
        (ν := ν) (n := n) (ω := ω)).mp hfail with ⟨t, ht, ht0, hlt⟩
      refine Set.mem_iUnion.2 ⟨t, ?_⟩
      refine Set.mem_iUnion.2 ⟨ht, ?_⟩
      exact ⟨ht, ht0, hlt⟩
    · intro hmem
      rcases Set.mem_iUnion.1 hmem with ⟨t, hmemt⟩
      rcases Set.mem_iUnion.1 hmemt with ⟨ht, hEt⟩
      exact (not_LinUCBTextbookMixtureBoundEventUpTo_iff
        (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
        (ν := ν) (n := n) (ω := ω)).mpr ⟨t, ht, hEt.2.1, hEt.2.2⟩
  rw [hset]
  exact Finset.measurableSet_biUnion (range n) fun t ht ↦
    measurableSet_textbookMixtureStatistic_crossing
      (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
      (ν := ν) (n := n) (t := t) (hstat t ht)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The horizon-local textbook mixture-event failure set is measurable when actions and rewards are
measurable. -/
lemma measurableSet_not_LinUCBTextbookMixtureBoundEventUpTo_of_process
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ}
    (hA : ∀ t, Measurable (A t)) (hR : ∀ t, Measurable (R t)) :
    MeasurableSet {ω | ¬ LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω} := by
  exact measurableSet_not_LinUCBTextbookMixtureBoundEventUpTo
    (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x) (ν := ν)
    (n := n)
    (fun t _ht ↦ measurable_textbookSelfNormalizedMixtureStatistic
      (A := A) (R := R) hA hR reg σ2 x ν t)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- First positive time before `n` at which the textbook Gaussian-mixture statistic crosses
`1 / δ`.

If no crossing occurs, this value is defined to be `0`. This is the stopping-time-shaped object
needed by the textbook Ville/mixture proof. -/
noncomputable def firstTextbookMixtureFailureTime
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (δ : ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) (ω : Ω) : ℕ :=
  if h : ∃ t, t ∈ range n ∧ t ≠ 0 ∧
      1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω then
    Nat.find h
  else
    0

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If the mixture event fails, the first failure time is a positive time in the horizon and the
mixture statistic crosses `1 / δ` there. -/
lemma firstTextbookMixtureFailureTime_spec
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ} {ω : Ω}
    (hfail : ¬ LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω) :
    firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω ∈ range n ∧
      firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω ≠ 0 ∧
        1 / δ <
          textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν
            (firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω) ω := by
  classical
  have hcross :
      ∃ t, t ∈ range n ∧ t ≠ 0 ∧
        1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω :=
    (not_LinUCBTextbookMixtureBoundEventUpTo_iff
      (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
      (ν := ν) (n := n) (ω := ω)).mp hfail
  unfold firstTextbookMixtureFailureTime
  rw [dif_pos hcross]
  exact Nat.find_spec hcross

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Before the first mixture failure time, no positive-time threshold crossing has occurred. -/
lemma not_textbookMixture_crossing_before_firstFailureTime
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n s : ℕ} {ω : Ω}
    (hfail : ¬ LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω)
    (hs : s < firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω) :
    ¬ (s ∈ range n ∧ s ≠ 0 ∧
      1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν s ω) := by
  classical
  have hcross :
      ∃ t, t ∈ range n ∧ t ≠ 0 ∧
        1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω :=
    (not_LinUCBTextbookMixtureBoundEventUpTo_iff
      (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
      (ν := ν) (n := n) (ω := ω)).mp hfail
  unfold firstTextbookMixtureFailureTime at hs
  rw [dif_pos hcross] at hs
  exact Nat.find_min hcross hs

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Characterization of the first mixture failure time by threshold crossing at that time and no
earlier crossing. -/
lemma firstTextbookMixtureFailureTime_eq_iff_of_mixture_failure
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n t : ℕ} {ω : Ω}
    (hfail : ¬ LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω) :
    firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω = t ↔
      (t ∈ range n ∧ t ≠ 0 ∧
        1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω) ∧
        ∀ s, s < t →
          ¬ (s ∈ range n ∧ s ≠ 0 ∧
            1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν s ω) := by
  classical
  have hcross :
      ∃ s, s ∈ range n ∧ s ≠ 0 ∧
        1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν s ω :=
    (not_LinUCBTextbookMixtureBoundEventUpTo_iff
      (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
      (ν := ν) (n := n) (ω := ω)).mp hfail
  unfold firstTextbookMixtureFailureTime
  rw [dif_pos hcross]
  simpa using
    (Nat.find_eq_iff
      (p := fun s ↦ s ∈ range n ∧ s ≠ 0 ∧
        1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν s ω)
      (m := t) hcross)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If the mixture event holds, the chosen fallback value for the first failure time is `0`. -/
lemma firstTextbookMixtureFailureTime_eq_zero_of_mixtureBound
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ} {ω : Ω}
    (hmix : LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω) :
    firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω = 0 := by
  classical
  have hnot :
      ¬ ∃ t, t ∈ range n ∧ t ≠ 0 ∧
        1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω := by
    rintro ⟨t, ht, ht0, hlt⟩
    exact (not_lt_of_ge (hmix t ht ht0)) hlt
  unfold firstTextbookMixtureFailureTime
  rw [dif_neg hnot]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Optional-stopping-friendly first crossing time for the textbook Gaussian-mixture statistic.

This agrees with the first positive threshold crossing before `n` when such a crossing exists, and
otherwise stops at the deterministic horizon `n`. The fallback value `n` makes the stopping-time
proof match the usual textbook argument. -/
noncomputable def boundedTextbookMixtureFailureTime
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (δ : ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) (ω : Ω) : ℕ :=
  if h : ∃ t, t ∈ range n ∧ t ≠ 0 ∧
      1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω then
    Nat.find h
  else
    n

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If the horizon-local mixture event fails, the bounded first crossing time is a positive
crossing time before the horizon. -/
lemma boundedTextbookMixtureFailureTime_spec
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ} {ω : Ω}
    (hfail : ¬ LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω) :
    boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω ∈ range n ∧
      boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω ≠ 0 ∧
        1 / δ <
          textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν
            (boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω) ω := by
  classical
  have hcross :
      ∃ t, t ∈ range n ∧ t ≠ 0 ∧
        1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω :=
    (not_LinUCBTextbookMixtureBoundEventUpTo_iff
      (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
      (ν := ν) (n := n) (ω := ω)).mp hfail
  unfold boundedTextbookMixtureFailureTime
  rw [dif_pos hcross]
  exact Nat.find_spec hcross

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The bounded textbook mixture failure time is always bounded by the horizon. -/
lemma boundedTextbookMixtureFailureTime_le
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ} {ω : Ω} :
    boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω ≤ n := by
  classical
  by_cases hcross :
      ∃ t, t ∈ range n ∧ t ≠ 0 ∧
        1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω
  · unfold boundedTextbookMixtureFailureTime
    rw [dif_pos hcross]
    exact Nat.le_of_lt (mem_range.mp (Nat.find_spec hcross).1)
  · unfold boundedTextbookMixtureFailureTime
    rw [dif_neg hcross]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The bounded first-crossing time is a stopping time for any filtration to which the textbook
mixture statistic is strongly adapted. -/
lemma isStoppingTime_boundedTextbookMixtureFailureTime
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ} {ℱ : Filtration ℕ mΩ}
    (hstat :
      StronglyAdapted ℱ
        (fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω)) :
    IsStoppingTime ℱ
      (fun ω ↦ (boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞)) := by
  classical
  intro i
  change MeasurableSet[ℱ i]
    {ω | (boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞) ≤ (i : ℕ∞)}
  by_cases hni : n ≤ i
  · have h_univ :
        {ω |
          (boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞) ≤ i} =
          Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact_mod_cast (boundedTextbookMixtureFailureTime_le
        (K := K) (d := d) (A := A) (R := R) (reg := reg) (σ2 := σ2)
        (δ := δ) (x := x) (ν := ν) (n := n) (ω := ω)).trans hni
    rw [h_univ]
    exact MeasurableSet.univ
  · have hi_lt_n : i < n := Nat.lt_of_not_ge hni
    let C : ℕ → Set Ω := fun t ↦
      {ω | t ≠ 0 ∧
        1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω}
    have hC_meas : ∀ t, t ∈ range (i + 1) → MeasurableSet[ℱ i] (C t) := by
      intro t ht
      by_cases ht0 : t = 0
      · have hempty : C t = ∅ := by
          ext ω
          simp [C, ht0]
        rw [hempty]
        exact (@MeasurableSet.empty Ω (ℱ i))
      · have hti : t ≤ i := Nat.le_of_lt_succ (mem_range.mp ht)
        have hstrong :
            StronglyMeasurable[ℱ i]
              (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω) :=
          hstat.stronglyMeasurable_le hti
        have hcross :
            MeasurableSet[ℱ i]
              {ω | 1 / δ <
                textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω} :=
          measurableSet_lt
            (@measurable_const ℝ Ω _ (ℱ i) (1 / δ))
            hstrong.measurable
        have hCeq :
            C t =
              {ω | 1 / δ <
                textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω} := by
          ext ω
          simp [C, ht0]
        rw [hCeq]
        exact hcross
    have h_eq :
        {ω |
          (boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞) ≤ i} =
          ⋃ t ∈ (range (i + 1) : Finset ℕ), C t := by
      ext ω
      constructor
      · intro hω
        simp only [Set.mem_setOf_eq] at hω
        by_cases hcross :
            ∃ t, t ∈ range n ∧ t ≠ 0 ∧
              1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω
        · unfold boundedTextbookMixtureFailureTime at hω
          rw [dif_pos hcross] at hω
          have hfind_le_i : Nat.find hcross ≤ i := by
            exact_mod_cast hω
          refine Set.mem_iUnion.2 ⟨Nat.find hcross, ?_⟩
          refine Set.mem_iUnion.2 ⟨mem_range.mpr (Nat.lt_succ_of_le hfind_le_i), ?_⟩
          exact ⟨(Nat.find_spec hcross).2.1, (Nat.find_spec hcross).2.2⟩
        · unfold boundedTextbookMixtureFailureTime at hω
          rw [dif_neg hcross] at hω
          have hn_le_i : n ≤ i := by
            exact_mod_cast hω
          exact False.elim (hni hn_le_i)
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨t, hωt⟩
        rcases Set.mem_iUnion.1 hωt with ⟨ht, hCt⟩
        have hti : t ≤ i := Nat.le_of_lt_succ (mem_range.mp ht)
        have htn : t ∈ range n := mem_range.mpr (lt_of_le_of_lt hti hi_lt_n)
        have hcross :
            ∃ s, s ∈ range n ∧ s ≠ 0 ∧
              1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν s ω :=
          ⟨t, htn, hCt.1, hCt.2⟩
        unfold boundedTextbookMixtureFailureTime
        simp only [Set.mem_setOf_eq]
        rw [dif_pos hcross]
        have hfind_le_t :
            Nat.find hcross ≤ t :=
          Nat.find_min' hcross ⟨htn, hCt.1, hCt.2⟩
        exact_mod_cast hfind_le_t.trans hti
    rw [h_eq]
    exact Finset.measurableSet_biUnion (range (i + 1)) hC_meas

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Textbook mixture statistic stopped at the optional-stopping-friendly bounded first crossing
time. -/
noncomputable def boundedStoppedTextbookMixtureStatistic
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (δ : ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν
    (boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω) ω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- On mixture-event failure, the bounded stopped statistic is strictly above `1 / δ`. -/
lemma inv_delta_lt_boundedStoppedTextbookMixtureStatistic_of_mixture_failure
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ} {ω : Ω}
    (hfail : ¬ LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω) :
    1 / δ < boundedStoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω := by
  have hspec := boundedTextbookMixtureFailureTime_spec (K := K) (d := d) hfail
  simpa [boundedStoppedTextbookMixtureStatistic] using hspec.2.2

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The bounded stopped mixture statistic is mathlib's stopped value for the bounded first
crossing time. -/
lemma boundedStoppedTextbookMixtureStatistic_eq_stoppedValue
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (δ : ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) :
    (fun ω ↦ boundedStoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω) =
      stoppedValue
        (fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω)
        (fun ω ↦ (boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞)) := by
  rfl

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The bounded stopped textbook Gaussian-mixture statistic is pointwise nonnegative. -/
lemma boundedStoppedTextbookMixtureStatistic_nonneg
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (δ : ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ boundedStoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω :=
  textbookSelfNormalizedMixtureStatistic_nonneg (A := A) (R := R) (reg := reg)
    (σ2 := σ2) (x := x) (ν := ν)
    (n := boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω) (ω := ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The textbook mixture statistic stopped at the first positive threshold crossing before `n`.

This is the random variable whose expectation has to be bounded by one in the remaining
Gaussian-mixture/Ville step. -/
noncomputable def stoppedTextbookMixtureStatistic
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (δ : ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν
    (firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω) ω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The stopped textbook Gaussian-mixture statistic is pointwise nonnegative. -/
lemma stoppedTextbookMixtureStatistic_nonneg
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (δ : ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ stoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω :=
  textbookSelfNormalizedMixtureStatistic_nonneg (A := A) (R := R) (reg := reg)
    (σ2 := σ2) (x := x) (ν := ν)
    (n := firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω) (ω := ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- On mixture-event failure, the stopped statistic is strictly above `1 / δ`. -/
lemma inv_delta_lt_stoppedTextbookMixtureStatistic_of_mixture_failure
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ} {ω : Ω}
    (hfail : ¬ LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω) :
    1 / δ < stoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω := by
  have hspec := firstTextbookMixtureFailureTime_spec (K := K) (d := d) hfail
  simpa [stoppedTextbookMixtureStatistic] using hspec.2.2

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The first mixture failure time is always bounded by the horizon. -/
lemma firstTextbookMixtureFailureTime_le
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ} {ω : Ω} :
    firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω ≤ n := by
  classical
  by_cases hmix : LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω
  · rw [firstTextbookMixtureFailureTime_eq_zero_of_mixtureBound (K := K) (d := d) hmix]
    exact Nat.zero_le n
  · have hspec :=
      firstTextbookMixtureFailureTime_spec (K := K) (d := d)
        (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
        (ν := ν) (n := n) (ω := ω) hmix
    exact Nat.le_of_lt (by simpa using hspec.1)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The event that the first textbook mixture failure time equals a fixed time is measurable, as
soon as the finitely many fixed-time mixture statistics in the horizon are measurable. -/
lemma measurableSet_firstTextbookMixtureFailureTime_eq
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ}
    (hstat : ∀ s, s ∈ range n →
      Measurable fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν s ω)
    (t : ℕ) :
    MeasurableSet {ω |
      firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω = t} := by
  classical
  let C : ℕ → Set Ω := fun s ↦
    {ω | s ∈ range n ∧ s ≠ 0 ∧
      1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν s ω}
  have hC : ∀ s, MeasurableSet (C s) := by
    intro s
    by_cases hs : s ∈ range n
    · exact measurableSet_textbookMixtureStatistic_crossing
        (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
        (ν := ν) (n := n) (t := s) (hstat s hs)
    · have hempty : C s = ∅ := by
        ext ω
        constructor
        · intro hω
          exact False.elim (hs hω.1)
        · intro hω
          exact False.elim hω
      rw [hempty]
      exact MeasurableSet.empty
  by_cases ht0 : t = 0
  · subst t
    have h_eq :
        {ω |
          firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω = 0} =
          {ω | LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω} := by
      ext ω
      constructor
      · intro hτ
        by_contra hfail
        have hspec :=
          firstTextbookMixtureFailureTime_spec (K := K) (d := d)
            (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
            (ν := ν) (n := n) (ω := ω) hfail
        exact hspec.2.1 hτ
      · intro hmix
        exact firstTextbookMixtureFailureTime_eq_zero_of_mixtureBound
          (K := K) (d := d) (A := A) (R := R) (reg := reg) (σ2 := σ2)
          (δ := δ) (x := x) (ν := ν) (n := n) (ω := ω) hmix
    rw [h_eq]
    have hfail_meas :
        MeasurableSet
          {ω | ¬ LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω} :=
      measurableSet_not_LinUCBTextbookMixtureBoundEventUpTo
        (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
        (ν := ν) (n := n) hstat
    simpa [Set.compl_setOf] using hfail_meas.compl
  · have h_eq :
        {ω |
          firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω = t} =
          C t ∩ ⋂ s ∈ (range t : Finset ℕ), (C s)ᶜ := by
      ext ω
      constructor
      · intro hτ
        have hfail :
            ¬ LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω := by
          intro hmix
          have hzero :=
            firstTextbookMixtureFailureTime_eq_zero_of_mixtureBound
              (K := K) (d := d) (A := A) (R := R) (reg := reg) (σ2 := σ2)
              (δ := δ) (x := x) (ν := ν) (n := n) (ω := ω) hmix
          rw [hτ] at hzero
          exact ht0 hzero
        have hiff :=
          (firstTextbookMixtureFailureTime_eq_iff_of_mixture_failure
            (K := K) (d := d) (A := A) (R := R) (reg := reg) (σ2 := σ2)
            (δ := δ) (x := x) (ν := ν) (n := n) (ω := ω) (t := t) hfail).mp hτ
        refine ⟨hiff.1, ?_⟩
        refine Set.mem_iInter.2 fun s ↦ ?_
        refine Set.mem_iInter.2 fun hs ↦ ?_
        exact hiff.2 s (mem_range.mp hs)
      · intro hmem
        have hfail :
            ¬ LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω :=
          (not_LinUCBTextbookMixtureBoundEventUpTo_iff
            (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
            (ν := ν) (n := n) (ω := ω)).mpr ⟨t, hmem.1.1, hmem.1.2.1, hmem.1.2.2⟩
        have hbefore : ∀ s, s < t →
            ¬ (s ∈ range n ∧ s ≠ 0 ∧
              1 / δ < textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν s ω) := by
          intro s hs hCs
          exact (Set.mem_iInter.1 (Set.mem_iInter.1 hmem.2 s) (mem_range.mpr hs)) hCs
        exact
          (firstTextbookMixtureFailureTime_eq_iff_of_mixture_failure
            (K := K) (d := d) (A := A) (R := R) (reg := reg) (σ2 := σ2)
            (δ := δ) (x := x) (ν := ν) (n := n) (ω := ω) (t := t) hfail).mpr
            ⟨hmem.1, hbefore⟩
    rw [h_eq]
    exact (hC t).inter
      (Finset.measurableSet_biInter (range t) fun s _hs ↦ (hC s).compl)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Process-level version of
`measurableSet_firstTextbookMixtureFailureTime_eq`. -/
lemma measurableSet_firstTextbookMixtureFailureTime_eq_of_process
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ}
    (hA : ∀ s, Measurable (A s)) (hR : ∀ s, Measurable (R s)) (t : ℕ) :
    MeasurableSet {ω |
      firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω = t} :=
  measurableSet_firstTextbookMixtureFailureTime_eq
    (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x) (ν := ν)
    (n := n)
    (fun s _hs ↦ measurable_textbookSelfNormalizedMixtureStatistic
      (A := A) (R := R) hA hR reg σ2 x ν s)
    t

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The stopped textbook mixture statistic is exactly mathlib's stopped value of the deterministic
time-indexed mixture-statistic process. -/
lemma stoppedTextbookMixtureStatistic_eq_stoppedValue
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (δ : ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) :
    (fun ω ↦ stoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω) =
      stoppedValue
        (fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω)
        (fun ω ↦ (firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞)) := by
  rfl

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Finite decomposition of the stopped textbook mixture statistic over possible stopping times
`0, ..., n`. This is the finite-range form used to reduce stopped measurability and integrability
to fixed-time obligations. -/
lemma stoppedTextbookMixtureStatistic_eq_sum_range_succ
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (δ : ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) :
    (fun ω ↦ stoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω) =
      ∑ t ∈ range (n + 1),
        Set.indicator
          {ω | (firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞) = t}
          (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω) := by
  rw [stoppedTextbookMixtureStatistic_eq_stoppedValue]
  refine stoppedValue_eq_of_mem_finset (u := fun t ω ↦
    textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω)
    (τ := fun ω ↦ (firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞))
    (s := range (n + 1)) ?_
  intro ω
  refine ⟨firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω, ?_, rfl⟩
  exact mem_range.mpr
    (Nat.lt_succ_of_le (firstTextbookMixtureFailureTime_le
      (K := K) (d := d) (A := A) (R := R) (reg := reg) (σ2 := σ2)
      (δ := δ) (x := x) (ν := ν) (n := n) (ω := ω)))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The stopped textbook mixture statistic is measurable if the fixed-time mixture statistics and
the first-failure-time level sets are measurable on the finite stopping range. -/
lemma measurable_stoppedTextbookMixtureStatistic
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ}
    (hstat : ∀ t, t ∈ range (n + 1) →
      Measurable fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω)
    (hτ : ∀ t, t ∈ range (n + 1) →
      MeasurableSet {ω | firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω = t}) :
    Measurable fun ω ↦ stoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω := by
  rw [stoppedTextbookMixtureStatistic_eq_sum_range_succ]
  change Measurable fun a ↦
    (∑ t ∈ range (n + 1),
      (Set.indicator
        {ω | (firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞) = (t : ℕ∞)}
        (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω) : Ω → ℝ)) a
  simpa only [Finset.sum_apply] using
    (Finset.measurable_sum (s := range (n + 1))
      (f := fun (t : ℕ) ↦
        (Set.indicator
          {ω | (firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞) = (t : ℕ∞)}
          (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω) : Ω → ℝ))
      (by
        intro t ht
        have hτ_top :
            MeasurableSet
              {ω | (firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞) = t} := by
          convert hτ t ht using 1
          ext ω
          simp
        exact (hstat t ht).indicator hτ_top))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Process-level measurability of the stopped textbook mixture statistic. -/
lemma measurable_stoppedTextbookMixtureStatistic_of_process
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ}
    (hA : ∀ t, Measurable (A t)) (hR : ∀ t, Measurable (R t)) :
    Measurable fun ω ↦ stoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω :=
  measurable_stoppedTextbookMixtureStatistic
    (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x) (ν := ν)
    (n := n)
    (fun t _ht ↦ measurable_textbookSelfNormalizedMixtureStatistic
      (A := A) (R := R) hA hR reg σ2 x ν t)
    (fun t _ht ↦ measurableSet_firstTextbookMixtureFailureTime_eq_of_process
      (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
      (ν := ν) (n := n) hA hR t)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The stopped textbook mixture statistic is integrable if the fixed-time mixture statistics are
integrable on the finite stopping range. -/
lemma integrable_stoppedTextbookMixtureStatistic
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ}
    (hstat_int : ∀ t, t ∈ range (n + 1) →
      Integrable (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω) P)
    (hτ : ∀ t, t ∈ range (n + 1) →
      MeasurableSet {ω | firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω = t}) :
    Integrable (fun ω ↦ stoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω) P := by
  rw [stoppedTextbookMixtureStatistic_eq_sum_range_succ]
  change Integrable
    (∑ t ∈ range (n + 1),
      (Set.indicator
        {ω | (firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞) = (t : ℕ∞)}
        (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω) : Ω → ℝ)) P
  refine integrable_finsetSum' (μ := P) (range (n + 1)) ?_
  intro t ht
  have hτ_top :
      MeasurableSet
        {ω | (firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞) = t} := by
    convert hτ t ht using 1
    ext ω
    simp
  exact (hstat_int t ht).indicator hτ_top

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Process-level integrability of the stopped textbook mixture statistic from fixed-time
integrability. -/
lemma integrable_stoppedTextbookMixtureStatistic_of_process
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ}
    (hA : ∀ t, Measurable (A t)) (hR : ∀ t, Measurable (R t))
    (hstat_int : ∀ t, t ∈ range (n + 1) →
      Integrable (fun ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω) P) :
    Integrable (fun ω ↦ stoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω) P :=
  integrable_stoppedTextbookMixtureStatistic
    (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x) (ν := ν)
    (n := n) (P := P) hstat_int
    (fun t _ht ↦ measurableSet_firstTextbookMixtureFailureTime_eq_of_process
      (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
      (ν := ν) (n := n) hA hR t)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Optional-stopping bridge for a bounded stopping time and a real-valued supermartingale.

This is the generic Ville step needed by the future Gaussian-mixture proof: once the mixture
statistic is proved to be a supermartingale, stopping at the first threshold crossing cannot
increase its expectation above the initial expectation. -/
lemma integral_stoppedValue_le_initial_of_supermartingale
    {ℱ : Filtration ℕ mΩ} [SigmaFiniteFiltration P ℱ]
    {M : ℕ → Ω → ℝ} {τ : Ω → ℕ∞} {N : ℕ}
    (hM : Supermartingale M ℱ P)
    (hτ : IsStoppingTime ℱ τ)
    (hτ_le : ∀ ω, τ ω ≤ N) :
    P[stoppedValue M τ] ≤ P[M 0] := by
  have hsub : Submartingale (fun n ω ↦ -M n ω) ℱ P := hM.neg
  have hτ0 : IsStoppingTime ℱ (fun _ : Ω ↦ (0 : ℕ∞)) := isStoppingTime_const ℱ 0
  have hle : (fun _ : Ω ↦ (0 : ℕ∞)) ≤ τ := fun ω ↦ by
    exact bot_le
  have hmono :=
    hsub.expected_stoppedValue_mono hτ0 hτ hle hτ_le
  change P[fun ω ↦ -M 0 ω] ≤ P[fun ω ↦ -stoppedValue M τ ω] at hmono
  rw [integral_neg, integral_neg] at hmono
  linarith

omit [IsMarkovKernel ν] in
/-- If the textbook mixture statistic is a supermartingale, then the statistic stopped at the
first finite-horizon threshold crossing has expectation at most one. -/
lemma integral_stoppedTextbookMixtureStatistic_le_one_of_supermartingale
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ}
    {ℱ : Filtration ℕ mΩ} [SigmaFiniteFiltration P ℱ]
    (hM :
      Supermartingale
        (fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω) ℱ P)
    (hτ :
      IsStoppingTime ℱ
        (fun ω ↦ (firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞)))
    (hreg_pos : 0 < reg) :
    (∫ ω, stoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω ∂P) ≤ 1 := by
  have hτ_le :
      ∀ ω, (firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞) ≤ n := by
    intro ω
    exact_mod_cast firstTextbookMixtureFailureTime_le
      (K := K) (d := d) (A := A) (R := R) (reg := reg) (σ2 := σ2)
      (δ := δ) (x := x) (ν := ν) (n := n) (ω := ω)
  have hle :=
    integral_stoppedValue_le_initial_of_supermartingale
      (P := P) (ℱ := ℱ)
      (M := fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω)
      (τ := fun ω ↦ (firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞))
      (N := n) hM hτ hτ_le
  change
    (∫ ω, stoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω ∂P) ≤
      ∫ ω, textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν 0 ω ∂P at hle
  refine hle.trans_eq ?_
  simp [textbookSelfNormalizedMixtureStatistic_zero_of_reg_pos
    (A := A) (R := R) (reg := reg) (σ2 := σ2) (x := x) (ν := ν), hreg_pos]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If the textbook mixture statistic is a supermartingale, then the stopped statistic is
integrable. -/
lemma integrable_stoppedTextbookMixtureStatistic_of_supermartingale
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ}
    {ℱ : Filtration ℕ mΩ}
    (hM :
      Supermartingale
        (fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω) ℱ P)
    (hτ :
      IsStoppingTime ℱ
        (fun ω ↦ (firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞))) :
    Integrable (fun ω ↦ stoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω) P := by
  have hτ_le :
      ∀ ω, (firstTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞) ≤ n := by
    intro ω
    exact_mod_cast firstTextbookMixtureFailureTime_le
      (K := K) (d := d) (A := A) (R := R) (reg := reg) (σ2 := σ2)
      (δ := δ) (x := x) (ν := ν) (n := n) (ω := ω)
  exact integrable_stoppedValue ℕ hτ hM.integrable hτ_le

omit [IsMarkovKernel ν] in
/-- If the textbook mixture statistic is a supermartingale, then the bounded stopped statistic has
expectation at most one. This is the optional-stopping step in the textbook-shaped proof. -/
lemma integral_boundedStoppedTextbookMixtureStatistic_le_one_of_supermartingale
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ}
    {ℱ : Filtration ℕ mΩ} [SigmaFiniteFiltration P ℱ]
    (hM :
      Supermartingale
        (fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω) ℱ P)
    (hreg_pos : 0 < reg) :
    (∫ ω, boundedStoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω ∂P) ≤ 1 := by
  have hτ :
      IsStoppingTime ℱ
        (fun ω ↦ (boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞)) :=
    isStoppingTime_boundedTextbookMixtureFailureTime
      (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
      (ν := ν) (n := n) (ℱ := ℱ) hM.stronglyAdapted
  have hτ_le :
      ∀ ω, (boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞) ≤ n := by
    intro ω
    exact_mod_cast boundedTextbookMixtureFailureTime_le
      (K := K) (d := d) (A := A) (R := R) (reg := reg) (σ2 := σ2)
      (δ := δ) (x := x) (ν := ν) (n := n) (ω := ω)
  have hle :=
    integral_stoppedValue_le_initial_of_supermartingale
      (P := P) (ℱ := ℱ)
      (M := fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω)
      (τ := fun ω ↦ (boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞))
      (N := n) hM hτ hτ_le
  change
    (∫ ω, boundedStoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω ∂P) ≤
      ∫ ω, textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν 0 ω ∂P at hle
  refine hle.trans_eq ?_
  simp [textbookSelfNormalizedMixtureStatistic_zero_of_reg_pos
    (A := A) (R := R) (reg := reg) (σ2 := σ2) (x := x) (ν := ν), hreg_pos]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If the textbook mixture statistic is a supermartingale, then the bounded stopped statistic is
integrable. -/
lemma integrable_boundedStoppedTextbookMixtureStatistic_of_supermartingale
    {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
    {reg : ℝ} {σ2 : ℝ≥0} {δ : ℝ} {x : Fin K → Feature d}
    {ν : Kernel (Fin K) ℝ} {n : ℕ}
    {ℱ : Filtration ℕ mΩ}
    (hM :
      Supermartingale
        (fun t ω ↦ textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν t ω) ℱ P) :
    Integrable (fun ω ↦ boundedStoppedTextbookMixtureStatistic A R reg σ2 δ x ν n ω) P := by
  have hτ :
      IsStoppingTime ℱ
        (fun ω ↦ (boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞)) :=
    isStoppingTime_boundedTextbookMixtureFailureTime
      (A := A) (R := R) (reg := reg) (σ2 := σ2) (δ := δ) (x := x)
      (ν := ν) (n := n) (ℱ := ℱ) hM.stronglyAdapted
  have hτ_le :
      ∀ ω, (boundedTextbookMixtureFailureTime A R reg σ2 δ x ν n ω : ℕ∞) ≤ n := by
    intro ω
    exact_mod_cast boundedTextbookMixtureFailureTime_le
      (K := K) (d := d) (A := A) (R := R) (reg := reg) (σ2 := σ2)
      (δ := δ) (x := x) (ν := ν) (n := n) (ω := ω)
  exact integrable_stoppedValue ℕ hτ hM.integrable hτ_le

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If the textbook determinant-radius bound fails, then the Gaussian-mixture statistic exceeds
`1 / δ`.

This is only deterministic algebra: it rewrites
`2 σ² log(sqrt(detRatio) / δ) < ‖S_t‖²_{V_t⁻¹}` as
`1 / δ < exp(‖S_t‖²_{V_t⁻¹} / (2 σ²)) / sqrt(detRatio)`. -/
lemma inv_delta_lt_textbookSelfNormalizedMixtureStatistic_of_textbookBound_lt
    {σ2 : ℝ≥0} {δ : ℝ}
    (hσ2_pos : 0 < (σ2 : ℝ)) (hδ_pos : 0 < δ)
    (hratio_pos : 0 < designDetRatio A reg x n ω)
    (hfail :
      textbookSelfNormalizedNoiseBound σ2 δ (designDetRatio A reg x n ω) <
        centeredNoiseQuadraticForm A R ν reg x n ω) :
    1 / δ <
      textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν n ω := by
  let q := centeredNoiseQuadraticForm A R ν reg x n ω
  let ratio := designDetRatio A reg x n ω
  have hcoef : 0 < 2 * (σ2 : ℝ) := by positivity
  have hlog_lt : Real.log (√ratio / δ) < q / (2 * (σ2 : ℝ)) := by
    rw [lt_div_iff₀ hcoef]
    simpa [q, ratio, textbookSelfNormalizedNoiseBound, mul_assoc, mul_comm, mul_left_comm]
      using hfail
  have hsqrt_pos : 0 < √ratio := Real.sqrt_pos.2 (by simpa [ratio] using hratio_pos)
  have harg_pos : 0 < √ratio / δ := div_pos hsqrt_pos hδ_pos
  have hexp_lt : √ratio / δ < Real.exp (q / (2 * (σ2 : ℝ))) := by
    calc
      √ratio / δ = Real.exp (Real.log (√ratio / δ)) := by
        rw [Real.exp_log harg_pos]
      _ < Real.exp (q / (2 * (σ2 : ℝ))) := Real.exp_lt_exp.mpr hlog_lt
  have hstat : 1 / δ < Real.exp (q / (2 * (σ2 : ℝ))) / √ratio := by
    rw [lt_div_iff₀ hsqrt_pos]
    calc
      1 / δ * √ratio = √ratio / δ := by ring
      _ < Real.exp (q / (2 * (σ2 : ℝ))) := hexp_lt
  simpa [textbookSelfNormalizedMixtureStatistic, q, ratio] using hstat

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A pointwise Gaussian-mixture-statistic bound implies the textbook self-normalized quadratic
bound at the same time. -/
lemma centeredNoiseQuadraticForm_le_textbookSelfNormalizedNoiseBound_of_mixture_le
    {σ2 : ℝ≥0} {δ : ℝ}
    (hσ2_pos : 0 < (σ2 : ℝ)) (hδ_pos : 0 < δ)
    (hratio_pos : 0 < designDetRatio A reg x n ω)
    (hmix :
      textbookSelfNormalizedMixtureStatistic A R reg σ2 x ν n ω ≤ 1 / δ) :
    centeredNoiseQuadraticForm A R ν reg x n ω ≤
      textbookSelfNormalizedNoiseBound σ2 δ (designDetRatio A reg x n ω) := by
  by_contra hnot
  have hfail :
      textbookSelfNormalizedNoiseBound σ2 δ (designDetRatio A reg x n ω) <
        centeredNoiseQuadraticForm A R ν reg x n ω :=
    lt_of_not_ge hnot
  have hgt :=
    inv_delta_lt_textbookSelfNormalizedMixtureStatistic_of_textbookBound_lt
      (A := A) (R := R) (reg := reg) (x := x) (ν := ν) (n := n) (ω := ω)
      hσ2_pos hδ_pos hratio_pos hfail
  exact (not_lt_of_ge hmix) hgt

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The horizon-local Gaussian-mixture event implies the horizon-local textbook self-normalized
noise event, assuming the realized determinant ratios are positive. -/
lemma LinUCBTextbookSelfNormalizedNoiseEventUpTo.of_mixtureBound
    {σ2 : ℝ≥0} {δ : ℝ}
    (hσ2_pos : 0 < (σ2 : ℝ)) (hδ_pos : 0 < δ)
    (hratio_pos : ∀ t, t ∈ range n → t ≠ 0 → 0 < designDetRatio A reg x t ω)
    (h_mix :
      LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω) :
    LinUCBTextbookSelfNormalizedNoiseEventUpTo A R reg σ2 δ x ν n ω := by
  intro t ht ht0
  exact centeredNoiseQuadraticForm_le_textbookSelfNormalizedNoiseBound_of_mixture_le
    (A := A) (R := R) (reg := reg) (x := x) (ν := ν) (n := t) (ω := ω)
    hσ2_pos hδ_pos (hratio_pos t ht ht0) (h_mix t ht ht0)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Under positive regularization, the horizon-local Gaussian-mixture event implies the textbook
self-normalized noise event. -/
lemma LinUCBTextbookSelfNormalizedNoiseEventUpTo.of_mixtureBound_of_reg_pos
    {σ2 : ℝ≥0} {δ : ℝ}
    (hσ2_pos : 0 < (σ2 : ℝ)) (hδ_pos : 0 < δ) (hreg_pos : 0 < reg)
    (h_mix :
      LinUCBTextbookMixtureBoundEventUpTo A R reg σ2 δ x ν n ω) :
    LinUCBTextbookSelfNormalizedNoiseEventUpTo A R reg σ2 δ x ν n ω := by
  exact LinUCBTextbookSelfNormalizedNoiseEventUpTo.of_mixtureBound
    (A := A) (R := R) (reg := reg) (x := x) (ν := ν) (n := n) (ω := ω)
    hσ2_pos hδ_pos
    (fun t _ht _ht0 ↦ designDetRatio_pos_of_reg_pos (A := A) (reg := reg)
      (x := x) (n := t) (ω := ω) hreg_pos)
    h_mix

end AlgorithmBehavior

end LinUCB

end Bandits
