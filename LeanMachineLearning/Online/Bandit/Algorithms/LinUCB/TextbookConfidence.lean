/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Fawad Haider
-/
module

public import LeanMachineLearning.Online.Bandit.Algorithms.LinUCB.TextbookMixture

/-!
# LinUCB Textbook Confidence Events

Deterministic bridges from centered-noise and textbook self-normalized events to
LinUCB prediction-confidence events.
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

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Horizon-local coordinate-wise centered-noise event.

This is a conservative finite-dimensional interface for reusing scalar projection concentration:
if every coordinate of the centered response vector is bounded, then the centered-noise quadratic
form is bounded through `centeredNoiseQuadraticForm_le_nat_mul_coord_sq_div_reg`. -/
def LinUCBCenteredNoiseCoordinateBoundEventUpTo
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (coordBudget : ℕ → ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) (ω : Ω) : Prop :=
  ∀ t, t ∈ range n → t ≠ 0 → ∀ i,
    |centeredResponseVector A R ν x t ω i| ≤ coordBudget (t + 1)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Upper-tail failure for one coordinate of the finite-horizon centered-noise vector. -/
def centeredNoiseCoordinateUpperFailure
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (coordBudget : ℕ → ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (t : ℕ) (i : Fin d) : Set Ω :=
  {ω | coordBudget (t + 1) < centeredResponseVector A R ν x t ω i}

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Lower-tail failure for one coordinate of the finite-horizon centered-noise vector. -/
def centeredNoiseCoordinateLowerFailure
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (coordBudget : ℕ → ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (t : ℕ) (i : Fin d) : Set Ω :=
  {ω | centeredResponseVector A R ν x t ω i < -coordBudget (t + 1)}

omit [IsMarkovKernel ν] in
/-- A global centered-noise-plus-bias confidence event implies its finite-horizon restriction. -/
lemma LinUCBCenteredNoiseBiasConfidenceEvent.toUpTo
    (θ : Feature d)
    (h_noise : LinUCBCenteredNoiseBiasConfidenceEvent A R reg β x ν θ ω) :
    LinUCBCenteredNoiseBiasConfidenceEventUpTo A R reg β x ν θ n ω := by
  intro t _ht ht0
  exact h_noise t ht0

omit [IsMarkovKernel ν] in
/-- A coordinate-wise centered-noise event implies the centered-noise quadratic-form event under the
corresponding conservative budget. -/
lemma LinUCBCenteredNoiseConfidenceEventUpTo.of_coordinateBound
    (hreg_pos : 0 < reg)
    {coordBudget noiseBudget : ℕ → ℝ}
    (hcoord :
      LinUCBCenteredNoiseCoordinateBoundEventUpTo A R coordBudget x ν n ω)
    (hcoord_nonneg : ∀ t, t ∈ range n → t ≠ 0 → 0 ≤ coordBudget (t + 1))
    (h_budget : ∀ t, t ∈ range n → t ≠ 0 →
      (d : ℝ) * coordBudget (t + 1) ^ 2 / reg ≤ noiseBudget (t + 1)) :
    LinUCBCenteredNoiseConfidenceEventUpTo A R reg noiseBudget x ν n ω := by
  intro t ht ht0
  exact
    (centeredNoiseQuadraticForm_le_nat_mul_coord_sq_div_reg (A := A) (R := R)
      (reg := reg) (x := x) (ν := ν) (n := t) (ω := ω) hreg_pos
      (hcoord_nonneg t ht ht0) (hcoord t ht ht0)).trans
      (h_budget t ht ht0)

omit [IsMarkovKernel ν] in
/-- A horizon-local centered-noise event plus a parameter norm bound implies the
centered-noise-plus-ridge-bias event.

This is the finite-horizon deterministic half of the textbook confidence-set proof:
the future self-normalized concentration theorem only has to control
`centeredNoiseQuadraticForm`; the ridge-bias contribution is bounded here by
`reg * S2`. -/
lemma LinUCBCenteredNoiseBiasConfidenceEventUpTo.of_centeredNoise
    (θ : Feature d) (S2 : ℝ)
    (hreg_pos : 0 < reg)
    (hθ : ParameterSqNormBound θ S2)
    {noiseBudget : ℕ → ℝ}
    (h_noise :
      LinUCBCenteredNoiseConfidenceEventUpTo A R reg noiseBudget x ν n ω)
    (h_budget : ∀ t, t ∈ range n → t ≠ 0 →
      (√(noiseBudget (t + 1)) + √(reg * S2)) ^ 2 ≤ β (t + 1)) :
    LinUCBCenteredNoiseBiasConfidenceEventUpTo A R reg β x ν θ n ω := by
  intro t ht ht0
  exact
    (centeredNoiseBiasQuadraticForm_le_sqrt_bounds_sq (A := A) (R := R)
      (reg := reg) (x := x) (ν := ν) (n := t) (ω := ω) θ hreg_pos
      (noiseBudget (t + 1)) (reg * S2) (h_noise t ht ht0)
      (regularizationBiasQuadraticForm_le_of_parameterSqNormBound (A := A)
        (reg := reg) (x := x) (n := t) (ω := ω) θ hreg_pos hθ)).trans
      (h_budget t ht ht0)

omit [IsMarkovKernel ν] in
/-- The textbook determinant-ratio self-normalized noise event plus the ridge-bias radius implies
the existing centered-noise-plus-bias confidence event.

This is the deterministic bridge from the future Gaussian-mixture concentration theorem to the
confidence event already consumed by the LinUCB regret proof. -/
lemma LinUCBCenteredNoiseBiasConfidenceEventUpTo.of_textbookSelfNormalizedNoise
    (θ : Feature d) (S2 : ℝ) {σ2 : ℝ≥0} {δ : ℝ}
    (hreg_pos : 0 < reg)
    (hθ : ParameterSqNormBound θ S2)
    (h_noise :
      LinUCBTextbookSelfNormalizedNoiseEventUpTo A R reg σ2 δ x ν n ω)
    (h_budget : ∀ t, t ∈ range n → t ≠ 0 →
      (√(textbookSelfNormalizedNoiseBound σ2 δ (designDetRatio A reg x t ω)) +
        √(reg * S2)) ^ 2 ≤ β (t + 1)) :
    LinUCBCenteredNoiseBiasConfidenceEventUpTo A R reg β x ν θ n ω := by
  intro t ht ht0
  exact
    (centeredNoiseBiasQuadraticForm_le_sqrt_bounds_sq (A := A) (R := R)
      (reg := reg) (x := x) (ν := ν) (n := t) (ω := ω) θ hreg_pos
      (textbookSelfNormalizedNoiseBound σ2 δ (designDetRatio A reg x t ω))
      (reg * S2) (h_noise t ht ht0)
      (regularizationBiasQuadraticForm_le_of_parameterSqNormBound (A := A)
        (reg := reg) (x := x) (n := t) (ω := ω) θ hreg_pos hθ)).trans
      (h_budget t ht ht0)

omit [IsMarkovKernel ν] in
/-- The centered-noise-plus-bias confidence event implies the textbook parameter ellipsoid event
under linear realizability and positive regularization. -/
lemma LinUCBParameterEllipsoidConfidenceEvent.of_centeredNoiseBias
    (θ : Feature d)
    (h_linear : LinearMeanModel ν x θ)
    (hreg_pos : 0 < reg)
    (h_noise :
      LinUCBCenteredNoiseBiasConfidenceEvent A R reg β x ν θ ω) :
    LinUCBParameterEllipsoidConfidenceEvent A R reg β x θ ω := by
  intro t ht
  rw [parameterErrorQuadraticForm_eq_centeredNoiseBiasQuadraticForm (A := A) (R := R)
    (reg := reg) (x := x) (ν := ν) (n := t) (ω := ω) θ h_linear hreg_pos]
  exact h_noise t ht

omit [IsMarkovKernel ν] in
/-- The horizon-local centered-noise-plus-bias event implies the horizon-local parameter ellipsoid
event under linear realizability and positive regularization. -/
lemma LinUCBParameterEllipsoidConfidenceEventUpTo.of_centeredNoiseBias
    (θ : Feature d)
    (h_linear : LinearMeanModel ν x θ)
    (hreg_pos : 0 < reg)
    (h_noise :
      LinUCBCenteredNoiseBiasConfidenceEventUpTo A R reg β x ν θ n ω) :
    LinUCBParameterEllipsoidConfidenceEventUpTo A R reg β x θ n ω := by
  intro t ht ht0
  rw [parameterErrorQuadraticForm_eq_centeredNoiseBiasQuadraticForm (A := A) (R := R)
    (reg := reg) (x := x) (ν := ν) (n := t) (ω := ω) θ h_linear hreg_pos]
  exact h_noise t ht ht0

omit [IsMarkovKernel ν] in
/-- Under linear realizability and positive regularization, the parameter ellipsoid event is exactly
the centered-noise-plus-bias confidence event. -/
lemma linUCBParameterEllipsoidConfidenceEvent_iff_centeredNoiseBiasConfidenceEvent
    (θ : Feature d)
    (h_linear : LinearMeanModel ν x θ)
    (hreg_pos : 0 < reg) :
    LinUCBParameterEllipsoidConfidenceEvent A R reg β x θ ω ↔
      LinUCBCenteredNoiseBiasConfidenceEvent A R reg β x ν θ ω := by
  constructor
  · intro h_ellipsoid t ht
    rw [← parameterErrorQuadraticForm_eq_centeredNoiseBiasQuadraticForm (A := A) (R := R)
      (reg := reg) (x := x) (ν := ν) (n := t) (ω := ω) θ h_linear hreg_pos]
    exact h_ellipsoid t ht
  · intro h_noise
    exact LinUCBParameterEllipsoidConfidenceEvent.of_centeredNoiseBias (A := A) (R := R)
      (reg := reg) (β := β) (x := x) (ν := ν) (ω := ω) θ h_linear hreg_pos h_noise

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Action-wise prediction-error confidence event around a linear parameter `θ`.

This is the finite-action consequence of the textbook ellipsoid event after applying the
matrix Cauchy-Schwarz inequality to each arm. -/
def LinUCBParameterPredictionConfidenceEvent
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d)
    (θ : Feature d) (ω : Ω) : Prop :=
  ∀ t, t ≠ 0 → ∀ a,
    |dotProduct (thetaHat A R reg x t ω - θ) (x a)| ≤
      √(β (t + 1)) * width A reg x a t ω

/-- Uniform self-normalized prediction-error event for finite-action LinUCB.

This is the event that a future self-normalized martingale concentration theorem should prove with
high probability, for a concrete textbook choice of `β`. It says that, at every positive time and
for every finite action, the least-squares prediction error is bounded by the LinUCB confidence
radius. -/
def LinUCBSelfNormalizedConfidenceEvent
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (ω : Ω) : Prop :=
  ∀ t, t ≠ 0 → ∀ a,
    |estimatedReward A R reg x a t ω - (ν a)[id]| ≤
      √(β (t + 1)) * width A reg x a t ω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Horizon-local self-normalized prediction-error event.

This is the finite-horizon version of `LinUCBSelfNormalizedConfidenceEvent`. For regret through
time `n`, the proof only needs prediction confidence for positive `t ∈ range n`. -/
def LinUCBSelfNormalizedConfidenceEventUpTo
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) (ω : Ω) : Prop :=
  ∀ t, t ∈ range n → t ≠ 0 → ∀ a,
    |estimatedReward A R reg x a t ω - (ν a)[id]| ≤
      √(β (t + 1)) * width A reg x a t ω

omit [IsMarkovKernel ν] in
/-- A global self-normalized prediction-error event implies its finite-horizon restriction. -/
lemma LinUCBSelfNormalizedConfidenceEvent.toUpTo
    (h_self : LinUCBSelfNormalizedConfidenceEvent A R reg β x ν ω) :
    LinUCBSelfNormalizedConfidenceEventUpTo A R reg β x ν n ω := by
  intro t _ht ht0 a
  exact h_self t ht0 a

omit [IsMarkovKernel ν] in
/-- A parameter prediction-confidence event implies the self-normalized confidence event once the
arm means are realized by that parameter. -/
lemma LinUCBSelfNormalizedConfidenceEvent.of_parameterPrediction
    (θ : Feature d)
    (h_linear : LinearMeanModel ν x θ)
    (h_param : LinUCBParameterPredictionConfidenceEvent A R reg β x θ ω) :
    LinUCBSelfNormalizedConfidenceEvent A R reg β x ν ω := by
  intro t ht a
  have h_param_t := h_param t ht a
  have h_error :
      estimatedReward A R reg x a t ω - (ν a)[id] =
        dotProduct (thetaHat A R reg x t ω - θ) (x a) := by
    calc
      estimatedReward A R reg x a t ω - (ν a)[id]
          = dotProduct (thetaHat A R reg x t ω) (x a) - dotProduct θ (x a) := by
              rw [estimatedReward, h_linear a]
      _ = dotProduct (thetaHat A R reg x t ω - θ) (x a) := by
              rw [sub_dotProduct]
  rw [h_error]
  simpa [sub_dotProduct] using h_param_t

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The textbook ellipsoid event implies action-wise parameter prediction confidence under positive
regularization, by the matrix Cauchy-Schwarz step. -/
lemma LinUCBParameterPredictionConfidenceEvent.of_ellipsoid
    (θ : Feature d)
    (hreg_pos : 0 < reg)
    (h_ellipsoid : LinUCBParameterEllipsoidConfidenceEvent A R reg β x θ ω) :
    LinUCBParameterPredictionConfidenceEvent A R reg β x θ ω := by
  intro t ht a
  have h_cauchy_t :=
    linUCBPredictionErrorCauchySchwarz_of_reg_pos (A := A) (reg := reg) (x := x)
      hreg_pos (thetaHat A R reg x t ω - θ) a t ω
  have h_radius :
      √(parameterErrorQuadraticForm A R reg x θ t ω) ≤ √(β (t + 1)) :=
    Real.sqrt_le_sqrt (h_ellipsoid t ht)
  calc
    |dotProduct (thetaHat A R reg x t ω - θ) (x a)|
        ≤ √(parameterErrorQuadraticForm A R reg x θ t ω) * width A reg x a t ω := by
          simpa [parameterErrorQuadraticForm] using h_cauchy_t
    _ ≤ √(β (t + 1)) * width A reg x a t ω := by
          exact mul_le_mul_of_nonneg_right h_radius (Real.sqrt_nonneg _)

omit [IsMarkovKernel ν] in
/-- The textbook ellipsoid event implies the self-normalized prediction-error event under positive
regularization and linear realizability. -/
lemma LinUCBSelfNormalizedConfidenceEvent.of_parameterEllipsoid
    (θ : Feature d)
    (h_linear : LinearMeanModel ν x θ)
    (hreg_pos : 0 < reg)
    (h_ellipsoid : LinUCBParameterEllipsoidConfidenceEvent A R reg β x θ ω) :
    LinUCBSelfNormalizedConfidenceEvent A R reg β x ν ω :=
  LinUCBSelfNormalizedConfidenceEvent.of_parameterPrediction (A := A) (R := R)
    (reg := reg) (β := β) (x := x) (ν := ν) (ω := ω) θ h_linear
    (LinUCBParameterPredictionConfidenceEvent.of_ellipsoid (A := A) (R := R)
      (reg := reg) (β := β) (x := x) (ω := ω) θ hreg_pos h_ellipsoid)

omit [IsMarkovKernel ν] in
/-- The horizon-local textbook ellipsoid event implies the horizon-local self-normalized
prediction-error event under positive regularization and linear realizability. -/
lemma LinUCBSelfNormalizedConfidenceEventUpTo.of_parameterEllipsoid
    (θ : Feature d)
    (h_linear : LinearMeanModel ν x θ)
    (hreg_pos : 0 < reg)
    (h_ellipsoid : LinUCBParameterEllipsoidConfidenceEventUpTo A R reg β x θ n ω) :
    LinUCBSelfNormalizedConfidenceEventUpTo A R reg β x ν n ω := by
  intro t ht ht0 a
  have h_cauchy_t :=
    linUCBPredictionErrorCauchySchwarz_of_reg_pos (A := A) (reg := reg) (x := x)
      hreg_pos (thetaHat A R reg x t ω - θ) a t ω
  have h_radius :
      √(parameterErrorQuadraticForm A R reg x θ t ω) ≤ √(β (t + 1)) :=
    Real.sqrt_le_sqrt (h_ellipsoid t ht ht0)
  have h_error :
      estimatedReward A R reg x a t ω - (ν a)[id] =
        dotProduct (thetaHat A R reg x t ω - θ) (x a) := by
    calc
      estimatedReward A R reg x a t ω - (ν a)[id]
          = dotProduct (thetaHat A R reg x t ω) (x a) - dotProduct θ (x a) := by
              rw [estimatedReward, h_linear a]
      _ = dotProduct (thetaHat A R reg x t ω - θ) (x a) := by
              rw [sub_dotProduct]
  rw [h_error]
  calc
    |dotProduct (thetaHat A R reg x t ω - θ) (x a)|
        ≤ √(parameterErrorQuadraticForm A R reg x θ t ω) * width A reg x a t ω := by
          simpa [parameterErrorQuadraticForm] using h_cauchy_t
    _ ≤ √(β (t + 1)) * width A reg x a t ω := by
          exact mul_le_mul_of_nonneg_right h_radius (Real.sqrt_nonneg _)

omit [IsMarkovKernel ν] in
/-- The horizon-local centered-noise-plus-bias event implies the horizon-local self-normalized
prediction-error event under linear realizability and positive regularization. -/
lemma LinUCBSelfNormalizedConfidenceEventUpTo.of_centeredNoiseBias
    (θ : Feature d)
    (h_linear : LinearMeanModel ν x θ)
    (hreg_pos : 0 < reg)
    (h_noise : LinUCBCenteredNoiseBiasConfidenceEventUpTo A R reg β x ν θ n ω) :
    LinUCBSelfNormalizedConfidenceEventUpTo A R reg β x ν n ω :=
  LinUCBSelfNormalizedConfidenceEventUpTo.of_parameterEllipsoid (A := A) (R := R)
    (reg := reg) (β := β) (x := x) (ν := ν) (n := n) (ω := ω) θ h_linear hreg_pos
    (LinUCBParameterEllipsoidConfidenceEventUpTo.of_centeredNoiseBias (A := A) (R := R)
      (reg := reg) (β := β) (x := x) (ν := ν) (n := n) (ω := ω)
      θ h_linear hreg_pos h_noise)

end AlgorithmBehavior

end LinUCB

end Bandits
