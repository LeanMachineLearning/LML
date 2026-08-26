/-
Copyright (c) 2026 Fawad Haider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Fawad Haider
-/
module

public import LeanMachineLearning.Online.Bandit.Algorithms.LinUCB.Matrix

/-!
# LinUCB Confidence Events

Basic confidence events and modeling assumptions consumed by the finite-action LinUCB regret proof.
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

/-- The pointwise LinUCB confidence event used by the finite-action regret proof.

For every positive process time, the best arm's true mean lies below its optimistic index, and the
selected arm's pessimistic index lies below its true mean. On this event, the max-index property of
LinUCB turns optimism into an instantaneous regret bound. -/
def LinUCBConfidenceEvent [Nonempty (Fin K)]
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (ω : Ω) : Prop :=
  ∀ t, t ≠ 0 →
    (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) t ω ∧
      estimatedReward A R reg x (A t ω) t ω -
        √(β (t + 1)) * width A reg x (A t ω) t ω ≤ (ν (A t ω))[id]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Horizon-local LinUCB confidence event.

The regret theorem up to horizon `n` only uses the confidence inequalities at times
`t ∈ range n`. This finite-horizon event is the natural target for a high-probability
self-normalized concentration theorem with a fixed horizon, and avoids requiring confidence at all
future times when proving an `n`-round regret bound. -/
def LinUCBConfidenceEventUpTo [Nonempty (Fin K)]
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) (ω : Ω) : Prop :=
  ∀ t, t ∈ range n → t ≠ 0 →
    (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) t ω ∧
      estimatedReward A R reg x (A t ω) t ω -
        √(β (t + 1)) * width A reg x (A t ω) t ω ≤ (ν (A t ω))[id]

omit [IsMarkovKernel ν] in
/-- A global LinUCB confidence event implies its finite-horizon restriction. -/
lemma LinUCBConfidenceEvent.toUpTo [Nonempty (Fin K)]
    (h_conf : LinUCBConfidenceEvent A R reg β x ν ω) :
    LinUCBConfidenceEventUpTo A R reg β x ν n ω := by
  intro t _ht ht0
  exact h_conf t ht0

omit [IsMarkovKernel ν] in
/-- First projection from the horizon-local LinUCB confidence event: optimism for the best arm. -/
lemma LinUCBConfidenceEventUpTo.best [Nonempty (Fin K)]
    (h_conf : LinUCBConfidenceEventUpTo A R reg β x ν n ω) :
    ∀ t, t ∈ range n → t ≠ 0 →
      (ν (bestArm ν))[id] ≤ index A R reg β x (bestArm ν) t ω := by
  intro t ht ht0
  exact (h_conf t ht ht0).1

omit [IsMarkovKernel ν] in
/-- Second projection from the horizon-local LinUCB confidence event: validity of the selected
arm's lower confidence inequality. -/
lemma LinUCBConfidenceEventUpTo.arm [Nonempty (Fin K)]
    (h_conf : LinUCBConfidenceEventUpTo A R reg β x ν n ω) :
    ∀ t, t ∈ range n → t ≠ 0 →
      estimatedReward A R reg x (A t ω) t ω -
        √(β (t + 1)) * width A reg x (A t ω) t ω ≤ (ν (A t ω))[id] := by
  intro t ht ht0
  exact (h_conf t ht ht0).2

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Linear realizability of the arm means by a parameter `θ`.

The actual self-normalized concentration theorem for LinUCB needs an assumption of this shape:
each arm's mean reward must be represented by the finite-dimensional linear model
`x_aᵀ θ`. Without such a realizability assumption, no concentration theorem can imply
`LinUCBConfidenceEvent`, because the least-squares predictor may be biased away from the true arm
means for structural reasons rather than random noise. -/
def LinearMeanModel (ν : Kernel (Fin K) ℝ) (x : Fin K → Feature d) (θ : Feature d) : Prop :=
  ∀ a, (ν a)[id] = dotProduct θ (x a)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Squared Euclidean-norm bound on a linear-bandit parameter. This is the finite-dimensional
version of the textbook assumption `‖θ‖₂ ≤ S`, written as `θᵀθ ≤ S2`. -/
def ParameterSqNormBound (θ : Feature d) (S2 : ℝ) : Prop :=
  dotProduct θ θ ≤ S2

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Mean response vector predicted by a linear mean model along the realized actions. -/
noncomputable def meanResponseVector
    (A : ℕ → Ω → Fin K) (ν : Kernel (Fin K) ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : Feature d :=
  ∑ s ∈ range n, (ν (A s ω))[id] • x (A s ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Centered response vector, i.e. the accumulated reward-feature vector minus its conditional mean
under the finite-action linear mean model. This is the deterministic noise vector that the later
self-normalized concentration theorem must control. -/
noncomputable def centeredResponseVector
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (ν : Kernel (Fin K) ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : Feature d :=
  responseVector A R x n ω - meanResponseVector A ν x n ω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Scalar reward noise at time `t`, centered at the mean of the selected arm. -/
noncomputable def rewardNoise
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (ν : Kernel (Fin K) ℝ)
    (t : ℕ) (ω : Ω) : ℝ :=
  R t ω - (ν (A t ω))[id]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Arm-wise centered reward subgaussianity.

This is the LinUCB analogue of the scalar noise assumption used in `UCB.lean`: for each arm, the
reward centered at that arm's mean has a subgaussian moment-generating-function bound. A future
vector self-normalized concentration theorem should start from this assumption, together with the
linear mean model, and prove the centered-noise-plus-bias confidence event. -/
def RewardNoiseSubgaussian (ν : Kernel (Fin K) ℝ) (σ2 : ℝ≥0) : Prop :=
  ∀ a, HasSubgaussianMGF (fun r ↦ r - (ν a)[id]) σ2 (ν a)

end AlgorithmBehavior

end LinUCB

end Bandits
