/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.SequentialLearning.Algorithm
public import LeanMachineLearning.ForMathlib.Probability.Kernel.Cond

/-!
# Decision-based Optimization Algorithms

An interface for decision-based optimization algorithms, which sample points satisfying a
user-defined decision rule at each iteration. These algorithms are defined by a sequence of
decision rules that determine from which set to sample at each iteration, based on the observed
data. The `Decision` algorithm is a special case of the `Algorithm` structure, where the Markov
kernel is defined through the decision rules.

## Main definitions

* `Decision`: The Decision algorithm that starts by sampling from the initial measure `μ` and then
samples points satisfying the decision rules at each iteration using the defined kernel.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (μ : Measure α) [IsProbabilityMeasure μ]
  (κs : (n : ℕ) → Kernel ((Iic n) → α × β) α) [∀ n, IsSFiniteKernel (κs n)]
  {decision : (n : ℕ) → ((Iic n) → α × β) → Set α}
  (measurableSet_decision_prod :
    ∀ ⦃n⦄, MeasurableSet {p : (Iic n → α × β) × α | p.2 ∈ decision n p.1}) {n : ℕ}

/- We need that the decisions has non-zero measure at each iteration,
ensuring that the algorithm can sample from it. -/
variable (h₀ : ∀ n (data : Iic n → α × β), κs n data (decision n data) ≠ 0)
  (htop : ∀ n (data : Iic n → α × β), κs n data (decision n data) ≠ ⊤)

/-- The interface for decision-based optimization algorithms. -/
noncomputable def Decision : Algorithm α β where
  policy n := (κs n).cond <| measurableSet_decision_prod (n := n)
  p0 := μ
  h_policy n := Kernel.isMarkovKernel_cond_of_finite _ (h₀ n) (htop n)
