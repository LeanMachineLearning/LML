/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.Optimization.Algorithms.Utils.Tuple
public import LeanMachineLearning.SequentialLearning.Algorithm

/-!
# Decision-based Optimization Algorithms

An interface for decision-based optimization algorithms, which sample points satisfying a
user-defined decision rule at each iteration. These algorithms are defined by a sequence of
decision rules that determine from which set to sample at each iteration, based on the observed
data. The `Decision` algorithm is a special case of the `Algorithm` structure, where the Markov
kernel is defined through the decision rules.

## Main definitions

* `decision_kernel`: The Markov kernel that samples from the decision set rules according to a
given measure `μ`.
* `Decision`: The Decision algorithm that starts by sampling from the initial measure `μ` and then
samples points satisfying the decision rules at each iteration using the defined kernel.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (μ : Measure α) [IsProbabilityMeasure μ] {decision : (n : ℕ) → ((Iic n) → α × β) → Set α}
  (measurableSet_decision_prod :
    ∀ n, MeasurableSet {p : (Iic n → α × β) × α | p.2 ∈ decision n p.1}) {n : ℕ}

include measurableSet_decision_prod in
lemma measurable_decision_inter {s : Set α} (hs : MeasurableSet s) :
    Measurable (fun data : Iic n → α × β ↦ μ (decision n data ∩ s)) := by
  set E := {p : (Iic n → α × β) × α | p.2 ∈ decision n p.1 ∩ s}
  have hE_meas : MeasurableSet E :=
    (measurableSet_decision_prod n).inter
      <| measurableSet_preimage measurable_snd hs
  exact measurable_measure_prodMk_left hE_meas

/-- The Markov kernel that samples from the decision set according to a given
measure `μ`. -/
noncomputable def decision_kernel : Kernel (Iic n → α × β) α := by
  refine ⟨fun data ↦ cond μ <| decision n data, ?_⟩
  rw [Measure.measurable_measure]
  intro s hs
  simp only [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul]
  refine Measurable.mul ?_ ?_
  · refine Measurable.inv ?_
    convert measurable_decision_inter μ measurableSet_decision_prod (MeasurableSet.univ)
    simp [Set.inter_univ]
  · simp_rw [μ.restrict_apply hs]
    convert measurable_decision_inter μ measurableSet_decision_prod hs using 1
    simp [Set.inter_comm]

/- We need that the decisions has non-zero measure at each iteration,
ensuring that the algorithm can sample from it. -/
variable (h : ∀ n (data : Iic n → α × β), μ (decision n data) ≠ 0)

/-- The interface for decision-based optimization algorithms. -/
noncomputable def Decision : Algorithm α β where
  policy _ := decision_kernel μ measurableSet_decision_prod
  p0 := μ
  h_policy n := ⟨fun data => cond_isProbabilityMeasure (h n data)⟩
