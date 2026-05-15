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

An interface for decision-based optimization algorithms, which sample from a set of potential
maximizers using a fixed probability measure at each iteration. This module defines the `Decision`
algorithm, which relies on a user-defined set of potential maximizers and a probability measure to
sample from it.

## Main definitions

* `potential_max_kernel`: The Markov kernel that samples from the set of potential maximizers
according to a given measure `μ`.
* `Decision`: The Decision algorithm that starts by sampling from the initial measure `μ` and then
samples from the set of potential maximizers at each iteration using the defined kernel.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (μ : Measure α) [IsProbabilityMeasure μ] {potential_max : (n : ℕ) → ((Iic n) → α × β) → Set α}
  (measurableSet_potential_max_prod :
    ∀ n, MeasurableSet {p : (Iic n → α × β) × α | p.2 ∈ potential_max n p.1}) {n : ℕ}

include measurableSet_potential_max_prod in
lemma measurable_potential_max_inter {s : Set α} (hs : MeasurableSet s) :
    Measurable (fun data : Iic n → α × β ↦ μ (potential_max n data ∩ s)) := by
  set E := {p : (Iic n → α × β) × α | p.2 ∈ potential_max n p.1 ∩ s}
  have hE_meas : MeasurableSet E :=
    (measurableSet_potential_max_prod n).inter
      <| measurableSet_preimage measurable_snd hs
  exact measurable_measure_prodMk_left hE_meas

/-- The Markov kernel that samples from the set of potential maximizers according to a given
measure `μ`. -/
noncomputable def potential_max_kernel : Kernel (Iic n → α × β) α := by
  refine ⟨fun data ↦ cond μ <| potential_max n data, ?_⟩
  rw [Measure.measurable_measure]
  intro s hs
  simp only [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul]
  refine Measurable.mul ?_ ?_
  · refine Measurable.inv ?_
    convert measurable_potential_max_inter μ measurableSet_potential_max_prod (MeasurableSet.univ)
    simp [Set.inter_univ]
  · simp_rw [μ.restrict_apply hs]
    convert measurable_potential_max_inter μ measurableSet_potential_max_prod hs using 1
    simp [Set.inter_comm]

/- We need that the set of potential maximizers has non-zero measure at each iteration,
ensuring that the algorithm can sample from it. -/
variable (h : ∀ n (data : Iic n → α × β), μ (potential_max n data) ≠ 0)

/-- The interface for decision-based optimization algorithms. -/
noncomputable def Decision : Algorithm α β where
  policy _ := potential_max_kernel μ measurableSet_potential_max_prod
  p0 := μ
  h_policy n := ⟨fun data => cond_isProbabilityMeasure (h n data)⟩
