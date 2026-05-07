/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.Probability.Independence.IndepFun
public import LeanMachineLearning.SequentialLearning.Algorithm

/-!
# Random Sampling

Implementation of the _Random Sampling_ algorithm, which samples from a fixed probability
measure at each iteration.

## Main definitions

* `randomSampling`: The random sampling algorithm that samples from a fixed distribution at
each iteration.

## Main statements

* `hasLaw_action`: Each action follows the distribution μ.
* `iIndep_action`: Actions are mutually independent across time steps.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Finset ENNReal Filter

open scoped Topology

namespace Learning

variable {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β] [StandardBorelSpace α] [Nonempty α]
  [StandardBorelSpace β] [Nonempty β] {μ : Measure α} [IsProbabilityMeasure μ] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

open Set in
/-- The _Random Sampling_ algorithm, which samples from a fixed probability
measure at each iteration. -/
@[simps]
noncomputable def randomSampling (μ : Measure α) [IsProbabilityMeasure μ] : Algorithm α β where
  policy _ := Kernel.const _ μ
  p0 := μ

namespace randomSampling

variable {A : ℕ → Ω → α} {R : ℕ → Ω → β} {env : Environment α β}

/-- Each action follows the distribution μ. -/
lemma hasLaw_action (h : IsAlgEnvSeq A R (randomSampling μ) env P) (n : ℕ) :
    HasLaw (A n) μ P := by
  by_cases hn : n = 0
  · rw [hn]
    exact h.hasLaw_action_zero
  · push Not at hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact (h.hasCondDistrib_action k).hasLaw_of_const

/-- Actions are mutually independent. -/
lemma iIndep_action (h : IsAlgEnvSeq A R (randomSampling μ) env P) :
    iIndepFun A P := by
  have hA := h.measurable_A
  rw [iIndepFun_nat_iff_forall_indepFun (by fun_prop)]
  intro n
  have condDistrib_eq := (h.hasCondDistrib_action n).condDistrib_eq
  simp only [randomSampling_policy] at condDistrib_eq
  have law_eq := (hasLaw_action h (n + 1)).map_eq
  rw [← law_eq, ← indepFun_iff_condDistrib_eq_const ?_ (by fun_prop)] at condDistrib_eq
  · have meas_fst : Measurable (fun (f : Iic n → α × β) ↦ (fun i ↦ (f i).1)) := by
      fun_prop
    exact (condDistrib_eq.comp meas_fst measurable_id).symm
  · exact (IsAlgEnvSeq.measurable_hist (h.measurable_A) (h.measurable_R) n).aemeasurable

end randomSampling

end Learning
