/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.SequentialLearning.Algorithm

import LeanMachineLearning.ForMathlib.Probability.Independence.IndepFun

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

variable {𝓞 𝓐 𝓨 Ω : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}
  {mΩ : MeasurableSpace Ω} {μ : Measure 𝓐} [IsProbabilityMeasure μ]
  {P : Measure Ω} [IsProbabilityMeasure P]

open Set in
/-- The _Random Sampling_ algorithm, which samples from a fixed probability
measure at each iteration. -/
@[simps]
noncomputable def randomSampling (μ : Measure 𝓐) [IsProbabilityMeasure μ] :
    Algorithm 𝓞 𝓐 𝓨 where
  policy _ := Kernel.const _ μ

namespace randomSampling

variable {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {env : Environment 𝓞 𝓐 𝓨}

/-- Each action follows the distribution μ. -/
lemma hasLaw_action (h : IsAlgEnvSeq O A Y (randomSampling μ) env P) (n : ℕ) :
    HasLaw (A n) μ P :=
  (h.hasCondDistrib_action n).hasLaw_of_const

/-- Actions are mutually independent. -/
lemma iIndep_action (h : IsAlgEnvSeq O A Y (randomSampling μ) env P) :
    iIndepFun A P := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  rw [iIndepFun_nat_iff_forall_indepFun (by fun_prop)]
  intro n
  have map_eq := (h.hasCondDistrib_action (n + 1)).map_eq
  simp only [randomSampling_policy, Measure.compProd_const] at map_eq
  have law_eq : P.map (A (n + 1)) = μ := (hasLaw_action h (n + 1)).map_eq
  rw [← law_eq, ← indepFun_iff_map_prod_eq_prod_map_map] at map_eq
  · change A (n + 1) ⟂ᵢ[P] (fun (p : Hist 𝓞 𝓐 𝓨 (n + 1) × 𝓞) (i : Iic n) ↦
      (p.1 ⟨i.1, Nat.lt_succ_of_le (mem_Iic.mp i.2)⟩).action) ∘
      (fun ω ↦ (history O A Y (n + 1) ω, O (n + 1) ω))
    refine map_eq.symm.comp measurable_id (by fun_prop)
  · exact ((h.measurable_history (n + 1)).prodMk (h.measurable_obs (n + 1))).aemeasurable
  · exact (h.measurable_action (n + 1)).aemeasurable

end randomSampling

end Learning
