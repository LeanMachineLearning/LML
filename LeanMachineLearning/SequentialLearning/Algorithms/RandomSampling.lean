/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepFun
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

variable {𝓐 𝓨 Ω : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨} {mΩ : MeasurableSpace Ω}
  {μ : Measure 𝓐} [IsProbabilityMeasure μ]
  {P : Measure Ω} [IsProbabilityMeasure P]

open Set in
/-- The _Random Sampling_ algorithm, which samples from a fixed probability
measure at each iteration. -/
@[simps]
noncomputable def randomSampling (μ : Measure 𝓐) [IsProbabilityMeasure μ] : Algorithm 𝓐 𝓨 where
  policy _ := Kernel.const _ μ
  p0 := μ

namespace randomSampling

variable {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {env : Environment 𝓐 𝓨}

/-- Each action follows the distribution μ. -/
lemma hasLaw_action (h : IsAlgEnvSeq A Y (randomSampling μ) env P) (n : ℕ) :
    HasLaw (A n) μ P := by
  by_cases hn : n = 0
  · rw [hn]
    exact h.hasLaw_action_zero
  · push Not at hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact (h.hasCondDistrib_action k).hasLaw_of_const

/-- Actions are mutually independent. -/
lemma iIndep_action (h : IsAlgEnvSeq A Y (randomSampling μ) env P) :
    iIndepFun A P := by
  have hA := h.measurable_action
  rw [iIndepFun_nat_iff_forall_indepFun (by fun_prop)]
  intro n
  have map_eq := (h.hasCondDistrib_action n).map_eq
  simp only [randomSampling_policy, Measure.compProd_const] at map_eq
  have law_eq : P.map (A (n + 1)) = μ := (hasLaw_action h (n + 1)).map_eq
  rw [← law_eq, ← indepFun_iff_map_prod_eq_prod_map_map] at map_eq
  · change A (n + 1) ⟂ᵢ[P] (fun (f : Iic n → 𝓐 × 𝓨) ↦ (fun i ↦ (f i).1))∘ (history A Y n)
    refine map_eq.symm.comp measurable_id (by fun_prop)
  · exact (h.measurable_history n).aemeasurable
  · exact (h.measurable_action (n + 1)).aemeasurable

end randomSampling

end Learning
