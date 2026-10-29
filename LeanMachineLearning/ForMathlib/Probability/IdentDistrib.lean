/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.ForMathlib.Probability.ConditionalProbability
public import Mathlib.Probability.IdentDistrib

/-!
# Lemmas about identically distributed random variables

## Main statements

* `identDistrib_map_right_iff`, `identDistrib_map_left_iff`: identical distribution with a random
  variable under an image measure.
* `identDistrib_of_forall_identDistrib_cond`: two random variables which are identically
  distributed conditionally on each atom of a countable measurable partition are identically
  distributed.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

section Map

variable {Ω Ω' E : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mE : MeasurableSpace E} {μ ν : Measure Ω}

lemma identDistrib_map_right_iff {X : Ω → E} {Y : Ω' → E} {f : Ω → Ω'}
    (hf : AEMeasurable f ν) (hX : AEMeasurable X μ) (hY : AEMeasurable Y (ν.map f)) :
    IdentDistrib X Y μ (ν.map f) ↔ IdentDistrib X (Y ∘ f) μ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · constructor
    · exact hX
    · fun_prop
    · rw [h.map_eq, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hf]
  · constructor
    · exact hX
    · fun_prop
    · rw [h.map_eq, AEMeasurable.map_map_of_aemeasurable hY hf]

lemma identDistrib_comm (X : Ω → E) (Y : Ω' → E) {ν : Measure Ω'} :
    IdentDistrib X Y μ ν ↔ IdentDistrib Y X ν μ :=
  ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩

lemma identDistrib_map_left_iff {X : Ω → E} {Y : Ω' → E} {f : Ω → Ω'}
    (hf : AEMeasurable f ν) (hX : AEMeasurable X μ) (hY : AEMeasurable Y (ν.map f)) :
    IdentDistrib Y X (ν.map f) μ ↔ IdentDistrib (Y ∘ f) X ν μ := by
  rw [identDistrib_comm Y, identDistrib_comm _ X]
  exact identDistrib_map_right_iff hf hX hY

end Map

section Cond

variable {Ω 𝓧 ι : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {P : Measure Ω}
  [Countable ι] {mι : MeasurableSpace ι} [MeasurableSingletonClass ι]

/-- Two random variables which are identically distributed conditionally on each atom of a
countable measurable partition are identically distributed. -/
lemma identDistrib_of_forall_identDistrib_cond [IsFiniteMeasure P] {g : Ω → ι}
    (hg : Measurable g) {X Y : Ω → 𝓧} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h : ∀ i, IdentDistrib X Y P[|g ⁻¹' {i}] P[|g ⁻¹' {i}]) :
    IdentDistrib X Y P P where
  aemeasurable_fst := hX
  aemeasurable_snd := hY
  map_eq := by
    rw [← Measure.sum_meas_smul_cond_fiber hg P] at hX hY ⊢
    simp_rw [Measure.map_sum hX, Measure.map_sum hY]
    congr with i : 1
    rw [Measure.map_smul _ (h i).aemeasurable_fst, Measure.map_smul _ (h i).aemeasurable_snd,
      (h i).map_eq]

end Cond

end ProbabilityTheory
