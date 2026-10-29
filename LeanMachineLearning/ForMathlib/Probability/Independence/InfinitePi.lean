/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Probability.Independence.InfinitePi

/-! # Lemmas about independence and infinite products

## Main statements

* `indepFun_proj_infinitePi_infinitePi`: under a product of product measures, two distinct
  columns of coordinates are independent.
* `iIndepFun_map_iff`: independence of a family of random variables under an image measure.
-/

@[expose] public section

open MeasureTheory Measure ProbabilityTheory Set Function

namespace ProbabilityTheory

section Proj

variable {ι κ : Type*} {𝓧 : ι → κ → Type*} [m𝓧 : ∀ i j, MeasurableSpace (𝓧 i j)]
    {μ : (i : ι) → (j : κ) → Measure (𝓧 i j)} [∀ i j, IsProbabilityMeasure (μ i j)]

lemma indepFun_proj_infinitePi_infinitePi {a b : κ} (h : a ≠ b) :
    IndepFun (fun ω i ↦ ω i a) (fun ω i ↦ ω i b) (infinitePi (fun i ↦ infinitePi (μ i))) := by
  simp_rw [IndepFun_iff_Indep, MeasurableSpace.comap_pi]
  have hd : Disjoint (range fun i : ι ↦ (i, a)) (range fun i ↦ (i, b)) := by
    simp [disjoint_range_iff, h]
  convert indep_iSup_of_disjoint (fun _ ↦ Measurable.comap_le (by fun_prop))
    (iIndepFun_uncurry_infinitePi' (X := fun _ _ x ↦ x) μ (by fun_prop)) hd
  all_goals rw [iSup_range]

end Proj

section Map

variable {Ω Ω' E ι : Type*} [Countable ι] {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mE : MeasurableSpace E} {μ : Measure Ω}

lemma iIndepFun_map_iff [IsProbabilityMeasure μ] {X : ι → Ω' → E} {f : Ω → Ω'}
    (hf : AEMeasurable f μ) (hX : ∀ n, AEMeasurable (X n) (μ.map f)) :
    iIndepFun X (μ.map f) ↔ iIndepFun (fun n ↦ X n ∘ f) μ := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀' hX,
    iIndepFun_iff_map_fun_eq_infinitePi_map₀' (by fun_prop)]
  rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hf]
  congr! 3
  rw [AEMeasurable.map_map_of_aemeasurable (hX _) hf]

end Map

end ProbabilityTheory
