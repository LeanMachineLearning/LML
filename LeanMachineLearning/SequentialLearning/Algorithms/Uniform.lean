/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.MeasureTheory.Measure.AbsolutelyContinuous
public import LeanMachineLearning.SequentialLearning.Algorithm

/-! # The Uniform Algorithm -/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning

namespace Bandits

variable {K : ℕ}

/-- The Uniform algorithm: actions are chosen uniformly at random. -/
noncomputable
def uniformAlgorithm (hK : 0 < K) : Algorithm (Fin K) ℝ :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  have : IsProbabilityMeasure (uniformOn (Set.univ : Set (Fin K))) :=
    isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty
  { policy _ := Kernel.const _ (uniformOn Set.univ)
    p0 := uniformOn Set.univ }

lemma absolutelyContinuous_uniformAlgorithm (hK : 0 < K) (alg : Algorithm (Fin K) ℝ) :
    alg ≪ₐ uniformAlgorithm hK where
  p0 := Measure.absolutelyContinuous_of_measure_singleton_ne_zero
    (by simp [uniformAlgorithm, uniformOn, ← pos_iff_ne_zero, cond_pos_of_inter_ne_zero])
  policy n h := Measure.absolutelyContinuous_of_measure_singleton_ne_zero
    (by simp [uniformAlgorithm, uniformOn, ← pos_iff_ne_zero, cond_pos_of_inter_ne_zero])

end Bandits
