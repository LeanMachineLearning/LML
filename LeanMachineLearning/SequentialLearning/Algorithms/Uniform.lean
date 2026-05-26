/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber, Rémy Degenne
-/
module

public import LeanMachineLearning.MeasureTheory.Measure.AbsolutelyContinuous
public import LeanMachineLearning.SequentialLearning.AlgorithmDensity

/-! # The Uniform algorithm

We introduce an algorithm that chooses actions uniformly at random.

## Main definitions

* `uniformAlgorithm hK`: a uniform algorithm with actions in `Fin K` given `hK : 0 < K`.

## Main results

* `absolutelyContinuous_uniformAlgorithm`: every algorithm with actions in `Fin K` is absolutely
  continuous with respect to the uniform algorithm with the same type of feedback.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning

open scoped Algorithm

namespace Bandits

variable {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} {K : ℕ}

/-- The Uniform algorithm: actions are chosen uniformly at random. -/
noncomputable
def uniformAlgorithm (hK : 0 < K) : Algorithm (Fin K) 𝓨 :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  have : IsProbabilityMeasure (uniformOn (Set.univ : Set (Fin K))) :=
    isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty
  { policy _ := Kernel.const _ (uniformOn Set.univ)
    p0 := uniformOn Set.univ }

lemma absolutelyContinuous_uniformAlgorithm (hK : 0 < K) (alg : Algorithm (Fin K) 𝓨) :
    alg ≪ₐ uniformAlgorithm hK where
  p0 := Measure.absolutelyContinuous_of_measure_singleton_ne_zero
    (by simp [uniformAlgorithm, uniformOn, ← pos_iff_ne_zero, cond_pos_of_inter_ne_zero])
  policy n h := Measure.absolutelyContinuous_of_measure_singleton_ne_zero
    (by simp [uniformAlgorithm, uniformOn, ← pos_iff_ne_zero, cond_pos_of_inter_ne_zero])

end Bandits
