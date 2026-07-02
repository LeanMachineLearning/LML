/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber, Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import LeanMachineLearning.SequentialLearning.AlgorithmDensity
public import LeanMachineLearning.SequentialLearning.Algorithms.RandomSampling.Basic

/-! # The Uniform algorithm

An algorithm that chooses actions uniformly at random in every situation.

## Main definitions

* `uniformAlgorithm`: a uniform algorithm with actions in a finite non-empty type `𝓐`.

## Main results

* `absolutelyContinuous_uniformAlgorithm`: every algorithm with actions in `𝓐` is absolutely
  continuous with respect to the uniform algorithm with the same type of feedback.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning

open scoped Algorithm

namespace Learning

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}

/-- The Uniform algorithm: actions are chosen uniformly at random. -/
noncomputable
def uniformAlgorithm [Finite 𝓐] [Nonempty 𝓐] : Algorithm 𝓐 𝓨 := randomSampling (uniformOn Set.univ)

lemma absolutelyContinuous_uniformAlgorithm [Finite 𝓐] [Nonempty 𝓐] {alg : Algorithm 𝓐 𝓨} :
    alg ≪ₐ uniformAlgorithm where
  p0 := Measure.absolutelyContinuous_of_measure_singleton_ne_zero
    (by simp [uniformAlgorithm, uniformOn, ← pos_iff_ne_zero, cond_pos_of_inter_ne_zero])
  policy n h := Measure.absolutelyContinuous_of_measure_singleton_ne_zero
    (by simp [uniformAlgorithm, uniformOn, ← pos_iff_ne_zero, cond_pos_of_inter_ne_zero])

end Learning
