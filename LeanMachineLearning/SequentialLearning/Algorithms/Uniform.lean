/-
Copyright (c) 2026 Paulo Rauber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Rauber, Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.AlgorithmDensity
public import LeanMachineLearning.SequentialLearning.Algorithms.RandomSampling.Basic

import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-! # The Uniform algorithm

An algorithm that chooses actions uniformly at random in every situation.

## Main definitions

* `Algorithm.uniform`: a uniform algorithm with actions in a finite non-empty type `𝓐`.

## Main statements

* `Algorithm.absolutelyContinuous_uniform`: every algorithm with actions in `𝓐` is absolutely
  continuous with respect to the uniform algorithm with the same type of feedback.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning

open scoped Algorithm

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}

/-- The Uniform algorithm: actions are chosen uniformly at random. -/
noncomputable
def Algorithm.uniform [Finite 𝓐] [Nonempty 𝓐] : Algorithm 𝓞 𝓐 𝓨 :=
  Algorithm.const (uniformOn Set.univ)

instance [Finite 𝓐] [Nonempty 𝓐] : (Algorithm.uniform : Algorithm 𝓞 𝓐 𝓨).IsMarkov :=
  inferInstanceAs (Algorithm.const (uniformOn Set.univ) : Algorithm 𝓞 𝓐 𝓨).IsMarkov

lemma Algorithm.absolutelyContinuous_uniform [Finite 𝓐] [Nonempty 𝓐] (alg : Algorithm 𝓞 𝓐 𝓨) :
    alg ≪ₐ Algorithm.uniform where
  policy n h := Measure.absolutelyContinuous_of_measure_singleton_ne_zero
    (by simp [Algorithm.uniform, uniformOn, ← pos_iff_ne_zero, cond_pos_of_inter_ne_zero])

end Learning
