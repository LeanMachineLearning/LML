/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Deterministic

/-!
# The algorithm playing a fixed sequence

`Algorithm.ofSeq x` plays the action `x n` at round `n`, whatever the history and the
observation: the deterministic algorithm that reads neither the history nor the observation (an
open-loop algorithm, or *fixed design*).

## Main definitions

* `Learning.Algorithm.ofSeq x : Algorithm 𝓞 𝓐 𝓨`: the deterministic algorithm playing the
  sequence `x`.

## Main statements

* `Learning.IsAlgEnvSeq.action_ae_all_eq_ofSeq`: in an algorithm-environment sequence of
  `Algorithm.ofSeq x`, the actions are almost surely the sequence `x`.

Adapted from the LMLPapers project (same author).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}

/-- The deterministic algorithm that plays the fixed sequence `x : ℕ → 𝓐` regardless of the
observations and feedbacks (a *fixed design*). -/
noncomputable def Algorithm.ofSeq (x : ℕ → 𝓐) : Algorithm 𝓞 𝓐 𝓨 :=
  Algorithm.deterministic (fun n _ ↦ x n) fun _ ↦ measurable_const

/-- The defining formula of `Algorithm.ofSeq`. -/
lemma Algorithm.ofSeq_def (x : ℕ → 𝓐) :
    (Algorithm.ofSeq x : Algorithm 𝓞 𝓐 𝓨)
      = Algorithm.deterministic (fun n _ ↦ x n) fun _ ↦ measurable_const :=
  (rfl)

instance (x : ℕ → 𝓐) : (Algorithm.ofSeq x : Algorithm 𝓞 𝓐 𝓨).IsDeterministic :=
  inferInstanceAs (Algorithm.deterministic _ _).IsDeterministic

@[simp]
lemma Algorithm.policy_ofSeq (x : ℕ → 𝓐) (n : ℕ) :
    (Algorithm.ofSeq x : Algorithm 𝓞 𝓐 𝓨).policy n
      = Kernel.deterministic (fun _ ↦ x n) measurable_const := (rfl)

/-- The actions of an algorithm-environment sequence of the algorithm playing `x` are almost
surely `x`. -/
lemma IsAlgEnvSeq.action_ae_all_eq_ofSeq [MeasurableEq 𝓐] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [SFinite P] {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
    {x : ℕ → 𝓐} {env : Environment 𝓞 𝓐 𝓨} (h : IsAlgEnvSeq O X Y (Algorithm.ofSeq x) env P) :
    ∀ᵐ ω ∂P, ∀ n, X n ω = x n :=
  IsAlgEnvSeq.action_ae_all_eq_deterministic h

end Learning
