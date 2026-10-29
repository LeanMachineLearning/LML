/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Sigma
public import LeanMachineLearning.ForMathlib.Probability.HasLaw
public import LeanMachineLearning.ForMathlib.Probability.Process.HittingTime
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

/-!
# Stopping rules and stopped histories

A *stopping rule* is a measurable set `S : Set (Σ n, Hist 𝓞 𝓐 𝓨 n)` of histories of variable
length: the interaction stops after `n` rounds if the history of these `n` rounds belongs to `S`.

## Main definitions

* `Learning.sigmaHistory O X Y n : Ω → Σ n, Hist 𝓞 𝓐 𝓨 n`: the history of the first `n`
  rounds, as a history of variable length;
* `Learning.stoppedHistMeasure alg env S`: the law of the history stopped by `S`.

## Main statements

* `IsAlgEnvSeq.hasLaw_stoppedValue_sigmaHistory`: the law of the history stopped by `S` is
  `stoppedHistMeasure alg env S`, hence it is determined by the algorithm and the environment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 Ω : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {mΩ : MeasurableSpace Ω}
  {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}
  {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {S : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)}
  {τ : Ω → WithTop ℕ}

/-- The history of the first `n` rounds, as a history of variable length in the sigma type
`Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n`. -/
def sigmaHistory (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (n : ℕ) (ω : Ω) :
    Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n :=
  ⟨n, history O X Y n ω⟩

lemma sigmaHistory_apply (n : ℕ) (ω : Ω) : sigmaHistory O X Y n ω = ⟨n, history O X Y n ω⟩ := rfl

@[simp] lemma fst_sigmaHistory (n : ℕ) (ω : Ω) : (sigmaHistory O X Y n ω).1 = n := rfl

section Measurability

variable (hO : ∀ n, Measurable (O n)) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
include hO hX hY

@[fun_prop]
lemma measurable_sigmaHistory (n : ℕ) : Measurable (sigmaHistory O X Y n) :=
  (measurable_sigmaMk n).comp (measurable_history hO hX hY n)

@[fun_prop]
lemma measurable_hittingAfter_sigmaHistory (hS : MeasurableSet S) :
    Measurable (hittingAfter (sigmaHistory O X Y) S 0) := by
  refine measurable_to_countable' fun x ↦ ?_
  induction x with
  | top =>
    have : hittingAfter (sigmaHistory O X Y) S 0 ⁻¹' {⊤} =
        ⋂ n, sigmaHistory O X Y n ⁻¹' Sᶜ := by ext; simp [hittingAfter_eq_top_iff]
    rw [this]
    exact MeasurableSet.iInter fun n ↦ measurable_sigmaHistory hO hX hY n hS.compl
  | coe n =>
    have : hittingAfter (sigmaHistory O X Y) S 0 ⁻¹' {WithTop.some n} =
        sigmaHistory O X Y n ⁻¹' S ∩ ⋂ j < n, sigmaHistory O X Y j ⁻¹' Sᶜ := by
      ext ω
      rw [Set.mem_preimage, Set.mem_singleton_iff, hittingAfter_eq_coe_iff]
      simp
    rw [this]
    exact (measurable_sigmaHistory hO hX hY n hS).inter
      (.iInter fun j ↦ .iInter fun _ ↦ (measurable_sigmaHistory hO hX hY j hS).compl)

@[fun_prop]
lemma measurable_stoppedValue_sigmaHistory (hτ : Measurable τ) :
    Measurable (stoppedValue (sigmaHistory O X Y) τ) :=
  Measurable.sigmaMk (by fun_prop) (measurable_history hO hX hY)

end Measurability

section Filtration

variable {P : Measure Ω}

-- TODO: it is also adapted for the filtration at the time before?
lemma IsAlgEnvSeq.adapted_sigmaHistory (h : IsAlgEnvSeq O X Y alg env P) :
    Adapted h.filtration (sigmaHistory O X Y) :=
  fun n ↦ (measurable_sigmaMk n).comp (h.adapted_history n)

end Filtration

section StoppedHistMeasure

/-! ### The law of the stopped history

The stopping time and the stopped history are functions of the trajectory, whose law is
determined by the algorithm and the environment (`IsAlgEnvSeq.hasLaw_trajectory`). Hence the law
of the stopped history is determined by the algorithm and the environment: it is the law
`stoppedHistMeasure alg env S` of the stopped history on the canonical space `trajMeasure`. -/

/-- The law of the history stopped by the stopping rule `S`, for the algorithm `alg` in the
environment `env`: the law of the stopped history on the canonical space `trajMeasure alg env`.
This is the law of the stopped history for any algorithm-environment sequence
(`IsAlgEnvSeq.hasLaw_stoppedValue_sigmaHistory`). -/
noncomputable def stoppedHistMeasure (alg : Algorithm 𝓞 𝓐 𝓨) (env : Environment 𝓞 𝓐 𝓨)
    (S : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) :
    Measure (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) :=
  (trajMeasure alg env).map
    (stoppedValue (sigmaHistory IT.obs IT.action IT.feedback)
      (hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0))
deriving IsProbabilityMeasure

/-- The law of the history stopped by `S` under any algorithm-environment sequence for `alg` and
`env` is `stoppedHistMeasure alg env S`. -/
lemma IsAlgEnvSeq.hasLaw_stoppedValue_sigmaHistory {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O X Y alg env P) (hS : MeasurableSet S) :
    HasLaw (stoppedValue (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0))
      (stoppedHistMeasure alg env S) P :=
  (hasLaw_map (measurable_stoppedValue_sigmaHistory IT.measurable_obs IT.measurable_action
    IT.measurable_feedback
      (measurable_hittingAfter_sigmaHistory IT.measurable_obs IT.measurable_action
        IT.measurable_feedback hS)).aemeasurable).comp h.hasLaw_trajectory

end StoppedHistMeasure

end Learning
