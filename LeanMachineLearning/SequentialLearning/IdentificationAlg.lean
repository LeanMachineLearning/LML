/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.StoppedHistory

/-!
# Identification algorithms: sampling rule, stopping rule, output rule

An *identification algorithm* `A : IdentAlg 𝓞 𝓐 𝓨 𝓓` with outputs in `𝓓` is a sampling rule
`A.alg : Algorithm 𝓞 𝓐 𝓨` together with

* a *stopping rule* `A.stopSet`, a measurable set of histories of variable length: the algorithm
  stops after `n` rounds if the history of these `n` rounds belongs to `A.stopSet`;
* an *output rule* `A.output`, a Markov kernel from histories of variable length to `𝓓`: the
  distribution of the output given the history of the rounds played.

A *run* of the algorithm in an environment `env`, on a probability space `(Ω, P)`, consists of
observation, action and feedback processes `O, X, Y` forming an algorithm-environment sequence
for `A.alg` and `env` (`IsAlgEnvSeq`) and an output `out : Ω → 𝓓` whose conditional law given the
history at the stopping time is the output rule (`IdentAlg.IsRun`).

The law of the output of a run is determined by `A` and `env`: it is `A.outputMeasure env`, see
`IdentAlg.IsRun.hasLaw_output`. Properties of the algorithm are stated in terms of this law: `A`
is *PAC at level `δ`* (`IdentAlg.IsPAC`) for a family of environments `env θ` and a badness
predicate `bad θ` if, for every `θ`, the output in `env θ` is `bad θ` with probability at most `δ`.

## Main definitions

* `IdentAlg 𝓞 𝓐 𝓨 𝓓`: the structure.
* `IdentAlg.stoppingTime A O X Y : Ω → ℕ∞`: the number of rounds played, a hitting time.
* `IdentAlg.stoppedHist A O X Y : Ω → Σ n, Hist 𝓞 𝓐 𝓨 n`: the history at the stopping time.
* `IdentAlg.IsRun A env O X Y out P`: `(O, X, Y, out)` is a run of `A` in `env` on `(Ω, P)`.
* `IdentAlg.outputMeasure A env : Measure 𝓓`: the law of the output of `A` in `env`.
* `IdentAlg.IsPAC A env bad δ`: for every parameter `θ`, the output of `A` in `env θ` is
  `bad θ` with probability at most `δ`.

Time is `0`-indexed: after `n` rounds the actions `a_0, …, a_{n-1}` have been played.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped ENat

namespace Learning

variable {𝓞 𝓐 𝓨 𝓓 Ω : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓓 : MeasurableSpace 𝓓} {mΩ : MeasurableSpace Ω}
  {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

/-- An identification algorithm with outputs in `𝓓`: a sampling rule `alg`, a stopping rule
`stopSet` (the algorithm stops after `n` rounds if the history of these rounds belongs to
`stopSet`) and an output rule `output`, a Markov kernel giving the distribution of the output
given the history of the rounds played. -/
structure IdentAlg (𝓞 𝓐 𝓨 𝓓 : Type*) [MeasurableSpace 𝓞] [MeasurableSpace 𝓐]
    [MeasurableSpace 𝓨] [MeasurableSpace 𝓓] where
  /-- The sampling rule. -/
  alg : Algorithm 𝓞 𝓐 𝓨
  /-- The stopping rule: the algorithm stops after `n` rounds if the history of these rounds
  belongs to `stopSet`. -/
  stopSet : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)
  /-- The stopping rule is measurable. -/
  measurableSet_stopSet : MeasurableSet stopSet
  /-- The output rule: distribution of the output given the history of the rounds played. -/
  output : Kernel (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) 𝓓
  /-- The output rule is a Markov kernel. -/
  [isMarkovKernel_output : IsMarkovKernel output]

namespace IdentAlg

variable {A : IdentAlg 𝓞 𝓐 𝓨 𝓓} {env : Environment 𝓞 𝓐 𝓨} {out : Ω → 𝓓} {P : Measure Ω}

instance : IsMarkovKernel A.output := A.isMarkovKernel_output

/-- The stopping time of `A` on the observation, action and feedback processes `O`, `X`, `Y`: the
number of rounds played, that is the first `n` such that the history of the first `n` rounds
belongs to the stopping rule `A.stopSet` (`⊤` if there is none). -/
noncomputable def stoppingTime (A : IdentAlg 𝓞 𝓐 𝓨 𝓓)
    (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) :
    Ω → ℕ∞ :=
  hittingAfter (sigmaHistory O X Y) A.stopSet 0

lemma stoppingTime_def : A.stoppingTime O X Y = hittingAfter (sigmaHistory O X Y) A.stopSet 0 := rfl

/-- The history of the rounds played by an identification algorithm `A`, as a history of variable
length: the history stopped at `A.stoppingTime O X Y`
(the history of an arbitrary number of rounds if `A` never stops). -/
noncomputable def stoppedHist (A : IdentAlg 𝓞 𝓐 𝓨 𝓓)
    (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) :
    Ω → Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n :=
  stoppedValue (sigmaHistory O X Y) (A.stoppingTime O X Y)

lemma stoppedHist_def :
    A.stoppedHist O X Y = stoppedValue (sigmaHistory O X Y) (A.stoppingTime O X Y) := rfl

/-- The law of the output of an identification algorithm in an environment. -/
noncomputable def outputMeasure (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (env : Environment 𝓞 𝓐 𝓨) : Measure 𝓓 :=
  A.output ∘ₘ stoppedHistMeasure A.alg env A.stopSet
deriving IsProbabilityMeasure

/-- `(O, X, Y, out)` is a *run* of the identification algorithm `A` in the environment `env` on
the probability space `(Ω, P)`: the observation, action and feedback processes `O`, `X`, `Y` form
an algorithm-environment sequence for the sampling rule `A.alg` and `env`, and the output `out` has
conditional law `A.output` given the history at the stopping time. -/
structure IsRun (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (env : Environment 𝓞 𝓐 𝓨)
    (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (out : Ω → 𝓓)
    (P : Measure Ω := by volume_tac) [IsFiniteMeasure P] : Prop where
  /-- The actions and feedbacks are generated by the sampling rule in the environment. -/
  isAlgEnvSeq : IsAlgEnvSeq O X Y A.alg env P
  /-- The output is drawn from the output rule applied to the history at the stopping time. -/
  hasCondDistrib_output : HasCondDistrib out (A.stoppedHist O X Y) A.output P

/-- The stopping time of an identification algorithm `A` is a stopping time of the history
filtration of any algorithm-environment sequence `O`, `X`, `Y`.
Most often used with `alg = A.alg`. -/
lemma isStoppingTime_stoppingTime (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) {alg : Algorithm 𝓞 𝓐 𝓨}
    [IsFiniteMeasure P] (h : IsAlgEnvSeq O X Y alg env P) :
    IsStoppingTime h.filtration (A.stoppingTime O X Y) :=
  h.adapted_sigmaHistory.isStoppingTime_hittingAfter A.measurableSet_stopSet

lemma stoppedHist_mem_stopSet_of_ne_top {ω : Ω} (h : A.stoppingTime O X Y ω ≠ ⊤) :
    A.stoppedHist O X Y ω ∈ A.stopSet :=
  hittingAfter_mem_set_of_ne_top h

/-- The history at the stopping time of any run of `A` in `env` has law
`stoppedHistMeasure A.alg env A.stopSet`. -/
lemma IsRun.hasLaw_stoppedHist [IsProbabilityMeasure P] (h : A.IsRun env O X Y out P) :
    HasLaw (A.stoppedHist O X Y) (stoppedHistMeasure A.alg env A.stopSet) P :=
  h.isAlgEnvSeq.hasLaw_stoppedValue_sigmaHistory A.measurableSet_stopSet

/-- The output of any run of `A` in `env` has law `A.outputMeasure env`. -/
lemma IsRun.hasLaw_output [IsProbabilityMeasure P] (h : A.IsRun env O X Y out P) :
    HasLaw out (A.outputMeasure env) P := by
  have h_comp := h.hasCondDistrib_output.hasLaw_comp
  rwa [h.hasLaw_stoppedHist.map_eq] at h_comp

section IsPAC

/-- `A` is *PAC at level `δ`* for the family of environments `env : Θ → Environment 𝓞 𝓐 𝓨` and
the predicate `bad : Θ → 𝓓 → Prop` if, for every `θ`, the output of `A` in `env θ` is
`bad θ` with probability at most `δ`.
See `IsPAC.measureReal_not_good_of_isRun` for the corresponding statement about any run of `A`. -/
def IsPAC {Θ : Type*} (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (env : Θ → Environment 𝓞 𝓐 𝓨)
    (bad : Θ → 𝓓 → Prop) (δ : ℝ) : Prop :=
  ∀ θ, (A.outputMeasure (env θ)).real {d | bad θ d} ≤ δ

/-- For a PAC algorithm at level `δ`, the output of any run in `env θ` is `bad θ` with
probability at most `δ`. -/
lemma IsPAC.measureReal_bad_of_isRun {Θ : Type*} {env : Θ → Environment 𝓞 𝓐 𝓨}
    {bad : Θ → 𝓓 → Prop} {δ : ℝ} [IsProbabilityMeasure P]
    (hA : A.IsPAC env bad δ) {θ : Θ} (hbad : MeasurableSet {d | bad θ d})
    (h : A.IsRun (env θ) O X Y out P) :
    P.real {ω | bad θ (out ω)} ≤ δ := by
  rw [h.hasLaw_output.measureReal_eq hbad]
  exact hA θ

end IsPAC

end IdentAlg

end Learning
