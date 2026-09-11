/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Deterministic
public import LeanMachineLearning.SequentialLearning.StoppedHistory

/-!
# Identification algorithms: sampling rule, stopping rule, output rule

An *identification algorithm* with outputs in `𝓞` is an LML sampling rule
`alg : Algorithm Unit 𝓐 𝓨` (an algorithm without observations: LML's observation type is `Unit`,
and `𝓞` denotes here the type of *outputs*) together with

* a *stopping rule*: `stop n h` says that the algorithm stops after `n` rounds when the history
  of these rounds is `h : Hist Unit 𝓐 𝓨 n` (each `{h | stop n h}` is measurable);
* an *output rule*: for each `n`, a Markov kernel `output n` from histories of length `n` to `𝓞`
  (the distribution of the output when the algorithm stops after `n` rounds).

A *run* of the algorithm in an environment `env`, on a probability space `(Ω, P)`, consists of
observation, action and feedback processes `O, X, Y` (with `O` trivially `Unit`-valued) forming an
algorithm-environment sequence for `alg` and `env` (LML `IsAlgEnvSeq`) and an output `out : Ω → 𝓞`
whose conditional law given the history at the
stopping time is the output rule (`IdentAlg.IsRun`). The stopping time `IdentAlg.stoppingTime`
is the stopping time `Learning.stoppingTime` of the stopping rule `A.stopSet` (the hitting time,
Mathlib `hittingAfter`, of the stopping rule by the process of histories), a stopping time of
the history filtration, and the history at the stopping time is `Learning.stoppedHist`.

Examples: best-arm identification (`𝓞 = 𝓐`, output = recommended arm), hypothesis tests
(`𝓞 = Bool`), estimation (`𝓞 = ℝ`).

A *fixed-budget* algorithm is the special case where the stopping rule is "stop after exactly
`T` rounds" (`IsFixedBudget A T`; constructor `fixedBudget alg T ρ`); a *fixed-confidence*
algorithm stops adaptively.

## Main definitions

* `IdentAlg 𝓐 𝓨 𝓞`: the structure.
* `IdentAlg.stoppingTime A O X Y : Ω → ℕ∞`: the number of rounds played, a hitting time.
* `IdentAlg.stoppedHist A O X Y : Ω → Σ n, Hist Unit 𝓐 𝓨 n`: the history at the stopping time.
* `IdentAlg.IsRun A env O X Y out P`: `(O, X, Y, out)` is a run of `A` in `env` on `(Ω, P)`.
* `IdentAlg.IsPAC A env good δ`: for every parameter `θ` of the family `env θ` of environments
  and every run of `A` in `env θ`, the output is `good θ` with probability at least `1 - δ`.
* `IdentAlg.IsFixedBudget A T`, `IdentAlg.fixedBudget alg T ρ`: fixed-budget algorithms.
* `fixedDesignAlg x`: the deterministic algorithm playing the sequence `x` whatever the
  observations; `IdentAlg.IsFixedDesign A` says that the sampling rule of `A` is of this form.

Time is `0`-indexed: after `n` rounds the actions `a_0, …, a_{n-1}` have been played.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped ENat

universe u

namespace Learning

variable {𝓞 𝓐 𝓨 𝓓 Ω : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {m𝓞 : MeasurableSpace 𝓞} {m𝓓 : MeasurableSpace 𝓓} {mΩ : MeasurableSpace Ω}

-- TODO: move
/-- The deterministic algorithm that plays the fixed sequence `x : ℕ → 𝓐` regardless of the
observations (a *fixed design*). -/
noncomputable def fixedDesignAlg (x : ℕ → 𝓐) : Algorithm 𝓞 𝓐 𝓨 :=
  detAlgorithm (fun n _ ↦ x n) fun _ ↦ measurable_const

/-- An identification algorithm with outputs in `𝓞`: a sampling rule `alg`, a stopping rule
`stop` (`stop n h`: stop after `n` rounds when their history is `h`) and an output rule `output`
(the distribution of the output given the history of the `n` rounds played), a Markov kernel. -/
structure IdentAlg (𝓞 𝓐 𝓨 𝓓 : Type*) [MeasurableSpace 𝓞] [MeasurableSpace 𝓐]
    [MeasurableSpace 𝓨] [MeasurableSpace 𝓓] where
  /-- The sampling rule. -/
  alg : Algorithm 𝓞 𝓐 𝓨
  /-- The stopping rule: `stop n h` means that the algorithm stops after `n` rounds when the
  history of these rounds is `h`. -/
  stop : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n → Prop
  /-- The stopping rule is measurable. -/
  measurableSet_stop : ∀ n, MeasurableSet {h | stop n h}
  /-- The output rule: distribution of the output given the history of the `n` rounds played. -/
  output : (n : ℕ) → Kernel (Hist 𝓞 𝓐 𝓨 n) 𝓓
  /-- The output rules are Markov kernels. -/
  [isMarkovKernel_output : ∀ n, IsMarkovKernel (output n)]

namespace IdentAlg

variable (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)

instance (n : ℕ) : IsMarkovKernel (A.output n) := A.isMarkovKernel_output n

/-- The stopping time of `A` on the observation, action and feedback processes `O`, `X`, `Y`: the
number of rounds
played, that is the first `n` such that the stopping rule fires on the history of the first `n`
rounds (`⊤` if it never does). It is the stopping time `Learning.stoppingTime` of the stopping
rule `{h | A.stop h.1 h.2}`. -/
noncomputable def stoppingTime : Ω → ℕ∞ := Learning.stoppingTime O X Y {h | A.stop h.1 h.2}

lemma stoppingTime_def :
  A.stoppingTime O X Y = Learning.stoppingTime O X Y {h | A.stop h.1 h.2} := rfl

lemma measurableSet_stopSet : MeasurableSet {h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n | A.stop h.1 h.2} :=
  measurableSet_sigma_iff.2 A.measurableSet_stop

/-- The stopping time of an identification algorithm is a stopping time of the history
filtration of any algorithm-environment sequence `X`, `Y`. -/
lemma isStoppingTime_stoppingTime {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}
    {P : Measure Ω} [IsFiniteMeasure P] (h : IsAlgEnvSeq O X Y alg env P) :
    IsStoppingTime h.filtration (A.stoppingTime O X Y) :=
  h.isStoppingTime_stoppingTime A.measurableSet_stopSet

/-- The history of the rounds played by `A`, as a history of variable length (of length `0` if
`A` never stops): the history stopped at `A.stoppingTime O X Y`. -/
noncomputable def stoppedHist : Ω → Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n :=
  Learning.stoppedHist O X Y (A.stoppingTime O X Y)

lemma stoppedHist_def :
    A.stoppedHist O X Y = Learning.stoppedHist O X Y (A.stoppingTime O X Y) := rfl

/-- When the stopping time is finite, the history at the stopping time belongs to the stopping
rule. -/
lemma stoppedHist_mem_stopSet_of_ne_top {ω : Ω} (h : A.stoppingTime O X Y ω ≠ ⊤) :
    A.stoppedHist O X Y ω ∈ {h | A.stop h.1 h.2} :=
  Learning.stoppedHist_mem_of_ne_top h

/-- The output rule of `A` as a single kernel on histories of variable length. -/
noncomputable def outputKernel : Kernel (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) 𝓓 where
  toFun h := A.output h.1 h.2
  measurable' := measurable_sigma_of_measurable_comp_mk fun n ↦ (A.output n).measurable

instance : IsMarkovKernel A.outputKernel :=
  ⟨fun h ↦ (A.isMarkovKernel_output h.1).isProbabilityMeasure h.2⟩

/-- `(O, X, Y, out)` is a *run* of the identification algorithm `A` in the environment `env` on
the probability space `(Ω, P)`: the observation, action and feedback processes `O`, `X`, `Y` form
an algorithm-environment sequence for the sampling rule `A.alg` and `env`, and the output `out` has
conditional law `A.output` given the history at the stopping time. -/
structure IsRun (env : Environment 𝓞 𝓐 𝓨) (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (out : Ω → 𝓓) (P : Measure Ω) [IsFiniteMeasure P] : Prop where
  /-- The actions and feedbacks are generated by the sampling rule in the environment. -/
  isAlgEnvSeq : IsAlgEnvSeq O X Y A.alg env P
  /-- The output is drawn from the output rule applied to the history at the stopping time. -/
  hasCondDistrib_output : HasCondDistrib out (A.stoppedHist O X Y) A.outputKernel P

/-- `A` is *PAC at level `δ`* for the family of environments `env : Θ → Environment 𝓞 𝓐 𝓨` and
the goodness predicate `good : Θ → 𝓓 → Prop` if, for every `θ` and every run of `A` in `env θ` on
a probability space `(Ω, P)`, the output is `good θ` with probability at least `1 - δ`. -/
def IsPAC {Θ : Type*} (env : Θ → Environment 𝓞 𝓐 𝓨) (good : Θ → 𝓓 → Prop) (δ : ℝ) : Prop :=
  ∀ θ, ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (out : Ω → 𝓓),
    A.IsRun (env θ) O X Y out P →
    1 - δ ≤ P.real {ω | good θ (out ω)}

/-- `A` is a *fixed-budget* algorithm with budget `T` if its stopping rule is "stop after exactly
`T` rounds". -/
def IsFixedBudget (T : ℕ) : Prop := A.stop = fun n _ ↦ n = T

/-- The fixed-budget identification algorithm with sampling rule `alg`, budget `T` and output
kernel `ρ` on histories of length `T` (the output rule at other lengths, never used, is an
arbitrary constant). -/
noncomputable def fixedBudget [Nonempty 𝓓] (alg : Algorithm 𝓞 𝓐 𝓨) (T : ℕ)
    (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓓) [IsMarkovKernel ρ] : IdentAlg 𝓞 𝓐 𝓨 𝓓 where
  alg := alg
  stop n _ := n = T
  measurableSet_stop n := by by_cases h : n = T <;> simp [h]
  output n := if h : n = T then ρ.comap (fun x i ↦ x (Fin.cast h.symm i)) (by fun_prop)
    else Kernel.const _ (Measure.dirac (Classical.arbitrary 𝓓))
  isMarkovKernel_output n := by
    by_cases h : n = T <;> simp only [h, ↓reduceDIte] <;> infer_instance

lemma isFixedBudget_fixedBudget [Nonempty 𝓞] (alg : Algorithm Unit 𝓐 𝓨) (T : ℕ)
    (ρ : Kernel (Hist Unit 𝓐 𝓨 T) 𝓞) [IsMarkovKernel ρ] :
    (fixedBudget alg T ρ).IsFixedBudget T := rfl

/-- The output rule of `fixedBudget alg T ρ` at the budget `T` is `ρ`. -/
lemma output_fixedBudget [Nonempty 𝓞] (alg : Algorithm Unit 𝓐 𝓨) (T : ℕ)
    (ρ : Kernel (Hist Unit 𝓐 𝓨 T) 𝓞) [IsMarkovKernel ρ] :
    (fixedBudget alg T ρ).output T = ρ := by
  change (if h : T = T then ρ.comap (fun x i ↦ x (Fin.cast h.symm i)) (by fun_prop)
    else Kernel.const _ (Measure.dirac (Classical.arbitrary 𝓞))) = ρ
  simp only [↓reduceDIte, Fin.cast_eq_self]
  ext y u _
  simp

end IdentAlg

end Learning
