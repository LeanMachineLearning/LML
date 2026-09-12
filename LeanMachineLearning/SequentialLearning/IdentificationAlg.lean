/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Kernel.Sigma
public import LeanMachineLearning.SequentialLearning.Deterministic
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
history at the stopping time is the output rule (`IdentAlg.IsRun`). The stopping time
`IdentAlg.stoppingTime A O X Y` is the stopping time `Learning.stoppingTime` of the stopping rule
`A.stopSet` (the hitting time, Mathlib `hittingAfter`, of the stopping rule by the process of
histories), a stopping time of the history filtration, and the history at the stopping time is
`IdentAlg.stoppedHist A O X Y` (`Learning.stoppedHist`, the stopped value of the process of
histories). If the algorithm never stops, the history at the stopping time is the history of an
arbitrary, unspecified number of rounds, and the output is then drawn from the output rule at that
history.

The law of the output of a run is determined by `A` and `env`: it is `A.outputMeasure env`, the
law of the output on the canonical probability space of the interaction (`trajMeasure`), see
`IdentAlg.IsRun.hasLaw_output`. Properties of the algorithm are stated in terms of this law: `A`
is *PAC at level `δ`* (`IdentAlg.IsPAC`) for a family of environments `env θ` and a goodness
predicate `good θ` if, for every `θ`, the output in `env θ` is `good θ` with probability at least
`1 - δ`. `IdentAlg.IsPAC.measureReal_good_of_isRun` transfers this bound to any run of `A`.

Examples: best-arm identification (`𝓓 = 𝓐`, output = recommended arm), hypothesis tests
(`𝓓 = Bool`), estimation (`𝓓 = ℝ`).

A *fixed-budget* algorithm is the special case where the stopping rule is "stop after exactly
`T` rounds" (`IsFixedBudget A T`; constructor `fixedBudget alg T ρ`); a *fixed-confidence*
algorithm stops adaptively. A *fixed-design* algorithm (`IsFixedDesign A`) is one whose sampling
rule plays a fixed sequence of actions (`fixedDesignAlg x`).

## Main definitions

* `IdentAlg 𝓞 𝓐 𝓨 𝓓`: the structure.
* `IdentAlg.stoppingTime A O X Y : Ω → ℕ∞`: the number of rounds played, a hitting time.
* `IdentAlg.stoppedHist A O X Y : Ω → Σ n, Hist 𝓞 𝓐 𝓨 n`: the history at the stopping time.
* `IdentAlg.IsRun A env O X Y out P`: `(O, X, Y, out)` is a run of `A` in `env` on `(Ω, P)`.
* `IdentAlg.outputMeasure A env : Measure 𝓓`: the law of the output of `A` in `env`.
* `IdentAlg.IsPAC A env good δ`: for every parameter `θ`, the output of `A` in `env θ` is
  `good θ` with probability at least `1 - δ`.
* `IdentAlg.IsFixedBudget A T`, `IdentAlg.fixedBudget alg T ρ`: fixed-budget algorithms.
* `IdentAlg.IsFixedDesign A`: the sampling rule of `A` is `fixedDesignAlg x` for some `x`.

Time is `0`-indexed: after `n` rounds the actions `a_0, …, a_{n-1}` have been played.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped ENat

namespace Learning

variable {𝓞 𝓐 𝓨 𝓓 Ω : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓓 : MeasurableSpace 𝓓} {mΩ : MeasurableSpace Ω}

/-- An identification algorithm with outputs in `𝓓`: a sampling rule `alg`, a stopping rule
`stopSet` (the algorithm stops after `n` rounds if the history of these rounds, as a history of
variable length, belongs to `stopSet`) and an output rule `output`, a Markov kernel giving the
distribution of the output given the history of the rounds played. -/
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

variable (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)

instance : IsMarkovKernel A.output := A.isMarkovKernel_output

/-- The stopping time of `A` on the observation, action and feedback processes `O`, `X`, `Y`: the
number of rounds played, that is the first `n` such that the history of the first `n` rounds
belongs to the stopping rule `A.stopSet` (`⊤` if there is none). -/
noncomputable def stoppingTime : Ω → ℕ∞ := Learning.stoppingTime O X Y A.stopSet

lemma stoppingTime_def : A.stoppingTime O X Y = Learning.stoppingTime O X Y A.stopSet := rfl

/-- The history of the rounds played by `A`, as a history of variable length: the history stopped
at `A.stoppingTime O X Y` (the history of an arbitrary number of rounds if `A` never stops). -/
noncomputable def stoppedHist : Ω → Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n :=
  Learning.stoppedHist O X Y (A.stoppingTime O X Y)

lemma stoppedHist_def :
    A.stoppedHist O X Y = Learning.stoppedHist O X Y (A.stoppingTime O X Y) := rfl

/-- The law of the output of `A` in the environment `env`: the output rule applied to the law of
the history at the stopping time. This is the law of the output of any run of `A` in `env`
(`IsRun.hasLaw_output`). -/
noncomputable def outputMeasure (env : Environment 𝓞 𝓐 𝓨) : Measure 𝓓 :=
  A.output ∘ₘ stoppedHistMeasure A.alg env A.stopSet

instance (env : Environment 𝓞 𝓐 𝓨) : IsProbabilityMeasure (A.outputMeasure env) := by
  unfold outputMeasure
  infer_instance

/-- `(O, X, Y, out)` is a *run* of the identification algorithm `A` in the environment `env` on
the probability space `(Ω, P)`: the observation, action and feedback processes `O`, `X`, `Y` form
an algorithm-environment sequence for the sampling rule `A.alg` and `env`, and the output `out` has
conditional law `A.output` given the history at the stopping time (the history of an arbitrary
number of rounds if `A` never stops). -/
structure IsRun (env : Environment 𝓞 𝓐 𝓨) (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (out : Ω → 𝓓) (P : Measure Ω) [IsFiniteMeasure P] : Prop where
  /-- The actions and feedbacks are generated by the sampling rule in the environment. -/
  isAlgEnvSeq : IsAlgEnvSeq O X Y A.alg env P
  /-- The output is drawn from the output rule applied to the history at the stopping time. -/
  hasCondDistrib_output : HasCondDistrib out (A.stoppedHist O X Y) A.output P

/-- `A` is *PAC at level `δ`* for the family of environments `env : Θ → Environment 𝓞 𝓐 𝓨` and
the goodness predicate `good : Θ → 𝓓 → Prop` if, for every `θ`, the output of `A` in `env θ` is
`good θ` with probability at least `1 - δ`. See `IsPAC.measureReal_good_of_isRun` for the
corresponding statement about any run of `A`. -/
def IsPAC {Θ : Type*} (env : Θ → Environment 𝓞 𝓐 𝓨) (good : Θ → 𝓓 → Prop) (δ : ℝ) : Prop :=
  ∀ θ, 1 - δ ≤ (A.outputMeasure (env θ)).real {d | good θ d}

/-- `A` is a *fixed-budget* algorithm with budget `T` if its stopping rule is "stop after exactly
`T` rounds". -/
def IsFixedBudget (T : ℕ) : Prop := A.stopSet = {h | h.1 = T}

/-- `A` is a *fixed-design* algorithm if its sampling rule plays a fixed sequence of actions,
whatever the history and the observations. -/
def IsFixedDesign : Prop := ∃ x : ℕ → 𝓐, A.alg = fixedDesignAlg x

variable {A O X Y} {env : Environment 𝓞 𝓐 𝓨} {out : Ω → 𝓓} {P : Measure Ω}

/-- The stopping time of an identification algorithm is a stopping time of the history
filtration of any algorithm-environment sequence `O`, `X`, `Y`. -/
lemma isStoppingTime_stoppingTime (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) {alg : Algorithm 𝓞 𝓐 𝓨}
    [IsFiniteMeasure P] (h : IsAlgEnvSeq O X Y alg env P) :
    IsStoppingTime h.filtration (A.stoppingTime O X Y) :=
  h.isStoppingTime_stoppingTime A.measurableSet_stopSet

/-- When the stopping time is finite, the history at the stopping time belongs to the stopping
rule. -/
lemma stoppedHist_mem_stopSet_of_ne_top {ω : Ω} (h : A.stoppingTime O X Y ω ≠ ⊤) :
    A.stoppedHist O X Y ω ∈ A.stopSet :=
  Learning.stoppedHist_mem_of_ne_top h

/-- The history at the stopping time of any run of `A` in `env` has law
`stoppedHistMeasure A.alg env A.stopSet`. -/
lemma IsRun.hasLaw_stoppedHist [IsProbabilityMeasure P] (h : A.IsRun env O X Y out P) :
    HasLaw (A.stoppedHist O X Y) (stoppedHistMeasure A.alg env A.stopSet) P :=
  h.isAlgEnvSeq.hasLaw_stoppedHist_stoppingTime A.measurableSet_stopSet

/-- The output of any run of `A` in `env` has law `A.outputMeasure env`. -/
lemma IsRun.hasLaw_output [IsProbabilityMeasure P] (h : A.IsRun env O X Y out P) :
    HasLaw out (A.outputMeasure env) P := by
  have h_comp := h.hasCondDistrib_output.hasLaw_comp
  rw [h.hasLaw_stoppedHist.map_eq] at h_comp
  exact h_comp

/-- For a PAC algorithm at level `δ`, the output of any run in `env θ` is `good θ` with
probability at least `1 - δ`. -/
lemma IsPAC.measureReal_good_of_isRun {Θ : Type*} {env : Θ → Environment 𝓞 𝓐 𝓨}
    {good : Θ → 𝓓 → Prop} {δ : ℝ} (hA : A.IsPAC env good δ) {θ : Θ}
    (hgood : MeasurableSet {d | good θ d}) [IsProbabilityMeasure P]
    (h : A.IsRun (env θ) O X Y out P) :
    1 - δ ≤ P.real {ω | good θ (out ω)} := by
  rw [h.hasLaw_output.measureReal_eq hgood]
  exact hA θ

section FixedBudget

variable [Nonempty 𝓓] (alg : Algorithm 𝓞 𝓐 𝓨) (T : ℕ) (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓓)
  [IsMarkovKernel ρ]

/-- The output rule of a fixed-budget algorithm with output kernel `ρ` on histories of length
`T`: `ρ` on histories of length `T`, an arbitrary constant (never used) on other lengths. -/
noncomputable def fixedBudgetOutput (n : ℕ) : Kernel (Hist 𝓞 𝓐 𝓨 n) 𝓓 :=
  if h : n = T then ρ.comap (fun x i ↦ x (Fin.cast h.symm i)) (by fun_prop)
  else Kernel.const _ (Measure.dirac (Classical.arbitrary 𝓓))

instance (n : ℕ) : IsMarkovKernel (fixedBudgetOutput T ρ n) := by
  unfold fixedBudgetOutput
  by_cases h : n = T <;> simp only [h, ↓reduceDIte] <;> infer_instance

omit [IsMarkovKernel ρ] in
@[simp]
lemma fixedBudgetOutput_self : fixedBudgetOutput T ρ T = ρ := by
  simp only [fixedBudgetOutput, ↓reduceDIte, Fin.cast_eq_self]
  ext y u _
  simp

/-- The fixed-budget identification algorithm with sampling rule `alg`, budget `T` and output
kernel `ρ` on histories of length `T`. -/
noncomputable def fixedBudget : IdentAlg 𝓞 𝓐 𝓨 𝓓 where
  alg := alg
  stopSet := {h | h.1 = T}
  measurableSet_stopSet := measurable_sigma_fst (MeasurableSet.of_discrete (s := {T}))
  output := Kernel.sigma (fixedBudgetOutput T ρ)

@[simp] lemma alg_fixedBudget : (fixedBudget alg T ρ).alg = alg := rfl

@[simp] lemma stopSet_fixedBudget : (fixedBudget alg T ρ).stopSet = {h | h.1 = T} := rfl

@[simp] lemma output_fixedBudget :
    (fixedBudget alg T ρ).output = Kernel.sigma (fixedBudgetOutput T ρ) := rfl

lemma isFixedBudget_fixedBudget : (fixedBudget alg T ρ).IsFixedBudget T := rfl

/-- The output rule of `fixedBudget alg T ρ` on a history of length `T` is `ρ`. -/
lemma output_fixedBudget_mk (h : Hist 𝓞 𝓐 𝓨 T) : (fixedBudget alg T ρ).output ⟨T, h⟩ = ρ h := by
  simp

end FixedBudget

end IdentAlg

end Learning
