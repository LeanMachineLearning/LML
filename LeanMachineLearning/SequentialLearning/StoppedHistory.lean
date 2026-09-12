/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Sigma
public import LeanMachineLearning.ForMathlib.Probability.HasLaw
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
public import Mathlib.Probability.Process.HittingTime

/-!
# Stopping rules, stopping times and stopped histories

A *stopping rule* is a measurable set `S : Set (Σ n, Hist 𝓞 𝓐 𝓨 n)` of histories of variable
length: the interaction stops after `n` rounds if the history of these `n` rounds belongs to
`S`. Its *stopping time* `stoppingTime O X Y S : Ω → ℕ∞` is the number of rounds played, the
hitting time (Mathlib `hittingAfter`) of `S` by the process `sigmaHistory O X Y` of the histories
seen as histories of variable length. For a random time `τ : Ω → ℕ∞`, `stoppedHist O X Y τ` is
the history of the first `τ` rounds, as a history of variable length: the stopped value (Mathlib
`stoppedValue`) of the process `sigmaHistory O X Y` at `τ` (when `τ = ⊤`, this is the history of
an arbitrary, unspecified number of rounds). The history of the first `min τ M` rounds is the
stopped process (Mathlib `stoppedProcess`) `stoppedProcess (sigmaHistory O X Y) τ M`.

* `stoppingTime_le_iff`, `lt_stoppingTime_iff`, `stoppingTime_eq_coe_iff`,
  `stoppingTime_eq_top_iff`: characterizations of the stopping time;
* `stoppedHist_mem_of_ne_top`: the stopped history belongs to `S` when the stopping time is
  finite; `notMem_of_lt_stoppingTime`: the history of `n < τ` rounds does not;
* `measurable_stoppingTime`, `measurable_stoppedHist`;
* `measurableSet_comap_history_lt_stoppingTime`, `measurableSet_comap_history_stoppingTime_le`:
  the events `{n < stoppingTime O X Y S}` and `{stoppingTime O X Y S ≤ n}` are determined by the
  first `n` rounds; `IsAlgEnvSeq.isStoppingTime_stoppingTime`: `stoppingTime O X Y S` is a
  stopping time of the history filtration of an algorithm-environment sequence;
* `hasLaw_stoppedProcess_sigmaHistory_add`, `hasLaw_stoppedProcess_sigmaHistory_succ_add`: the
  laws of the histories stopped at `min τ M` and `min τ (M + 1)` split according to whether
  `τ ≤ M`;
* `IsAlgEnvSeq.hasCondDistrib_step_restrict_lt_stoppingTime` (and `obs`, `action`, `feedback`):
  on the event `{M < τ}`, which is determined by the first `M` rounds, the round at time `M` keeps
  its conditional laws; `IsAlgEnvSeq.hasLaw_history_succ_restrict_lt_stoppingTime`: on this
  event, the law of the first `M + 1` rounds is the composition-product of the law of the first
  `M` rounds with the step kernel;
* `stoppedHistMeasure alg env S`, `IsAlgEnvSeq.hasLaw_stoppedHist_stoppingTime`: the law of the
  history stopped by `S` is determined by the algorithm and the environment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

open scoped ENat

namespace Learning

variable {𝓞 𝓐 𝓨 Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The history of the first `n` rounds, as a history of variable length: the process
`n ↦ ⟨n, history O X Y n⟩`, of which the stopping time of a stopping rule is a hitting time. -/
def sigmaHistory (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (n : ℕ) (ω : Ω) :
    Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n :=
  ⟨n, history O X Y n ω⟩

/-- The stopping time of the stopping rule `S` on the observation, action and feedback processes
`O`, `X`, `Y`: the number of rounds played, that is the first `n` such that the history of the
first `n` rounds belongs to `S` (`⊤` if there is none). -/
noncomputable def stoppingTime (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (S : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) : Ω → ℕ∞ :=
  hittingAfter (sigmaHistory O X Y) S 0

/-- The history of the first `τ ω` rounds, as a history of variable length: the stopped value of
the process `sigmaHistory O X Y` at the random time `τ`. When `τ ω = ⊤`, this is the history of an
arbitrary, unspecified number of rounds. -/
noncomputable def stoppedHist (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (τ : Ω → ℕ∞) :
    Ω → Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n :=
  stoppedValue (sigmaHistory O X Y) τ

variable {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {S : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)}
  {τ : Ω → ℕ∞} {ω : Ω} {n M : ℕ}

lemma sigmaHistory_apply (n : ℕ) (ω : Ω) :
    sigmaHistory O X Y n ω = ⟨n, history O X Y n ω⟩ := rfl

lemma fst_sigmaHistory (n : ℕ) (ω : Ω) : (sigmaHistory O X Y n ω).1 = n := rfl

lemma stoppedHist_def (τ : Ω → ℕ∞) :
    stoppedHist O X Y τ = stoppedValue (sigmaHistory O X Y) τ := rfl

section stoppingTime

lemma stoppingTime_le_iff :
    stoppingTime O X Y S ω ≤ n ↔ ∃ j ≤ n, sigmaHistory O X Y j ω ∈ S :=
  (hittingAfter_le_iff (u := sigmaHistory O X Y) (s := S) (n := 0) (i := n) (ω := ω)).trans
    (by simp)

lemma lt_stoppingTime_iff :
    (n : ℕ∞) < stoppingTime O X Y S ω ↔ ∀ j ≤ n, sigmaHistory O X Y j ω ∉ S := by
  rw [← not_le, stoppingTime_le_iff]
  simp

lemma stoppingTime_eq_top_iff :
    stoppingTime O X Y S ω = ⊤ ↔ ∀ n, sigmaHistory O X Y n ω ∉ S :=
  (hittingAfter_eq_top_iff (u := sigmaHistory O X Y) (s := S) (n := 0) (ω := ω)).trans (by simp)

lemma notMem_of_lt_stoppingTime (h : (n : ℕ∞) < stoppingTime O X Y S ω) :
    sigmaHistory O X Y n ω ∉ S :=
  notMem_of_lt_hittingAfter h (Nat.zero_le n)

lemma stoppingTime_eq_coe_iff :
    stoppingTime O X Y S ω = n ↔
      sigmaHistory O X Y n ω ∈ S ∧ ∀ j < n, sigmaHistory O X Y j ω ∉ S := by
  constructor
  · intro h
    refine ⟨?_, fun j hj ↦ notMem_of_lt_stoppingTime (h ▸ ENat.natCast_lt_natCast.2 hj)⟩
    obtain ⟨j, hjn, hjS⟩ := stoppingTime_le_iff.1 h.le
    rcases hjn.lt_or_eq with hjn | rfl
    · exact absurd hjS (notMem_of_lt_stoppingTime (h ▸ ENat.natCast_lt_natCast.2 hjn))
    · exact hjS
  · rintro ⟨h1, h2⟩
    refine le_antisymm (hittingAfter_le_of_mem (Nat.zero_le n) h1) (not_lt.1 fun hlt ↦ ?_)
    obtain ⟨j, hj, hjS⟩ := hittingAfter_lt_iff.1 hlt
    exact h2 j hj.2 hjS

/-- The empty stopping rule never stops. -/
lemma stoppingTime_empty : stoppingTime O X Y (∅ : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) = fun _ ↦ ⊤ :=
  hittingAfter_empty 0

lemma stoppedHist_congr (τ τ' : Ω → ℕ∞) (h : τ ω = τ' ω) :
    stoppedHist O X Y τ ω = stoppedHist O X Y τ' ω := by
  simp only [stoppedHist, stoppedValue, h]

lemma stoppedHist_coe (M : ℕ) (ω : Ω) :
    stoppedHist O X Y (fun _ ↦ (M : ℕ∞)) ω = sigmaHistory O X Y M ω := rfl

/-- The stopped history belongs to the stopping rule when the stopping time is finite. -/
lemma stoppedHist_mem_of_ne_top (h : stoppingTime O X Y S ω ≠ ⊤) :
    stoppedHist O X Y (stoppingTime O X Y S) ω ∈ S :=
  hittingAfter_mem_set_of_ne_top h

/-! The history of the first `min τ M` rounds is `stoppedProcess (sigmaHistory O X Y) τ M`: it
is the history of the first `M` rounds if `M ≤ τ` (`stoppedProcess_eq_of_le`) and the history
stopped at `τ` otherwise (`stoppedProcess_eq_of_ge`). -/

/-- The history of the first `min τ M` rounds has length at most `M`. -/
lemma fst_stoppedProcess_sigmaHistory_le :
    (stoppedProcess (sigmaHistory O X Y) τ M ω).1 ≤ M :=
  (WithTop.untopA_le_iff (ne_top_of_le_ne_top (ENat.natCast_ne_top M) (min_le_left _ _))).2
    (min_le_left _ _)

/-- The history of the first `min τ 0` rounds is the empty history. -/
lemma stoppedProcess_sigmaHistory_zero (τ : Ω → ℕ∞) :
    stoppedProcess (sigmaHistory O X Y) τ 0 = fun _ ↦ ⟨0, default⟩ :=
  funext fun ω ↦ (stoppedProcess_eq_of_le (zero_le : (0 : ℕ∞) ≤ τ ω)).trans
    (congrArg (Sigma.mk 0) (Subsingleton.elim _ _))

end stoppingTime

section natCast

omit mΩ in
lemma compl_setOf_le_natCast (τ : Ω → ℕ∞) (M : ℕ) :
    {ω | τ ω ≤ M}ᶜ = {ω | (M : ℕ∞) < τ ω} := by
  ext ω
  simp

/-- Every subset of `ℕ∞` is measurable, hence so is `{τ ≤ M}` for a measurable `τ`. -/
lemma measurableSet_le_natCast (hτ : Measurable τ) (M : ℕ) : MeasurableSet {ω | τ ω ≤ M} :=
  hτ (MeasurableSet.of_discrete (s := Set.Iic (M : ℕ∞)))

lemma measurableSet_natCast_lt (hτ : Measurable τ) (M : ℕ) :
    MeasurableSet {ω | (M : ℕ∞) < τ ω} :=
  hτ (MeasurableSet.of_discrete (s := Set.Ioi (M : ℕ∞)))

end natCast

variable {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}

/-- The history of the first `min τ 0` rounds has law the Dirac mass at the empty history. -/
lemma hasLaw_stoppedProcess_sigmaHistory_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : Ω → ℕ∞) :
    HasLaw (stoppedProcess (sigmaHistory O X Y) τ 0)
      (Measure.dirac (⟨0, default⟩ : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) P := by
  rw [stoppedProcess_sigmaHistory_zero]
  exact hasLaw_dirac_of_ae_eq (ae_eq_refl _)

section measurability

variable (hO : ∀ n, Measurable (O n)) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
include hO hX hY

lemma measurable_sigmaHistory (n : ℕ) : Measurable (sigmaHistory O X Y n) :=
  (measurable_sigma_mk n).comp (measurable_history hO hX hY n)

lemma measurable_stoppingTime (hS : MeasurableSet S) : Measurable (stoppingTime O X Y S) := by
  refine measurable_to_countable' fun x ↦ ?_
  induction x using ENat.recTopCoe with
  | top =>
    have : stoppingTime O X Y S ⁻¹' {⊤} = ⋂ n, sigmaHistory O X Y n ⁻¹' Sᶜ := by
      ext ω
      simp [stoppingTime_eq_top_iff]
    rw [this]
    exact MeasurableSet.iInter fun n ↦ measurable_sigmaHistory hO hX hY n hS.compl
  | coe n =>
    have : stoppingTime O X Y S ⁻¹' {(n : ℕ∞)} =
        sigmaHistory O X Y n ⁻¹' S ∩ ⋂ j < n, sigmaHistory O X Y j ⁻¹' Sᶜ := by
      ext ω
      simp [stoppingTime_eq_coe_iff]
    rw [this]
    exact (measurable_sigmaHistory hO hX hY n hS).inter
      (MeasurableSet.biInter (Set.to_countable _) fun j _ ↦
        measurable_sigmaHistory hO hX hY j hS.compl)

lemma measurable_stoppedHist (hτ : Measurable τ) : Measurable (stoppedHist O X Y τ) :=
  Measurable.sigmaMk (measurable_from_top.comp hτ) (measurable_history hO hX hY)

lemma measurable_stoppedProcess_sigmaHistory (hτ : Measurable τ) (M : ℕ) :
    Measurable (stoppedProcess (sigmaHistory O X Y) τ M) :=
  measurable_stoppedHist hO hX hY
    ((measurable_from_top (f := fun t : ℕ∞ ↦ min (M : ℕ∞) t)).comp hτ)

end measurability

section comap

/-- The event `{n < stoppingTime O X Y S}` is determined by the history of the first `n` rounds:
it is measurable for the σ-algebra generated by `history O X Y n`. -/
lemma measurableSet_comap_history_lt_stoppingTime (hS : MeasurableSet S) (n : ℕ) :
    MeasurableSet[MeasurableSpace.comap (history O X Y n) inferInstance]
      {ω | (n : ℕ∞) < stoppingTime O X Y S ω} := by
  refine MeasurableSpace.measurableSet_comap.2 ⟨⋂ j, ⋂ (hj : j ≤ n),
    {h | (⟨j, fun i ↦ h (Fin.castLE hj i)⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∉ S}, ?_, ?_⟩
  · refine MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun hj ↦ ?_
    exact ((measurable_sigma_mk j).comp (Measurable.of_eval fun _ ↦ measurable_pi_apply _))
      hS.compl
  · ext ω
    simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq, lt_stoppingTime_iff]
    exact ⟨fun h j hj ↦ h j hj, fun h j hj ↦ h j hj⟩

/-- The event `{stoppingTime O X Y S ≤ n}` is determined by the history of the first `n`
rounds: it is measurable for the σ-algebra generated by `history O X Y n`. -/
lemma measurableSet_comap_history_stoppingTime_le (hS : MeasurableSet S) (n : ℕ) :
    MeasurableSet[MeasurableSpace.comap (history O X Y n) inferInstance]
      {ω | stoppingTime O X Y S ω ≤ n} := by
  rw [← compl_compl {ω | stoppingTime O X Y S ω ≤ n}, compl_setOf_le_natCast]
  exact (measurableSet_comap_history_lt_stoppingTime hS n).compl

end comap

section law

variable {P : Measure Ω}

/-- The law of the history of the first `min τ M` rounds splits according to whether `τ ≤ M`:
on `{τ ≤ M}` it is the law of the history stopped at `τ` (or equivalently of the first `min τ M`
rounds), on `{M < τ}` it is the law of the history of the first `M` rounds. -/
lemma hasLaw_stoppedProcess_sigmaHistory_add (hτ : Measurable τ)
    {μ : Measure (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)} {ν : Measure (Hist 𝓞 𝓐 𝓨 M)}
    (hμ : HasLaw (stoppedProcess (sigmaHistory O X Y) τ M) μ (P.restrict {ω | τ ω ≤ M}))
    (hν : HasLaw (history O X Y M) ν (P.restrict {ω | (M : ℕ∞) < τ ω})) :
    HasLaw (stoppedProcess (sigmaHistory O X Y) τ M) (μ + ν.map (Sigma.mk M)) P := by
  refine hμ.add_of_restrict_compl (measurableSet_le_natCast hτ M) ?_
  rw [compl_setOf_le_natCast]
  refine (((measurable_sigma_mk M).hasLaw_map ν).comp hν).congr
    ((ae_restrict_iff' (measurableSet_natCast_lt hτ M)).2
      (Filter.Eventually.of_forall fun ω hω ↦ ?_))
  exact stoppedProcess_eq_of_le hω.le

/-- The law of the history of the first `min τ (M + 1)` rounds splits according to whether
`τ ≤ M`: on `{τ ≤ M}` it is the law of the history of the first `min τ M` rounds, on `{M < τ}` it
is the law of the history of the first `M + 1` rounds. -/
lemma hasLaw_stoppedProcess_sigmaHistory_succ_add (hτ : Measurable τ)
    {μ : Measure (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)} {ν : Measure (Hist 𝓞 𝓐 𝓨 (M + 1))}
    (hμ : HasLaw (stoppedProcess (sigmaHistory O X Y) τ M) μ (P.restrict {ω | τ ω ≤ M}))
    (hν : HasLaw (history O X Y (M + 1)) ν (P.restrict {ω | (M : ℕ∞) < τ ω})) :
    HasLaw (stoppedProcess (sigmaHistory O X Y) τ (M + 1)) (μ + ν.map (Sigma.mk (M + 1))) P := by
  refine HasLaw.add_of_restrict_compl (measurableSet_le_natCast hτ M) ?_ ?_
  · refine hμ.congr ((ae_restrict_iff' (measurableSet_le_natCast hτ M)).2
      (Filter.Eventually.of_forall fun ω hω ↦ ?_))
    rw [stoppedProcess_eq_of_ge hω, stoppedProcess_eq_of_ge
      (hω.trans (by exact_mod_cast M.le_succ : (M : ℕ∞) ≤ ((M + 1 : ℕ) : ℕ∞)))]
  · rw [compl_setOf_le_natCast]
    refine (((measurable_sigma_mk (M + 1)).hasLaw_map ν).comp hν).congr
      ((ae_restrict_iff' (measurableSet_natCast_lt hτ M)).2
        (Filter.Eventually.of_forall fun ω hω ↦ ?_))
    have hω' : (M : ℕ∞) < τ ω := hω
    have h_succ : ((M + 1 : ℕ) : ℕ∞) ≤ τ ω := by exact_mod_cast Order.add_one_le_of_lt hω'
    exact stoppedProcess_eq_of_le h_succ

/-- The history of the first `min τ M` rounds has length at most `M`: its law gives measure zero
to the histories of length `> M`. -/
lemma _root_.ProbabilityTheory.HasLaw.stoppedProcess_sigmaHistory_apply_compl_fst_le
    {μ : Measure (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)}
    (hμ : HasLaw (stoppedProcess (sigmaHistory O X Y) τ M) μ P) :
    μ {h | h.1 ≤ M}ᶜ = 0 :=
  hμ.measure_eq_zero_of_ae_notMem (measurableSet_sigma_fst_le M).compl
    (ae_of_all _ fun _ h ↦ h fst_stoppedProcess_sigmaHistory_le)

variable (hO : ∀ n, Measurable (O n)) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
  (hS : MeasurableSet S)
include hO hX hY hS

/-- On `{τ ≤ M}`, the history of the first `min τ M` rounds belongs to the stopping rule: its
law under the restriction of `P` to `{τ ≤ M}` gives measure zero to `Sᶜ`. -/
lemma _root_.ProbabilityTheory.HasLaw.stoppedProcess_sigmaHistory_stoppingTime_apply_compl
    {μ : Measure (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)}
    (hμ : HasLaw (stoppedProcess (sigmaHistory O X Y) (stoppingTime O X Y S) M) μ
      (P.restrict {ω | stoppingTime O X Y S ω ≤ M})) :
    μ Sᶜ = 0 := by
  refine hμ.measure_eq_zero_of_ae_notMem hS.compl
    ((ae_restrict_iff' (measurableSet_le_natCast (measurable_stoppingTime hO hX hY hS) M)).2
      (Filter.Eventually.of_forall fun ω hω h ↦ h ?_))
  rw [stoppedProcess_eq_of_ge hω]
  exact stoppedHist_mem_of_ne_top (ne_top_of_le_ne_top (ENat.natCast_ne_top M) hω)

/-- On `{M < τ}`, the history of the first `M` rounds does not belong to the stopping rule: if it
has law `ν` under the restriction of `P` to `{M < τ}`, the image of `ν` by `Sigma.mk M` gives
measure zero to `S`. -/
lemma _root_.ProbabilityTheory.HasLaw.history_restrict_lt_stoppingTime_map_sigmaMk_apply
    {ν : Measure (Hist 𝓞 𝓐 𝓨 M)}
    (hν : HasLaw (history O X Y M) ν (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω})) :
    (ν.map (Sigma.mk M)) S = 0 :=
  (((measurable_sigma_mk M).hasLaw_map ν).comp hν).measure_eq_zero_of_ae_notMem hS
    ((ae_restrict_iff' (measurableSet_natCast_lt (measurable_stoppingTime hO hX hY hS) M)).2
      (Filter.Eventually.of_forall fun _ hω ↦ notMem_of_lt_stoppingTime hω))

end law

section filtration

variable {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨} {P : Measure Ω} [IsFiniteMeasure P]

lemma IsAlgEnvSeq.adapted_sigmaHistory (h : IsAlgEnvSeq O X Y alg env P) :
    Adapted h.filtration (sigmaHistory O X Y) :=
  fun n ↦ (measurable_sigma_mk n).comp (h.adapted_history n)

/-- The stopping time of a stopping rule is a stopping time of the history filtration of any
algorithm-environment sequence. -/
lemma IsAlgEnvSeq.isStoppingTime_stoppingTime (h : IsAlgEnvSeq O X Y alg env P)
    (hS : MeasurableSet S) :
    IsStoppingTime h.filtration (stoppingTime O X Y S) :=
  h.adapted_sigmaHistory.isStoppingTime_hittingAfter hS

/-- On the event `{M < τ}`, which is determined by the first `M` rounds, the round at time `M`
keeps its conditional law given the first `M` rounds. -/
lemma IsAlgEnvSeq.hasCondDistrib_step_restrict_lt_stoppingTime
    (h : IsAlgEnvSeq O X Y alg env P) (hS : MeasurableSet S) (M : ℕ) :
    HasCondDistrib (step O X Y M) (history O X Y M) (stepKernel alg env M)
      (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}) :=
  (h.hasCondDistrib_step M).restrict_of_measurableSet_comap (h.measurable_history M)
    (h.measurable_step M) (measurableSet_comap_history_lt_stoppingTime hS M)

/-- On the event `{M < τ}`, which is determined by the first `M` rounds, the observation at time
`M` keeps its conditional law given the first `M` rounds. -/
lemma IsAlgEnvSeq.hasCondDistrib_obs_restrict_lt_stoppingTime (h : IsAlgEnvSeq O X Y alg env P)
    (hS : MeasurableSet S) (M : ℕ) :
    HasCondDistrib (O M) (history O X Y M) (env.obs M)
      (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}) :=
  (h.hasCondDistrib_obs M).restrict_of_measurableSet_comap (h.measurable_history M)
    (h.measurable_obs M) (measurableSet_comap_history_lt_stoppingTime hS M)

/-- On the event `{M < τ}`, which is determined by the first `M` rounds, the action at time `M`
keeps its conditional law given the first `M` rounds and the observation at time `M`. -/
lemma IsAlgEnvSeq.hasCondDistrib_action_restrict_lt_stoppingTime (h : IsAlgEnvSeq O X Y alg env P)
    (hS : MeasurableSet S) (M : ℕ) :
    HasCondDistrib (X M) (fun ω ↦ (history O X Y M ω, O M ω)) (alg.policy M)
      (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}) :=
  (h.hasCondDistrib_action M).restrict_of_measurableSet_comap
    ((h.measurable_history M).prodMk (h.measurable_obs M)) (h.measurable_action M)
    (measurable_iff_comap_le.mp (h.measurable_history_filtrationObs M) _
      (measurableSet_comap_history_lt_stoppingTime hS M))

/-- On the event `{M < τ}`, which is determined by the first `M` rounds, the feedback at time `M`
keeps its conditional law given the first `M` rounds, the observation and the action at time
`M`. -/
lemma IsAlgEnvSeq.hasCondDistrib_feedback_restrict_lt_stoppingTime
    (h : IsAlgEnvSeq O X Y alg env P) (hS : MeasurableSet S) (M : ℕ) :
    HasCondDistrib (Y M) (fun ω ↦ ((history O X Y M ω, O M ω), X M ω)) (env.feedback M)
      (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}) :=
  (h.hasCondDistrib_feedback M).restrict_of_measurableSet_comap
    (((h.measurable_history M).prodMk (h.measurable_obs M)).prodMk (h.measurable_action M))
    (h.measurable_feedback M)
    (measurable_iff_comap_le.mp (h.measurable_history_filtrationAction M) _
      (measurableSet_comap_history_lt_stoppingTime hS M))

/-- On the event `{M < τ}`, if the first `M` rounds have law `μ`, the first `M + 1` rounds have
law the composition-product of `μ` with the step kernel. -/
lemma IsAlgEnvSeq.hasLaw_history_succ_restrict_lt_stoppingTime (h : IsAlgEnvSeq O X Y alg env P)
    (hS : MeasurableSet S) {μ : Measure (Hist 𝓞 𝓐 𝓨 M)}
    (hμ : HasLaw (history O X Y M) μ (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω})) :
    HasLaw (history O X Y (M + 1))
      ((μ ⊗ₘ stepKernel alg env M).map (MeasurableEquiv.finSuccProd (Round 𝓞 𝓐 𝓨) M).symm)
      (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}) :=
  hasLaw_history_succ hμ (h.hasCondDistrib_step_restrict_lt_stoppingTime hS M)

end filtration

section trajMeasure

/-! ### The law of the stopped history

The stopping time and the stopped history are functions of the trajectory, whose law is
determined by the algorithm and the environment (`IsAlgEnvSeq.hasLaw_trajectory`). Hence the law
of the stopped history is determined by the algorithm and the environment: it is the law
`stoppedHistMeasure alg env S` of the stopped history on the canonical space `trajMeasure`. -/

variable {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}

/-- The law of the history stopped by the stopping rule `S`, for the algorithm `alg` in the
environment `env`: the law of the stopped history on the canonical space `trajMeasure alg env`.
This is the law of the stopped history for any algorithm-environment sequence
(`IsAlgEnvSeq.hasLaw_stoppedHist_stoppingTime`). -/
noncomputable def stoppedHistMeasure (alg : Algorithm 𝓞 𝓐 𝓨) (env : Environment 𝓞 𝓐 𝓨)
    (S : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) :
    Measure (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) :=
  (trajMeasure alg env).map
    (stoppedHist IT.obs IT.action IT.feedback (stoppingTime IT.obs IT.action IT.feedback S))
deriving IsProbabilityMeasure

/-- The law of the history stopped by `S` under any algorithm-environment sequence for `alg` and
`env` is `stoppedHistMeasure alg env S`. -/
lemma IsAlgEnvSeq.hasLaw_stoppedHist_stoppingTime {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O X Y alg env P) (hS : MeasurableSet S) :
    HasLaw (stoppedHist O X Y (stoppingTime O X Y S)) (stoppedHistMeasure alg env S) P :=
  ((measurable_stoppedHist IT.measurable_obs IT.measurable_action IT.measurable_feedback
    (measurable_stoppingTime IT.measurable_obs IT.measurable_action IT.measurable_feedback
      hS)).hasLaw_map _).comp h.hasLaw_trajectory

end trajMeasure

end Learning
