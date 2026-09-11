/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Sigma
public import LeanMachineLearning.ForMathlib.Probability.HasLaw
public import LeanMachineLearning.SequentialLearning.Algorithm
public import Mathlib.Probability.Process.HittingTime

/-!
# Stopping rules, stopping times and stopped histories

A *stopping rule* is a measurable set `S : Set (Σ n, Hist 𝓞 𝓐 𝓨 n)` of histories of variable
length: the interaction stops after `n` rounds if the history of these `n` rounds belongs to
`S`. Its *stopping time* `stoppingTime O X Y S : Ω → ℕ∞` is the number of rounds played, the
hitting time (Mathlib `hittingAfter`) of `S` by the process `n ↦ ⟨n, history O X Y n⟩`. For a
random time `τ : Ω → ℕ∞`, `stoppedHist O X Y τ` is the history of the first `τ` rounds, as a
history of variable length (of length `0` if `τ = ⊤`).

* `stoppingTime_le_iff`, `lt_stoppingTime_iff`, `stoppingTime_eq_coe_iff`,
  `stoppingTime_eq_top_iff`: characterizations of the stopping time;
* `stoppedHist_mem_of_ne_top`: the stopped history belongs to `S` when the stopping time is
  finite; `notMem_of_lt_stoppingTime`: the history of `n < τ` rounds does not;
* `measurable_stoppingTime`, `measurable_stoppedHist`;
* `IsAlgEnvSeq.isStoppingTime_stoppingTime`: `stoppingTime O X Y S` is a stopping time of the
  history filtration of an algorithm-environment sequence;
* `exists_measurableSet_preimage_lt_stoppingTime`: the event `{n < stoppingTime O X Y S}` is
  determined by the first `n` rounds;
* `hasLaw_stoppedHist_min_add`, `hasLaw_stoppedHist_min_succ_add`: the laws of the histories
  stopped at `min τ M` and `min τ (M + 1)` split according to whether `τ ≤ M`;
  `IsAlgEnvSeq.hasCondDistrib_step_restrict_lt_stoppingTime`,
  `IsAlgEnvSeq.hasCondDistrib_obs_restrict_lt_stoppingTime`,
  `IsAlgEnvSeq.hasCondDistrib_action_restrict_lt_stoppingTime`: on the event `{M < τ}`, which is
  determined by the first `M` rounds, the step, the observation and the action at round `M` keep
  their conditional laws; `IsAlgEnvSeq.hasLaw_history_succ_restrict_lt_stoppingTime`: on this
  event, the law of the first `M + 1` rounds is the composition-product of the law of the first
  `M` rounds with the step kernel.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

open scoped ENat

namespace Learning

variable {𝓞 𝓐 𝓨 Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The stopping time of the stopping rule `S` on the action and feedback processes `X`, `Y`:
the number of rounds played, that is the first `n` such that the history of the first `n` rounds
belongs to `S` (`⊤` if there is none). -/
noncomputable def stoppingTime (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (S : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) : Ω → ℕ∞ :=
  hittingAfter (fun n ω ↦ (⟨n, history O X Y n ω⟩ : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) S 0

/-- The history of the first `τ ω` rounds, as a history of variable length (of length `0` if
`τ ω = ⊤`). -/
noncomputable def stoppedHist (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (τ : Ω → ℕ∞)
    (ω : Ω) :
    Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n :=
  ⟨(τ ω).toNat, history O X Y _ ω⟩

variable {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {S : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)}
  {τ : Ω → ℕ∞} {ω : Ω} {n M : ℕ}

section stoppingTime

lemma stoppingTime_le_iff :
    stoppingTime O X Y S ω ≤ n ↔ ∃ j ≤ n, (⟨j, history O X Y j ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∈ S :=
  (hittingAfter_le_iff (u := fun n ω ↦ (⟨n, history O X Y n ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n))
    (s := S) (n := 0) (i := n) (ω := ω)).trans (by simp)

lemma lt_stoppingTime_iff :
    (n : ℕ∞) < stoppingTime O X Y S ω ↔
      ∀ j ≤ n, (⟨j, history O X Y j ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∉ S := by
  rw [← not_le, stoppingTime_le_iff]
  simp

lemma stoppingTime_eq_top_iff :
    stoppingTime O X Y S ω = ⊤ ↔ ∀ n, (⟨n, history O X Y n ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∉ S :=
  (hittingAfter_eq_top_iff (u := fun n ω ↦ (⟨n, history O X Y n ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n))
    (s := S) (n := 0) (ω := ω)).trans (by simp)

lemma notMem_of_lt_stoppingTime (h : (n : ℕ∞) < stoppingTime O X Y S ω) :
    (⟨n, history O X Y n ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∉ S :=
  notMem_of_lt_hittingAfter h (Nat.zero_le n)

lemma stoppingTime_eq_coe_iff :
    stoppingTime O X Y S ω = n ↔
      (⟨n, history O X Y n ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∈ S ∧
        ∀ j < n, (⟨j, history O X Y j ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∉ S := by
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
  unfold stoppedHist
  rw [h]

lemma stoppedHist_coe (M : ℕ) (ω : Ω) :
    stoppedHist O X Y (fun _ ↦ (M : ℕ∞)) ω = ⟨M, history O X Y M ω⟩ := by
  change (⟨(M : ℕ∞).toNat, history O X Y (M : ℕ∞).toNat ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) = _
  rw [ENat.toNat_natCast]

/-- The stopped history belongs to the stopping rule when the stopping time is finite. -/
lemma stoppedHist_mem_of_ne_top (h : stoppingTime O X Y S ω ≠ ⊤) :
    stoppedHist O X Y (stoppingTime O X Y S) ω ∈ S := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h
  rw [stoppedHist_congr (stoppingTime O X Y S) (fun _ ↦ (n : ℕ∞)) hn.symm, stoppedHist_coe]
  exact (stoppingTime_eq_coe_iff.1 hn.symm).1

/-- If `τ ω ≤ M`, the history stopped at `min τ M` is the history stopped at `τ`. -/
lemma stoppedHist_min_of_le (h : τ ω ≤ M) :
    stoppedHist O X Y (fun ω ↦ min (τ ω) M) ω = stoppedHist O X Y τ ω :=
  stoppedHist_congr (fun ω ↦ min (τ ω) M) τ (min_eq_left h)

/-- If `M < τ ω`, the history stopped at `min τ M` is the history of the first `M` rounds. -/
lemma stoppedHist_min_of_lt (h : (M : ℕ∞) < τ ω) :
    stoppedHist O X Y (fun ω ↦ min (τ ω) M) ω = ⟨M, history O X Y M ω⟩ := by
  rw [stoppedHist_congr (fun ω ↦ min (τ ω) M) (fun _ ↦ (M : ℕ∞)) (min_eq_right h.le),
    stoppedHist_coe]

/-- If `M < τ ω`, the history stopped at `min τ (M + 1)` is the history of the first `M + 1`
rounds. -/
lemma stoppedHist_min_succ_of_lt (h : (M : ℕ∞) < τ ω) :
    stoppedHist O X Y (fun ω ↦ min (τ ω) (M + 1 : ℕ)) ω = ⟨M + 1, history O X Y (M + 1) ω⟩ := by
  rw [stoppedHist_congr (fun ω ↦ min (τ ω) (M + 1 : ℕ)) (fun _ ↦ ((M + 1 : ℕ) : ℕ∞))
    (min_eq_right ?_), stoppedHist_coe]
  exact_mod_cast Order.add_one_le_of_lt h

/-- The history stopped at `min τ M` has length at most `M`. -/
lemma fst_stoppedHist_min_le : (stoppedHist O X Y (fun ω ↦ min (τ ω) M) ω).1 ≤ M :=
  ENat.toNat_le_of_le_natCast (min_le_right _ _)

/-- The history stopped at `min τ 0` is the empty history. -/
lemma stoppedHist_min_zero (τ : Ω → ℕ∞) :
    (stoppedHist O X Y fun ω ↦ min (τ ω) ((0 : ℕ) : ℕ∞)) = fun _ ↦ ⟨0, default⟩ := by
  funext ω
  rw [stoppedHist_congr (fun ω ↦ min (τ ω) ((0 : ℕ) : ℕ∞)) (fun _ ↦ ((0 : ℕ) : ℕ∞))
    (min_eq_right (by simp)), stoppedHist_coe]
  exact congrArg (Sigma.mk 0) (Subsingleton.elim _ _)

end stoppingTime

variable {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}

/-- The history stopped at `min τ 0` has law the Dirac mass at the empty history. -/
lemma hasLaw_stoppedHist_min_zero (P : Measure Ω) [IsProbabilityMeasure P] (τ : Ω → ℕ∞) :
    HasLaw (stoppedHist O X Y fun ω ↦ min (τ ω) ((0 : ℕ) : ℕ∞))
      (Measure.dirac (⟨0, default⟩ : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) P := by
  rw [stoppedHist_min_zero]
  exact hasLaw_dirac_of_ae_eq (ae_eq_refl _)

section measurableSet

/-- The set of histories of variable length of length at most `M` is measurable. -/
lemma measurableSet_fst_le (M : ℕ) :
    MeasurableSet {h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n | h.1 ≤ M} :=
  measurable_sigma_fst (MeasurableSet.of_discrete (s := Set.Iic M))

/-- The set of histories of variable length of length less than `M` is measurable. -/
lemma measurableSet_fst_lt (M : ℕ) :
    MeasurableSet {h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n | h.1 < M} :=
  measurable_sigma_fst (MeasurableSet.of_discrete (s := Set.Iio M))

omit m𝓞 m𝓐 m𝓨 in
lemma measurable_min_natCast (hτ : Measurable τ) (M : ℕ) :
    Measurable fun ω ↦ min (τ ω) (M : ℕ∞) :=
  (measurable_from_top (f := fun t : ℕ∞ ↦ min t M)).comp hτ

end measurableSet

section measurability

variable (hO : ∀ n, Measurable (O n)) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
include hO hX hY

lemma measurable_stoppingTime (hS : MeasurableSet S) : Measurable (stoppingTime O X Y S) := by
  have hu : ∀ n, Measurable fun ω ↦ (⟨n, history O X Y n ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) :=
    fun n ↦ (measurable_sigma_mk n).comp (measurable_history hO hX hY n)
  refine measurable_to_countable' fun x ↦ ?_
  induction x using ENat.recTopCoe with
  | top =>
    have : stoppingTime O X Y S ⁻¹' {⊤} =
        ⋂ n, (fun ω ↦ (⟨n, history O X Y n ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n)) ⁻¹' Sᶜ := by
      ext ω
      simp [stoppingTime_eq_top_iff]
    rw [this]
    exact MeasurableSet.iInter fun n ↦ hu n hS.compl
  | coe n =>
    have : stoppingTime O X Y S ⁻¹' {(n : ℕ∞)} =
        (fun ω ↦ (⟨n, history O X Y n ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n)) ⁻¹' S ∩
          ⋂ j < n, (fun ω ↦ (⟨j, history O X Y j ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n)) ⁻¹' Sᶜ := by
      ext ω
      simp [stoppingTime_eq_coe_iff]
    rw [this]
    exact (hu n hS).inter (MeasurableSet.biInter (Set.to_countable _) fun j _ ↦ hu j hS.compl)

lemma measurableSet_stoppingTime_le (hS : MeasurableSet S) (M : ℕ) :
    MeasurableSet {ω | stoppingTime O X Y S ω ≤ M} :=
  measurable_stoppingTime hO hX hY hS (MeasurableSet.of_discrete (s := Set.Iic (M : ℕ∞)))

lemma measurableSet_lt_stoppingTime (hS : MeasurableSet S) (M : ℕ) :
    MeasurableSet {ω | (M : ℕ∞) < stoppingTime O X Y S ω} :=
  measurable_stoppingTime hO hX hY hS (MeasurableSet.of_discrete (s := Set.Ioi (M : ℕ∞)))

lemma measurable_stoppedHist (hτ : Measurable τ) : Measurable (stoppedHist O X Y τ) :=
  Measurable.sigmaMk (measurable_from_top.comp hτ) (measurable_history hO hX hY)

lemma measurable_stoppedHist_min (hτ : Measurable τ) (M : ℕ) :
    Measurable (stoppedHist O X Y fun ω ↦ min (τ ω) M) :=
  measurable_stoppedHist hO hX hY (measurable_min_natCast hτ M)

omit hO hX hY in
/-- The event `{n < stoppingTime O X Y S}` is determined by the history of the first `n` rounds. -/
lemma exists_measurableSet_preimage_lt_stoppingTime (hS : MeasurableSet S) (n : ℕ) :
    ∃ B : Set (Hist 𝓞 𝓐 𝓨 n), MeasurableSet B ∧
      {ω | (n : ℕ∞) < stoppingTime O X Y S ω} = history O X Y n ⁻¹' B := by
  refine ⟨⋂ j, ⋂ (hj : j ≤ n),
    {h | (⟨j, fun i ↦ h (Fin.castLE hj i)⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∉ S}, ?_, ?_⟩
  · refine MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun hj ↦ ?_
    exact ((measurable_sigma_mk j).comp (Measurable.of_eval fun _ ↦ measurable_pi_apply _))
      hS.compl
  · ext ω
    simp only [Set.mem_ofPred_eq, lt_stoppingTime_iff, Set.mem_preimage, Set.mem_iInter]
    exact ⟨fun h j hj ↦ h j hj, fun h j hj ↦ h j hj⟩

end measurability

section law

variable (hO : ∀ n, Measurable (O n)) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
  (hS : MeasurableSet S) {P : Measure Ω}
include hO hX hY hS

omit m𝓞 m𝓐 m𝓨 hO hX hY hS in
lemma compl_setOf_stoppingTime_le :
    {ω | stoppingTime O X Y S ω ≤ M}ᶜ = {ω | (M : ℕ∞) < stoppingTime O X Y S ω} := by
  ext ω
  simp

/-- The law of the history stopped at `min τ M` splits according to whether `τ ≤ M`: on
`{τ ≤ M}` it is the law of the history stopped at `τ` (or equivalently at `min τ M`), on
`{M < τ}` it is the law of the history of the first `M` rounds. -/
lemma hasLaw_stoppedHist_min_add {μ : Measure (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)}
    {ν : Measure (Hist 𝓞 𝓐 𝓨 M)}
    (hμ : HasLaw (stoppedHist O X Y fun ω ↦ min (stoppingTime O X Y S ω) M) μ
      (P.restrict {ω | stoppingTime O X Y S ω ≤ M}))
    (hν : HasLaw (history O X Y M) ν (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω})) :
    HasLaw (stoppedHist O X Y fun ω ↦ min (stoppingTime O X Y S ω) M)
      (μ + ν.map (Sigma.mk M)) P := by
  refine hμ.add_of_restrict_compl (measurableSet_stoppingTime_le hO hX hY hS M) ?_
  rw [compl_setOf_stoppingTime_le]
  refine (((measurable_sigma_mk M).hasLaw_map ν).comp hν).congr
    ((ae_restrict_iff' (measurableSet_lt_stoppingTime hO hX hY hS M)).2
      (Filter.Eventually.of_forall fun ω hω ↦ ?_))
  exact stoppedHist_min_of_lt hω

/-- The law of the history stopped at `min τ (M + 1)` splits according to whether `τ ≤ M`: on
`{τ ≤ M}` it is the law of the history stopped at `min τ M`, on `{M < τ}` it is the law of the
history of the first `M + 1` rounds. -/
lemma hasLaw_stoppedHist_min_succ_add {μ : Measure (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)}
    {ν : Measure (Hist 𝓞 𝓐 𝓨 (M + 1))}
    (hμ : HasLaw (stoppedHist O X Y fun ω ↦ min (stoppingTime O X Y S ω) M) μ
      (P.restrict {ω | stoppingTime O X Y S ω ≤ M}))
    (hν : HasLaw (history O X Y (M + 1)) ν
      (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω})) :
    HasLaw (stoppedHist O X Y fun ω ↦ min (stoppingTime O X Y S ω) (M + 1 : ℕ))
      (μ + ν.map (Sigma.mk (M + 1))) P := by
  refine HasLaw.add_of_restrict_compl (measurableSet_stoppingTime_le hO hX hY hS M) ?_ ?_
  · refine hμ.congr ((ae_restrict_iff' (measurableSet_stoppingTime_le hO hX hY hS M)).2
      (Filter.Eventually.of_forall fun ω hω ↦ ?_))
    rw [stoppedHist_min_of_le hω, stoppedHist_min_of_le (hω.trans (by exact_mod_cast M.le_succ))]
  · rw [compl_setOf_stoppingTime_le]
    refine (((measurable_sigma_mk (M + 1)).hasLaw_map ν).comp hν).congr
      ((ae_restrict_iff' (measurableSet_lt_stoppingTime hO hX hY hS M)).2
        (Filter.Eventually.of_forall fun ω hω ↦ ?_))
    exact stoppedHist_min_succ_of_lt hω

/-- On `{τ ≤ M}`, the history stopped at `min τ M` belongs to the stopping rule: its law under
the restriction of `P` to `{τ ≤ M}` gives measure zero to `Sᶜ`. -/
lemma _root_.ProbabilityTheory.HasLaw.stoppedHist_min_restrict_stoppingTime_le_apply_compl
    {μ : Measure (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)}
    (hμ : HasLaw (stoppedHist O X Y fun ω ↦ min (stoppingTime O X Y S ω) M) μ
      (P.restrict {ω | stoppingTime O X Y S ω ≤ M})) :
    μ Sᶜ = 0 := by
  refine hμ.measure_eq_zero_of_ae_notMem hS.compl
    ((ae_restrict_iff' (measurableSet_stoppingTime_le hO hX hY hS M)).2
      (Filter.Eventually.of_forall fun ω hω h ↦ h ?_))
  rw [stoppedHist_min_of_le hω]
  exact stoppedHist_mem_of_ne_top (ne_top_of_le_ne_top (ENat.natCast_ne_top M) hω)

omit hO hX hY hS in
/-- The history stopped at `min τ M` has length at most `M`: its law gives measure zero to the
histories of length `> M`. -/
lemma _root_.ProbabilityTheory.HasLaw.stoppedHist_min_apply_compl_fst_le
    {μ : Measure (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)}
    (hμ : HasLaw (stoppedHist O X Y fun ω ↦ min (τ ω) M) μ P) :
    μ {h | h.1 ≤ M}ᶜ = 0 :=
  hμ.measure_eq_zero_of_ae_notMem (measurableSet_fst_le M).compl
    (ae_of_all _ fun _ h ↦ h fst_stoppedHist_min_le)

/-- On `{M < τ}`, the history of the first `M` rounds does not belong to the stopping rule: if it
has law `ν` under the restriction of `P` to `{M < τ}`, the image of `ν` by `Sigma.mk M` gives
measure zero to `S`. -/
lemma _root_.ProbabilityTheory.HasLaw.history_restrict_lt_stoppingTime_map_sigmaMk_apply
    {ν : Measure (Hist 𝓞 𝓐 𝓨 M)}
    (hν : HasLaw (history O X Y M) ν (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω})) :
    (ν.map (Sigma.mk M)) S = 0 :=
  (((measurable_sigma_mk M).hasLaw_map ν).comp hν).measure_eq_zero_of_ae_notMem hS
    ((ae_restrict_iff' (measurableSet_lt_stoppingTime hO hX hY hS M)).2
      (Filter.Eventually.of_forall fun _ hω ↦ notMem_of_lt_stoppingTime hω))

omit hO hX hY hS in
/-- A history of length `M + 1` does not have length at most `M`. -/
lemma map_sigmaMk_succ_apply_fst_le (μ : Measure (Hist 𝓞 𝓐 𝓨 (M + 1))) :
    (μ.map (Sigma.mk (M + 1))) {h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n | h.1 ≤ M} = 0 := by
  rw [Measure.map_apply (measurable_sigma_mk (M + 1)) (measurableSet_fst_le M)]
  have : Sigma.mk (M + 1) ⁻¹' {h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n | h.1 ≤ M} = ∅ := by
    ext h
    simp
  rw [this, measure_empty]

end law

section filtration

variable {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨} {P : Measure Ω} [IsFiniteMeasure P]

lemma IsAlgEnvSeq.adapted_sigmaHistory (h : IsAlgEnvSeq O X Y alg env P) :
    Adapted h.filtration
      (fun n ω ↦ (⟨n, history O X Y n ω⟩ : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) :=
  fun n ↦ (measurable_sigma_mk n).comp (h.adapted_history n)

/-- The stopping time of a stopping rule is a stopping time of the history filtration of any
algorithm-environment sequence. -/
lemma IsAlgEnvSeq.isStoppingTime_stoppingTime (h : IsAlgEnvSeq O X Y alg env P)
    (hS : MeasurableSet S) :
    IsStoppingTime h.filtration (stoppingTime O X Y S) :=
  h.adapted_sigmaHistory.isStoppingTime_hittingAfter hS

/-- On the event `{M < τ}`, which is determined by the first `M` rounds, the step at round `M`
keeps its conditional law given the first `M` rounds. -/
lemma IsAlgEnvSeq.hasCondDistrib_step_restrict_lt_stoppingTime
    (h : IsAlgEnvSeq O X Y alg env P) (hS : MeasurableSet S) (M : ℕ) :
    HasCondDistrib (step O X Y M) (history O X Y M) (stepKernel alg env M)
      (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}) := by
  obtain ⟨B, hB, hB_eq⟩ :=
    exists_measurableSet_preimage_lt_stoppingTime (O := O) (X := X) (Y := Y) hS M
  rw [hB_eq]
  exact (h.hasCondDistrib_step M).restrict_preimage
    (h.measurable_history M) (h.measurable_step M) hB

/-- On the event `{M < τ}`, if the first `M` rounds have law `μ`, the first `M + 1` rounds have
law the composition-product of `μ` with the step kernel. -/
lemma IsAlgEnvSeq.hasLaw_history_succ_restrict_lt_stoppingTime (h : IsAlgEnvSeq O X Y alg env P)
    (hS : MeasurableSet S) {μ : Measure (Hist 𝓞 𝓐 𝓨 M)}
    (hμ : HasLaw (history O X Y M) μ (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω})) :
    HasLaw (history O X Y (M + 1))
      ((μ ⊗ₘ stepKernel alg env M).map (MeasurableEquiv.finSuccProd (Round 𝓞 𝓐 𝓨) M).symm)
      (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}) := by
  rw [history_succ]
  exact ((MeasurableEquiv.finSuccProd (Round 𝓞 𝓐 𝓨) M).symm.measurable.hasLaw_map _).comp
    (hμ.prodMk_of_hasCondDistrib (h.hasCondDistrib_step_restrict_lt_stoppingTime hS M))

/-- On the event `{M < τ}`, which is determined by the first `M` rounds, the observation at round
`M` keeps its conditional law given the first `M` rounds. -/
lemma IsAlgEnvSeq.hasCondDistrib_obs_restrict_lt_stoppingTime (h : IsAlgEnvSeq O X Y alg env P)
    (hS : MeasurableSet S) (M : ℕ) :
    HasCondDistrib (O M) (history O X Y M) (env.obs M)
      (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}) := by
  obtain ⟨B, hB, hB_eq⟩ :=
    exists_measurableSet_preimage_lt_stoppingTime (O := O) (X := X) (Y := Y) hS M
  rw [hB_eq]
  exact (h.hasCondDistrib_obs M).restrict_preimage (h.measurable_history M) (h.measurable_obs M) hB

/-- On the event `{M < τ}`, which is determined by the first `M` rounds, the action at round `M`
keeps its conditional law given the first `M` rounds and the observation at round `M`. -/
lemma IsAlgEnvSeq.hasCondDistrib_action_restrict_lt_stoppingTime (h : IsAlgEnvSeq O X Y alg env P)
    (hS : MeasurableSet S) (M : ℕ) :
    HasCondDistrib (X M) (fun ω ↦ (history O X Y M ω, O M ω)) (alg.policy M)
      (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}) := by
  obtain ⟨B, hB, hB_eq⟩ :=
    exists_measurableSet_preimage_lt_stoppingTime (O := O) (X := X) (Y := Y) hS M
  have hB' : history O X Y M ⁻¹' B = (fun ω ↦ (history O X Y M ω, O M ω)) ⁻¹' (B ×ˢ Set.univ) := by
    ext ω
    simp
  rw [hB_eq, hB']
  exact (h.hasCondDistrib_action M).restrict_preimage
    ((h.measurable_history M).prodMk (h.measurable_obs M)) (h.measurable_action M)
    (hB.prod MeasurableSet.univ)

end filtration

end Learning
