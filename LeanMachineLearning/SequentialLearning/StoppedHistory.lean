/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Sigma
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
* `truncHist M`, `truncHist_stoppedHist`: truncating the stopped history to its first `M` rounds
  gives the history stopped at `min τ M`; `map_stoppedHist_min_eq_map_truncHist`: the law of
  the history stopped at `min τ M` is the image of the law of the history stopped at an almost
  surely finite `τ` by the truncation, and `restrict_map_truncHist`: both laws agree on histories
  of length `< M`;
* `map_stoppedHist_min_eq_add`, `map_stoppedHist_min_succ_eq_add`: the laws of the histories
  stopped at `min τ M` and `min τ (M + 1)` split according to whether `τ ≤ M`;
  `IsAlgEnvSeq.map_history_succ_restrict_lt_stoppingTime`,
  `IsAlgEnvSeq.map_history_obs_restrict_lt_stoppingTime`,
  `IsAlgEnvSeq.map_action_restrict_lt_stoppingTime`: on the event `{M < τ}`, which is determined
  by the first `M` rounds, the step, the observation and the action at round `M` keep their
  conditional laws.

TODO: convert lots of map_eq statements to HasLaw or HasCondDistrib.

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

/-- The law of the history stopped at `min τ 0` is the Dirac mass at the empty history. -/
lemma map_stoppedHist_min_zero (P : Measure Ω) [IsProbabilityMeasure P] (τ : Ω → ℕ∞) :
    P.map (stoppedHist O X Y fun ω ↦ min (τ ω) ((0 : ℕ) : ℕ∞)) =
      Measure.dirac (⟨0, default⟩ : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) := by
  rw [stoppedHist_min_zero, Measure.map_const, measure_univ, one_smul]

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

section truncation

/-- Truncation of a history of variable length to its first `M` rounds. -/
def truncHist (M : ℕ) (h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n :=
  if hM : h.1 ≤ M then h else ⟨M, fun i ↦ h.2 (Fin.castLE (not_le.1 hM).le i)⟩

lemma measurable_truncHist (M : ℕ) :
    Measurable (truncHist (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨) M) := by
  refine measurable_sigma_of_measurable_comp_mk fun n ↦ ?_
  by_cases hn : n ≤ M
  · simp only [Function.comp_def, truncHist, hn, dite_true]
    exact measurable_sigma_mk n
  · simp only [Function.comp_def, truncHist, hn, dite_false]
    exact (measurable_sigma_mk M).comp
      (Measurable.of_eval fun i ↦ measurable_pi_apply (Fin.castLE (not_le.1 hn).le i))

omit m𝓞 m𝓐 m𝓨 in
/-- Truncating the history stopped at a finite time `τ` to its first `M` rounds gives the history
stopped at `min τ M`. -/
lemma truncHist_stoppedHist (h : τ ω ≠ ⊤) :
    truncHist M (stoppedHist O X Y τ ω) = stoppedHist O X Y (fun ω ↦ min (τ ω) M) ω := by
  rcases le_or_gt (τ ω) M with hτ | hτ
  · rw [stoppedHist_min_of_le hτ, truncHist, dite_eq_left]
    exact ENat.toNat_le_of_le_natCast hτ
  · rw [stoppedHist_min_of_lt hτ, truncHist, dite_eq_right]
    · rfl
    · change ¬ (τ ω).toNat ≤ M
      rw [not_le, ← ENat.natCast_lt_natCast, ENat.natCast_toNat h]
      exact hτ

omit m𝓞 m𝓐 m𝓨 in
lemma truncHist_of_fst_le {h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n} (hM : h.1 ≤ M) : truncHist M h = h :=
  dite_eq_left hM

omit m𝓞 m𝓐 m𝓨 in
lemma preimage_truncHist_fst_lt (M : ℕ) :
    truncHist M ⁻¹' {h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n | h.1 < M} = {h | h.1 < M} := by
  ext h
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, truncHist]
  split_ifs with hM
  · rfl
  · simp only [lt_self_iff_false, false_iff, not_lt]
    exact (not_le.1 hM).le

/-- The image of a measure by the truncation to the first `M` rounds agrees with the measure on
histories of length `< M`. -/
lemma restrict_map_truncHist (μ : Measure (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) (M : ℕ) :
    (μ.map (truncHist M)).restrict {h | h.1 < M} = μ.restrict {h | h.1 < M} := by
  rw [Measure.restrict_map (measurable_truncHist M) (measurableSet_fst_lt M),
    preimage_truncHist_fst_lt]
  conv_rhs => rw [← Measure.map_id (μ := μ.restrict {h | h.1 < M})]
  refine Measure.map_congr ((ae_restrict_iff' (measurableSet_fst_lt M)).2
    (Filter.Eventually.of_forall fun h hh ↦ ?_))
  exact truncHist_of_fst_le hh.le

end truncation

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

/-- The law of the history stopped at `min τ M` is the image by the truncation to the first `M`
rounds of the law of the history stopped at an almost surely finite `τ`. -/
lemma map_stoppedHist_min_eq_map_truncHist {P : Measure Ω} (hτ : Measurable τ)
    (hτ_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (M : ℕ) :
    P.map (stoppedHist O X Y fun ω ↦ min (τ ω) M) =
      (P.map (stoppedHist O X Y τ)).map (truncHist M) := by
  rw [Measure.map_map (measurable_truncHist M) (measurable_stoppedHist hO hX hY hτ)]
  refine Measure.map_congr ?_
  filter_upwards [hτ_top] with ω hω
  exact (truncHist_stoppedHist hω).symm

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
`{τ ≤ M}` it is the law of the history stopped at `τ`, on `{M < τ}` it is the law of the history
of the first `M` rounds. -/
lemma map_stoppedHist_min_eq_add (M : ℕ) :
    P.map (stoppedHist O X Y fun ω ↦ min (stoppingTime O X Y S ω) M) =
      (P.restrict {ω | stoppingTime O X Y S ω ≤ M}).map
          (stoppedHist O X Y fun ω ↦ min (stoppingTime O X Y S ω) M) +
        ((P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}).map (history O X Y M)).map
          (Sigma.mk M) := by
  have hZ := measurable_stoppedHist_min hO hX hY (measurable_stoppingTime hO hX hY hS) M
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := P)
    (measurableSet_stoppingTime_le hO hX hY hS M), Measure.map_add _ _ hZ,
    compl_setOf_stoppingTime_le]
  congr 1
  rw [Measure.map_map (measurable_sigma_mk M) (measurable_history hO hX hY M)]
  refine Measure.map_congr ((ae_restrict_iff' (measurableSet_lt_stoppingTime hO hX hY hS M)).2
    (Filter.Eventually.of_forall fun ω hω ↦ ?_))
  exact stoppedHist_min_of_lt hω

/-- The law of the history stopped at `min τ (M + 1)` splits according to whether `τ ≤ M`: on
`{τ ≤ M}` it is the law of the history stopped at `min τ M`, on `{M < τ}` it is the law of the
history of the first `M + 1` rounds. -/
lemma map_stoppedHist_min_succ_eq_add (M : ℕ) :
    P.map (stoppedHist O X Y fun ω ↦ min (stoppingTime O X Y S ω) (M + 1 : ℕ)) =
      (P.restrict {ω | stoppingTime O X Y S ω ≤ M}).map
          (stoppedHist O X Y fun ω ↦ min (stoppingTime O X Y S ω) M) +
        ((P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}).map (history O X Y (M + 1))).map
          (Sigma.mk (M + 1)) := by
  have hZ := measurable_stoppedHist_min hO hX hY (measurable_stoppingTime hO hX hY hS) (M + 1)
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := P)
    (measurableSet_stoppingTime_le hO hX hY hS M), Measure.map_add _ _ hZ,
    compl_setOf_stoppingTime_le]
  congr 1
  · refine Measure.map_congr ((ae_restrict_iff' (measurableSet_stoppingTime_le hO hX hY hS M)).2
      (Filter.Eventually.of_forall fun ω hω ↦ ?_))
    rw [stoppedHist_min_of_le hω, stoppedHist_min_of_le (hω.trans (by exact_mod_cast M.le_succ))]
  · rw [Measure.map_map (measurable_sigma_mk (M + 1)) (measurable_history hO hX hY (M + 1))]
    refine Measure.map_congr ((ae_restrict_iff' (measurableSet_lt_stoppingTime hO hX hY hS M)).2
      (Filter.Eventually.of_forall fun ω hω ↦ ?_))
    exact stoppedHist_min_succ_of_lt hω

omit hO hX hY hS in
/-- The image of the restriction of `P` to `A` by `f` gives measure zero to a set avoided by `f`
on `A`. -/
lemma _root_.MeasureTheory.Measure.map_restrict_apply_of_forall_notMem {H : Type*}
    {mH : MeasurableSpace H} {f : Ω → H} (hf : Measurable f) {A : Set Ω} {T : Set H}
    (hT : MeasurableSet T) (h : ∀ ω ∈ A, f ω ∉ T) : ((P.restrict A).map f) T = 0 := by
  rw [Measure.map_apply hf hT, Measure.restrict_apply (hf hT)]
  exact measure_mono_null (fun ω hω ↦ (h ω hω.2 hω.1).elim) measure_empty

/-- On `{τ ≤ M}`, the history stopped at `min τ M` belongs to the stopping rule. -/
lemma map_restrict_stoppingTime_le_stoppedHist_min_apply_compl (M : ℕ) :
    ((P.restrict {ω | stoppingTime O X Y S ω ≤ M}).map
      (stoppedHist O X Y fun ω ↦ min (stoppingTime O X Y S ω) M)) Sᶜ = 0 := by
  refine Measure.map_restrict_apply_of_forall_notMem
    (measurable_stoppedHist_min hO hX hY (measurable_stoppingTime hO hX hY hS) M) hS.compl
    fun ω hω h ↦ h ?_
  rw [stoppedHist_min_of_le hω]
  exact stoppedHist_mem_of_ne_top (ne_top_of_le_ne_top (ENat.natCast_ne_top M) hω)

/-- The history stopped at `min τ M` has length at most `M`. -/
lemma map_restrict_stoppedHist_min_apply_compl_fst_le (A : Set Ω) (M : ℕ) :
    ((P.restrict A).map (stoppedHist O X Y fun ω ↦ min (stoppingTime O X Y S ω) M))
      {h | h.1 ≤ M}ᶜ = 0 :=
  Measure.map_restrict_apply_of_forall_notMem
    (measurable_stoppedHist_min hO hX hY (measurable_stoppingTime hO hX hY hS) M)
    (measurableSet_fst_le M).compl fun _ _ h ↦ h fst_stoppedHist_min_le

/-- On `{M < τ}`, the history of the first `M` rounds does not belong to the stopping rule. -/
lemma map_restrict_lt_stoppingTime_map_sigmaMk_apply (M : ℕ) :
    (((P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}).map (history O X Y M)).map
      (Sigma.mk M)) S = 0 := by
  rw [Measure.map_map (measurable_sigma_mk M) (measurable_history hO hX hY M)]
  exact Measure.map_restrict_apply_of_forall_notMem
    ((measurable_sigma_mk M).comp (measurable_history hO hX hY M)) hS
    fun ω hω ↦ notMem_of_lt_stoppingTime hω

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

/-- On the event `{M < τ}`, the law of the first `M + 1` rounds is the composition-product of
the law of the first `M` rounds with the step kernel. -/
lemma IsAlgEnvSeq.map_history_succ_restrict_lt_stoppingTime (h : IsAlgEnvSeq O X Y alg env P)
    (hS : MeasurableSet S) (M : ℕ) :
    (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}).map (history O X Y (M + 1)) =
      ((P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}).map (history O X Y M) ⊗ₘ
        stepKernel alg env M).map ((MeasurableEquiv.finSuccProd (Round 𝓞 𝓐 𝓨) M).symm) := by
  rw [history_succ, ← (h.hasCondDistrib_step_restrict_lt_stoppingTime hS M).map_eq,
    Measure.map_map (MeasurableEquiv.finSuccProd (Round 𝓞 𝓐 𝓨) _).symm.measurable]
  exact (h.measurable_history _).prodMk (h.measurable_step _)

/-- On the event `{M < τ}`, the law of the first `M` rounds together with the observation at
round `M` is the composition-product of the law of the first `M` rounds with the observation
kernel. -/
lemma IsAlgEnvSeq.map_history_obs_restrict_lt_stoppingTime (h : IsAlgEnvSeq O X Y alg env P)
    (hS : MeasurableSet S) (M : ℕ) :
    (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}).map
        (fun ω ↦ (history O X Y M ω, O M ω)) =
      (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}).map (history O X Y M) ⊗ₘ env.obs M := by
  obtain ⟨B, hB, hB_eq⟩ :=
    exists_measurableSet_preimage_lt_stoppingTime (O := O) (X := X) (Y := Y) hS M
  rw [hB_eq]
  exact ((h.hasCondDistrib_obs M).restrict_preimage (h.measurable_history M) (h.measurable_obs M)
    hB).map_eq

/-- On the event `{M < τ}`, the law of the action at round `M` is the policy applied to the law
of the first `M` rounds and of the observation at round `M`. -/
lemma IsAlgEnvSeq.map_action_restrict_lt_stoppingTime (h : IsAlgEnvSeq O X Y alg env P)
    (hS : MeasurableSet S) (M : ℕ) :
    (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}).map (X M) =
      alg.policy M ∘ₘ (P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}).map
        (fun ω ↦ (history O X Y M ω, O M ω)) := by
  obtain ⟨B, hB, hB_eq⟩ :=
    exists_measurableSet_preimage_lt_stoppingTime (O := O) (X := X) (Y := Y) hS M
  have hB' : history O X Y M ⁻¹' B = (fun ω ↦ (history O X Y M ω, O M ω)) ⁻¹' (B ×ˢ Set.univ) := by
    ext ω
    simp
  rw [hB_eq, hB']
  exact ((h.hasCondDistrib_action M).restrict_preimage
    ((h.measurable_history M).prodMk (h.measurable_obs M)) (h.measurable_action M)
    (hB.prod MeasurableSet.univ)).hasLaw_comp.map_eq

end filtration

end Learning
