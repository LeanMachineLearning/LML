/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.SequentialLearning.Algorithm
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Martingale.BorelCantelli

import LeanMachineLearning.ForMathlib.Probability.Process.HittingTime

/-!
# Bookkeeping definitions for sequential learning problems with discrete actions

We define the number of times each action was chosen, the time at which an action was chosen for
the `m`-th time and the reward obtained at that time.
The sums of rewards and empirical means are in `SequentialLearning/SumRewards.lean`.

For each definition that takes as arguments a time `t : ℕ`, an outcome `ω : Ω`, and possibly
other parameters, we put the time and the outcome at the end in this order, so that the definition
can be seen as a stochastic process indexed by time `t`.

## Main definitions

* `pullCount A a t ω`: number of times action `a` was chosen before time `t`. `pullCount'` is the
  same quantity, as a function of the history.
* `stepsUntil A a m ω`: the time at which action `a` is chosen for the `m`-th time, or `⊤` if it
  is never chosen `m` times.
* `rewardByCount A R' a m ω`: the reward obtained when choosing action `a` for the `m`-th time.
* `rewardByCountUntil A R' t ω`: the array of rewards by count, truncated at time `t`.

## Main statements

* `IsAlgEnvSeq.isStronglyPredictable_pullCount`: `pullCount A a` is predictable.
* `IsAlgEnvSeq.isStoppingTime_stepsUntil`: `stepsUntil A a m` is a stopping time.
* `sum_pullCount`: the pull counts of all actions sum to the time.
-/

@[expose] public section

open MeasureTheory Finset Learning

namespace Learning

variable {𝓞 𝓐 R Ω : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {mR : MeasurableSpace R} {mΩ : MeasurableSpace Ω}
  [DecidableEq 𝓐]
  {alg : Algorithm 𝓞 𝓐 R} {env : Environment 𝓞 𝓐 R}
  {P : Measure Ω}
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {R' : ℕ → Ω → R}
  {a : 𝓐} {m n t : ℕ} {ω : Ω}

section PullCount

/-- Number of times action `a` was chosen up to time `t` (excluding `t`). -/
noncomputable
def pullCount (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : ℕ :=
  #(filter (fun s ↦ A s ω = a) (range t))

/-- Number of pulls of arm `a` in the history before time `n`.
This is the number of entries in `h` in which the arm is `a`. -/
noncomputable
def pullCount' (n : ℕ) (h : Hist 𝓞 𝓐 R n) (a : 𝓐) : ℕ := #{s | (h s).action = a}

@[simp]
lemma pullCount_zero (a : 𝓐) : pullCount A a 0 = 0 := by ext; simp [pullCount]

lemma pullCount_zero_apply (a : 𝓐) (ω : Ω) : pullCount A a 0 ω = 0 := by simp

lemma pullCount_one : pullCount A a 1 ω = if A 0 ω = a then 1 else 0 := by
  simp only [pullCount, range_one]
  split_ifs with h
  · rw [card_eq_one]
    refine ⟨0, by simp [h]⟩
  · simp [h]

lemma monotone_pullCount (a : 𝓐) (ω : Ω) : Monotone (pullCount A a · ω) :=
  fun _ _ _ ↦ card_le_card (filter_subset_filter _ (by simpa))

@[mono, gcongr]
lemma pullCount_mono (a : 𝓐) {n m : ℕ} (hnm : n ≤ m) (ω : Ω) :
    pullCount A a n ω ≤ pullCount A a m ω :=
  monotone_pullCount a ω hnm

lemma pullCount_action_eq_pullCount_add_one (t : ℕ) (ω : Ω) :
    pullCount A (A t ω) (t + 1) ω = pullCount A (A t ω) t ω + 1 := by
  simp [pullCount, range_add_one, filter_insert]

lemma pullCount_eq_pullCount_of_action_ne (ha : A t ω ≠ a) :
    pullCount A a (t + 1) ω = pullCount A a t ω := by
  simp [pullCount, range_add_one, filter_insert, ha]

lemma pullCount_add_one :
    pullCount A a (t + 1) ω = pullCount A a t ω + if A t ω = a then 1 else 0 := by
  split_ifs with h
  · rw [← h, pullCount_action_eq_pullCount_add_one]
  · rw [pullCount_eq_pullCount_of_action_ne h, add_zero]

lemma pullCount_eq_sum (a : 𝓐) (t : ℕ) (ω : Ω) :
    pullCount A a t ω = ∑ s ∈ range t, if A s ω = a then 1 else 0 := by simp [pullCount]

lemma pullCount'_eq_sum (n : ℕ) (h : Hist 𝓞 𝓐 R n) (a : 𝓐) :
    pullCount' n h a = ∑ s : Fin n, if (h s).action = a then 1 else 0 := by simp [pullCount']

lemma pullCount_eq_pullCount' {n : ℕ} {ω : Ω} :
    pullCount A a n ω = pullCount' n (history O A R' n ω) a := by
  rw [pullCount_eq_sum, pullCount'_eq_sum]
  exact (Fin.sum_univ_eq_sum_range (fun i ↦ if A i ω = a then 1 else 0) n).symm

/-- `pullCount A a n` is a function of the history before time `n`. -/
lemma pullCount_eq_comp_history (a : 𝓐) (n : ℕ) :
    pullCount A a n = (fun h : Hist 𝓞 𝓐 R n ↦ pullCount' n h a) ∘ history O A R' n := by
  ext ω
  exact pullCount_eq_pullCount'

/-- `pullCount A a n` is a function of the trajectory. -/
lemma pullCount_eq_comp_trajectory (a : 𝓐) (n : ℕ) :
    pullCount A a n =
      (fun p : ℕ → Round 𝓞 𝓐 R ↦ ∑ i ∈ range n, if (p i).action = a then 1 else 0) ∘
        trajectory O A R' := by
  ext
  simp [pullCount, trajectory]
  rfl

lemma pullCount'_mono {n m : ℕ} (hnm : n ≤ m) :
    pullCount' n (history O A R' n ω) a ≤ pullCount' m (history O A R' m ω) a := by
  rw [← pullCount_eq_pullCount' (O := O), ← pullCount_eq_pullCount' (O := O)]
  exact pullCount_mono a hnm _

lemma pullCount_le (a : 𝓐) (t : ℕ) (ω : Ω) : pullCount A a t ω ≤ t :=
  (card_filter_le _ _).trans_eq (by simp)

lemma pullCount_congr {ω' : Ω} (h_eq : ∀ i ≤ n, A i ω = A i ω') :
    pullCount A a (n + 1) ω = pullCount A a (n + 1) ω' := by
  unfold pullCount
  congr 1 with s
  simp only [mem_filter, mem_range, and_congr_right_iff]
  intro hs
  rw [Nat.lt_add_one_iff] at hs
  rw [h_eq s hs]

lemma pullCount_lt_of_forall_ne (h_lt : ∀ s, pullCount A a (s + 1) ω ≠ t) (ht : t ≠ 0) :
    pullCount A a n ω < t := by
  induction n with
  | zero => simpa using ht.bot_lt
  | succ n hn =>
    specialize h_lt n
    rw [pullCount_add_one] at h_lt ⊢
    grind

lemma exists_pullCount_eq_of_le (hnm : t ≤ pullCount A a (n + 1) ω) (ht : t ≠ 0) :
    ∃ s, pullCount A a (s + 1) ω = t := by
  by_contra! h_contra
  refine lt_irrefl (pullCount A a (n + 1) ω) ?_
  refine lt_of_lt_of_le ?_ hnm
  exact pullCount_lt_of_forall_ne h_contra ht

lemma pullCount_le_add (a : 𝓐) (n C : ℕ) (ω : Ω) :
    pullCount A a n ω ≤ C + 1 +
      ∑ s ∈ range n, {s | A s ω = a ∧ C < pullCount A a s ω}.indicator 1 s := by
  rw [pullCount_eq_sum]
  calc ∑ s ∈ range n, if A s ω = a then 1 else 0
  _ ≤ ∑ s ∈ range n, ({s | A s ω = a ∧ pullCount A a s ω ≤ C}.indicator 1 s +
      {s | A s ω = a ∧ C < pullCount A a s ω}.indicator 1 s) := by
    gcongr with s hs
    simp [Set.indicator_apply]
    grind
  _ = ∑ s ∈ range n, {s | A s ω = a ∧ pullCount A a s ω ≤ C}.indicator 1 s +
      ∑ s ∈ range n, {s | A s ω = a ∧ C < pullCount A a s ω}.indicator 1 s := by
    rw [Finset.sum_add_distrib]
  _ ≤ C + 1 + ∑ s ∈ range n, {s | A s ω = a ∧ C < pullCount A a s ω}.indicator 1 s := by
    gcongr
    have h_le n : ∑ s ∈ range n, {s | A s ω = a ∧ pullCount A a s ω ≤ C}.indicator 1 s ≤
        pullCount A a n ω := by
      rw [pullCount_eq_sum]
      gcongr with s hs
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
      grind
    induction n with
    | zero => simp
    | succ n hn =>
      rw [Finset.sum_range_succ]
      rcases le_or_gt (pullCount A a n ω) C with h_pc | h_pc
      · have hn' : ∑ s ∈ range n, {s | A s ω = a ∧ pullCount A a s ω ≤ C}.indicator 1 s ≤ C :=
          (h_le n).trans h_pc
        grw [hn']
        gcongr
        simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
        grind
      · refine le_trans ?_ hn
        simp [h_pc]

section Measurability

@[fun_prop]
lemma measurable_pullCount [MeasurableSingletonClass 𝓐] (hA : ∀ n, Measurable (A n))
    (a : 𝓐) (t : ℕ) :
    Measurable (fun ω : Ω ↦ pullCount A a t ω) := by
  simp_rw [pullCount_eq_sum]
  have h_meas s : Measurable (fun ω : Ω ↦ if A s ω = a then 1 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_uncurry_pullCount [MeasurableEq 𝓐]
    (hA : ∀ n, Measurable (A n)) (t : ℕ) :
    Measurable (fun p : Ω × 𝓐 ↦ pullCount A p.2 t p.1) := by
  simp_rw [pullCount_eq_sum]
  have h_meas s : Measurable (fun h : Ω × 𝓐 ↦ if A s h.1 = h.2 then 1 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_uncurry_pullCount_comp [Countable 𝓐] [MeasurableSingletonClass 𝓐]
    (hA : ∀ n, Measurable (A n)) {f : Ω → 𝓐} (hf : Measurable f) {g : Ω → ℕ} (hg : Measurable g) :
    Measurable (fun ω ↦ pullCount A (f ω) (g ω) ω) := by
  have h_meas a : Measurable (fun ω ↦ pullCount A a (g ω) ω) :=
    (measurable_from_prod_countable_right (f := fun p : ℕ × Ω ↦ pullCount A a p.1 p.2)
      (measurable_pullCount hA a)).comp (hg.prodMk measurable_id)
  exact (measurable_from_prod_countable_right (f := fun p : 𝓐 × Ω ↦ pullCount A p.1 (g p.2) p.2)
    h_meas).comp (hf.prodMk measurable_id)

@[fun_prop]
lemma measurable_pullCount' [MeasurableSingletonClass 𝓐] (n : ℕ) (a : 𝓐) :
    Measurable (fun h : Hist 𝓞 𝓐 R n ↦ pullCount' n h a) := by
  simp_rw [pullCount'_eq_sum]
  have h_meas s : Measurable (fun (h : Hist 𝓞 𝓐 R n) ↦ if (h s).action = a then 1 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_uncurry_pullCount' [MeasurableEq 𝓐] (n : ℕ) :
    Measurable (fun p : Hist 𝓞 𝓐 R n × 𝓐 ↦ pullCount' n p.1 p.2) := by
  simp_rw [pullCount'_eq_sum]
  have h_meas s : Measurable
      (fun h : Hist 𝓞 𝓐 R n × 𝓐 ↦ if (h.1 s).action = h.2 then 1 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
  fun_prop

lemma IsAlgEnvSeq.adapted_pullCount_add_one [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq O A R' alg env P) (a : 𝓐) :
    Adapted h.filtration (fun n ↦ pullCount A a (n + 1)) := by
  intro n
  beta_reduce
  rw [h.filtration_eq_comap, pullCount_eq_comp_history (O := O) (R' := R')]
  exact measurable_comp_comap _ (measurable_pullCount' (n + 1) a)

lemma IsAlgEnvSeq.stronglyAdapted_pullCount_add_one [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq O A R' alg env P) (a : 𝓐) :
    StronglyAdapted h.filtration (fun n ↦ pullCount A a (n + 1)) :=
  (h.adapted_pullCount_add_one a).stronglyAdapted

lemma IsAlgEnvSeq.isStronglyPredictable_pullCount [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq O A R' alg env P) (a : 𝓐) :
    IsStronglyPredictable h.filtration (pullCount A a) := by
  rw [IsStronglyPredictable.iff_measurable_add_one]
  refine ⟨?_, h.stronglyAdapted_pullCount_add_one a⟩
  simp only [pullCount_zero]
  fun_prop

lemma measurableSet_action_eq_and_pullCount_eq [MeasurableSingletonClass 𝓐]
    (hA : ∀ n, Measurable (A n)) (t : ℕ) (b : 𝓐) (k : ℕ) :
    MeasurableSet {x | A t x = b ∧ pullCount A b t x = k} :=
  ((measurableSet_singleton _).preimage (hA t)).inter
    ((measurableSet_singleton _).preimage (measurable_pullCount hA b t))

lemma measurableSet_snd_eq_and_pullCount'_eq [MeasurableSingletonClass 𝓐]
    (n : ℕ) (b : 𝓐) (k : ℕ) :
    MeasurableSet {u : (Hist 𝓞 𝓐 R n × 𝓞) × 𝓐 | u.2 = b ∧ pullCount' n u.1.1 b = k} :=
  ((measurableSet_singleton _).preimage measurable_snd).inter
    ((measurableSet_singleton _).preimage
      ((measurable_pullCount' n b).comp (measurable_fst.comp measurable_fst)))

/-- The event that the action at time `n` is `b` and that `b` was pulled `k` times before is
a preimage by `((history O A R' n, O n), A n)`. -/
lemma setOf_action_eq_and_pullCount_eq_eq_preimage (n : ℕ) (b : 𝓐) (k : ℕ) :
    {x | A n x = b ∧ pullCount A b n x = k}
      = (fun x ↦ ((history O A R' n x, O n x), A n x))
        ⁻¹' {u | u.2 = b ∧ pullCount' n u.1.1 b = k} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  rw [pullCount_eq_pullCount' (O := O) (R' := R')]

lemma integrable_pullCount [IsFiniteMeasure P] [MeasurableSingletonClass 𝓐]
    (hA : ∀ n, Measurable (A n)) (a : 𝓐) (n : ℕ) :
    Integrable (fun ω ↦ (pullCount A a n ω : ℝ)) P := by
  refine integrable_of_le_of_le (g₁ := 0) (g₂ := fun _ ↦ n) (by fun_prop)
    (ae_of_all _ fun ω ↦ by simp) (ae_of_all _ fun ω ↦ ?_) (integrable_const _) (integrable_const _)
  simp only [Nat.cast_le]
  exact pullCount_le a n ω

end Measurability

end PullCount

section StepsUntil

-- TODO: replace this by leastGE, once leastGE is generalized
/-- Number of steps until action `a` was pulled exactly `m` times. -/
noncomputable
def stepsUntil (A : ℕ → Ω → 𝓐) (a : 𝓐) (m : ℕ) (ω : Ω) : ℕ∞ :=
  sInf ((↑) '' {s | pullCount A a (s + 1) ω = m})

lemma stepsUntil_eq_top_iff : stepsUntil A a m ω = ⊤ ↔ ∀ s, pullCount A a (s + 1) ω ≠ m := by
  simp [stepsUntil, sInf_eq_top]

lemma stepsUntil_ne_top (h_exists : ∃ s, pullCount A a (s + 1) ω = m) : stepsUntil A a m ω ≠ ⊤ := by
  simpa [stepsUntil_eq_top_iff]

lemma exists_pullCount_eq (h' : stepsUntil A a m ω ≠ ⊤) :
    ∃ s, pullCount A a (s + 1) ω = m := by
  by_contra! h_contra
  rw [← stepsUntil_eq_top_iff] at h_contra
  simp [h_contra] at h'

lemma stepsUntil_zero_of_ne (hka : A 0 ω ≠ a) : stepsUntil A a 0 ω = 0 := by
  unfold stepsUntil
  simp_rw [← bot_eq_zero, sInf_eq_bot, bot_eq_zero]
  intro n hn
  refine ⟨0, ?_, hn⟩
  simp only [Set.mem_image, Set.mem_ofPred_eq, Nat.cast_eq_zero, exists_eq_right, zero_add]
  rw [← zero_add 1, pullCount_eq_pullCount_of_action_ne hka]
  simp

lemma stepsUntil_zero_of_eq (hka : A 0 ω = a) : stepsUntil A a 0 ω = ⊤ := by
  rw [stepsUntil_eq_top_iff]
  suffices 0 < pullCount A a 1 ω from fun _ ↦ (this.trans_le (monotone_pullCount _ _ (by lia))).ne'
  rw [← hka, ← zero_add 1, pullCount_action_eq_pullCount_add_one]
  simp

lemma stepsUntil_eq_dite (a : 𝓐) (m : ℕ) (ω : Ω)
    [Decidable (∃ s, pullCount A a (s + 1) ω = m)] :
    stepsUntil A a m ω =
      if h : ∃ s, pullCount A a (s + 1) ω = m then (Nat.find h : ℕ∞) else ⊤ := by
  unfold stepsUntil
  split_ifs with h'
  · refine le_antisymm ?_ ?_
    · refine sInf_le ?_
      simpa using Nat.find_spec h'
    · simp only [le_sInf_iff, Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, Nat.cast_le, Nat.find_le_iff]
      exact fun n hn ↦ ⟨n, le_rfl, hn⟩
  · push Not at h'
    suffices {s | pullCount A a (s + 1) ω = m} = ∅ by simp [this]
    ext s
    simpa using (h' s)

lemma stepsUntil_pullCount_le (ω : Ω) (a : 𝓐) (t : ℕ) :
    stepsUntil A a (pullCount A a (t + 1) ω) ω ≤ t := by
  rw [stepsUntil]
  exact csInf_le (OrderBot.bddBelow _) ⟨t, rfl, rfl⟩

lemma stepsUntil_pullCount_eq (ω : Ω) (t : ℕ) :
    stepsUntil A (A t ω) (pullCount A (A t ω) (t + 1) ω) ω = t := by
  apply le_antisymm (stepsUntil_pullCount_le ω (A t ω) t)
  suffices ∀ t', pullCount A (A t ω) (t' + 1) ω = pullCount A (A t ω) t ω + 1 → t ≤ t' by
    simpa [stepsUntil, pullCount_action_eq_pullCount_add_one]
  exact fun t' h' ↦ Nat.le_of_lt_succ ((monotone_pullCount (A t ω) ω).reflect_lt
    (h' ▸ lt_add_one _))

/-- If we pull action `a` at time 0, the first time at which it is pulled once is 0. -/
lemma stepsUntil_one_of_eq (hka : A 0 ω = a) : stepsUntil A a 1 ω = 0 := by
  classical
  have h_pull : pullCount A a 1 ω = 1 := by simp [pullCount_one, hka]
  have h_le := stepsUntil_pullCount_le (A := A) ω a 0
  simpa [h_pull] using h_le

lemma stepsUntil_eq_zero_iff :
    stepsUntil A a m ω = 0 ↔ (m = 0 ∧ A 0 ω ≠ a) ∨ (m = 1 ∧ A 0 ω = a) := by
  classical
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · have h_exists : ∃ s, pullCount A a (s + 1) ω = m := exists_pullCount_eq (by simp [h'])
    simp only [stepsUntil_eq_dite, h_exists, ↓reduceDIte, Nat.cast_eq_zero, Nat.find_eq_zero,
      zero_add] at h'
    rw [pullCount_one] at h'
    by_cases hka : A 0 ω = a <;> simp_all
  · cases h' with
  | inl h =>
    rw [h.1, stepsUntil_zero_of_ne h.2]
  | inr h =>
    rw [h.1]
    exact stepsUntil_one_of_eq h.2

lemma action_stepsUntil (hm : m ≠ 0) (h_exists : ∃ s, pullCount A a (s + 1) ω = m) :
    A (stepsUntil A a m ω).toNat ω = a := by
  classical
  simp only [stepsUntil_eq_dite, h_exists, ↓reduceDIte, ENat.toNat_natCast]
  have h_spec := Nat.find_spec h_exists
  have h_spec' n := Nat.find_min h_exists (m := n)
  by_cases h_zero : Nat.find h_exists = 0
  · simp only [h_zero, zero_add, not_lt_zero, IsEmpty.forall_iff, implies_true] at *
    by_contra h_ne
    rw [← zero_add 1, pullCount_eq_pullCount_of_action_ne h_ne] at h_spec
    simp only [pullCount_zero] at h_spec
    exact hm h_spec.symm
  have h_pos : 0 < Nat.find h_exists := Nat.pos_of_ne_zero h_zero
  by_contra h_ne
  refine h_spec' (Nat.find h_exists - 1) ?_ ?_
  · simp [h_pos]
  rw [Nat.sub_add_cancel (by omega)]
  rwa [← pullCount_eq_pullCount_of_action_ne]

lemma action_eq_of_stepsUntil_eq_coe (hm : m ≠ 0) (h : stepsUntil A a m ω = n) :
    A n ω = a := by
  have : n = (stepsUntil A a m ω).toNat := by simp [h]
  rw [this]
  have h_exists : ∃ s, pullCount A a (s + 1) ω = m := exists_pullCount_eq (by simp [h])
  exact action_stepsUntil hm h_exists

lemma pullCount_stepsUntil_add_one (h_exists : ∃ s, pullCount A a (s + 1) ω = m) :
    pullCount A a (stepsUntil A a m ω + 1).toNat ω = m := by
  classical
  have h_eq := stepsUntil_eq_dite (A := A) a m ω
  simp only [h_exists, ↓reduceDIte] at h_eq
  have h' := Nat.find_spec h_exists
  rw [h_eq]
  rw [ENat.toNat_add (by simp) (by simp)]
  simp only [ENat.toNat_natCast, ENat.toNat_one]
  exact h'

lemma pullCount_stepsUntil (hm : m ≠ 0) (h_exists : ∃ s, pullCount A a (s + 1) ω = m) :
    pullCount A a (stepsUntil A a m ω).toNat ω = m - 1 := by
  have h_action := action_eq_of_stepsUntil_eq_coe (A := A) (n := (stepsUntil A a m ω).toNat)
    (a := a) (ω := ω) hm ?_
  swap; · symm; simpa [stepsUntil_eq_top_iff]
  have h_add_one := pullCount_stepsUntil_add_one h_exists
  nth_rw 1 [← h_action] at h_add_one
  rw [ENat.toNat_add ?_ (by simp), ENat.toNat_one, pullCount_action_eq_pullCount_add_one]
    at h_add_one
  swap; · simpa [stepsUntil_eq_top_iff]
  grind

lemma pullCount_lt_of_lt_stepsUntil (a : 𝓐) {n m : ℕ} (ω : Ω)
    (h_exists : ∃ s, pullCount A a (s + 1) ω = m) (hn : n < stepsUntil A a m ω) :
    pullCount A a (n + 1) ω < m := by
  classical
  have h_eq := stepsUntil_eq_dite (A := A) a m ω
  simp only [h_exists, ↓reduceDIte] at h_eq
  rw [← ENat.natCast_toNat (stepsUntil_ne_top h_exists)] at hn
  refine lt_of_le_of_ne ?_ ?_
  · calc pullCount A a (n + 1) ω
    _ ≤ pullCount A a (stepsUntil A a m ω + 1).toNat ω := by
      refine monotone_pullCount a ω ?_
      rw [ENat.toNat_add (stepsUntil_ne_top h_exists) (by simp)]
      simp only [ENat.toNat_one, add_le_add_iff_right]
      exact mod_cast hn.le
    _ = m := pullCount_stepsUntil_add_one h_exists
  · refine Nat.find_min h_exists (m := n) ?_
    suffices n < (stepsUntil A a m ω).toNat by
      rwa [h_eq, ENat.toNat_natCast] at this
    exact mod_cast hn

lemma pullCount_eq_of_stepsUntil_eq_coe {ω : Ω} (hm : m ≠ 0)
    (h : stepsUntil A a m ω = n) :
    pullCount A a n ω = m - 1 := by
  have : n = (stepsUntil A a m ω).toNat := by simp [h]
  rw [this, pullCount_stepsUntil hm]
  exact exists_pullCount_eq (by simp [h])

lemma pullCount_add_one_eq_of_stepsUntil_eq_coe {ω : Ω}
    (h : stepsUntil A a m ω = n) :
    pullCount A a (n + 1) ω = m := by
  have : n + 1 = (stepsUntil A a m ω + 1).toNat := by
    rw [ENat.toNat_add (by simp [h]) (by simp)]; simp [h]
  rw [this, pullCount_stepsUntil_add_one]
  exact exists_pullCount_eq (by simp [h])

lemma stepsUntil_eq_iff {ω : Ω} (n : ℕ) :
    stepsUntil A a m ω = n ↔
      pullCount A a (n + 1) ω = m ∧ (∀ k < n, pullCount A a (k + 1) ω < m) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h_exists : ∃ s, pullCount A a (s + 1) ω = m := exists_pullCount_eq (by simp [h])
    refine ⟨pullCount_add_one_eq_of_stepsUntil_eq_coe h, fun k hk ↦ ?_⟩
    exact pullCount_lt_of_lt_stepsUntil a ω h_exists (by rw [h]; exact mod_cast hk)
  · classical
    rw [stepsUntil_eq_dite a m ω, dite_eq_left ⟨n, h.1⟩]
    simp only [Nat.cast_inj]
    rw [Nat.find_eq_iff]
    exact ⟨h.1, fun k hk ↦ (h.2 k hk).ne⟩

lemma stepsUntil_eq_iff' {ω : Ω} (hm : m ≠ 0) (n : ℕ) :
    stepsUntil A a m ω = n ↔ A n ω = a ∧ pullCount A a n ω = m - 1 := by
  by_cases hn : n = 0
  · simp [hn, stepsUntil_eq_zero_iff, hm]
    grind
  rw [stepsUntil_eq_iff n]
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩, fun ⟨h1, h2⟩ ↦ ⟨?_, fun k hk ↦ ?_⟩⟩
  · rw [pullCount_add_one] at h1
    specialize h2 (n - 1) (by lia)
    grind
  · rw [pullCount_add_one] at h1
    specialize h2 (n - 1) (by lia)
    grind
  · rw [pullCount_add_one, h1, h2]
    grind
  · rw [Nat.lt_iff_le_pred (by grind)]
    rw [← h2]
    refine monotone_pullCount a ω ?_
    grind

lemma stepsUntil_eq_congr {ω' : Ω} (h_eq : ∀ i ≤ n, A i ω = A i ω') :
    stepsUntil A a m ω = n ↔ stepsUntil A a m ω' = n := by
  simp_rw [stepsUntil_eq_iff n]
  congr! 1
  · rw [pullCount_congr h_eq]
  · congr! 3 with k hk
    rw [pullCount_congr]
    grind

lemma stepsUntil_eq_leastGE (a : 𝓐) (hm : m ≠ 0) :
    stepsUntil A a m = leastGE (fun n (ω : Ω) ↦ pullCount A a (n + 1) ω) m := by
  ext ω
  rw [leastGE]
  cases h : hittingAfter (fun n ω ↦ pullCount A a (n + 1) ω) (Set.Ici m) ⊥ ω with
  | top =>
    rw [hittingAfter_eq_top_iff] at h
    exact stepsUntil_eq_top_iff.2 fun s hs ↦ h s bot_le (by simp [hs])
  | coe n =>
    rw [hittingAfter_eq_coe_iff] at h
    simp only [Set.mem_Ici, Set.mem_Ico, Nat.bot_eq_zero, zero_le, true_and, not_le] at h
    -- the count increases by at most one at each step, so it reaches `m` exactly at time `n`
    refine (stepsUntil_eq_iff n).2 ⟨le_antisymm ?_ h.1, h.2⟩
    rw [pullCount_add_one]
    cases n with
    | zero => rw [pullCount_zero_apply]; split_ifs <;> omega
    | succ n => have := h.2 n (by omega); split_ifs <;> omega

lemma stepsUntil_mono (a : 𝓐) (ω : Ω) {n m : ℕ} (hn : n ≠ 0) (hnm : n ≤ m) :
    stepsUntil A a n ω ≤ stepsUntil A a m ω := by
  rw [stepsUntil_eq_leastGE a hn, stepsUntil_eq_leastGE a (by lia)]
  simp_rw [leastGE]
  exact hittingAfter_anti (fun n ω ↦ (pullCount A a (n + 1) ω)) 0 (fun x ↦ by grind) ω

section Measurability

lemma IsAlgEnvSeq.isStoppingTime_stepsUntil [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq O A R' alg env P) (a : 𝓐) (hm : m ≠ 0) :
    IsStoppingTime h.filtration (stepsUntil A a m) := by
  rw [stepsUntil_eq_leastGE _ hm]
  refine StronglyAdapted.isStoppingTime_leastGE _ fun n ↦ ?_
  suffices StronglyMeasurable[h.filtration n] (pullCount A a (n + 1)) by
    fun_prop
  refine Measurable.stronglyMeasurable ?_
  exact h.adapted_pullCount_add_one a n

@[fun_prop]
lemma measurable_stepsUntil [MeasurableSingletonClass 𝓐]
    (hA : ∀ n, Measurable (A n)) (a : 𝓐) (m : ℕ) :
    Measurable (stepsUntil A a m) := by
  refine measurable_to_countable' fun x ↦ ?_
  induction x using ENat.recTopCoe with
  | top =>
    have : stepsUntil A a m ⁻¹' {⊤} = ⋂ s, {ω | pullCount A a (s + 1) ω = m}ᶜ := by
      ext; simp [stepsUntil_eq_top_iff]
    rw [this]
    exact .iInter fun s ↦ (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl
  | coe n =>
    have : stepsUntil A a m ⁻¹' {(n : ℕ∞)} = {ω | pullCount A a (n + 1) ω = m} ∩
        ⋂ k < n, {ω | pullCount A a (k + 1) ω < m} := by
      ext; simp [stepsUntil_eq_iff]
    rw [this]
    exact (measurableSet_eq_fun (by fun_prop) (by fun_prop)).inter
      (.iInter fun k ↦ .iInter fun _ ↦ measurableSet_lt (by fun_prop) (by fun_prop))

lemma measurable_stepsUntil' [MeasurableSingletonClass 𝓐]
    (hA : ∀ n, Measurable (A n)) (a : 𝓐) (m : ℕ) :
    Measurable (fun ω : Ω × (ℕ → 𝓐 → R) ↦ stepsUntil A a m ω.1) :=
  (measurable_stepsUntil hA a m).comp measurable_fst

lemma measurable_comap_indicator_stepsUntil_eq [MeasurableSingletonClass 𝓐]
    (O : ℕ → Ω → 𝓞) (R' : ℕ → Ω → R) (a : 𝓐) (m n : ℕ) :
    Measurable[MeasurableSpace.comap
        (fun ω : Ω ↦ ((history O A R' n ω, O n ω), A n ω)) inferInstance]
      ({ω | stepsUntil A a m ω = ↑n}.indicator fun _ ↦ 1) := by
  by_cases hm : m = 0
  · simp only [hm]
    by_cases hn : n = 0
    · subst hn
      simp only [CharP.cast_eq_zero, stepsUntil_eq_zero_iff, ne_eq, true_and, zero_ne_one,
        false_and, or_false]
      refine Measurable.indicator measurable_const ?_
      refine (measurableSet_singleton _).compl.preimage ?_
      rw [measurable_iff_comap_le, Prod.instMeasurableSpace, MeasurableSpace.comap_prodMk]
      exact le_sup_of_le_right le_rfl
    · have : {ω | stepsUntil A a 0 ω = n} = ∅ := by
        ext ω
        by_cases ha : A 0 ω = a
        · simp [stepsUntil_zero_of_eq ha]
        · simp only [Set.mem_ofPred_eq, stepsUntil_zero_of_ne ha, Set.mem_empty_iff_false,
            iff_false]
          norm_cast
          exact Ne.symm hn
      simp [this]
  simp_rw [stepsUntil_eq_iff' hm]
  refine Measurable.indicator measurable_const ?_
  refine ((measurableSet_singleton _).preimage ?_).inter ((measurableSet_singleton _).preimage ?_)
  · rw [measurable_iff_comap_le, Prod.instMeasurableSpace, MeasurableSpace.comap_prodMk]
    exact le_sup_of_le_right le_rfl
  · have h_comp : pullCount A a n
        = (fun p : (Hist 𝓞 𝓐 R n × 𝓞) × 𝓐 ↦ pullCount' n p.1.1 a) ∘
          (fun ω ↦ ((history O A R' n ω, O n ω), A n ω)) := by
      rw [pullCount_eq_comp_history (O := O) (R' := R')]
      rfl
    rw [h_comp]
    exact measurable_comp_comap _ (by fun_prop)

lemma measurable_indicator_stepsUntil_eq [MeasurableSingletonClass 𝓐]
    (hA : ∀ n, Measurable (A n)) (a : 𝓐) (m n : ℕ) :
    Measurable ({ω : Ω | stepsUntil A a m ω = ↑n}.indicator fun _ ↦ 1) :=
  measurable_const.indicator (measurableSet_eq_fun (measurable_stepsUntil hA a m) measurable_const)

lemma measurableSet_stepsUntil_eq [MeasurableSingletonClass 𝓐]
    (O : ℕ → Ω → 𝓞) (R' : ℕ → Ω → R) (a : 𝓐) (m n : ℕ) :
    MeasurableSet[MeasurableSpace.comap
        (fun ω : Ω ↦ ((history O A R' n ω, O n ω), A n ω)) inferInstance]
      {ω : Ω | stepsUntil A a m ω = ↑n} := by
  let mProd := MeasurableSpace.comap
    (fun ω : Ω ↦ ((history O A R' n ω, O n ω), A n ω)) inferInstance
  suffices Measurable[mProd] ({ω | stepsUntil A a m ω = ↑n}.indicator fun x ↦ 1) by
    rwa [measurable_indicator_const_iff] at this
  exact measurable_comap_indicator_stepsUntil_eq O R' a m n

/-- `stepsUntil a m` is a stopping time with respect to the filtration `filtrationAction`. -/
lemma IsAlgEnvSeq.isStoppingTime_stepsUntil_filtrationAction [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq O A R' alg env P) (a : 𝓐) (m : ℕ) :
    IsStoppingTime h.filtrationAction (stepsUntil A a m) := by
  refine isStoppingTime_of_measurableSet_eq fun n ↦ ?_
  rw [h.filtrationAction_eq_comap n]
  exact measurableSet_stepsUntil_eq O R' a m n

end Measurability

end StepsUntil

section RewardByCount

/-- Reward obtained when pulling action `a` for the `m`-th time.
If it is never pulled `m` times, the reward is given by the second component of `ω`, which in
applications will be independent with the same law. -/
noncomputable
def rewardByCount (A : ℕ → Ω → 𝓐) (R' : ℕ → Ω → R) (a : 𝓐) (m : ℕ) (ω : Ω × (ℕ → 𝓐 → R)) : R :=
  match (stepsUntil A a m ω.1) with
  | ⊤ => ω.2 m a
  | (n : ℕ) => R' n ω.1

variable {ω : Ω × (ℕ → 𝓐 → R)}

lemma rewardByCount_eq_ite (a : 𝓐) (m : ℕ) (ω : Ω × (ℕ → 𝓐 → R)) :
    rewardByCount A R' a m ω =
      if (stepsUntil A a m ω.1) = ⊤ then ω.2 m a else R' (stepsUntil A a m ω.1).toNat ω.1 := by
  unfold rewardByCount
  cases stepsUntil A a m ω.1
  · simp; rfl
  · simp

lemma rewardByCount_eq_add [AddMonoid R] (a : 𝓐) (m : ℕ) :
    rewardByCount A R' a m =
      {ω : Ω × (ℕ → 𝓐 → R) | stepsUntil A a m ω.1 ≠ ⊤}.indicator
          (fun ω ↦ R' (stepsUntil A a m ω.1).toNat ω.1)
        + {ω | stepsUntil A a m ω.1 = ⊤}.indicator (fun ω ↦ ω.2 m a) := by
  ext ω
  simp only [rewardByCount_eq_ite, ne_eq, Pi.add_apply, Set.indicator_apply, Set.mem_ofPred_eq,
    ite_not]
  grind

lemma rewardByCount_of_stepsUntil_eq_top (h : stepsUntil A a m ω.1 = ⊤) :
    rewardByCount A R' a m ω = ω.2 m a := by simp [rewardByCount_eq_ite, h]

lemma rewardByCount_of_stepsUntil_ne_top (h : stepsUntil A a m ω.1 ≠ ⊤) :
    rewardByCount A R' a m ω = R' (stepsUntil A a m ω.1).toNat ω.1 := by
  simp [rewardByCount_eq_ite, h]

lemma rewardByCount_eq_stoppedValue (h : stepsUntil A a m ω.1 ≠ ⊤) :
    rewardByCount A R' a m ω = stoppedValue R' (stepsUntil A a m) ω.1 := by
  unfold stoppedValue
  rw [rewardByCount_of_stepsUntil_ne_top h]
  lift stepsUntil A a m ω.1 to ℕ using h with n
  simp

lemma rewardByCount_of_stepsUntil_eq_coe (h : stepsUntil A a m ω.1 = n) :
    rewardByCount A R' a m ω = R' n ω.1 := by simp [rewardByCount_eq_ite, h]

/-- The value at 0 does not matter (it would be the "zeroth" reward).
It should be considered a junk value. -/
@[simp]
lemma rewardByCount_zero (a : 𝓐) (ω : Ω × (ℕ → 𝓐 → R)) :
    rewardByCount A R' a 0 ω = if A 0 ω.1 = a then ω.2 0 a else R' 0 ω.1 := by
  rw [rewardByCount_eq_ite]
  by_cases ha : A 0 ω.1 = a
  · simp [ha, stepsUntil_zero_of_eq]
  · simp [stepsUntil_zero_of_ne, ha]

lemma rewardByCount_pullCount_add_one_eq_reward (t : ℕ) (ω : Ω × (ℕ → 𝓐 → R)) :
    rewardByCount A R' (A t ω.1) (pullCount A (A t ω.1) t ω.1 + 1) ω = R' t ω.1 := by
  rw [rewardByCount, ← pullCount_action_eq_pullCount_add_one, stepsUntil_pullCount_eq]

@[fun_prop]
lemma measurable_rewardByCount [MeasurableSingletonClass 𝓐]
    (hA : ∀ n, Measurable (A n)) (hR' : ∀ n, Measurable (R' n)) (a : 𝓐) (m : ℕ) :
    Measurable (fun ω : Ω × (ℕ → 𝓐 → R) ↦ rewardByCount A R' a m ω) := by
  simp_rw [rewardByCount_eq_ite]
  refine Measurable.ite ?_ ?_ ?_
  · exact (measurableSet_singleton _).preimage <| measurable_stepsUntil' hA a m
  · fun_prop
  · exact (measurable_from_prod_countable_right (f := fun p : ℕ × Ω ↦ R' p.1 p.2)
      hR').comp ((measurable_stepsUntil' hA a m).enat_toNat.prodMk (by fun_prop))

/-- Array of rewards by count, truncated at time `t`: the entry `(a, m)` is the reward received at
the `(m + 1)`-th pull of action `a` if that pull happened before time `t`, and the entry
`(m + 1, a)` of the auxiliary array `ω.2` otherwise.

This is an auxiliary definition used to prove results about the distribution of `rewardByCount`.

It is defined recursively: at time `t`, the
entry `(A t, pullCount A (A t) t)` is replaced by the reward `R' t`.
See `rewardByCountUntil_apply_of_lt_pullCount` and `rewardByCountUntil_apply_of_pullCount_le`. -/
noncomputable
def rewardByCountUntil (A : ℕ → Ω → 𝓐) (R' : ℕ → Ω → R) : ℕ → Ω × (ℕ → 𝓐 → R) → 𝓐 × ℕ → R
  | 0, ω => fun p ↦ ω.2 (p.2 + 1) p.1
  | t + 1, ω => Function.update (rewardByCountUntil A R' t ω)
      (A t ω.1, pullCount A (A t ω.1) t ω.1) (R' t ω.1)

@[simp]
lemma rewardByCountUntil_zero (ω : Ω × (ℕ → 𝓐 → R)) :
    rewardByCountUntil A R' 0 ω = fun p ↦ ω.2 (p.2 + 1) p.1 := rfl

lemma rewardByCountUntil_add_one (t : ℕ) (ω : Ω × (ℕ → 𝓐 → R)) :
    rewardByCountUntil A R' (t + 1) ω = Function.update (rewardByCountUntil A R' t ω)
      (A t ω.1, pullCount A (A t ω.1) t ω.1) (R' t ω.1) := rfl

/-- If action `a` was pulled at most `m` times before time `t`, then the entry `(a, m)` of
`rewardByCountUntil A R' t ω` is the entry `(m + 1, a)` of the auxiliary array. -/
lemma rewardByCountUntil_apply_of_pullCount_le (h : pullCount A a t ω.1 ≤ m) :
    rewardByCountUntil A R' t ω (a, m) = ω.2 (m + 1) a := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [rewardByCountUntil_add_one, Function.update_of_ne,
      ih ((pullCount_mono a (Nat.le_succ t) _).trans h)]
    intro hp
    obtain ⟨rfl, hm⟩ := Prod.mk.inj hp
    rw [pullCount_action_eq_pullCount_add_one] at h
    omega

/-- If action `a` was pulled more than `m` times before time `t`, then the entry `(a, m)` of
`rewardByCountUntil A R' t ω` is the reward received at the `(m + 1)`-th pull of `a`. -/
lemma rewardByCountUntil_apply_of_lt_pullCount (h : m < pullCount A a t ω.1) :
    rewardByCountUntil A R' t ω (a, m) = rewardByCount A R' a (m + 1) ω := by
  induction t with
  | zero => simp at h
  | succ t ih =>
    rw [rewardByCountUntil_add_one]
    by_cases hp : (a, m) = (A t ω.1, pullCount A (A t ω.1) t ω.1)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      rw [Function.update_self, rewardByCount_pullCount_add_one_eq_reward]
    · rw [Function.update_of_ne hp]
      refine ih ?_
      rw [pullCount_add_one] at h
      split_ifs at h with hA
      · rw [hA] at hp
        have hm : m ≠ pullCount A a t ω.1 := fun hm ↦ hp (by rw [hm])
        omega
      · simpa using h

/-- `rewardByCountUntil A R' t (x, z) p` depends on `z` only through `z (p.2 + 1) p.1`. -/
lemma rewardByCountUntil_congr {x : Ω} {z z' : ℕ → 𝓐 → R} (t : ℕ) (p : 𝓐 × ℕ)
    (hz : z (p.2 + 1) p.1 = z' (p.2 + 1) p.1) :
    rewardByCountUntil A R' t (x, z) p = rewardByCountUntil A R' t (x, z') p := by
  induction t with
  | zero => exact hz
  | succ t ih =>
    simp only [rewardByCountUntil_add_one, Function.update_apply]
    split_ifs
    · rfl
    · exact ih

/-- For each entry, `rewardByCountUntil A R' t ω` coincides with `rewardByCount` for `t` large
enough. -/
lemma eventually_rewardByCountUntil_eq (ω : Ω × (ℕ → 𝓐 → R)) (p : 𝓐 × ℕ) :
    ∀ᶠ t in Filter.atTop,
      rewardByCountUntil A R' t ω p = rewardByCount A R' p.1 (p.2 + 1) ω := by
  obtain ⟨a, m⟩ := p
  by_cases h : ∃ t, m < pullCount A a t ω.1
  · obtain ⟨t, ht⟩ := h
    filter_upwards [Filter.eventually_ge_atTop t] with s hs
    exact rewardByCountUntil_apply_of_lt_pullCount (ht.trans_le (pullCount_mono a hs ω.1))
  · push Not at h
    refine Filter.Eventually.of_forall fun t ↦ ?_
    rw [rewardByCountUntil_apply_of_pullCount_le (h t), rewardByCount_of_stepsUntil_eq_top]
    rw [stepsUntil_eq_top_iff]
    exact fun s ↦ ((h (s + 1)).trans_lt (Nat.lt_succ_self m)).ne

/-- Measurability of `rewardByCountUntil A R' t` with respect to a σ-algebra `m` for which the
actions and rewards before time `t` and the auxiliary array are measurable. -/
lemma measurable_rewardByCountUntil_of {m : MeasurableSpace (Ω × (ℕ → 𝓐 → R))}
    [MeasurableEq 𝓐] (t : ℕ)
    (hA : ∀ i < t, Measurable[m] (fun ω : Ω × (ℕ → 𝓐 → R) ↦ A i ω.1))
    (hR : ∀ i < t, Measurable[m] (fun ω : Ω × (ℕ → 𝓐 → R) ↦ R' i ω.1))
    (hZ : Measurable[m] (Prod.snd : Ω × (ℕ → 𝓐 → R) → ℕ → 𝓐 → R)) :
    Measurable[m] (rewardByCountUntil A R' t) := by
  induction t with
  | zero =>
    have : rewardByCountUntil A R' 0 = (fun z (p : 𝓐 × ℕ) ↦ z (p.2 + 1) p.1) ∘ Prod.snd := rfl
    rw [this]
    exact Measurable.comp (by fun_prop) hZ
  | succ t ih =>
    have ht : t < t + 1 := Nat.lt_succ_self t
    have ih := ih (fun i hi ↦ hA i (hi.trans ht)) (fun i hi ↦ hR i (hi.trans ht))
    have hg : Measurable[m] (fun ω : Ω × (ℕ → 𝓐 → R) ↦
        (A t ω.1, pullCount A (A t ω.1) t ω.1)) := by
      refine Measurable.prodMk (hA t ht) ?_
      simp_rw [pullCount_eq_sum]
      refine Finset.measurable_sum _ fun s hs ↦ Measurable.ite ?_ measurable_const measurable_const
      exact measurableSet_eq_fun (hA s ((Finset.mem_range.1 hs).trans ht)) (hA t ht)
    refine measurable_pi_iff.2 fun p ↦ ?_
    simp_rw [rewardByCountUntil_add_one, Function.update_apply]
    refine Measurable.ite ?_ (hR t ht) ((measurable_pi_apply p).comp ih)
    have h_set : {ω : Ω × (ℕ → 𝓐 → R) | p = (A t ω.1, pullCount A (A t ω.1) t ω.1)}
        = (fun ω : Ω × (ℕ → 𝓐 → R) ↦ (A t ω.1, pullCount A (A t ω.1) t ω.1)) ⁻¹' {p} := by
      ext ω
      simp [eq_comm]
    rw [h_set]
    exact hg (measurableSet_singleton p)

@[fun_prop]
lemma measurable_rewardByCountUntil [MeasurableEq 𝓐]
    (hA : ∀ n, Measurable (A n)) (hR' : ∀ n, Measurable (R' n)) (t : ℕ) :
    Measurable (rewardByCountUntil A R' t) :=
  measurable_rewardByCountUntil_of t (fun i _ ↦ (hA i).comp measurable_fst)
    (fun i _ ↦ (hR' i).comp measurable_fst) measurable_snd

end RewardByCount

lemma sum_pullCount_mul [Fintype 𝓐] [NonAssocSemiring R] (ω : Ω) (f : 𝓐 → R) (t : ℕ) :
    ∑ a, pullCount A a t ω * f a = ∑ s ∈ range t, f (A s ω) := by
  unfold pullCount
  classical
  simp_rw [card_eq_sum_ones]
  push_cast
  simp_rw [sum_mul, one_mul]
  exact sum_fiberwise' (range t) (A · ω) f

lemma sum_pullCount [Fintype 𝓐] {ω : Ω} : ∑ a, pullCount A a t ω = t := by
  simpa using sum_pullCount_mul (R := ℕ) ω 1 t

lemma sum_comp_pullCount [Fintype 𝓐] [AddCommMonoid R] (f : ℕ → R) (t : ℕ) (ω : Ω) :
    ∑ s ∈ range t, f (pullCount A (A s ω) s ω) = ∑ a, ∑ j ∈ range (pullCount A a t ω), f j := by
  induction t with
  | zero => simp
  | succ n ih =>
    have hf : f (pullCount A (A n ω) n ω) =
      ∑ a, if A n ω = a then f (pullCount A a n ω) else 0 := by simp
    simp_rw [sum_range_succ, ih, hf, ← sum_add_distrib, pullCount_add_one]
    congr 1 with a
    split_ifs
    · simp [sum_range_succ]
    · simp

lemma sum_pullCount' [Fintype 𝓐] (n : ℕ) (h : Hist 𝓞 𝓐 R n) : ∑ a, pullCount' n h a = n := by
  simp_rw [pullCount'_eq_sum]
  rw [Finset.sum_comm]
  have hcol (s : Fin n) : ∑ a, (if (h s).action = a then (1 : ℕ) else 0) = 1 := by
    simp [Finset.sum_ite_eq univ (h s).action (fun _ ↦ (1 : ℕ))]
  simp [hcol]

end Learning
