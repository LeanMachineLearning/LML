/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.SequentialLearning.Algorithm
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Martingale.BorelCantelli

/-!
# Bookkeeping definitions for finite action space sequential learning problems

If the number of actions is finite, it makes sense to define the number of times each action was
chosen, the time at which an action was chosen for the nth time, the value of the reward at that
time, the sum of rewards obtained for each action, the empirical mean reward for each action, etc.

For each definition that take as arguments a time `t : ℕ`, a history `h : ℕ → 𝓐 × R`, and possibly
other parameters, we put the time and history at the end in this order, so that the definition can
be seen as a stochastic process indexed by time `t` on the measurable space `ℕ → 𝓐 × R`.

-/

@[expose] public section

open MeasureTheory Finset Learning

namespace Learning

variable {𝓐 R Ω : Type*} {m𝓐 : MeasurableSpace 𝓐} {mR : MeasurableSpace R} {mΩ : MeasurableSpace Ω}
  [DecidableEq 𝓐]
  {alg : Algorithm 𝓐 R} {env : Environment 𝓐 R}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {R' : ℕ → Ω → R}
  {a : 𝓐} {m n t : ℕ} {ω : Ω}

section PullCount

/-- Number of times action `a` was chosen up to time `t` (excluding `t`). -/
noncomputable
def pullCount (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : ℕ :=
  #(filter (fun s ↦ A s ω = a) (range t))

/-- Number of pulls of arm `a` in the history before time `n`.
This is the number of entries in `h` in which the arm is `a`. -/
noncomputable
def pullCount' (n : ℕ) (h : Fin n → 𝓐 × R) (a : 𝓐) := #{s | (h s).1 = a}

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

lemma pullCount'_eq_sum (n : ℕ) (h : Fin n → 𝓐 × R) (a : 𝓐) :
    pullCount' n h a = ∑ s : Fin n, if (h s).1 = a then 1 else 0 := by simp [pullCount']

lemma pullCount_eq_pullCount' {n : ℕ} {ω : Ω} :
    pullCount A a n ω = pullCount' n (fun i ↦ (A i ω, R' i ω)) a := by
  rw [pullCount_eq_sum, pullCount'_eq_sum]
  exact (Fin.sum_univ_eq_sum_range (fun i ↦ if A i ω = a then 1 else 0) n).symm

/-- `pullCount A a n` is a function of the history before time `n`. -/
lemma pullCount_eq_comp_history (a : 𝓐) (n : ℕ) :
    pullCount A a n = (fun h : Fin n → 𝓐 × R ↦ pullCount' n h a) ∘ history A R' n := by
  ext ω
  exact pullCount_eq_pullCount'

lemma pullCount'_mono {n m : ℕ} (hnm : n ≤ m) :
    pullCount' n (fun i ↦ (A i ω, R' i ω)) a ≤ pullCount' m (fun i ↦ (A i ω, R' i ω)) a := by
  rw [← pullCount_eq_pullCount', ← pullCount_eq_pullCount']
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
  change Measurable ((fun aω ↦ pullCount A aω.1 (g aω.2) aω.2) ∘ fun ω ↦ (f ω, ω))
  apply Measurable.comp _ (by fun_prop)
  refine measurable_from_prod_countable_right fun a ↦ ?_
  change Measurable ((fun tω ↦ pullCount A a tω.1 tω.2) ∘ fun ω ↦ (g ω, ω))
  apply Measurable.comp _ (by fun_prop)
  exact measurable_from_prod_countable_right (fun t ↦ measurable_pullCount hA a t)

@[fun_prop]
lemma measurable_pullCount' [MeasurableSingletonClass 𝓐] (n : ℕ) (a : 𝓐) :
    Measurable (fun h : Fin n → 𝓐 × R ↦ pullCount' n h a) := by
  simp_rw [pullCount'_eq_sum]
  have h_meas s : Measurable (fun (h : Fin n → 𝓐 × R) ↦ if (h s).1 = a then 1 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_uncurry_pullCount' [MeasurableEq 𝓐] (n : ℕ) :
    Measurable (fun p : (Fin n → 𝓐 × R) × 𝓐 ↦ pullCount' n p.1 p.2) := by
  simp_rw [pullCount'_eq_sum]
  have h_meas s : Measurable (fun h : (Fin n → 𝓐 × R) × 𝓐 ↦ if (h.1 s).1 = h.2 then 1 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
  fun_prop

lemma adapted_pullCount_add_one [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq A R' alg env P) (a : 𝓐) :
    Adapted h.filtration (fun n ↦ pullCount A a (n + 1)) := by
  intro n
  change Measurable[h.filtration n] (pullCount A a (n + 1))
  rw [measurable_iff_comap_le, h.filtration_eq_comap, pullCount_eq_comp_history (R' := R'),
    ← measurable_iff_comap_le]
  exact measurable_comp_comap _ (measurable_pullCount' (n + 1) a)

lemma stronglyAdapted_pullCount_add_one [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq A R' alg env P) (a : 𝓐) :
    StronglyAdapted h.filtration (fun n ↦ pullCount A a (n + 1)) :=
  (adapted_pullCount_add_one h a).stronglyAdapted

lemma isStronglyPredictable_pullCount [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq A R' alg env P) (a : 𝓐) :
    IsStronglyPredictable h.filtration (pullCount A a) := by
  rw [IsStronglyPredictable.iff_measurable_add_one]
  refine ⟨?_, stronglyAdapted_pullCount_add_one h a⟩
  simp only [pullCount_zero]
  fun_prop

lemma integrable_pullCount [MeasurableSingletonClass 𝓐]
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

set_option backward.isDefEq.respectTransparency false in
lemma stepsUntil_eq_leastGE (a : 𝓐) (hm : m ≠ 0) :
    stepsUntil A a m = leastGE (fun n (ω : Ω) ↦ pullCount A a (n + 1) ω) m := by
  classical
  ext ω
  rw [stepsUntil_eq_dite]
  unfold leastGE hittingAfter
  simp only [Nat.bot_eq_zero, zero_le, Set.mem_Ici, true_and]
  have h_iff : (∃ s, pullCount A a (s + 1) ω = m) ↔ (∃ s, m ≤ pullCount A a (s + 1) ω) := by
    refine ⟨fun ⟨s, hs⟩ ↦ ⟨s, hs.ge⟩, fun ⟨s, hs⟩ ↦ ?_⟩
    exact exists_pullCount_eq_of_le hs hm
  by_cases h_exists : ∃ s, m ≤ pullCount A a (s + 1) ω
  swap; · simp_rw [h_iff]; simp [h_exists]
  rw [ite_eq_left h_exists, dite_eq_left]
  swap; · rwa [h_iff]
  simp only [ENat.some_eq_natCast, Nat.cast_inj]
  rw [Nat.find_eq_iff]
  constructor
  · apply le_antisymm
    · by_contra! h_contra
      obtain ⟨s, hs⟩ : ∃ s, pullCount A a (s + 1) ω = m := exists_pullCount_eq_of_le h_contra.le hm
      rw [← hs] at h_contra
      refine h_contra.not_ge ?_
      gcongr
      exact csInf_le (by simp) (by simp)
    · exact Nat.sInf_mem (s := {j | m ≤ pullCount A a (j + 1) ω}) h_exists
  · intro n hn h_contra
    refine hn.not_ge ?_
    exact csInf_le (by simp) (by simp [h_contra])

lemma stepsUntil_mono (a : 𝓐) (ω : Ω) {n m : ℕ} (hn : n ≠ 0) (hnm : n ≤ m) :
    stepsUntil A a n ω ≤ stepsUntil A a m ω := by
  rw [stepsUntil_eq_leastGE a hn, stepsUntil_eq_leastGE a (by lia)]
  simp_rw [leastGE]
  exact hittingAfter_anti (fun n ω ↦ (pullCount A a (n + 1) ω)) 0 (fun x ↦ by grind) ω

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
  exact h_ne

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

lemma pullCount_lt_of_le_stepsUntil (a : 𝓐) {n m : ℕ} (ω : Ω)
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
    exact pullCount_lt_of_le_stepsUntil a ω h_exists (by rw [h]; exact mod_cast hk)
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

section Measurability

lemma isStoppingTime_stepsUntil [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq A R' alg env P) (a : 𝓐) (hm : m ≠ 0) :
    IsStoppingTime h.filtration (stepsUntil A a m) := by
  rw [stepsUntil_eq_leastGE _ hm]
  refine StronglyAdapted.isStoppingTime_leastGE _ fun n ↦ ?_
  suffices StronglyMeasurable[h.filtration n] (pullCount A a (n + 1)) by
    fun_prop
  refine Measurable.stronglyMeasurable ?_
  exact adapted_pullCount_add_one h a n

-- todo: get this from the stopping time property?
@[fun_prop]
lemma measurable_stepsUntil [MeasurableSingletonClass 𝓐]
    (hA : ∀ n, Measurable (A n)) (a : 𝓐) (m : ℕ) :
    Measurable (stepsUntil A a m) := by
  classical
  have h_union : {h' : Ω | ∃ s, pullCount A a (s + 1) h' = m}
      = ⋃ s : ℕ, {h' | pullCount A a (s + 1) h' = m} := by ext; simp
  have h_meas_set : MeasurableSet {h' : Ω | ∃ s, pullCount A a (s + 1) h' = m} := by
    rw [h_union]
    refine MeasurableSet.iUnion fun s ↦ (measurableSet_singleton _).preimage ?_
    exact measurable_pullCount hA a (s + 1)
  suffices Measurable fun k ↦ if h : k ∈ {k' | ∃ s, pullCount A a (s + 1) k' = m}
      then (Nat.find h : ℕ∞) else ⊤ by
    convert this with ω
    rw [stepsUntil_eq_dite a m ω]
    rfl
  refine Measurable.dite (s := {k' : Ω | ∃ s, pullCount A a (s + 1) k' = m})
    (f := fun x ↦ (Nat.find x.2 : ℕ∞)) (g := fun _ ↦ ⊤) ?_ (by fun_prop) h_meas_set
  refine Measurable.coe_nat_enat ?_
  refine measurable_find _ fun k ↦ ?_
  suffices MeasurableSet {x : Ω | pullCount A a (k + 1) x = m} by
    have : Subtype.val '' {x : {k' : Ω |
          ∃ s, pullCount A a (s + 1) k' = m} | pullCount A a (k + 1) (x : Ω) = m}
        = {x : Ω | pullCount A a (k + 1) x = m} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.coe_ofPred, Set.mem_image, Subtype.exists, exists_and_left,
        exists_prop, exists_eq_right_right, and_iff_left_iff_imp]
      exact fun h ↦ ⟨_, h⟩
    refine (MeasurableEmbedding.subtype_coe h_meas_set).measurableSet_image.mp ?_
    rw [this]
    exact (measurableSet_singleton _).preimage (by fun_prop)
  exact (measurableSet_singleton _).preimage (by fun_prop)

lemma measurable_stepsUntil' [MeasurableSingletonClass 𝓐]
    (hA : ∀ n, Measurable (A n)) (a : 𝓐) (m : ℕ) :
    Measurable (fun ω : Ω × (ℕ → 𝓐 → R) ↦ stepsUntil A a m ω.1) :=
  (measurable_stepsUntil hA a m).comp measurable_fst

lemma measurable_comap_indicator_stepsUntil_eq [MeasurableSingletonClass 𝓐]
    (R' : ℕ → Ω → R) (a : 𝓐) (m n : ℕ) :
    Measurable[MeasurableSpace.comap
        (fun ω : Ω ↦ (history A R' n ω, A n ω)) inferInstance]
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
  · rw [measurable_iff_comap_le, Prod.instMeasurableSpace, MeasurableSpace.comap_prodMk]
    refine le_sup_of_le_left ?_
    rw [← measurable_iff_comap_le, pullCount_eq_comp_history (R' := R')]
    exact measurable_comp_comap _ (measurable_pullCount' n a)

lemma measurable_indicator_stepsUntil_eq [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq A R' alg env P) (a : 𝓐) (m n : ℕ) :
    Measurable ({ω : Ω | stepsUntil A a m ω = ↑n}.indicator fun _ ↦ 1) := by
  refine (measurable_comap_indicator_stepsUntil_eq (mR := mR) R' a m n).mono ?_ le_rfl
  refine Measurable.comap_le ?_
  have hA := h.measurable_action
  have hR' := h.measurable_feedback
  fun_prop

lemma measurableSet_stepsUntil_eq [MeasurableSingletonClass 𝓐]
    (R' : ℕ → Ω → R) (a : 𝓐) (m n : ℕ) :
    MeasurableSet[MeasurableSpace.comap (fun ω : Ω ↦ (history A R' n ω, A n ω))
        inferInstance]
      {ω : Ω | stepsUntil A a m ω = ↑n} := by
  let mProd := MeasurableSpace.comap
    (fun ω : Ω ↦ (history A R' n ω, A n ω)) inferInstance
  suffices Measurable[mProd] ({ω | stepsUntil A a m ω = ↑n}.indicator fun x ↦ 1) by
    rwa [measurable_indicator_const_iff] at this
  exact measurable_comap_indicator_stepsUntil_eq R' a m n

/-- `stepsUntil a m` is a stopping time with respect to the filtration `filtrationAction`. -/
lemma isStoppingTime_stepsUntil_filtrationAction [MeasurableSingletonClass 𝓐]
    (h : IsAlgEnvSeq A R' alg env P) (a : 𝓐) (m : ℕ) :
    IsStoppingTime h.filtrationAction (stepsUntil A a m) := by
  refine isStoppingTime_of_measurableSet_eq fun n ↦ ?_
  rw [h.filtrationAction_eq_comap n]
  exact measurableSet_stepsUntil_eq R' a m n

end Measurability

end StepsUntil

section RewardByCount

/-- Reward obtained when pulling action `a` for the `m`-th time.
If it is never pulled `m` times, the reward is given by the second component of `ω`, which in
applications will be indepedent with same law. -/
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
  · change Measurable ((fun p : ℕ × Ω ↦ R' p.1 p.2)
      ∘ (fun ω : Ω × (ℕ → 𝓐 → R) ↦ ((stepsUntil A a m ω.1).toNat, ω.1)))
    have : Measurable fun ω : Ω × (ℕ → 𝓐 → R) ↦ ((stepsUntil A a m ω.1).toNat, ω.1) :=
      (measurable_stepsUntil' hA a m).toNat.prodMk (by fun_prop)
    refine Measurable.comp ?_ this
    refine measurable_from_prod_countable_right fun n ↦ ?_
    simp only
    fun_prop

end RewardByCount

lemma sum_pullCount_mul [Fintype 𝓐] [Semiring R] (ω : Ω) (f : 𝓐 → R) (t : ℕ) :
    ∑ a, pullCount A a t ω * f a = ∑ s ∈ range t, f (A s ω) := by
  unfold pullCount
  classical
  simp_rw [card_eq_sum_ones]
  push_cast
  simp_rw [sum_mul, one_mul]
  exact sum_fiberwise' (range t) (A · ω) f

-- todo: only in ℝ for now
lemma sum_pullCount [Fintype 𝓐] {ω : Ω} : ∑ a, pullCount A a t ω = t := by
  suffices ∑ a, pullCount A a t ω * (1 : ℝ) = t by norm_cast at this; simpa
  rw [sum_pullCount_mul]
  simp

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

lemma sum_pullCount' [Fintype 𝓐] (n : ℕ) (h : Fin n → 𝓐 × ℝ) : ∑ a, pullCount' n h a = n := by
  simp_rw [pullCount'_eq_sum]
  rw [Finset.sum_comm]
  have hcol (s : Fin n) : ∑ a, (if (h s).1 = a then (1 : ℕ) else 0) = 1 := by
    simp [Finset.sum_ite_eq univ (h s).1 (fun _ ↦ (1 : ℕ))]
  simp [hcol]

end Learning
