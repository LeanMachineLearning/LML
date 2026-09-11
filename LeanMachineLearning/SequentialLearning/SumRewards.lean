/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.SequentialLearning.FiniteActions

/-!
# Sums of rewards
-/

@[expose] public section

open MeasureTheory Finset Learning

namespace Learning

variable {𝓞 𝓐 𝓨 Ω : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {mΩ : MeasurableSpace Ω}
  [DecidableEq 𝓐] [AddCommGroup 𝓨]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {R : ℕ → Ω → 𝓨}
  {a : 𝓐} {m n t : ℕ} {ω : Ω}

/-- Sum of rewards obtained when pulling action `a` up to time `t` (exclusive). -/
noncomputable def sumRewards (A : ℕ → Ω → 𝓐) (R : ℕ → Ω → 𝓨) (a : 𝓐) (t : ℕ) (ω : Ω) : 𝓨 :=
  ∑ s ∈ range t, if A s ω = a then (R s) ω else 0

/-- Sum of rewards of arm `a` in the history before time `n`. -/
noncomputable
def sumRewards' (n : ℕ) (h : Hist 𝓞 𝓐 𝓨 n) (a : 𝓐) :=
  ∑ s, if (h s).action = a then (h s).feedback else 0

/-- Empirical mean reward obtained when pulling action `a` up to time `t` (exclusive). -/
noncomputable
def empMean (A : ℕ → Ω → 𝓐) (R : ℕ → Ω → ℝ) (a : 𝓐) (t : ℕ) (ω : Ω) : ℝ :=
  sumRewards A R a t ω / pullCount A a t ω

/-- Empirical mean of arm `a` in the history before time `n`. -/
noncomputable
def empMean' (n : ℕ) (h : Hist 𝓞 𝓐 ℝ n) (a : 𝓐) :=
  sumRewards' n h a / pullCount' n h a

@[simp]
lemma sumRewards_zero {R : ℕ → Ω → 𝓨} : sumRewards A R a 0 = 0 := by ext; simp [sumRewards]

lemma sumRewards_add_one {R : ℕ → Ω → 𝓨} :
    sumRewards A R a (t + 1) ω = sumRewards A R a t ω + if A t ω = a then R t ω else 0 := by
  unfold sumRewards
  rw [sum_range_succ]

lemma sumRewards_eq_of_pullCount_eq {R : ℕ → Ω → 𝓨} {s t : ℕ}
    (h_eq : pullCount A a s ω = pullCount A a t ω) :
    sumRewards A R a s ω = sumRewards A R a t ω := by
  wlog hst : s ≤ t
  · have hts : t ≤ s := by lia
    exact (this h_eq.symm hts).symm
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst' ih =>
    have h_mono' : pullCount A a t ω ≤ pullCount A a (t + 1) ω := pullCount_mono a (Nat.le_succ t) ω
    have h_eq_t : pullCount A a s ω = pullCount A a t ω :=
      le_antisymm (pullCount_mono a hst' ω) (h_eq ▸ h_mono')
    have hne : A t ω ≠ a := by
      intro ha
      have h1 := ha ▸ pullCount_action_eq_pullCount_add_one (A := A) t ω
      lia
    rw [sumRewards_add_one, ite_eq_right hne, add_zero, ih h_eq_t]

lemma sumRewards_eq_pullCount_mul_empMean {R : ℕ → Ω → ℝ} {ω : Ω}
    (h_pull : pullCount A a t ω ≠ 0) :
    sumRewards A R a t ω = pullCount A a t ω * empMean A R a t ω := by unfold empMean; field_simp

lemma sum_rewardByCount_eq_sumRewards {R : ℕ → Ω → 𝓨} (a : 𝓐) (t : ℕ) (ω : Ω × (ℕ → 𝓐 → 𝓨)) :
    ∑ m ∈ Icc 1 (pullCount A a t ω.1), rewardByCount A R a m ω = sumRewards A R a t ω.1 := by
  induction t with
  | zero => simp [pullCount, sumRewards]
  | succ t ht =>
    by_cases hta : A t ω.1 = a
    · rw [← hta] at ht ⊢
      rw [pullCount_action_eq_pullCount_add_one, sum_Icc_succ_top (Nat.le_add_left 1 _), ht]
      unfold sumRewards
      rw [sum_range_succ, ite_eq_left rfl, rewardByCount_pullCount_add_one_eq_reward]
    · unfold sumRewards
      rwa [pullCount_eq_pullCount_of_action_ne hta, sum_range_succ, ite_eq_right hta, add_zero]

lemma sumRewards_eq_sumRewards' {R : ℕ → Ω → 𝓨} {n : ℕ} {ω : Ω} :
    sumRewards A R a n ω = sumRewards' n (history O A R n ω) a :=
  (Fin.sum_univ_eq_sum_range (fun i ↦ if A i ω = a then R i ω else 0) n).symm

/-- `sumRewards A R a n` is a function of the history before time `n`. -/
lemma sumRewards_eq_comp_history {R : ℕ → Ω → 𝓨} (a : 𝓐) (n : ℕ) :
    sumRewards A R a n = (fun h : Hist 𝓞 𝓐 𝓨 n ↦ sumRewards' n h a) ∘ history O A R n := by
  ext ω
  exact sumRewards_eq_sumRewards'

lemma empMean_eq_empMean' {R : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω} :
    empMean A R a n ω = empMean' n (history O A R n ω) a := by
  unfold empMean empMean'
  rw [sumRewards_eq_sumRewards' (O := O), pullCount_eq_pullCount' (O := O)]

/-- `empMean A R a n` is a function of the history before time `n`. -/
lemma empMean_eq_comp_history {R : ℕ → Ω → ℝ} (a : 𝓐) (n : ℕ) :
    empMean A R a n = (fun h : Hist 𝓞 𝓐 ℝ n ↦ empMean' n h a) ∘ history O A R n := by
  ext ω
  exact empMean_eq_empMean'

lemma sumRewards_sub_pullCount_smul_eq_sum {R : ℕ → Ω → 𝓨} (c : 𝓐 → 𝓨) :
    sumRewards A R a (n + 1) ω - pullCount A a (n + 1) ω • c a =
      ∑ i ∈ range (n + 1), (if A i ω = a then R i ω - c a else 0) := by
  induction n with
  | zero => simp_rw [sumRewards_add_one, pullCount_add_one]; simp; grind
  | succ n hn =>
    simp_rw [sumRewards_add_one (t := n + 1), pullCount_add_one (t := n + 1)]
    split_ifs with ha
    · conv_rhs => rw [sum_range_succ]
      simp only [ha, ↓reduceIte]
      rw [add_smul]
      grind
    · simp only [add_zero, hn]
      conv_rhs => rw [sum_range_succ]
      simp [ha]

@[fun_prop]
lemma measurable_sumRewards [MeasurableSingletonClass 𝓐] [MeasurableAdd₂ 𝓨] {R : ℕ → Ω → 𝓨}
    (hA : ∀ n, Measurable (A n)) (hR : ∀ n, Measurable (R n)) (a : 𝓐) (t : ℕ) :
    Measurable (sumRewards A R a t) := by
  unfold sumRewards
  have h_meas s : Measurable (fun h : Ω ↦ if A s h = a then R s h else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_uncurry_sumRewards_comp [Countable 𝓐] [MeasurableSingletonClass 𝓐]
    [MeasurableAdd₂ 𝓨]
    {R : ℕ → Ω → 𝓨} (hA : ∀ n, Measurable (A n)) (hR : ∀ n, Measurable (R n)) {f : Ω → 𝓐}
    (hf : Measurable f) {g : Ω → ℕ} (hg : Measurable g) :
    Measurable (fun ω ↦ sumRewards A R (f ω) (g ω) ω) := by
  change Measurable ((fun aω ↦ sumRewards A R aω.1 (g aω.2) aω.2) ∘ fun ω ↦ (f ω, ω))
  apply Measurable.comp _ (by fun_prop)
  refine measurable_from_prod_countable_right fun a ↦ ?_
  change Measurable ((fun tω ↦ sumRewards A R a tω.1 tω.2) ∘ fun ω ↦ (g ω, ω))
  apply Measurable.comp _ (by fun_prop)
  exact measurable_from_prod_countable_right (fun t ↦ measurable_sumRewards hA hR a t)

@[fun_prop]
lemma measurable_empMean [MeasurableSingletonClass 𝓐] {R : ℕ → Ω → ℝ} (hA : ∀ n, Measurable (A n))
    (hR : ∀ n, Measurable (R n)) (a : 𝓐) (n : ℕ) :
    Measurable (empMean A R a n) := by unfold empMean; fun_prop

@[fun_prop]
lemma measurable_uncurry_empMean_comp [Countable 𝓐] [MeasurableSingletonClass 𝓐] {R : ℕ → Ω → ℝ}
    (hA : ∀ n, Measurable (A n)) (hR : ∀ n, Measurable (R n)) {f : Ω → 𝓐} (hf : Measurable f)
    {g : Ω → ℕ} (hg : Measurable g) :
    Measurable (fun ω ↦ empMean A R (f ω) (g ω) ω) := by unfold empMean; fun_prop

@[fun_prop]
lemma measurable_sumRewards' [MeasurableSingletonClass 𝓐] [MeasurableAdd₂ 𝓨] (n : ℕ) (a : 𝓐) :
    Measurable (sumRewards' (𝓞 := 𝓞) (𝓨 := 𝓨) n · a) := by
  simp_rw [sumRewards']
  have h_meas s : Measurable
      (fun (h : Hist 𝓞 𝓐 𝓨 n) ↦ if (h s).action = a then (h s).feedback else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_uncurry_sumRewards' [MeasurableEq 𝓐] [MeasurableAdd₂ 𝓨] (n : ℕ) :
    Measurable (fun p : Hist 𝓞 𝓐 𝓨 n × 𝓐 ↦ sumRewards' n p.1 p.2) := by
  simp_rw [sumRewards']
  have h_meas s : Measurable (fun p : Hist 𝓞 𝓐 𝓨 n × 𝓐 ↦
      if (p.1 s).action = p.2 then (p.1 s).feedback else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_empMean' [MeasurableSingletonClass 𝓐] (n : ℕ) (a : 𝓐) :
    Measurable (empMean' (𝓞 := 𝓞) n · a) := by unfold empMean'; fun_prop

@[fun_prop]
lemma measurable_uncurry_empMean' [MeasurableEq 𝓐] (n : ℕ) :
    Measurable (fun p : Hist 𝓞 𝓐 ℝ n × 𝓐 ↦ empMean' n p.1 p.2) := by unfold empMean'; fun_prop

variable [MeasurableSingletonClass 𝓐]

/-- The sum of rewards of action `a` before time `n` is a function of the first `n` rounds. -/
lemma IsAlgEnvSeq.adapted_sumRewards [MeasurableAdd₂ 𝓨]
    {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}
    (h : IsAlgEnvSeq O A R alg env P) (a : 𝓐) :
    Adapted h.filtration (sumRewards A R a) := by
  intro n
  change Measurable[h.filtration n] (sumRewards A R a n)
  rw [measurable_iff_comap_le, h.filtration_eq_comap, sumRewards_eq_comp_history (O := O),
    ← measurable_iff_comap_le]
  exact measurable_comp_comap _ (measurable_sumRewards' n a)

lemma IsAlgEnvSeq.stronglyAdapted_sumRewards {𝓨 : Type*} {_ : MeasurableSpace 𝓨}
    [NormedAddCommGroup 𝓨] [OpensMeasurableSpace 𝓨] [SecondCountableTopology 𝓨]
    {R : ℕ → Ω → 𝓨} {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}
    (h : IsAlgEnvSeq O A R alg env P) (a : 𝓐) :
    StronglyAdapted h.filtration (sumRewards A R a) := by
  refine fun n ↦ Finset.stronglyMeasurable_fun_sum _
    fun i hi ↦ (Measurable.ite ?_ ?_ (by fun_prop)).stronglyMeasurable
  · refine (measurableSet_singleton a).preimage ?_
    simp only [mem_range] at hi
    exact h.measurable_action_filtration_of_lt hi
  · simp only [mem_range] at hi
    exact h.measurable_feedback_filtration_of_lt hi

/-- The empirical mean of action `a` before time `n` is a function of the first `n` rounds. -/
lemma IsAlgEnvSeq.adapted_empMean {R' : ℕ → Ω → ℝ}
    {alg : Algorithm 𝓞 𝓐 ℝ} {env : Environment 𝓞 𝓐 ℝ}
    (h : IsAlgEnvSeq O A R' alg env P) (a : 𝓐) :
    Adapted h.filtration (empMean A R' a) := by
  intro n
  change Measurable[h.filtration n] (empMean A R' a n)
  rw [measurable_iff_comap_le, h.filtration_eq_comap, empMean_eq_comp_history (O := O),
    ← measurable_iff_comap_le]
  exact measurable_comp_comap _ (measurable_empMean' n a)

lemma IsAlgEnvSeq.stronglyAdapted_empMean {R' : ℕ → Ω → ℝ}
    {alg : Algorithm 𝓞 𝓐 ℝ} {env : Environment 𝓞 𝓐 ℝ}
    (h : IsAlgEnvSeq O A R' alg env P) (a : 𝓐) :
    StronglyAdapted h.filtration (empMean A R' a) :=
  (h.adapted_empMean a).stronglyAdapted

end Learning
