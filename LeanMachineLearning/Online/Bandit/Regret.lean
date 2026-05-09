/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.SequentialLearning.FiniteActions

/-!
# Regret, gap, best arm

## Main definitions

* `gap ν a` is the gap of an action `a`, i.e., the difference between the highest mean of the
  actions and the mean of `a`.
* `regret ν A t ω` is the regret of a sequence of pulls `A : ℕ → Ω → α` at time `t` for the reward
  kernel `ν : Kernel α ℝ` and the outcome `ω : Ω`.
* `bestArm ν` is an action with the highest mean.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset Learning

open scoped ENNReal NNReal

namespace Bandits

variable {α Ω : Type*} [DecidableEq α] {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
  {ν : Kernel α ℝ}
  {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}
  {ω : Ω} {m n t : ℕ} {a : α}

/-- Gap of an action `a`: difference between the highest mean of the actions and the mean of `a`. -/
noncomputable
-- ANCHOR: gap
def gap (ν : Kernel α ℝ) (a : α) : ℝ := (⨆ i, (ν i)[id]) - (ν a)[id]
-- ANCHOR_END: gap

omit [DecidableEq α] in
lemma gap_nonneg [Finite α] : 0 ≤ gap ν a := by
  rw [gap, sub_nonneg]
  exact le_ciSup (f := fun i ↦ (ν i)[id]) (by simp) a

/-- Regret of a sequence of pulls `k : ℕ → α` at time `t` for the reward kernel `ν ; Kernel α ℝ`. -/
noncomputable
-- ANCHOR: regret
def regret (ν : Kernel α ℝ) (A : ℕ → Ω → α) (t : ℕ) (ω : Ω) : ℝ :=
  t * (⨆ a, (ν a)[id]) - ∑ s ∈ range t, (ν (A s ω))[id]
-- ANCHOR_END: regret

omit [DecidableEq α] in
lemma regret_eq_sum_gap : regret ν A t ω = ∑ s ∈ range t, gap ν (A s ω) := by
  simp [regret, gap]

omit [DecidableEq α] in
lemma regret_nonneg [Finite α] : 0 ≤ regret ν A t ω := by
  rw [regret_eq_sum_gap]
  exact sum_nonneg (fun _ _ ↦ gap_nonneg)

omit [DecidableEq α] in
lemma gap_eq_zero_of_regret_eq_zero [Finite α] (hr : regret ν A t ω = 0) {s : ℕ} (hs : s < t) :
    gap ν (A s ω) = 0 := by
  rw [regret_eq_sum_gap] at hr
  exact (sum_eq_zero_iff_of_nonneg fun _ _ ↦ gap_nonneg).1 hr s (mem_range.2 hs)

lemma regret_eq_sum_pullCount_mul_gap [Fintype α] :
    regret ν A t ω = ∑ a, pullCount A a t ω * gap ν a := by
  simp_rw [regret_eq_sum_gap, sum_pullCount_mul]

lemma integral_regret_eq_sum_gap_mul_integral_pullCount
    [StandardBorelSpace α] [Fintype α] {P : Measure Ω} [IsProbabilityMeasure P]
    (hA : ∀ n, Measurable (A n)) :
    P[regret ν A n] = ∑ a, gap ν a * P[fun ω ↦ (pullCount A a n ω : ℝ)] := by
  simp_rw [regret_eq_sum_pullCount_mul_gap]
  rw [integral_finset_sum]
  swap; · exact fun i _ ↦ (integrable_pullCount hA i n).mul_const _
  congr with a
  rw [integral_mul_const, mul_comm]

/-- To bound the expected regret, it suffices to bound the expected number of pulls for each action
with positive gap. -/
lemma integral_regret_le_of_forall_integral_pullCount_le
    [Nonempty α] [StandardBorelSpace α] [Fintype α] {P : Measure Ω} [IsProbabilityMeasure P]
    {alg : Algorithm α ℝ} {env : Environment α ℝ} {B : α → ℝ}
    (h : IsAlgEnvSeq A R alg env P)
    (h_le : ∀ a, gap ν a ≠ 0 → ∫ ω, (pullCount A a n ω : ℝ) ∂P ≤ B a) :
    P[regret ν A n] ≤ ∑ a, gap ν a * B a := by
  have hA := h.measurable_action
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount hA]
  gcongr 1 with a
  by_cases h_gap : gap ν a = 0
  · simp [h_gap]
  gcongr
  · exact gap_nonneg
  · exact h_le a h_gap

section bestArm

variable [Fintype α] [Nonempty α]

/-- action with the highest mean. -/
noncomputable def bestArm (ν : Kernel α ℝ) : α :=
  (exists_max_image univ (fun a ↦ (ν a)[id]) (univ_nonempty_iff.mpr inferInstance)).choose

omit [DecidableEq α] in
lemma le_bestArm (a : α) : (ν a)[id] ≤ (ν (bestArm ν))[id] :=
  (exists_max_image univ (fun a ↦ (ν a)[id])
    (univ_nonempty_iff.mpr inferInstance)).choose_spec.2 _ (mem_univ a)

omit [DecidableEq α] in
lemma gap_eq_bestArm_sub : gap ν a = (ν (bestArm ν))[id] - (ν a)[id] := by
  rw [gap]
  congr
  refine le_antisymm ?_ (le_ciSup (f := fun a ↦ (ν a)[id]) (by simp) (bestArm ν))
  exact ciSup_le le_bestArm

omit [DecidableEq α] in
@[simp]
lemma gap_bestArm : gap ν (bestArm ν) = 0 := by
  rw [gap_eq_bestArm_sub, sub_self]

omit [DecidableEq α] in
lemma integral_eq_of_gap_eq_zero (hg : gap ν a = 0) : (ν (bestArm ν))[id] = (ν a)[id] := by
  rwa [← sub_eq_zero, ← gap_eq_bestArm_sub]

end bestArm

section Asymptotics

omit [DecidableEq α] in
/-- If the regret is sublinear, the average mean reward tends to the highest mean of the arms. -/
lemma avg_mean_reward_tendsto_of_sublinear_regret
    (hr : (regret ν A · ω) =o[atTop] fun t ↦ (t : ℝ)) :
    Tendsto (fun t ↦ (∑ s ∈ range t, (ν (A s ω))[id]) / (t : ℝ))
      atTop (nhds (⨆ a, (ν a)[id])) := by
  have ht : Tendsto (fun t ↦ (⨆ a, (ν a)[id]) - regret ν A t ω / t)
      atTop (nhds (⨆ a, (ν a)[id])) := by
    simpa using tendsto_const_nhds.sub hr.tendsto_div_nhds_zero
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with t ht
  rw [regret]
  field_simp
  ring

/-- If the regret is sublinear, the rate of suboptimal arm pulls tends to zero. -/
lemma pullCount_rate_tendsto_of_sublinear_regret [Finite α]
    (hr : (regret ν A · ω) =o[atTop] fun t ↦ (t : ℝ)) (hg : 0 < gap ν a) :
    Tendsto (fun t ↦ (pullCount A a t ω : ℝ) / t) atTop (nhds 0) := by
  have := Fintype.ofFinite α
  have hb (t : ℕ) : (pullCount A a t ω : ℝ) * gap ν a ≤ regret ν A t ω := by
    rw [regret_eq_sum_pullCount_mul_gap]
    exact single_le_sum (f := fun a ↦ pullCount A a t ω * gap ν a)
      (fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) gap_nonneg) (mem_univ a)
  have hb' (t : ℕ) : (pullCount A a t ω : ℝ) / t ≤ regret ν A t ω / t / gap ν a := by
    obtain ht | ht := eq_or_ne t 0
    · simp [ht]
    · calc (pullCount A a t ω : ℝ) / t
          = pullCount A a t ω * gap ν a / gap ν a / t := by field_simp
        _ ≤ regret ν A t ω / gap ν a / t := by gcongr; exact hb t
        _ = regret ν A t ω / t / gap ν a := by ring
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) (Eventually.of_forall hb')
  simpa using hr.tendsto_div_nhds_zero.div_const (gap ν a)

end Asymptotics

end Bandits
