/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.SumRewards

/-!
# The action indicator

`actionIndicator A k n ω = 𝟙{A n ω = k}` is the `{0,1}`-valued indicator that action `k` was chosen
at round `n`. It is the increment weight of every per-action sum attached to an action process:
`pullCount A k n` is its partial sum (`sum_range_actionIndicator_eq_pullCount`) and
`sumRewards A Y k n` is its reward-weighted partial sum (`sum_actionIndicator_mul`).


## Main definitions

* `Learning.actionIndicator`

## Main results

* `Learning.sum_range_actionIndicator_eq_pullCount`, `Learning.sum_actionIndicator_mul` — the two
  partial-sum identities.
* `Learning.adapted_actionIndicator`, `Learning.integrable_actionIndicator`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset

namespace Learning

variable {Ω 𝓞 𝓐 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓞 : MeasurableSpace 𝓞}
  {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  [MeasurableSingletonClass 𝓐] {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {P : Measure Ω}

/-- The `{0,1}`-valued assignment indicator of action `k`:
`actionIndicator A k n ω = 𝟙{A n ω = k}`. -/
noncomputable def actionIndicator (A : ℕ → Ω → 𝓐) (k : 𝓐) (n : ℕ) (ω : Ω) : ℝ :=
  {ω | A n ω = k}.indicator (fun _ ↦ (1 : ℝ)) ω

/-- `actionIndicator A k n ω = 1` exactly when action `k` is chosen at time `n`. -/
lemma actionIndicator_eq_one_iff {k : 𝓐} {n : ℕ} {ω : Ω} :
    actionIndicator A k n ω = 1 ↔ A n ω = k := by simp [actionIndicator]

lemma actionIndicator_nonneg (A : ℕ → Ω → 𝓐) (k : 𝓐) (n : ℕ) (ω : Ω) :
    0 ≤ actionIndicator A k n ω :=
  Set.indicator_apply_nonneg fun _ ↦ zero_le_one

lemma actionIndicator_le_one (A : ℕ → Ω → 𝓐) (k : 𝓐) (n : ℕ) (ω : Ω) :
    actionIndicator A k n ω ≤ 1 := by
  unfold actionIndicator
  by_cases h : A n ω = k <;> simp [h]

/-- Exactly one arm is pulled at each round, so the indicators sum to `1`. -/
lemma sum_actionIndicator [Fintype 𝓐] (A : ℕ → Ω → 𝓐) (j : ℕ) (ω : Ω) :
    ∑ k, actionIndicator A k j ω = 1 := by
  classical
  simp [actionIndicator, Set.indicator_apply]

lemma sum_actionIndicator_eq_pullCount [DecidableEq 𝓐] (A : ℕ → Ω → 𝓐) (k : 𝓐) (n : ℕ)
    (ω : Ω) :
    ∑ j ∈ range n, actionIndicator A k j ω = (pullCount A k n ω : ℝ) := by
  classical
  rw [pullCount_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [actionIndicator, Set.indicator_apply, Set.mem_ofPred_eq]

lemma sum_actionIndicator_smul [DecidableEq 𝓐] [AddCommGroup 𝓨] [Module ℝ 𝓨]
    (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (k : 𝓐) (t : ℕ) (ω : Ω) :
    ∑ j ∈ range t, actionIndicator A k j ω • Y j ω = sumRewards A Y k t ω := by
  rw [sumRewards]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [actionIndicator, Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp

lemma sum_actionIndicator_mul [DecidableEq 𝓐] (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (k : 𝓐) (t : ℕ)
    (ω : Ω) :
    ∑ j ∈ range t, actionIndicator A k j ω * Y j ω = sumRewards A Y k t ω :=
  sum_actionIndicator_smul A Y k t ω

lemma measurable_actionIndicator (k : 𝓐) {n : ℕ} (hA : Measurable (A n)) :
    Measurable (actionIndicator A k n) :=
  measurable_const.indicator (hA (measurableSet_singleton k))

lemma integrable_actionIndicator (P : Measure Ω) [IsFiniteMeasure P]
    (k : 𝓐) {n : ℕ} (hA : Measurable (A n)) :
    Integrable (actionIndicator A k n) P :=
  (integrable_const (1 : ℝ)).indicator (hA (measurableSet_singleton k))

/-- The action indicator is adapted to the history filtration: whether action `k` was chosen at `n`
is known at time `n`. -/
lemma IsAlgEnvSeq.adapted_actionIndicator {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}
    [IsFiniteMeasure P] (h : IsAlgEnvSeq O A Y alg env P) (k : 𝓐) :
    Adapted h.filtration (actionIndicator A k) :=
  fun _ ↦ Measurable.indicator measurable_const (h.adapted_action _ (measurableSet_singleton k))

/-- The action indicator is adapted to the history+action filtration: whether action `k` was chosen
at `n` is known once we know the action at `n`. -/
lemma IsAlgEnvSeq.adapted_actionIndicator_filtrationAction
    {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}
    [IsFiniteMeasure P] (h : IsAlgEnvSeq O A Y alg env P) (k : 𝓐) :
    Adapted h.filtrationAction (actionIndicator A k) :=
  fun _ ↦ Measurable.indicator measurable_const
    (h.adapted_action_filtrationAction _ (measurableSet_singleton k))

end Learning
