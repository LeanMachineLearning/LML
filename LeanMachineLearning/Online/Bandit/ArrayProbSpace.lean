/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.Probability.Independence.CondIndepFun
public import LeanMachineLearning.Probability.Independence.IndepFun
public import LeanMachineLearning.Probability.Independence.IndepInfinitePi
public import LeanMachineLearning.Probability.Integrable
public import LeanMachineLearning.MeasureTheory.Constructions.Polish.StandardBorel
public import LeanMachineLearning.SequentialLearning.FiniteActions
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Kernel.Representation

/-!
# Array-of-rewards probability space for stochastic bandits

We build a particular probability space for stochastic bandits, called the "array model", in which
an infinite array of i.i.d. rewards is first produced for all actions. When the algorithm chooses
action `a` for the `n`th time, it receives the reward in the row `a` of the array and column `n`.

Some statements about bandit algorithms are easier to prove in this space, and can then be
transfered to any other probability space using the fact that the conditinonal distributions of the
arms and rewards specified in the bandit model determine their laws uniquely.

## Main definitions

* `streamMeasure ν`: probability measure on the space of infinite arrays of rewards,
  where the rewards in each row are i.i.d. according to `ν`.
* `probSpace α R`: probability space for the array model of stochastic bandits with action space `α`
  and reward space `R`.
* `arrayMeasure ν`: probability measure on `probSpace α R` for the array model of stochastic bandits
  with reward kernel `ν`.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset Learning

open scoped ENNReal NNReal

namespace Bandits

variable {α R : Type*} {mα : MeasurableSpace α} {mR : MeasurableSpace R}

section MeasureSpace

/-- Measure of an infinite stream of rewards from each action. -/
noncomputable
def streamMeasure (ν : Kernel α R) : Measure (ℕ → α → R) :=
  Measure.infinitePi fun _ ↦ Measure.infinitePi ν

instance (ν : Kernel α R) [IsMarkovKernel ν] : IsProbabilityMeasure (streamMeasure ν) := by
  unfold streamMeasure
  infer_instance

section StreamMeasure

lemma _root_.hasLaw_eval_infinitePi {ι : Type*} {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}
  (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    HasLaw (Function.eval i) (μ i) (Measure.infinitePi μ) where
  aemeasurable := Measurable.aemeasurable (by fun_prop)
  map_eq := by exact (measurePreserving_eval_infinitePi μ i).map_eq

lemma hasLaw_eval_streamMeasure (ν : Kernel α R) [IsMarkovKernel ν] (n : ℕ) :
    HasLaw (fun h : ℕ → α → R ↦ h n) (Measure.infinitePi ν) (streamMeasure ν) :=
  hasLaw_eval_infinitePi (fun _ ↦ Measure.infinitePi ν) n

lemma hasLaw_eval_eval_streamMeasure (ν : Kernel α R) [IsMarkovKernel ν] (n : ℕ) (a : α) :
    HasLaw (fun h : ℕ → α → R ↦ h n a) (ν a) (streamMeasure ν) :=
  (hasLaw_eval_infinitePi ν a).comp (hasLaw_eval_streamMeasure ν n)

lemma identDistrib_eval_eval_id_streamMeasure (ν : Kernel α R) [IsMarkovKernel ν] (n : ℕ) (a : α) :
    IdentDistrib (fun h : ℕ → α → R ↦ h n a) id (streamMeasure ν) (ν a) where
  aemeasurable_fst := Measurable.aemeasurable (by fun_prop)
  aemeasurable_snd := Measurable.aemeasurable (by fun_prop)
  map_eq := by
    rw [← (hasLaw_eval_eval_streamMeasure ν n a).map_eq,
      Measure.map_map (by fun_prop) (by fun_prop)]
    simp

lemma integrable_eval_streamMeasure (ν : Kernel α ℝ) [IsMarkovKernel ν] (n : ℕ) (a : α)
    (h_int : Integrable id (ν a)) :
    Integrable (fun h : ℕ → α → ℝ ↦ h n a) (streamMeasure ν) :=
  Integrable.congr_identDistrib h_int (identDistrib_eval_eval_id_streamMeasure ν n a).symm

lemma integral_eval_streamMeasure (ν : Kernel α ℝ) [IsMarkovKernel ν] (n : ℕ) (a : α) :
    ∫ h, h n a ∂(streamMeasure ν) = (ν a)[id] := by
  calc ∫ h, h n a ∂(streamMeasure ν)
  _ = ∫ x, x ∂((streamMeasure ν).map (fun h ↦ h n a)) := by
    rw [integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  _ = (ν a)[id] := by simp [(hasLaw_eval_eval_streamMeasure ν n a).map_eq]

lemma iIndepFun_eval_streamMeasure' (ν : Kernel α R) [IsMarkovKernel ν] :
    iIndepFun (fun n ω ↦ ω n) (streamMeasure ν) :=
  iIndepFun_infinitePi (P := fun (_ : ℕ) ↦ Measure.infinitePi ν) (Ω := fun _ ↦ α → R)
    (X := fun i u ↦ u) (fun i ↦ by fun_prop)

lemma iIndepFun_eval_streamMeasure'' (ν : Kernel α R) [IsMarkovKernel ν] (a : α) :
    iIndepFun (fun n ω ↦ ω n a) (streamMeasure ν) :=
  (iIndepFun_eval_streamMeasure' ν).comp (g := fun i ω ↦ ω a) (by fun_prop)

lemma iIndepFun_eval_streamMeasure (ν : Kernel α R) [IsMarkovKernel ν] :
    iIndepFun (fun (p : ℕ × α) ω ↦ ω p.1 p.2) (streamMeasure ν) :=
  iIndepFun_uncurry_infinitePi' (X := fun _ _ ↦ id) (fun _ ↦ ν) (by fun_prop)

lemma indepFun_eval_streamMeasure (ν : Kernel α R) [IsMarkovKernel ν] {n m : ℕ} {a b : α}
    (h : n ≠ m ∨ a ≠ b) :
    IndepFun (fun ω ↦ ω n a) (fun ω ↦ ω m b) (streamMeasure ν) := by
  change IndepFun (fun ω ↦ ω (n, a).1 (n, a).2) (fun ω ↦ ω (m, b).1 (m, b).2)
    (streamMeasure ν)
  exact (iIndepFun_eval_streamMeasure ν).indepFun (by grind)

lemma indepFun_eval_streamMeasure' (ν : Kernel α R) [IsMarkovKernel ν] {a b : α} (h : a ≠ b) :
    IndepFun (fun ω n ↦ ω n a) (fun ω n ↦ ω n b) (streamMeasure ν) :=
  indepFun_proj_infinitePi_infinitePi h

end StreamMeasure

namespace ArrayModel

open unitInterval

section ProbabilitySpace

variable (α R) in
/-- Probability space for the array model of stochastic bandits. -/
def probSpace : Type _ := (ℕ → I) × (ℕ → α → R)

instance {α R : Type*} [MeasurableSpace R] : MeasurableSpace (probSpace α R) :=
  inferInstanceAs (MeasurableSpace ((ℕ → I) × (ℕ → α → R)))

instance {α R : Type*} [Countable α] [MeasurableSpace R] [StandardBorelSpace R] :
    StandardBorelSpace (probSpace α R) :=
  inferInstanceAs (StandardBorelSpace ((ℕ → I) × (ℕ → α → R)))

/-- Probability measure for the array model of stochastic bandits. -/
noncomputable
def arrayMeasure (ν : Kernel α R) : Measure (probSpace α R) :=
  (Measure.infinitePi fun _ ↦ volume).prod (streamMeasure ν)

instance (ν : Kernel α R) [IsMarkovKernel ν] : IsProbabilityMeasure (arrayMeasure ν) :=
  Measure.prod.instIsProbabilityMeasure _ _

variable [Nonempty α] [StandardBorelSpace α]

/-- The initial action is the image of a uniform random variable by this function. -/
noncomputable
def initAlgFunction (alg : Algorithm α R) : I → α :=
  (Measure.exists_measurable_map_eq alg.p0).choose

lemma initAlgFunction_map (alg : Algorithm α R) : volume.map (initAlgFunction alg) = alg.p0 :=
  (Measure.exists_measurable_map_eq alg.p0).choose_spec.2

@[fun_prop]
lemma measurable_initAlgFunction (alg : Algorithm α R) :
    Measurable (initAlgFunction alg) := (Measure.exists_measurable_map_eq alg.p0).choose_spec.1
/-- The next action is the image of the history and a uniform random variable by this function. -/
noncomputable
def algFunction (alg : Algorithm α R) (n : ℕ) :
    (Iic n → α × R) → I → α :=
  (Kernel.exists_measurable_map_eq_unitInterval (alg.policy n)).choose

lemma algFunction_map (alg : Algorithm α R) (n : ℕ) (h : Iic n → α × R) :
      volume.map (algFunction alg n h) = alg.policy n h :=
  (Kernel.exists_measurable_map_eq_unitInterval (alg.policy n)).choose_spec.2 h

@[fun_prop]
lemma measurable_algFunction (alg : Algorithm α R) (n : ℕ) :
    Measurable (Function.uncurry (algFunction alg n)) :=
  (Kernel.exists_measurable_map_eq_unitInterval (alg.policy n)).choose_spec.1

end ProbabilitySpace

variable [Nonempty α] [StandardBorelSpace α]

section HistoryActionReward

/-- History of actions and rewards up to time `n` in the array model. -/
noncomputable
def hist [DecidableEq α] (alg : Algorithm α R) (ω : probSpace α R) : (n : ℕ) → Iic n → α × R
| 0 => fun _ ↦ (initAlgFunction alg (ω.1 0), ω.2 0 (initAlgFunction alg (ω.1 0)))
| n + 1 =>
  let hn : Iic n → α × R := hist alg ω n
  let a : α := algFunction alg n hn (ω.1 (n + 1))
  fun i ↦ if hin : i ≤ n then hn ⟨i, by simp [hin]⟩ else (a, ω.2 (pullCount' n hn a) a)

@[simp]
lemma hist_zero [DecidableEq α] (alg : Algorithm α R) (ω : probSpace α R) :
    hist alg ω 0 = fun _ ↦ (initAlgFunction alg (ω.1 0), ω.2 0 (initAlgFunction alg (ω.1 0))) :=
  rfl

lemma hist_add_one [DecidableEq α] (alg : Algorithm α R) (ω : probSpace α R) (n : ℕ) :
    let a : α := algFunction alg n (hist alg ω n) (ω.1 (n + 1))
    hist alg ω (n + 1) =
      fun (i : Iic (n + 1)) ↦ if hin : i ≤ n then hist alg ω n ⟨i, by simp [hin]⟩
        else (a, ω.2 (pullCount' n (hist alg ω n) a) a) := rfl

lemma hist_eq [DecidableEq α] (alg : Algorithm α R) (ω : probSpace α R) (n : ℕ) :
    hist alg ω n = fun i : Iic n ↦ hist alg ω i ⟨i.1, by simp⟩ := by
  induction n with
  | zero =>
    ext i : 1
    simp only [hist]
    rw [Unique.eq_default i]
    simp [coe_default_Iic_zero]
  | succ n hn =>
    ext i : 1
    by_cases hin : i ≤ n
    · rw [hist_add_one]
      simp only [hin, ↓reduceDIte]
      rw [funext_iff] at hn
      simp_rw [hn]
    · grind

lemma hist_add_one_eq_IicSuccProd' [DecidableEq α] (alg : Algorithm α R) (ω : probSpace α R)
    (n : ℕ) :
    let a : α := algFunction alg n (hist alg ω n) (ω.1 (n + 1))
    hist alg ω (n + 1) =
      (MeasurableEquiv.IicSuccProd (fun _ ↦ α × R) n).symm
        (hist alg ω n, (a, ω.2 (pullCount' n (hist alg ω n) a) a)) := by
  intro a
  rw [hist_add_one]
  ext i : 1
  simp only [Kernel.symm_IicSuccProd, MeasurableEquiv.prodCongr, MeasurableEquiv.refl_toEquiv,
    MeasurableEquiv.piSingleton, eq_rec_constant, MeasurableEquiv.IicProdIoc,
    MeasurableEquiv.trans_apply, MeasurableEquiv.coe_mk, Equiv.prodCongr_apply, Equiv.coe_refl,
    Equiv.coe_fn_mk, Prod.map_apply, id_eq]
  rfl

/-- Action taken at time `n` in the array model. -/
noncomputable
def action [DecidableEq α] (alg : Algorithm α R) (n : ℕ) (ω : probSpace α R) : α :=
  (hist alg ω n ⟨n, by simp⟩).1

lemma action_zero [DecidableEq α] (alg : Algorithm α R) :
    action alg 0 = fun ω ↦ initAlgFunction alg (ω.1 0) := by
  ext
  simp [action, hist_zero]

lemma action_add_one_eq [DecidableEq α] (alg : Algorithm α R) (n : ℕ) :
    action alg (n + 1) = fun ω ↦ algFunction alg n (hist alg ω n) (ω.1 (n + 1)) := by
  ext ω
  rw [action, hist_add_one]
  simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, ↓reduceDIte]

/-- Reward received at time `n` in the array model. -/
noncomputable
def reward [DecidableEq α] (alg : Algorithm α R) (n : ℕ) (ω : probSpace α R) : R :=
  (hist alg ω n ⟨n, by simp⟩).2

lemma reward_zero [DecidableEq α] (alg : Algorithm α R) :
    reward alg 0 = fun ω ↦ ω.2 0 (action alg 0 ω) := by
  ext
  simp [reward, hist_zero, action_zero]

lemma reward_add_one [DecidableEq α] (alg : Algorithm α R) (n : ℕ) :
    reward alg (n + 1) =
      fun ω ↦ ω.2 (pullCount' n (hist alg ω n) (action alg (n + 1) ω)) (action alg (n + 1) ω) := by
  ext ω
  simp [reward, hist_add_one, action_add_one_eq]

lemma reward_eq [DecidableEq α] (alg : Algorithm α R) (n : ℕ) :
    reward alg n = fun ω ↦ ω.2 (pullCount (action alg) (action alg n ω) n ω) (action alg n ω) := by
  cases n with
  | zero => ext; simp [reward_zero, action_zero]
  | succ n =>
    ext ω
    rw [reward, hist_add_one]
    simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, ↓reduceDIte]
    rw [action_add_one_eq, pullCount_eq_pullCount' (R' := reward alg) (by simp)]
    simp only [Nat.add_one_sub_one]
    rw [hist_eq]
    rfl

lemma sumRewards_eq [DecidableEq α] (alg : Algorithm α ℝ) (a : α) (n : ℕ) (ω : probSpace α ℝ) :
    sumRewards (action alg) (reward alg) a n ω =
      ∑ i ∈ range (pullCount (action alg) a n ω), ω.2 i a := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases ha : action alg n ω = a
    · simp [ha, sumRewards_add_one, pullCount_add_one, sum_range_succ, ih, reward_eq]
    · simp [ha, sumRewards_add_one, pullCount_eq_pullCount_of_action_ne, ih]

section Measurability

lemma measurable_action_add_one' [DecidableEq α] {alg : Algorithm α R}
    (n : ℕ) (h : Measurable (hist alg · n)) :
    Measurable (fun x ↦ algFunction alg n (hist alg x n) (x.1 (n + 1))) := by fun_prop

lemma measurable_pullCount'_action_add_one [DecidableEq α] {alg : Algorithm α R}
    (n : ℕ) (h_hist : Measurable (hist alg · n)) :
    Measurable (fun x ↦
      pullCount' n (hist alg x n) (algFunction alg n (hist alg x n) (x.1 (n + 1)))) := by
  have h_alg_meas : Measurable (fun x ↦ algFunction alg n (hist alg x n) (x.1 (n + 1))) :=
    measurable_action_add_one' n h_hist
  exact (measurable_uncurry_pullCount' (α := α) n).comp (h_hist.prodMk h_alg_meas)

@[fun_prop]
lemma measurable_hist [DecidableEq α] [Countable α] (alg : Algorithm α R) (n : ℕ) :
    Measurable (fun ω ↦ hist alg ω n) := by
  induction n with
  | zero =>
    simp_rw [hist_zero, measurable_pi_iff]
    refine fun _ ↦ Measurable.prodMk (by fun_prop) ?_
    change Measurable ((fun x : α × ((ℕ → I) × (ℕ → α → R)) ↦ x.2.2 0 x.1) ∘
        (fun x : (ℕ → I) × (ℕ → α → R) ↦ (initAlgFunction alg (x.1 0), x)))
    have : Measurable (fun x : α × ((ℕ → I) × (ℕ → α → R)) ↦ x.2.2 0 x.1) :=
      measurable_from_prod_countable_right fun p ↦ by simp only; fun_prop
    exact Measurable.comp (by fun_prop) (Measurable.prodMk (by fun_prop) (by fun_prop))
  | succ n hn =>
    refine measurable_pi_iff.mpr fun i ↦ ?_
    by_cases hin : i ≤ n
    · simp only [hist, hin, ↓reduceDIte]
      rw [measurable_pi_iff] at hn
      exact hn ⟨i.1, by simp [hin]⟩
    · simp only [hist, hin, ↓reduceDIte]
      refine Measurable.prodMk (by fun_prop) ?_
      change Measurable ((fun (x : (ℕ → α → R) × ℕ × α) ↦ x.1 x.2.1 x.2.2) ∘
        (fun x ↦ (x.2, pullCount' n (hist alg x n) (algFunction alg n (hist alg x n) (x.1 (n + 1))),
          (algFunction alg n (hist alg x n) (x.1 (n + 1))))))
      have h1 : Measurable (fun (x : (ℕ → α → R) × ℕ × α) ↦ x.1 x.2.1 x.2.2) :=
        measurable_from_prod_countable_left fun p : ℕ × α ↦ (by simp only; fun_prop)
      refine Measurable.comp (by fun_prop) (Measurable.prodMk (by fun_prop) ?_)
      refine Measurable.prodMk ?_ (by fun_prop)
      exact measurable_pullCount'_action_add_one n hn

@[fun_prop]
lemma measurable_action [DecidableEq α] [Countable α] (alg : Algorithm α R) (n : ℕ) :
    Measurable (action alg n) := by unfold action; fun_prop

@[fun_prop]
lemma measurable_reward [DecidableEq α] [Countable α] (alg : Algorithm α R) (n : ℕ) :
    Measurable (reward alg n) := by unfold reward; fun_prop

lemma hist_add_one_eq_IicSuccProd [DecidableEq α] (alg : Algorithm α R) (ω : probSpace α R)
    (n : ℕ) :
    hist alg ω (n + 1) =
      (MeasurableEquiv.IicSuccProd (fun _ ↦ α × R) n).symm
        (hist alg ω n, (action alg (n + 1) ω, reward alg (n + 1) ω)) := by
  rw [hist_add_one_eq_IicSuccProd', reward_add_one, action_add_one_eq]

@[fun_prop]
lemma measurable_pullCount_action_add_one [DecidableEq α] [Countable α] (alg : Algorithm α R)
    (n : ℕ) :
    Measurable (fun ω ↦ pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω) := by
  change Measurable ((fun p : (probSpace α R) × α ↦ pullCount (action alg) p.2 (n + 1) p.1) ∘
    (fun ω : probSpace α R ↦ (ω, action alg (n + 1) ω)))
  exact (measurable_uncurry_pullCount (by fun_prop) _).comp (by fun_prop)

end Measurability

end HistoryActionReward

variable [DecidableEq α]

section Congruence

-- very useful to prove measurability
lemma hist_congr (alg : Algorithm α R) (n : ℕ) {ω ω' : probSpace α R}
    (hω1 : ∀ i ≤ n, ω.1 i = ω'.1 i)
    (hω2 : ∀ i a, i < pullCount (action alg) a (n + 1) ω → ω.2 i a = ω'.2 i a) :
    hist alg ω n = hist alg ω' n := by
  induction n with
  | zero =>
    simp only [zero_add, pullCount_one] at hω2
    simp_rw [hist_zero]
    ext i : 1
    simp only [le_refl, hω1, Prod.mk.injEq, true_and]
    refine hω2 0 _ ?_
    simp [action, hω1]
  | succ n hn =>
    simp_rw [hist_add_one_eq_IicSuccProd]
    specialize hn fun i hin ↦ hω1 i (by grind)
    have h_hist : hist alg ω n = hist alg ω' n := by
      refine hn fun i a hi ↦ hω2 i a (hi.trans_le ?_)
      exact pullCount_mono _ (by lia) _
    have h_action : action alg (n + 1) ω = action alg (n + 1) ω' := by
      simp_rw [action_add_one_eq]
      rw [h_hist, hω1 _ le_rfl]
    congr 3
    simp only [reward_add_one, h_hist, h_action]
    refine hω2 _ _ ?_
    rw [pullCount_add_one, h_action]
    simp only [↓reduceIte]
    rw [pullCount_eq_pullCount' (R' := reward alg) (by simp)]
    simp only [Nat.add_one_sub_one]
    rw [← h_hist, hist_eq]
    change pullCount' n  (fun i ↦ (action alg i ω, reward alg i ω)) (action alg (n + 1) ω') <
      pullCount' n (fun i ↦ (action alg i ω, reward alg i ω)) (action alg (n + 1) ω') + 1
    grind

lemma stepsUntil_congr_aux (alg : Algorithm α R)
    (a : α) (m n : ℕ) {ω ω' : probSpace α R}
    (hω1 : ∀ i, ω.1 i = ω'.1 i) (hω2_ne : ∀ i b, b ≠ a → ω.2 i b = ω'.2 i b)
    (hω2_eq : ∀ i, i + 1 ≤ m → ω.2 i a = ω'.2 i a)
    (h_eq : action alg (n + 1) ω = a ∧ pullCount (action alg) a (n + 1) ω = m) :
    action alg (n + 1) ω' = a ∧ pullCount (action alg) a (n + 1) ω' = m := by
  obtain ⟨h_action, h_pc⟩ := h_eq
  have h_hist := hist_congr alg n (ω := ω) (ω' := ω') (by grind) fun i b hi ↦ ?_
  swap
  · rcases eq_or_ne b a with (rfl | hba)
    · refine hω2_eq i ?_
      rw [h_pc] at hi
      grind
    · grind
  constructor
  · rw [← h_action, action_add_one_eq]
    simp [h_hist, hω1]
  · simp_rw [← h_pc, pullCount_eq_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    congr 2
    rw [hist_eq _ _ n, hist_eq _ _ n, funext_iff] at h_hist
    unfold action
    specialize h_hist ⟨i, by grind⟩
    simp only at h_hist
    rw [h_hist]

lemma stepsUntil_congr (alg : Algorithm α R) (a : α) (m n : ℕ) {ω ω' : probSpace α R}
    (hω1 : ∀ i, ω.1 i = ω'.1 i) (hω2_ne : ∀ i b, b ≠ a → ω.2 i b = ω'.2 i b)
    (hω2_eq : ∀ i, i + 1 ≤ m → ω.2 i a = ω'.2 i a) :
    (action alg (n + 1) ω = a ∧ pullCount (action alg) a (n + 1) ω = m) ↔
      (action alg (n + 1) ω' = a ∧ pullCount (action alg) a (n + 1) ω' = m) :=
  ⟨stepsUntil_congr_aux alg a m n hω1 hω2_ne hω2_eq,
    stepsUntil_congr_aux alg a m n (by grind) (by grind) (by grind)⟩

lemma stepsUntil_indicator_congr (alg : Algorithm α R) (a : α) (m n : ℕ) {ω ω' : probSpace α R}
    (hω1 : ∀ i, ω.1 i = ω'.1 i) (hω2_ne : ∀ i b, b ≠ a → ω.2 i b = ω'.2 i b)
    (hω2_eq : ∀ i, i + 1 ≤ m → ω.2 i a = ω'.2 i a) :
    {ω | action alg (n + 1) ω = a ∧ pullCount (action alg) a (n + 1) ω = m}.indicator (fun _ ↦ 1)
        ω =
      {ω | action alg (n + 1) ω = a ∧ pullCount (action alg) a (n + 1) ω = m}.indicator
        (fun _ ↦ 1) ω' := by
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  simp_rw [stepsUntil_congr alg a m n hω1 hω2_ne hω2_eq]

end Congruence

section MeasurabilityAdvanced

lemma measurable_hist_todo [Countable α] (alg : Algorithm α R) (n : ℕ) :
    Measurable[MeasurableSpace.comap (fun ω ↦ (fun (i : Iic n) ↦ ω.1 i, ω.2)) inferInstance]
      (hist alg · n) := by
  have h_eq : (hist alg · n) =
      ((hist alg · n) ∘ (fun p ↦ (fun i : ℕ ↦ p.1 ⟨min i n, by grind⟩, p.2))) ∘
        (fun ω ↦ (fun (i : Iic n) ↦ ω.1 i, ω.2)) := by
    ext ω : 1
    exact hist_congr alg n (by grind) (by simp)
  rw [h_eq]
  refine measurable_comp_comap _ (Measurable.comp (by fun_prop) ?_)
  refine Measurable.prodMk ?_ (by fun_prop)
  rw [measurable_pi_iff]
  intro i
  change Measurable ((fun p ↦ p ⟨min i n, by simp⟩) ∘ (fun x : (Iic n → I) × (ℕ → α → R) ↦ x.1))
  exact Measurable.comp (by fun_prop) measurable_fst

variable [Nonempty R]

-- very bad name
/-- All random variables in the space, except for the unseen rewards for action `a` after
time `n`. -/
noncomputable
def truePast (alg : Algorithm α R) (a : α) (n : ℕ) (ω : probSpace α R) :
    probSpace α R :=
  (ω.1, fun i b ↦ if b = a then if pullCount (action alg) a (n + 1) ω ≠ 0 then
      ω.2 (min i ((pullCount (action alg) a (n + 1) ω) - 1)) a else Nonempty.some inferInstance
    else ω.2 i b)

lemma truePast_eq_of_pullCount_eq (alg : Algorithm α R)
    (a : α) (n m : ℕ) (ω : probSpace α R)
    (h_pc : pullCount (action alg) a (n + 1) ω = m) :
    truePast alg a n ω = (ω.1, fun i b ↦ if b = a then if m ≠ 0 then
      ω.2 (min i (m - 1)) a else Nonempty.some inferInstance else ω.2 i b) := by
  simp [truePast, h_pc]

lemma truePast_eq_of_pullCount_eq_of_ne_zero (alg : Algorithm α R)
    (a : α) (n m : ℕ) (ω : probSpace α R)
    (h_pc : pullCount (action alg) a (n + 1) ω = m) (hm : m ≠ 0) :
    truePast alg a n ω = (ω.1, fun i b ↦ if b = a then
      ω.2 (min i (m - 1)) a else ω.2 i b) := by
  simp [truePast, h_pc, hm]

lemma measurable_hist_truePast [Countable α] (alg : Algorithm α R)
    (a : α) (n : ℕ) :
    Measurable[MeasurableSpace.comap (truePast alg a n) inferInstance] (hist alg · n) := by
  have h_eq : (hist alg · n) = (hist alg · n) ∘ (truePast alg a n) := by
    ext ω : 1
    refine hist_congr alg n (fun _ _ ↦ rfl) fun i b hi ↦ ?_
    by_cases hb : b = a
    · subst hb
      simp only [truePast, ↓reduceIte]
      rw [min_eq_left, if_pos (by grind)]
      grind
    · simp [truePast, hb]
  rw [h_eq]
  refine Measurable.comp ?_ (Measurable.of_comap_le le_rfl)
  fun_prop

lemma measurable_action_add_one_truePast [Countable α] (alg : Algorithm α R)
    (a : α) (n : ℕ) :
    Measurable[MeasurableSpace.comap (truePast alg a n) inferInstance]
      (action alg (n + 1)) := by
  rw [action_add_one_eq]
  change Measurable[MeasurableSpace.comap (truePast alg a n) inferInstance]
    ((fun p ↦ algFunction alg n p.1 p.2) ∘ (fun ω ↦ (hist alg ω n, ω.1 (n + 1))))
  refine (measurable_algFunction alg n).comp (Measurable.prodMk ?_ ?_)
  · exact measurable_hist_truePast alg a n
  · have : (fun ω ↦ ω.1 (n + 1)) =
      (fun (p : probSpace α R) ↦ p.1 (n + 1)) ∘ (truePast alg a n) := rfl
    rw [this]
    exact Measurable.comp (by fun_prop) (Measurable.of_comap_le le_rfl)

lemma measurable_pullCount_add_one_truePast [Countable α] (alg : Algorithm α R) (a : α) (n : ℕ) :
    Measurable[MeasurableSpace.comap (truePast alg a n) inferInstance]
      (pullCount (action alg) a (n + 1)) := by
  change Measurable[MeasurableSpace.comap (truePast alg a n) inferInstance]
    (fun ω ↦ pullCount (action alg) a (n + 1) ω)
  simp_rw [pullCount_eq_sum]
  refine measurable_sum _ fun i hi ↦ Measurable.ite ?_ (by fun_prop) (by fun_prop)
  refine (measurableSet_singleton _).preimage ?_
  have h_meas := measurable_hist_truePast alg a n
  simp_rw [hist_eq _ _ n, @measurable_pi_iff] at h_meas
  exact (h_meas ⟨i, by grind⟩).fst

lemma measurable_stepsUntil [Countable α] (alg : Algorithm α R) (a : α) (m n : ℕ) :
    Measurable[MeasurableSpace.comap
        (fun ω ↦ (ω.1, fun k b ↦ if b = a then if m ≠ 0 then ω.2 (min k (m - 1)) b
          else Nonempty.some inferInstance else ω.2 k b)) inferInstance]
      (({ω | action alg (n + 1) ω = a ∧
        pullCount (action alg) a (n + 1) ω = m}).indicator (fun _ ↦ 1)) := by
  let f := ({ω | action alg (n + 1) ω = a ∧ pullCount (action alg) a (n + 1) ω = m}).indicator
    (fun _ ↦ 1)
  have h_eq : f = f ∘
      fun ω ↦ (ω.1, fun k b ↦ if b = a then if m ≠ 0 then ω.2 (min k (m - 1)) b
        else Nonempty.some inferInstance else ω.2 k b) := by
    ext ω
    exact stepsUntil_indicator_congr alg a m n (by grind) (by grind) (by grind)
  change Measurable[MeasurableSpace.comap
    (fun ω ↦ (ω.1, fun k b ↦ if b = a then if m ≠ 0 then ω.2 (min k (m - 1)) b
      else Nonempty.some inferInstance else ω.2 k b)) inferInstance] f
  rw [h_eq]
  refine Measurable.comp ?_ (Measurable.of_comap_le le_rfl)
  refine Measurable.indicator (by fun_prop) ?_
  exact MeasurableSet.inter ((measurableSet_singleton _).preimage (by fun_prop))
    ((measurableSet_singleton _).preimage (by fun_prop))

omit [Nonempty R] in
lemma measurable_pullCount_action_add_one_hist (alg : Algorithm α R) (n : ℕ) :
    Measurable[MeasurableSpace.comap (fun ω ↦ (action alg (n + 1) ω, hist alg ω n)) inferInstance]
      (fun ω ↦ pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω) := by
  simp_rw [pullCount_eq_sum]
  refine measurable_sum _ fun i hi ↦ Measurable.ite ?_ (by fun_prop) (by fun_prop)
  refine measurableSet_eq_fun ?_ (measurable_comp_comap _ measurable_fst)
  rw [measurable_iff_comap_le]
  simp_rw [hist_eq _ _ n]
  rw [← measurable_iff_comap_le]
  unfold action
  refine Measurable.fst (mγ := inferInstance) ?_
  have : (hist alg · i ⟨i, by grind⟩) =
      (fun ω : α × (Iic n → α × R) ↦ ω.2 ⟨i, by grind⟩) ∘
        (fun ω ↦ (action alg (n + 1) ω, fun i : Iic n ↦ hist alg ω i ⟨i, by grind⟩)) := rfl
  rw [this]
  exact measurable_comp_comap _ (Measurable.prodMk (by fun_prop) (by fun_prop))

end MeasurabilityAdvanced

omit [Nonempty α] [StandardBorelSpace α] [DecidableEq α] in
lemma map_snd_apply_arrayMeasure {ν : Kernel α R} [IsMarkovKernel ν] (n : ℕ) (a : α) :
    (arrayMeasure ν).map (fun ω ↦ ω.2 n a) = ν a := by
  calc (arrayMeasure ν).map (fun ω ↦ ω.2 n a)
  _ = (arrayMeasure ν).snd.map (fun ω ↦ ω n a) := by
    rw [Measure.snd, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  _ = ν a := by
    rw [arrayMeasure, Measure.snd_prod, streamMeasure]
    have : (fun ω ↦ ω n a) = (fun h : α → R ↦ h a) ∘ (fun ω : ℕ → α → R ↦ ω n) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), Measure.infinitePi_map_eval,
      Measure.infinitePi_map_eval]

section Independence

omit [Nonempty α] [StandardBorelSpace α] [DecidableEq α] in
lemma indepFun_fst_snd (ν : Kernel α R) [IsMarkovKernel ν] :
    IndepFun Prod.fst Prod.snd (arrayMeasure ν) :=
  indepFun_prod measurable_id measurable_id

omit [Nonempty α] [StandardBorelSpace α] [DecidableEq α] in
lemma indepFun_fst_zero_snd_zero_action (ν : Kernel α R) [IsMarkovKernel ν] (a : α) :
    IndepFun (fun ω ↦ ω.1 0) (fun ω ↦ ω.2 0 a) (arrayMeasure ν) :=
  indepFun_prod (X := fun ω : ℕ → I ↦ ω 0) (Y := fun ω : ℕ → α → R ↦ ω 0 a)
    (by fun_prop) (by fun_prop)

-- proved by Claude, then slightly golfed
omit [DecidableEq α] [Nonempty α] [StandardBorelSpace α] in
lemma indepFun_fst_add_one_aux (ν : Kernel α R) [IsMarkovKernel ν] (n : ℕ) :
    (fun ω ↦ ω.1 (n + 1)) ⟂ᵢ[arrayMeasure ν] (fun ω ↦ (fun (i : Iic n) ↦ ω.1 i, ω.2)) := by
  let μ₁ : Measure (ℕ → I) := Measure.infinitePi fun _ ↦ volume
  let μ₂ : Measure (ℕ → α → R) := streamMeasure ν
  -- Coordinates of μ₁ are independent
  have h_indep : iIndepFun (fun i (ω : ℕ → I) ↦ ω i) μ₁ :=
    iIndepFun_infinitePi (fun _ ↦ measurable_id)
  have h_indep_n : IndepFun (fun ω ↦ ω (n + 1)) (fun ω ↦ fun i : Iic n ↦ ω i) μ₁ := by
    have h := h_indep.indepFun_finset₀ {n + 1} (Iic n) (by simp)
      (fun i ↦ (measurable_pi_apply i).aemeasurable)
    convert h.comp (measurable_pi_apply ⟨n + 1, by simp⟩) measurable_id using 1
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  let X : (ℕ → I) × (ℕ → α → R) → I := fun ω ↦ ω.1 (n + 1)
  let Y : (ℕ → I) × (ℕ → α → R) → (Iic n → I) × (ℕ → α → R) := fun ω ↦ (fun i ↦ ω.1 i, ω.2)
  change (μ₁.prod μ₂) (X ⁻¹' s ∩ Y ⁻¹' t) = (μ₁.prod μ₂) (X ⁻¹' s) * (μ₁.prod μ₂) (Y ⁻¹' t)
  -- Rewrite using Fubini
  rw [Measure.prod_apply (hs.preimage (by fun_prop : Measurable X)),
    Measure.prod_apply (ht.preimage (by fun_prop : Measurable Y)),
    Measure.prod_apply ((hs.preimage (by fun_prop : Measurable X)).inter
      (ht.preimage (by fun_prop : Measurable Y)))]
  -- Compute fibers
  have hX_fst ω₁ : μ₂ (Prod.mk ω₁ ⁻¹' (X ⁻¹' s)) = s.indicator 1 (ω₁ (n + 1)) := by
    simp only [X, Set.preimage_preimage]
    by_cases h : ω₁ (n + 1) ∈ s <;> simp [h]
  have hY_fst ω₁ : μ₂ (Prod.mk ω₁ ⁻¹' (Y ⁻¹' t)) = μ₂ {y | ((fun i : Iic n ↦ ω₁ i), y) ∈ t} := rfl
  have hXY ω₁ : μ₂ (Prod.mk ω₁ ⁻¹' (X ⁻¹' s ∩ Y ⁻¹' t)) =
      s.indicator 1 (ω₁ (n + 1)) * μ₂ {y | ((fun i : Iic n ↦ ω₁ i), y) ∈ t} := by
    simp only [X, Y, Set.preimage_inter, Set.preimage_preimage]
    by_cases h : ω₁ (n + 1) ∈ s
    · simp [h]
      grind
    · simp [h]
  simp_rw [hY_fst, hX_fst, hXY]
  -- Factor the integral using independence
  let g : (Iic n → I) → ENNReal := fun x ↦ μ₂ {y | (x, y) ∈ t}
  have hg_meas : Measurable g := measurable_measure_prodMk_left ht
  have hf_meas : Measurable (fun ω₁ : ℕ → I ↦ s.indicator (1 : I → ENNReal) (ω₁ (n + 1))) :=
    (measurable_one.indicator hs).comp (measurable_pi_apply _)
  have hindep_fg : IndepFun (fun ω₁ ↦ s.indicator (1 : I → ENNReal) (ω₁ (n + 1)))
      (fun ω₁ ↦ g (fun i ↦ ω₁ i)) μ₁ :=
    h_indep_n.comp (measurable_one.indicator hs) hg_meas
  have h_eq (ω₁ : ℕ → I) : μ₂ {y | ((fun i : Iic n ↦ ω₁ i), y) ∈ t} = g (fun i ↦ ω₁ i) := rfl
  simp_rw [h_eq]
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hf_meas (by fun_prop) hindep_fg

variable [StandardBorelSpace R] [Nonempty R]

lemma indepFun_fst_add_one_hist [Countable α] (alg : Algorithm α R)
    (ν : Kernel α R) [IsMarkovKernel ν] (n : ℕ) :
    IndepFun (fun ω ↦ ω.1 (n + 1)) (hist alg · n) (arrayMeasure ν) :=
  (indepFun_fst_add_one_aux ν n).of_measurable_right (measurable_hist_todo alg n)

-- proved by Claude
omit [Nonempty α] [StandardBorelSpace α] [StandardBorelSpace R] in
lemma indepFun_snd_apply_aux (ν : Kernel α R) [IsMarkovKernel ν] (a : α) (m : ℕ) :
    (fun ω ↦ ω.2 m a) ⟂ᵢ[arrayMeasure ν]
      (fun ω ↦ (ω.1, fun k b ↦ if b = a then if m ≠ 0 then ω.2 (min k (m - 1)) b
        else Nonempty.some inferInstance else ω.2 k b)) := by
  unfold arrayMeasure
  let μ₁ : Measure (ℕ → I) := Measure.infinitePi fun _ ↦ volume
  let μ₂ : Measure (ℕ → α → R) := Measure.infinitePi fun _ ↦ Measure.infinitePi ν
  -- Independence within μ₂: coordinates ω i are independent
  have h_indep₂ : iIndepFun (fun i (ω : ℕ → α → R) ↦ ω i) μ₂ :=
    iIndepFun_infinitePi (fun _ ↦ measurable_id)
  -- Independence within each infinitePi ν: coordinates f b are independent
  have h_indep_inner : iIndepFun (fun (b : α) (f : α → R) ↦ f b) (Measure.infinitePi ν) :=
    iIndepFun_infinitePi (fun _ ↦ measurable_id)
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  let X : (ℕ → I) × (ℕ → α → R) → R := fun ω ↦ ω.2 m a
  let Y : (ℕ → I) × (ℕ → α → R) → (ℕ → I) × (ℕ → α → R) :=
    fun ω ↦ (ω.1, fun k b ↦ if b = a then if m ≠ 0 then ω.2 (min k (m - 1)) b
      else Nonempty.some inferInstance else ω.2 k b)
  have hX_meas : Measurable X :=
    (measurable_pi_apply a).comp ((measurable_pi_apply m).comp measurable_snd)
  have hY_meas : Measurable Y := by
    change Measurable (fun ω : (ℕ → I) × (ℕ → α → R) ↦
      (ω.1, fun k b ↦ if b = a then if m ≠ 0 then ω.2 (min k (m - 1)) b
        else Nonempty.some inferInstance else ω.2 k b))
    refine Measurable.prod measurable_fst ?_
    refine measurable_pi_lambda _ (fun k ↦ ?_)
    refine measurable_pi_lambda _ (fun b ↦ ?_)
    by_cases hb : b = a
    · simp only [hb, ↓reduceIte]
      by_cases hm : m ≠ 0
      · simp only [ne_eq, hm, not_false_eq_true, ↓reduceIte]
        exact (measurable_pi_apply a).comp
          ((measurable_pi_apply (min k (m - 1))).comp measurable_snd)
      · simp only [hm, ↓reduceIte]
        exact measurable_const
    · simp only [hb, ↓reduceIte]
      exact (measurable_pi_apply b).comp ((measurable_pi_apply k).comp measurable_snd)
  change (μ₁.prod μ₂) (X ⁻¹' s ∩ Y ⁻¹' t) = (μ₁.prod μ₂) (X ⁻¹' s) * (μ₁.prod μ₂) (Y ⁻¹' t)
  -- Use Fubini on μ₁.prod μ₂
  rw [Measure.prod_apply (hs.preimage hX_meas),
    Measure.prod_apply (ht.preimage hY_meas),
    Measure.prod_apply ((hs.preimage hX_meas).inter (ht.preimage hY_meas))]
  -- X only depends on ω₂, so its fiber is constant in ω₁
  have hX_fst : ∀ ω₁, μ₂ (Prod.mk ω₁ ⁻¹' (X ⁻¹' s)) = μ₂ ((fun ω₂ ↦ ω₂ m a) ⁻¹' s) := fun _ ↦ rfl
  simp_rw [hX_fst]
  -- The LHS integral: fiber of X ∩ Y at ω₁
  -- Key: X depends only on ω₂ m a, while Y's dependence on ω₂ avoids (m, a)
  -- Define the "truncation" map on ω₂
  let trunc : (ℕ → α → R) → (ℕ → α → R) :=
    fun ω₂ k b ↦ if b = a then if m ≠ 0 then ω₂ (min k (m - 1)) b
      else Nonempty.some inferInstance else ω₂ k b
  -- The fiber of Y at ω₁ only depends on trunc(ω₂)
  have hY_fiber : ∀ ω₁, Prod.mk ω₁ ⁻¹' (Y ⁻¹' t) = (fun ω₂ ↦ (ω₁, trunc ω₂)) ⁻¹' t := fun _ ↦ rfl
  -- The fiber of X ∩ Y factors
  have hXY_fiber : ∀ ω₁, Prod.mk ω₁ ⁻¹' (X ⁻¹' s ∩ Y ⁻¹' t) =
      ((fun ω₂ ↦ ω₂ m a) ⁻¹' s) ∩ ((fun ω₂ ↦ (ω₁, trunc ω₂)) ⁻¹' t) := fun _ ↦ rfl
  simp_rw [hXY_fiber, hY_fiber]
  -- Now we use independence in μ₂: (ω₂ m a) is independent of (trunc ω₂)
  -- because trunc only uses indices (k, a) with k < m, and (k, b) with b ≠ a
  have h_trunc_meas : Measurable trunc := by
    refine measurable_pi_lambda _ (fun k ↦ ?_)
    refine measurable_pi_lambda _ (fun b ↦ ?_)
    simp only [trunc]
    by_cases hb : b = a
    · simp only [hb, ↓reduceIte]
      by_cases hm : m = 0
      · simp only [hm]
        exact measurable_const
      · simp only [ne_eq, hm, not_false_eq_true, ↓reduceIte]
        exact (measurable_pi_apply a).comp (measurable_pi_apply (min k (m - 1)))
    · simp only [hb, ↓reduceIte]
      exact (measurable_pi_apply b).comp (measurable_pi_apply k)
  -- Key independence: (ω₂ m a) ⟂ trunc because trunc only uses coordinates ≠ (m, a)
  have h_indep_trunc : IndepFun (fun ω₂ ↦ ω₂ m a) trunc μ₂ := by
    -- Factor trunc through proj which extracts the relevant coordinates
    let proj : (ℕ → α → R) → ((ℕ → R) × (ℕ → {b : α // b ≠ a} → R)) := fun ω₂ ↦
      (fun k ↦ if m ≠ 0 then ω₂ (min k (m - 1)) a else Nonempty.some inferInstance,
      fun k ⟨b, _⟩ ↦ ω₂ k b)
    have h_trunc_proj : ∀ ω₂, trunc ω₂ = (fun p k b ↦
        if h : b = a then if m ≠ 0 then p.1 k
          else Nonempty.some inferInstance else p.2 k ⟨b, h⟩) (proj ω₂) := by
      intro ω₂; ext k b; simp only [trunc, proj]; by_cases hb : b = a <;> simp [hb]; grind
    have h_proj_meas : Measurable proj := by
      refine Measurable.prod ?_ ?_
      · refine measurable_pi_lambda _ fun k ↦ ?_
        by_cases hm : m ≠ 0
        · simp only [proj, ne_eq, hm, not_false_eq_true, ↓reduceIte]
          exact (measurable_pi_apply a).comp (measurable_pi_apply (min k (m - 1)))
        · simp [proj, hm]
      · exact measurable_pi_lambda _ (fun k ↦ measurable_pi_lambda _ (fun ⟨b, _⟩ ↦
          (measurable_pi_apply b).comp (measurable_pi_apply k)))
    have h_g_meas : Measurable (fun p : (ℕ → R) × (ℕ → {b : α // b ≠ a} → R) ↦
        (fun k b ↦ if h : b = a then if m ≠ 0 then p.1 k else Nonempty.some inferInstance
          else p.2 k ⟨b, h⟩)) := by
      refine measurable_pi_lambda _ (fun k ↦ measurable_pi_lambda _ (fun b ↦ ?_))
      by_cases hb : b = a
      · simp only [hb, ↓reduceDIte]
        by_cases hm : m ≠ 0
        · simp only [ne_eq, hm, not_false_eq_true]
          exact (measurable_pi_apply k).comp measurable_fst
        · simp [hm]
      · simp only [hb, ↓reduceDIte]
        exact (measurable_pi_apply (⟨b, hb⟩ : {b : α // b ≠ a})).comp
          ((measurable_pi_apply k).comp measurable_snd)
    -- Show (ω₂ m a) ⟂ proj: proj uses coordinates disjoint from (m, a)
    have h_indep_proj : IndepFun (fun ω₂ ↦ ω₂ m a) proj μ₂ := by
      have h_row_bound (hm : m ≠ 0) : ∀ k, min k (m - 1) < m := by
        intro k
        calc min k (m - 1) ≤ m - 1 := Nat.min_le_right k (m - 1)
          _ < m := Nat.sub_lt (by grind) Nat.one_pos
      rw [indepFun_iff_measure_inter_preimage_eq_mul]
      intro s t' hs ht'
      -- rows_lt_m extracts column a at rows < m, other_cols extracts columns ≠ a
      let rows_lt_m : (ℕ → α → R) → (Iio m → R) := fun ω₂ ⟨j, _⟩ ↦ ω₂ j a
      let other_cols : (ℕ → α → R) → (ℕ → {b : α // b ≠ a} → R) := fun ω₂ k ⟨b, _⟩ ↦ ω₂ k b
      have h_proj_factor : ∀ ω₂, proj ω₂ =
          ((fun r k ↦ if hm : m ≠ 0 then r ⟨min k (m - 1), Finset.mem_Iio.mpr (h_row_bound hm k)⟩
            else Nonempty.some inferInstance) (rows_lt_m ω₂),
           other_cols ω₂) := by
        intro ω₂; ext1
        · ext k
          by_cases hm : m ≠ 0
          · simp [proj, rows_lt_m, hm]
          · simp [proj, hm]
        · rfl
      -- Use iIndepFun structure of the doubly-indexed infinite product
      have h_iindep : iIndepFun (fun (p : ℕ × α) ω ↦ ω p.1 p.2) μ₂ :=
        iIndepFun_uncurry_infinitePi' (X := fun _ _ ↦ id) (fun _ ↦ ν) (by fun_prop)
      have h_rows_meas : Measurable rows_lt_m :=
        measurable_pi_lambda _ (fun ⟨j, _⟩ ↦ (measurable_pi_apply a).comp (measurable_pi_apply j))
      have h_other_meas : Measurable other_cols :=
        measurable_pi_lambda _ (fun k ↦ measurable_pi_lambda _ (fun ⟨b, _⟩ ↦
          (measurable_pi_apply b).comp (measurable_pi_apply k)))
      -- Show (ω₂ m a) ⟂ (rows_lt_m, other_cols) via indep_iSup_of_disjoint
      have h_indep_combined : IndepFun (fun ω₂ ↦ ω₂ m a)
          (fun ω₂ ↦ (rows_lt_m ω₂, other_cols ω₂)) μ₂ := by
        rw [IndepFun_iff_Indep]
        have h_comap_le : (MeasurableSpace.pi.prod MeasurableSpace.pi).comap
            (fun ω₂ ↦ (rows_lt_m ω₂, other_cols ω₂)) ≤
            ⨆ (p : {p : ℕ × α // p ≠ (m, a)}), mR.comap (fun ω ↦ ω p.val.1 p.val.2) := by
          rw [MeasurableSpace.comap_prodMk]
          refine sup_le ?_ ?_
          · rw [MeasurableSpace.comap_pi]
            refine iSup_le (fun ⟨j, hj⟩ ↦ ?_)
            have h_ne : (j, a) ≠ (m, a) := fun h ↦ (Finset.mem_Iio.mp hj).ne (Prod.mk.inj h).1
            exact le_iSup_of_le ⟨(j, a), h_ne⟩ le_rfl
          · rw [MeasurableSpace.comap_pi]
            refine iSup_le (fun k ↦ ?_)
            rw [MeasurableSpace.comap_pi]
            refine iSup_le (fun ⟨b, hb⟩ ↦ ?_)
            have h_ne : (k, b) ≠ (m, a) := fun h ↦ hb (Prod.mk.inj h).2
            exact le_iSup_of_le ⟨(k, b), h_ne⟩ le_rfl
        refine indep_of_indep_of_le_right ?_ h_comap_le
        have h_disjoint : Disjoint ({(m, a)} : Set (ℕ × α)) {p | p ≠ (m, a)} := by simp
        have h_le : ∀ p : ℕ × α, mR.comap (fun ω : ℕ → α → R ↦ ω p.1 p.2) ≤
            MeasurableSpace.pi (m := fun _ ↦ MeasurableSpace.pi) := fun p ↦
          Measurable.comap_le ((measurable_pi_apply p.2).comp (measurable_pi_apply p.1))
        have h_iindep' : iIndep (fun p : ℕ × α ↦ mR.comap (fun ω : ℕ → α → R ↦ ω p.1 p.2)) μ₂ :=
          h_iindep.iIndep
        have h_indep := indep_iSup_of_disjoint h_le h_iindep' h_disjoint
        convert h_indep using 2
        · simp only [Set.mem_singleton_iff, iSup_iSup_eq_left]
        · simp only [ne_eq, Set.mem_setOf_eq, iSup_subtype']
      have h_proj_preimage : proj ⁻¹' t' = (fun ω₂ ↦ (rows_lt_m ω₂, other_cols ω₂)) ⁻¹'
          {p | ((fun r k ↦ if hm : m ≠ 0 then
            r ⟨min k (m - 1), Finset.mem_Iio.mpr (h_row_bound hm k)⟩
            else Nonempty.some inferInstance) p.1, p.2) ∈ t'}
          := by ext ω₂; simp only [Set.mem_preimage, Set.mem_setOf_eq, h_proj_factor]
      rw [indepFun_iff_measure_inter_preimage_eq_mul] at h_indep_combined
      rw [h_proj_preimage]
      let T : Set ((Iio m → R) × (ℕ → {b : α // b ≠ a} → R)) :=
        {p | ((fun r k ↦ if hm : m ≠ 0 then
          r ⟨min k (m - 1), Finset.mem_Iio.mpr (h_row_bound hm k)⟩
          else Nonempty.some inferInstance) p.1, p.2) ∈ t'}
      have hT_meas : MeasurableSet T := by
        refine ht'.preimage (Measurable.prod ?_ measurable_snd)
        refine measurable_pi_lambda _ (fun k ↦ ?_)
        by_cases hm : m ≠ 0
        · simp only [ne_eq, hm, not_false_eq_true, ↓reduceDIte]
          exact (measurable_pi_apply (⟨min k (m - 1), Finset.mem_Iio.mpr (h_row_bound hm k)⟩ :
            Iio m)).comp measurable_fst
        · simp [hm]
      change μ₂ ((fun ω₂ ↦ ω₂ m a) ⁻¹' s ∩ (fun ω₂ ↦ (rows_lt_m ω₂, other_cols ω₂)) ⁻¹' T) =
        μ₂ ((fun ω₂ ↦ ω₂ m a) ⁻¹' s) *
        μ₂ ((fun ω₂ ↦ (rows_lt_m ω₂, other_cols ω₂)) ⁻¹' T)
      exact h_indep_combined s T hs hT_meas
    have h_eq : trunc = (fun p k b ↦ if h : b = a then if m ≠ 0 then p.1 k
        else Nonempty.some inferInstance else p.2 k ⟨b, h⟩) ∘ proj := by
      funext ω₂; exact h_trunc_proj ω₂
    rw [h_eq]
    exact h_indep_proj.comp measurable_id h_g_meas
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h_indep_trunc
  have h_const : ∀ ω₁, μ₂ (((fun ω₂ ↦ ω₂ m a) ⁻¹' s) ∩ ((fun ω₂ ↦ (ω₁, trunc ω₂)) ⁻¹' t)) =
      μ₂ ((fun ω₂ ↦ ω₂ m a) ⁻¹' s) * μ₂ ((fun ω₂ ↦ (ω₁, trunc ω₂)) ⁻¹' t) := fun ω₁ ↦
    h_indep_trunc s _ hs (ht.preimage (by fun_prop))
  simp_rw [h_const]
  let c := μ₂ ((fun ω₂ ↦ ω₂ m a) ⁻¹' s)
  change ∫⁻ x, c * μ₂ ((fun ω₂ ↦ (x, trunc ω₂)) ⁻¹' t) ∂μ₁ =
    (∫⁻ _, c ∂μ₁) * ∫⁻ x, μ₂ ((fun ω₂ ↦ (x, trunc ω₂)) ⁻¹' t) ∂μ₁
  have h_preimage : ∀ x, (fun ω₂ ↦ (x, trunc ω₂)) ⁻¹' t = trunc ⁻¹' (Prod.mk x ⁻¹' t) := fun _ ↦ rfl
  simp_rw [h_preimage]
  have h_map : ∀ x, μ₂ (trunc ⁻¹' (Prod.mk x ⁻¹' t)) = (μ₂.map trunc) (Prod.mk x ⁻¹' t) := by
    intro x; rw [Measure.map_apply h_trunc_meas (ht.preimage (by fun_prop))]
  simp_rw [h_map]
  rw [lintegral_const_mul _ (measurable_measure_prodMk_left_finite ht),
    lintegral_const, measure_univ, mul_one]

omit [StandardBorelSpace R] in
lemma indepFun_snd_apply_pullCount_action [Countable α] (alg : Algorithm α R)
    (ν : Kernel α R) [IsMarkovKernel ν] (a : α) (m n : ℕ) :
    (fun ω ↦ ω.2 m a) ⟂ᵢ[arrayMeasure ν]
      ({ω | action alg (n + 1) ω = a ∧
        pullCount (action alg) a (n + 1) ω = m}).indicator (fun _ ↦ 1) :=
  (indepFun_snd_apply_aux ν a m).of_measurable_right (measurable_stepsUntil alg a m n)

lemma indepFun_todo {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} [MeasurableSingletonClass δ] {μ : Measure α}
    {X : α → β} {Y : α → γ} (hXY : X ⟂ᵢ[μ] Y) (hY : Measurable Y)
    {Z : γ → δ} (hZ : Measurable Z) (z : δ) :
    X ⟂ᵢ[μ[|(Z ∘ Y) ⁻¹' {z}]] Y := by
  have h_preim : (Z ∘ Y) ⁻¹' {z} = Y ⁻¹' (Z ⁻¹' {z}) := by grind
  simp_rw [h_preim]
  exact indepFun_cond_of_indepFun hXY hY (hZ (measurableSet_singleton z))

lemma indepFun_snd_hist_cond [Countable α] (alg : Algorithm α R)
    (ν : Kernel α R) [IsMarkovKernel ν] (a : α) (n m : ℕ) :
    (fun ω ↦ ω.2 m a) ⟂ᵢ[(arrayMeasure ν)[|(fun ω ↦ (action alg (n + 1) ω,
      pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω)) ⁻¹' {(a, m)}]]
    (hist alg · n) := by
  have h_meas := measurable_hist_truePast alg a n
  refine IndepFun.of_measurable_right ?_ h_meas
  have h_ae_eq : truePast alg a n =ᵐ[(arrayMeasure ν)[|(fun ω ↦ (action alg (n + 1) ω,
        pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω)) ⁻¹' {(a, m)}]]
      (fun ω ↦ (ω.1, fun k b ↦ if b = a then if m ≠ 0 then ω.2 (min k (m - 1)) b
        else Nonempty.some inferInstance else ω.2 k b)) := by
    refine ae_cond_of_forall_mem ?_ fun x hx ↦ ?_
    · refine (measurableSet_singleton _).preimage ?_
      have h_meas_pc : Measurable fun ω ↦
          pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω := by
        change Measurable ((fun p : (probSpace α R) × α ↦ pullCount (action alg) p.2 (n + 1) p.1) ∘
          (fun ω : probSpace α R ↦ (ω, action alg (n + 1) ω)))
        exact (measurable_uncurry_pullCount (by fun_prop) _).comp (by fun_prop)
      fun_prop
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    simp only [truePast]
    congr with i b
    by_cases hb : b = a
    · simp only [hb, ↓reduceIte]
      simp only [hx.1, true_and] at hx
      congr!
    · simp [hb]
  refine IndepFun.congr ?_ EventuallyEq.rfl h_ae_eq.symm
  suffices (fun ω ↦ ω.2 m a) ⟂ᵢ[(arrayMeasure ν)[|(({ω | action alg (n + 1) ω = a ∧
        pullCount (action alg) a (n + 1) ω = m}).indicator (fun _ ↦ 1)) ⁻¹' {1}]]
      fun ω ↦ (ω.1, fun k b ↦ if b = a then if m ≠ 0 then ω.2 (min k (m - 1)) b
        else Nonempty.some inferInstance else ω.2 k b) by
    convert this using 1
    congr with ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.indicator_apply,
      Set.mem_setOf_eq, ite_eq_left_iff, not_and, zero_ne_one, imp_false,
      Classical.not_imp, Decidable.not_not, and_congr_right_iff]
    intro ha
    simp [ha]
  have h_meas := measurable_stepsUntil alg a m n
  obtain ⟨f, hf, hf_eq⟩ := h_meas.exists_eq_measurable_comp
  simp_rw [hf_eq]
  refine indepFun_todo (Z := f) (z := 1) ?_ ?_ hf
  · exact indepFun_snd_apply_aux ν a m
  · refine Measurable.prodMk (by fun_prop) ?_
    simp_rw [measurable_pi_iff]
    intro i b
    refine Measurable.ite (MeasurableSet.const _) ?_ (by fun_prop)
    refine Measurable.ite (MeasurableSet.const _) (by fun_prop) (by fun_prop)

end Independence

section Laws

variable [Countable α]

lemma hasLaw_action_zero (alg : Algorithm α R) (ν : Kernel α R) [IsMarkovKernel ν] :
    HasLaw (action alg 0) alg.p0 (arrayMeasure ν) where
  map_eq := by
    calc (arrayMeasure ν).map (fun ω ↦ initAlgFunction alg (ω.1 0))
    _ = ((arrayMeasure ν).fst.map (Function.eval 0)).map (initAlgFunction alg) := by
      rw [Measure.fst, Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (volume : Measure I).map (initAlgFunction alg) := by
      simp only [arrayMeasure, Measure.fst_prod]
      rw [(measurePreserving_eval_infinitePi (fun _ ↦ volume) 0).map_eq]
    _ = alg.p0 := initAlgFunction_map alg

variable [StandardBorelSpace R] [Nonempty R]

lemma hasCondDistrib_reward_zero (alg : Algorithm α R) (ν : Kernel α R) [IsMarkovKernel ν] :
    HasCondDistrib (reward alg 0) (action alg 0) ν (arrayMeasure ν) where
  condDistrib_eq := by
    refine (condDistrib_ae_eq_cond (by fun_prop) (by fun_prop)).trans ?_
    rw [Filter.EventuallyEq, ae_iff_of_countable]
    intro a ha
    simp only [reward_zero]
    calc ((arrayMeasure ν)[|action alg 0 ⁻¹' {a}]).map (fun ω ↦ ω.2 0 (action alg 0 ω))
    _ = ((arrayMeasure ν)[|action alg 0 ⁻¹' {a}]).map (fun ω ↦ ω.2 0 a) := by
      refine Measure.map_congr
        (ae_cond_of_forall_mem ((measurableSet_singleton _).preimage (by fun_prop)) ?_)
      intro x hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      simp [hx]
    _ = ν a := by
      rw [cond_of_indepFun]
      · exact map_snd_apply_arrayMeasure 0 a
      · have : (fun ω ↦ ω.1 0) ⟂ᵢ[arrayMeasure ν] fun ω ↦ ω.2 0 a :=
          indepFun_fst_zero_snd_zero_action ν a
        rw [action_zero]
        exact this.comp (φ := initAlgFunction alg) (by fun_prop) measurable_id
      · fun_prop
      · fun_prop
      · simp
      · rwa [Measure.map_apply (by fun_prop) (by simp)] at ha

lemma hasCondDistrib_action' (alg : Algorithm α R) (ν : Kernel α R) [IsMarkovKernel ν] (n : ℕ) :
    HasCondDistrib (action alg (n + 1)) (hist alg · n) (alg.policy n) (arrayMeasure ν) := by
  rw [action_add_one_eq]
  have h_fun ω := algFunction_map alg n (hist alg ω n)
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  refine condDistrib_ae_eq_of_measure_eq_compProd _ (by fun_prop) ?_
  have h_indep : (arrayMeasure ν).map (fun ω ↦ (ω.1 (n + 1), hist alg ω n)) =
      (ℙ).prod ((arrayMeasure ν).map (hist alg · n)) := by
    have h_indep' := indepFun_fst_add_one_hist alg ν n
    rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)] at h_indep'
    rw [h_indep']
    congr
    simp only [arrayMeasure]
    calc ((Measure.infinitePi fun x ↦ ℙ).prod (streamMeasure ν)).map (fun ω ↦ ω.1 (n + 1))
    _ = (Measure.infinitePi fun x ↦ ℙ).map (Function.eval (n + 1)) := by
      nth_rw 2 [← Measure.fst_prod (μ := Measure.infinitePi fun x ↦ ℙ)
        (ν := streamMeasure ν)]
      rw [Measure.fst, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = ℙ := by rw [Measure.infinitePi_map_eval]
  have : (fun x ↦ (hist alg x n, algFunction alg n (hist alg x n) (x.1 (n + 1)))) =
      (fun p ↦ (p.2, algFunction alg n (p.2) (p.1))) ∘ (fun x ↦ (x.1 (n + 1), hist alg x n)) := rfl
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), h_indep]
  have : (ℙ : Measure I).prod ((arrayMeasure ν).map (hist alg · n)) =
      ((Kernel.const _ ℙ) ×ₖ Kernel.id) ∘ₘ ((arrayMeasure ν).map (hist alg · n)) := by
    have h := Measure.compProd_const (μ := (arrayMeasure ν).map (hist alg · n))
      (ν := (ℙ : Measure I))
    rw [Measure.compProd_eq_comp_prod] at h
    rw [← Measure.prod_swap, ← h, ← Measure.deterministic_comp_eq_map (by fun_prop),
      Measure.comp_assoc, ← Kernel.swap, Kernel.swap_prod]
  rw [this, ← Measure.deterministic_comp_eq_map (by fun_prop),
    ← Measure.deterministic_comp_eq_map (by fun_prop), Measure.compProd_eq_comp_prod,
    Measure.comp_assoc, Measure.comp_assoc, Measure.comp_assoc]
  congr 2
  ext ω : 1
  simp only [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap, Kernel.coe_comap,
    Function.comp_apply]
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.const_apply, Kernel.id_apply,
    Kernel.prod_apply, Kernel.id_apply, ← h_fun]
  calc (((ℙ).prod (Measure.dirac (hist alg ω n)))).map (fun p ↦ (p.2, algFunction alg n p.2 p.1))
  _ = (((ℙ).prod (Measure.dirac (hist alg ω n))).map Prod.swap).map
      (fun p ↦ (p.1, algFunction alg n p.1 p.2)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  _ = ((Measure.dirac (hist alg ω n)).prod ℙ).map (fun p ↦ (p.1, algFunction alg n p.1 p.2)) := by
    rw [Measure.prod_swap]
  _ = (Measure.dirac (hist alg ω n)).prod ((ℙ).map (algFunction alg n (hist alg ω n))) := by
    ext s hs
    rw [Measure.map_apply (by fun_prop) hs, Measure.prod_apply, lintegral_dirac, Measure.prod_apply,
      lintegral_dirac, Measure.map_apply (by fun_prop)]
    · congr
    · exact hs.preimage (by fun_prop)
    · exact hs
    · exact hs.preimage (by fun_prop)

/-- The conditional distribution of the reward at time `n + 1`, given the action at time `n + 1`
and the number of times that action has been pulled before time `n + 1`, is equal to
the kernel `ν`. -/
lemma hasCondDistrib_reward_pullCount_action
    (alg : Algorithm α R) (ν : Kernel α R) [IsMarkovKernel ν] (n : ℕ) :
    HasCondDistrib (reward alg (n + 1))
      (fun ω ↦ (action alg (n + 1) ω, pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω))
      (ν.prodMkRight _) (arrayMeasure ν) := by
  have h_meas : Measurable fun ω ↦ pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω := by
    change Measurable ((fun p : (probSpace α R) × α ↦ pullCount (action alg) p.2 (n + 1) p.1) ∘
      (fun ω : probSpace α R ↦ (ω, action alg (n + 1) ω)))
    exact (measurable_uncurry_pullCount (by fun_prop) _).comp (by fun_prop)
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  refine (condDistrib_ae_eq_cond
    (Measurable.prodMk (by fun_prop) (by fun_prop)) (by fun_prop)).trans ?_
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro ⟨a, m⟩ ham
  simp only [Kernel.prodMkRight_apply]
  calc
    Measure.map (reward alg (n + 1))
      (arrayMeasure ν)[|(fun ω ↦ (action alg (n + 1) ω,
        pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω)) ⁻¹' {(a, m)}]
  _ = Measure.map (fun ω ↦ ω.2 m a)
      (arrayMeasure ν)[|(fun ω ↦ (action alg (n + 1) ω,
        pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω)) ⁻¹' {(a, m)}] := by
    rw [reward_eq]
    refine Measure.map_congr
      (ae_cond_of_forall_mem ((measurableSet_singleton _).preimage (by fun_prop)) (fun x hx ↦ ?_))
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    simp only [hx.1] at hx ⊢
    simp [hx.2]
  _ = Measure.map (fun ω ↦ ω.2 m a)
      (arrayMeasure ν)[|({ω | action alg (n + 1) ω = a ∧
        pullCount (action alg) a (n + 1) ω = m}).indicator 1 ⁻¹' {1}] := by
    congr with ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.indicator_apply,
      Set.mem_setOf_eq, Pi.one_apply, ite_eq_left_iff, not_and, zero_ne_one, imp_false,
      Classical.not_imp, Decidable.not_not, and_congr_right_iff]
    intro ha
    simp [ha]
  _ = ν a := by
    rw [cond_of_indepFun, map_snd_apply_arrayMeasure m a]
    · exact (indepFun_snd_apply_pullCount_action alg ν a m n).symm
    · refine Measurable.indicator (by fun_prop) ?_
      exact MeasurableSet.inter ((measurableSet_singleton _).preimage (by fun_prop))
        ((measurableSet_singleton _).preimage (by fun_prop))
    · fun_prop
    · simp
    · rw [Measure.map_apply (by fun_prop) (by simp)] at ham
      convert ham
      ext ω
      simp only [Set.mem_preimage, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply,
        Set.mem_singleton_iff, ite_eq_left_iff, not_and, zero_ne_one, imp_false, Classical.not_imp,
        Decidable.not_not, Prod.mk.injEq, and_congr_right_iff]
      intro ha
      simp [ha]

omit [StandardBorelSpace R] [Nonempty R] in
lemma reward_ae_eq_cond (alg : Algorithm α R) (ν : Kernel α R) (a : α) (n m : ℕ) :
    reward alg (n + 1) =ᵐ[(arrayMeasure ν)[|(fun ω ↦ (action alg (n + 1) ω,
        pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω)) ⁻¹' {(a, m)}]]
      (fun ω ↦ ω.2 m a) := by
  rw [reward_eq]
  refine ae_cond_of_forall_mem ?_ ?_
  · have : Measurable fun ω ↦ pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω := by
      change Measurable ((fun p : (probSpace α R) × α ↦ pullCount (action alg) p.2 (n + 1) p.1) ∘
        (fun ω : probSpace α R ↦ (ω, action alg (n + 1) ω)))
      exact (measurable_uncurry_pullCount (by fun_prop) _).comp (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  intro ω hω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hω
  simp only [hω.2]
  simp [hω.1]

/-- The conditional distribution of the reward at time `n + 1`, given the history up to time `n`,
the action at time `n + 1`, and the number of times that action has been pulled before time `n + 1`,
is equal to the kernel `ν`. -/
lemma hasCondDistrib_reward_hist_action_pullCount
    (alg : Algorithm α R) (ν : Kernel α R) [IsMarkovKernel ν] (n : ℕ) :
    HasCondDistrib (reward alg (n + 1))
      (fun ω ↦ (hist alg ω n, action alg (n + 1) ω,
        pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω))
      ((ν.prodMkRight _).prodMkLeft _) (arrayMeasure ν) := by
  have h_meas : Measurable fun ω ↦ pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω := by
    change Measurable ((fun p : (probSpace α R) × α ↦ pullCount (action alg) p.2 (n + 1) p.1) ∘
      (fun ω : probSpace α R ↦ (ω, action alg (n + 1) ω)))
    exact (measurable_uncurry_pullCount (by fun_prop) _).comp (by fun_prop)
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  refine condDistrib_prod_of_forall_condDistrib_cond (by fun_prop) (by fun_prop) (by fun_prop) _ ?_
  intro (a, m) ham
  have h_eq : ((ν.prodMkRight _).prodMkLeft _).comap (fun ω : (Iic n → α × R) ↦ (ω, a, m))
        (by fun_prop) =
      Kernel.const _ (ν a) := by ext; simp
  rw [h_eq, condDistrib_congr_left (reward_ae_eq_cond alg ν a n m)]
  refine (condDistrib_of_indepFun ?_ (by fun_prop) (by fun_prop)).trans (ae_of_all _ fun ω ↦ ?_)
  · exact (indepFun_snd_hist_cond alg ν a n m).symm
  · simp only [Kernel.const_apply]
    have : (fun ω ↦ (action alg (n + 1) ω,
          pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω)) ⁻¹' {(a, m)} =
        ({ω | action alg (n + 1) ω = a ∧
          pullCount (action alg) a (n + 1) ω = m}).indicator 1 ⁻¹' {1} := by
      ext ω
      simp [Set.indicator_apply]
      grind
    rw [this, cond_of_indepFun, map_snd_apply_arrayMeasure m a]
    · exact (indepFun_snd_apply_pullCount_action alg ν a m n).symm
    · refine Measurable.indicator (by fun_prop) ?_
      exact MeasurableSet.inter ((measurableSet_singleton _).preimage (by fun_prop))
        ((measurableSet_singleton _).preimage (by fun_prop))
    · fun_prop
    · simp
    · convert ham
      ext ω
      simp only [Set.mem_preimage, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply,
        Set.mem_singleton_iff, ite_eq_left_iff, not_and, zero_ne_one, imp_false, Classical.not_imp,
        Decidable.not_not, Prod.mk.injEq, and_congr_right_iff]
      intro ha
      simp [ha]

/-- The reward at time `n + 1` is conditionally independent of the history up to time `n`,
given the action at time `n + 1` and the number of times that action has been pulled before
time `n + 1`. -/
lemma condIndepFun_reward_hist (alg : Algorithm α R) (ν : Kernel α R) [IsMarkovKernel ν] (n : ℕ) :
    (reward alg (n + 1)) ⟂ᵢ[(fun ω ↦ (action alg (n + 1) ω,
          pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω)),
        Measurable.prodMk (by fun_prop) (measurable_pullCount_action_add_one alg n);
        arrayMeasure ν]
      (hist alg · n) := by
  have h_cond := hasCondDistrib_reward_hist_action_pullCount alg ν n
  refine condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft (by fun_prop) (by fun_prop) ?_
    h_cond.condDistrib_eq
  exact Measurable.prodMk (by fun_prop) (measurable_pullCount_action_add_one alg n)

/-- The conditional distribution of the reward at time `n + 1`, given the history up to time `n`
and the action at time `n + 1`, is equal to the kernel `ν`. -/
lemma hasCondDistrib_reward' (alg : Algorithm α R) (ν : Kernel α R) [IsMarkovKernel ν] (n : ℕ) :
    HasCondDistrib (reward alg (n + 1)) (fun ω ↦ (hist alg ω n, action alg (n + 1) ω))
      (ν.prodMkLeft _) (arrayMeasure ν) := by
  let R' := reward alg (n + 1)
  let H := (hist alg · n)
  let A := action alg (n + 1)
  let P := fun ω ↦ pullCount (action alg) (action alg (n + 1) ω) (n + 1) ω
  have hP : Measurable P := measurable_pullCount_action_add_one alg n
  change HasCondDistrib R' (fun ω ↦ (H ω, A ω)) (ν.prodMkLeft _) _
  suffices HasCondDistrib R' (fun ω ↦ (A ω, H ω)) (ν.prodMkRight _) (arrayMeasure ν) by
    have h_eq : (fun ω ↦ (H ω, A ω)) = MeasurableEquiv.prodComm ∘ (fun ω ↦ (A ω, H ω)) := rfl
    rw [h_eq]
    exact this.comp_right (κ := ν.prodMkRight _) _
  suffices HasCondDistrib R' (fun ω ↦ ((A ω, H ω), P ω))
      ((ν.prodMkRight _).prodMkRight _) (arrayMeasure ν) by
    -- use that `P` is measurable wrt `(A, H)` to drop it from the conditioning
    have hP_meas :
        Measurable[MeasurableSpace.comap (fun ω ↦ (A ω, H ω)) inferInstance] P :=
      measurable_pullCount_action_add_one_hist alg n
    obtain ⟨f, hf_meas, hf_eq⟩ := hP_meas.exists_eq_measurable_comp
    simp only [hf_eq, Function.comp_apply] at this
    rwa [hasCondDistrib_prod_right_iff _ _ hf_meas] at this
  suffices HasCondDistrib R' (fun ω ↦ ((A ω, P ω), H ω))
      ((ν.prodMkRight _).prodMkRight _) (arrayMeasure ν) by
    let e : ((α × ℕ) × (Iic n → α × R)) ≃ᵐ ((α × (Iic n → α × R)) × ℕ) :=
    { toFun := fun x ↦ ((x.1.1, x.2), x.1.2)
      invFun := fun x ↦ ((x.1.1, x.2), x.1.2)
      measurable_toFun := by fun_prop
      measurable_invFun := by fun_prop }
    exact this.comp_right e
  suffices HasCondDistrib R' (fun ω ↦ (A ω, P ω)) (ν.prodMkRight _) (arrayMeasure ν) by
    have h_indep : H ⟂ᵢ[(fun ω ↦ (A ω, P ω)), (by fun_prop); arrayMeasure ν] R' :=
      (condIndepFun_reward_hist alg ν n).symm
    have h_condDistrib := this.condDistrib_eq
    rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight (by fun_prop) (by fun_prop)
      (by fun_prop)] at h_indep
    refine ⟨by fun_prop, by fun_prop, ?_⟩
    refine h_indep.trans ?_
    rw [Filter.EventuallyEq, ae_map_iff] at h_condDistrib ⊢
    · simpa only [Kernel.prodMkRight_apply]
    · fun_prop
    · exact Kernel.measurableSet_eq _ _
    · fun_prop
    · exact Kernel.measurableSet_eq _ _
  exact hasCondDistrib_reward_pullCount_action alg ν n

lemma hasCondDistrib_action (alg : Algorithm α R) (ν : Kernel α R) [IsMarkovKernel ν] (n : ℕ) :
    HasCondDistrib (action alg (n + 1))
      (fun ω (i : Iic n) ↦ (action alg i ω, reward alg i ω))
      (alg.policy n) (arrayMeasure ν) := by
  convert hasCondDistrib_action' alg ν n with ω i
  · simp only [action]
    rw [hist_eq _ _ n]
  · simp only [reward]
    rw [hist_eq _ _ n]

lemma hasCondDistrib_reward (alg : Algorithm α R) (ν : Kernel α R) [IsMarkovKernel ν]
    (n : ℕ) :
    HasCondDistrib (reward alg (n + 1))
      (fun ω ↦ (fun (i : Iic n) ↦ (action alg i ω, reward alg i ω), action alg (n + 1) ω))
      ((stationaryEnv ν).feedback n) (arrayMeasure ν) := by
  convert hasCondDistrib_reward' alg ν n with ω i
  · simp only [action]
    rw [hist_eq _ _ n]
  · simp only [reward]
    rw [hist_eq _ _ n]

lemma isAlgEnvSeq_arrayMeasure (alg : Algorithm α R) (ν : Kernel α R) [IsMarkovKernel ν] :
    IsAlgEnvSeq (action alg) (reward alg) alg (stationaryEnv ν) (arrayMeasure ν) where
  hasLaw_action_zero := hasLaw_action_zero alg ν
  hasCondDistrib_reward_zero := hasCondDistrib_reward_zero alg ν
  hasCondDistrib_action := hasCondDistrib_action alg ν
  hasCondDistrib_reward := hasCondDistrib_reward alg ν

end Laws

end ArrayModel

end MeasureSpace

end Bandits
