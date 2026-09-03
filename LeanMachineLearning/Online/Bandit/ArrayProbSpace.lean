/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Independence.CondIndepFun
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepFun
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepInfinitePi
public import LeanMachineLearning.ForMathlib.Probability.Integrable
public import LeanMachineLearning.SequentialLearning.SumRewards
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import Mathlib.Probability.Kernel.Representation

/-!
# Array-of-rewards probability space for stochastic bandits

We build a particular probability space for stochastic bandits, called the "array model", in which
an infinite array of i.i.d. rewards is first produced for all actions. When the algorithm chooses
action `a` for the `n`th time, it receives the reward in the row `a` of the array and column `n`.

Some statements about bandit algorithms are easier to prove in this space, and can then be
transferred to any other probability space using the fact that the conditional distributions of the
arms and rewards specified in the bandit model determine their laws uniquely.

## Main definitions

* `streamMeasure ν`: probability measure on the space of infinite arrays of rewards,
  where the rewards in each row are i.i.d. according to `ν`.
* `probSpace 𝓐 𝓡`: probability space for the array model of stochastic bandits with action space `𝓐`
  and reward space `𝓡`.
* `arrayMeasure ν`: probability measure on `probSpace 𝓐 𝓡` for the array model of stochastic bandits
  with reward kernel `ν`.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Learning

open scoped ENNReal NNReal

namespace Bandits

variable {𝓐 𝓡 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓡 : MeasurableSpace 𝓡}

section MeasureSpace

/-- Measure of an infinite stream of rewards from each action. -/
noncomputable
def streamMeasure (ν : Kernel 𝓐 𝓡) : Measure (ℕ → 𝓐 → 𝓡) :=
  Measure.infinitePi fun _ ↦ Measure.infinitePi ν

instance (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] : IsProbabilityMeasure (streamMeasure ν) := by
  unfold streamMeasure
  infer_instance

section StreamMeasure

lemma hasLaw_eval_streamMeasure (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (n : ℕ) :
    HasLaw (fun h : ℕ → 𝓐 → 𝓡 ↦ h n) (Measure.infinitePi ν) (streamMeasure ν) :=
  hasLaw_eval_infinitePi (fun _ ↦ Measure.infinitePi ν) n

lemma hasLaw_eval_eval_streamMeasure (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (n : ℕ) (a : 𝓐) :
    HasLaw (fun h : ℕ → 𝓐 → 𝓡 ↦ h n a) (ν a) (streamMeasure ν) :=
  (hasLaw_eval_infinitePi ν a).comp (hasLaw_eval_streamMeasure ν n)

lemma identDistrib_eval_eval_id_streamMeasure (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (n : ℕ) (a : 𝓐) :
    IdentDistrib (fun h : ℕ → 𝓐 → 𝓡 ↦ h n a) id (streamMeasure ν) (ν a) where
  aemeasurable_fst := Measurable.aemeasurable (by fun_prop)
  aemeasurable_snd := Measurable.aemeasurable (by fun_prop)
  map_eq := by
    rw [← (hasLaw_eval_eval_streamMeasure ν n a).map_eq,
      Measure.map_map (by fun_prop) (by fun_prop)]
    simp

lemma integrable_eval_streamMeasure (ν : Kernel 𝓐 ℝ) [IsMarkovKernel ν] (n : ℕ) (a : 𝓐)
    (h_int : Integrable id (ν a)) :
    Integrable (fun h : ℕ → 𝓐 → ℝ ↦ h n a) (streamMeasure ν) :=
  Integrable.congr_identDistrib h_int (identDistrib_eval_eval_id_streamMeasure ν n a).symm

lemma integral_eval_streamMeasure (ν : Kernel 𝓐 ℝ) [IsMarkovKernel ν] (n : ℕ) (a : 𝓐) :
    ∫ h, h n a ∂(streamMeasure ν) = (ν a)[id] := by
  simpa using (hasLaw_eval_eval_streamMeasure ν n a).integral_eq

lemma iIndepFun_eval_streamMeasure' (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] :
    iIndepFun (fun n ω ↦ ω n) (streamMeasure ν) :=
  iIndepFun_infinitePi fun _ ↦ measurable_id

lemma iIndepFun_eval_streamMeasure'' (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (a : 𝓐) :
    iIndepFun (fun n ω ↦ ω n a) (streamMeasure ν) :=
  (iIndepFun_eval_streamMeasure' ν).comp (g := fun i ω ↦ ω a) (by fun_prop)

lemma iIndepFun_eval_streamMeasure (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] :
    iIndepFun (fun (p : ℕ × 𝓐) ω ↦ ω p.1 p.2) (streamMeasure ν) :=
  iIndepFun_uncurry_infinitePi' (X := fun _ _ ↦ id) (fun _ ↦ ν) (by fun_prop)

lemma indepFun_eval_streamMeasure (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] {n m : ℕ} {a b : 𝓐}
    (h : n ≠ m ∨ a ≠ b) :
    IndepFun (fun ω ↦ ω n a) (fun ω ↦ ω m b) (streamMeasure ν) := by
  change IndepFun (fun ω ↦ ω (n, a).1 (n, a).2) (fun ω ↦ ω (m, b).1 (m, b).2)
    (streamMeasure ν)
  exact (iIndepFun_eval_streamMeasure ν).indepFun (by grind)

lemma indepFun_eval_streamMeasure' (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] {a b : 𝓐} (h : a ≠ b) :
    IndepFun (fun ω n ↦ ω n a) (fun ω n ↦ ω n b) (streamMeasure ν) :=
  indepFun_proj_infinitePi_infinitePi h

end StreamMeasure

namespace ArrayModel

open unitInterval

section ProbabilitySpace

variable (𝓐 𝓡) in
/-- Probability space for the array model of stochastic bandits. -/
abbrev probSpace : Type _ := (ℕ → I) × (ℕ → 𝓐 → 𝓡)

/-- Probability measure for the array model of stochastic bandits. -/
noncomputable
def arrayMeasure (ν : Kernel 𝓐 𝓡) : Measure (probSpace 𝓐 𝓡) :=
  (Measure.infinitePi fun _ ↦ volume).prod (streamMeasure ν)

instance (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] : IsProbabilityMeasure (arrayMeasure ν) :=
  Measure.prod.instIsProbabilityMeasure _ _

lemma hasLaw_fst_apply_arrayMeasure (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (n : ℕ) :
    HasLaw (fun ω : probSpace 𝓐 𝓡 ↦ ω.1 n) volume (arrayMeasure ν) :=
  (hasLaw_eval_infinitePi (fun _ ↦ volume) n).comp (hasLaw_fst_prod _ _)

lemma hasLaw_snd_apply_arrayMeasure (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (n : ℕ) (a : 𝓐) :
    HasLaw (fun ω : probSpace 𝓐 𝓡 ↦ ω.2 n a) (ν a) (arrayMeasure ν) :=
  (hasLaw_eval_eval_streamMeasure ν n a).comp (hasLaw_snd_prod _ _)

lemma map_snd_apply_arrayMeasure {ν : Kernel 𝓐 𝓡} [IsMarkovKernel ν] (n : ℕ) (a : 𝓐) :
    (arrayMeasure ν).map (fun ω ↦ ω.2 n a) = ν a :=
  (hasLaw_snd_apply_arrayMeasure ν n a).map_eq

/-- Modification of `ω` in which the rewards of action `a` are read only up to index `m - 1`:
in row `a` of the reward array, the entry at index `i` is kept if `i < m` and replaced by the entry
at index `m + 1 + i` otherwise. The result does not depend on the coordinate `(m, a)` of the
array. -/
def truncRow [DecidableEq 𝓐] (a : 𝓐) (m : ℕ) (ω : probSpace 𝓐 𝓡) : probSpace 𝓐 𝓡 :=
  (ω.1, fun i b ↦ if b = a then ω.2 (if i < m then i else m + 1 + i) b else ω.2 i b)

@[fun_prop]
lemma measurable_truncRow [DecidableEq 𝓐] (a : 𝓐) (m : ℕ) :
    Measurable (truncRow a m : probSpace 𝓐 𝓡 → probSpace 𝓐 𝓡) := by
  refine Measurable.prodMk measurable_fst
    (measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun b ↦ ?_)
  by_cases hb : b = a <;> simp only [hb, ↓reduceIte] <;> fun_prop

variable [Nonempty 𝓐] [StandardBorelSpace 𝓐]

/-- The next action is the image of the history and a uniform random variable by this function. -/
noncomputable
def algFunction (alg : Algorithm 𝓐 𝓡) (n : ℕ) :
    (Fin n → 𝓐 × 𝓡) → I → 𝓐 :=
  (Kernel.exists_measurable_map_eq_unitInterval (alg.policy n)).choose

lemma algFunction_map (alg : Algorithm 𝓐 𝓡) (n : ℕ) (h : Fin n → 𝓐 × 𝓡) :
    volume.map (algFunction alg n h) = alg.policy n h :=
  (Kernel.exists_measurable_map_eq_unitInterval (alg.policy n)).choose_spec.2 h

/-- The initial action is the image of a uniform random variable by `algFunction alg 0 default`. -/
lemma algFunction_zero_map (alg : Algorithm 𝓐 𝓡) :
    volume.map (algFunction alg 0 default) = alg.p0 :=
  algFunction_map alg 0 default

@[fun_prop]
lemma measurable_algFunction (alg : Algorithm 𝓐 𝓡) (n : ℕ) :
    Measurable (Function.uncurry (algFunction alg n)) :=
  (Kernel.exists_measurable_map_eq_unitInterval (alg.policy n)).choose_spec.1

end ProbabilitySpace

variable [Nonempty 𝓐] [StandardBorelSpace 𝓐]

section HistoryActionReward

/-- History of actions and rewards before time `n` in the array model. -/
noncomputable
def hist [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (ω : probSpace 𝓐 𝓡) : (n : ℕ) → Fin n → 𝓐 × 𝓡
| 0 => default
| n + 1 =>
  let hn : Fin n → 𝓐 × 𝓡 := hist alg ω n
  let a : 𝓐 := algFunction alg n hn (ω.1 n)
  Fin.snoc hn (a, ω.2 (pullCount' n hn a) a)

@[simp]
lemma hist_zero [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (ω : probSpace 𝓐 𝓡) :
    hist alg ω 0 = default := rfl

lemma hist_add_one [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (ω : probSpace 𝓐 𝓡) (n : ℕ) :
    hist alg ω (n + 1) =
      Fin.snoc (hist alg ω n) (algFunction alg n (hist alg ω n) (ω.1 n),
        ω.2 (pullCount' n (hist alg ω n) (algFunction alg n (hist alg ω n) (ω.1 n)))
          (algFunction alg n (hist alg ω n) (ω.1 n))) := rfl

lemma hist_add_one_eq_finSuccProd' [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (ω : probSpace 𝓐 𝓡)
    (n : ℕ) :
    hist alg ω (n + 1) =
      (MeasurableEquiv.finSuccProd (𝓐 × 𝓡) n).symm
        (hist alg ω n, (algFunction alg n (hist alg ω n) (ω.1 n),
          ω.2 (pullCount' n (hist alg ω n) (algFunction alg n (hist alg ω n) (ω.1 n)))
            (algFunction alg n (hist alg ω n) (ω.1 n)))) := by
  rw [MeasurableEquiv.finSuccProd_symm_apply]
  rfl

/-- Action taken at time `n` in the array model. -/
noncomputable
def action [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (n : ℕ) (ω : probSpace 𝓐 𝓡) : 𝓐 :=
  algFunction alg n (hist alg ω n) (ω.1 n)

lemma action_eq [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (n : ℕ) :
    action alg n = fun ω ↦ algFunction alg n (hist alg ω n) (ω.1 n) := rfl

lemma action_zero [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) :
    action alg 0 = fun ω ↦ algFunction alg 0 default (ω.1 0) := rfl

/-- Reward received at time `n` in the array model. -/
noncomputable
def reward [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (n : ℕ) (ω : probSpace 𝓐 𝓡) : 𝓡 :=
  (hist alg ω (n + 1) (Fin.last n)).2

lemma reward_eq' [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (n : ℕ) (ω : probSpace 𝓐 𝓡) :
    reward alg n ω = ω.2 (pullCount' n (hist alg ω n) (action alg n ω)) (action alg n ω) := by
  change (hist alg ω (n + 1) (Fin.last n)).2 = _
  rw [hist_add_one, Fin.snoc_last]
  rfl

lemma hist_succ [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (ω : probSpace 𝓐 𝓡) (n : ℕ) :
    hist alg ω (n + 1) = Fin.snoc (hist alg ω n) (action alg n ω, reward alg n ω) := by
  rw [hist_add_one, reward_eq']
  rfl

lemma hist_succ_eq_finSuccProd [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (ω : probSpace 𝓐 𝓡)
    (n : ℕ) :
    hist alg ω (n + 1) =
      (MeasurableEquiv.finSuccProd (𝓐 × 𝓡) n).symm
        (hist alg ω n, (action alg n ω, reward alg n ω)) := by
  rw [MeasurableEquiv.finSuccProd_symm_apply, hist_succ]

lemma hist_apply_last [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (ω : probSpace 𝓐 𝓡) (n : ℕ) :
    hist alg ω (n + 1) (Fin.last n) = (action alg n ω, reward alg n ω) := by
  rw [hist_succ, Fin.snoc_last]

lemma hist_eq [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (ω : probSpace 𝓐 𝓡) (n : ℕ) :
    hist alg ω n = fun i : Fin n ↦ (action alg i ω, reward alg i ω) := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n hn =>
    ext i : 1
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · rw [hist_apply_last]
      simp
    · rw [hist_succ, Fin.snoc_castSucc, hn]
      simp

/-- The history in the array model is the history of the action and reward processes. -/
lemma hist_eq_history [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (ω : probSpace 𝓐 𝓡) (n : ℕ) :
    hist alg ω n = history (action alg) (reward alg) n ω := hist_eq alg ω n

lemma pullCount_action_eq [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (a : 𝓐) (n : ℕ)
    (ω : probSpace 𝓐 𝓡) :
    pullCount (action alg) a n ω = pullCount' n (hist alg ω n) a := by
  rw [pullCount_eq_pullCount' (R' := reward alg), hist_eq]

lemma pullCount_action_eq_comp [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (a : 𝓐) (n : ℕ) :
    pullCount (action alg) a n = (fun h ↦ pullCount' n h a) ∘ (hist alg · n) := by
  ext ω
  exact pullCount_action_eq alg a n ω

lemma reward_eq [DecidableEq 𝓐] (alg : Algorithm 𝓐 𝓡) (n : ℕ) :
    reward alg n = fun ω ↦ ω.2 (pullCount (action alg) (action alg n ω) n ω) (action alg n ω) := by
  ext ω
  rw [reward_eq', pullCount_action_eq]

lemma sumRewards_eq [DecidableEq 𝓐] (alg : Algorithm 𝓐 ℝ) (a : 𝓐) (n : ℕ) (ω : probSpace 𝓐 ℝ) :
    sumRewards (action alg) (reward alg) a n ω =
      ∑ i ∈ range (pullCount (action alg) a n ω), ω.2 i a := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases ha : action alg n ω = a
    · simp [ha, sumRewards_add_one, pullCount_add_one, sum_range_succ, ih, reward_eq]
    · simp [ha, sumRewards_add_one, pullCount_eq_pullCount_of_action_ne, ih]

section Measurability

lemma measurable_action' [DecidableEq 𝓐] {alg : Algorithm 𝓐 𝓡}
    (n : ℕ) (h : Measurable (hist alg · n)) :
    Measurable (fun x ↦ algFunction alg n (hist alg x n) (x.1 n)) := by fun_prop

lemma measurable_pullCount'_action [DecidableEq 𝓐] {alg : Algorithm 𝓐 𝓡}
    (n : ℕ) (h_hist : Measurable (hist alg · n)) :
    Measurable (fun x ↦
      pullCount' n (hist alg x n) (algFunction alg n (hist alg x n) (x.1 n))) := by
  have h_alg_meas : Measurable (fun x ↦ algFunction alg n (hist alg x n) (x.1 n)) :=
    measurable_action' n h_hist
  exact (measurable_uncurry_pullCount' (𝓐 := 𝓐) n).comp (h_hist.prodMk h_alg_meas)

@[fun_prop]
lemma measurable_hist [DecidableEq 𝓐] [Countable 𝓐] (alg : Algorithm 𝓐 𝓡) (n : ℕ) :
    Measurable (fun ω ↦ hist alg ω n) := by
  induction n with
  | zero =>
    simp only [hist_zero]
    exact measurable_const
  | succ n hn =>
    have h_eq : (fun ω ↦ hist alg ω (n + 1)) =
        (MeasurableEquiv.finSuccProd (𝓐 × 𝓡) n).symm ∘
          (fun ω ↦ (hist alg ω n, (algFunction alg n (hist alg ω n) (ω.1 n),
            ω.2 (pullCount' n (hist alg ω n) (algFunction alg n (hist alg ω n) (ω.1 n)))
              (algFunction alg n (hist alg ω n) (ω.1 n))))) := by
      ext ω : 1
      exact hist_add_one_eq_finSuccProd' alg ω n
    rw [h_eq]
    refine (MeasurableEquiv.measurable _).comp (hn.prodMk ?_)
    refine Measurable.prodMk (measurable_action' n hn) ?_
    change Measurable ((fun (x : (ℕ → 𝓐 → 𝓡) × ℕ × 𝓐) ↦ x.1 x.2.1 x.2.2) ∘
      (fun x ↦ (x.2, pullCount' n (hist alg x n) (algFunction alg n (hist alg x n) (x.1 n)),
        (algFunction alg n (hist alg x n) (x.1 n)))))
    have h1 : Measurable (fun (x : (ℕ → 𝓐 → 𝓡) × ℕ × 𝓐) ↦ x.1 x.2.1 x.2.2) :=
      measurable_from_prod_countable_left fun p : ℕ × 𝓐 ↦ (by simp only; fun_prop)
    refine h1.comp (Measurable.prodMk (by fun_prop) ?_)
    exact (measurable_pullCount'_action n hn).prodMk (measurable_action' n hn)

@[fun_prop]
lemma measurable_action [DecidableEq 𝓐] [Countable 𝓐] (alg : Algorithm 𝓐 𝓡) (n : ℕ) :
    Measurable (action alg n) := by unfold action; fun_prop

@[fun_prop]
lemma measurable_reward [DecidableEq 𝓐] [Countable 𝓐] (alg : Algorithm 𝓐 𝓡) (n : ℕ) :
    Measurable (reward alg n) := by unfold reward; fun_prop

@[fun_prop]
lemma measurable_pullCount_action [DecidableEq 𝓐] [Countable 𝓐] (alg : Algorithm 𝓐 𝓡)
    (n : ℕ) :
    Measurable (fun ω ↦ pullCount (action alg) (action alg n ω) n ω) := by
  change Measurable ((fun p : (probSpace 𝓐 𝓡) × 𝓐 ↦ pullCount (action alg) p.2 n p.1) ∘
    (fun ω : probSpace 𝓐 𝓡 ↦ (ω, action alg n ω)))
  exact (measurable_uncurry_pullCount (by fun_prop) _).comp (by fun_prop)

end Measurability

end HistoryActionReward

variable [DecidableEq 𝓐]

section Congruence

-- very useful to prove measurability
lemma hist_congr (alg : Algorithm 𝓐 𝓡) (n : ℕ) {ω ω' : probSpace 𝓐 𝓡}
    (hω1 : ∀ i < n, ω.1 i = ω'.1 i)
    (hω2 : ∀ i a, i < pullCount (action alg) a n ω → ω.2 i a = ω'.2 i a) :
    hist alg ω n = hist alg ω' n := by
  induction n with
  | zero => rfl
  | succ n hn =>
    have h_hist : hist alg ω n = hist alg ω' n := by
      refine hn (fun i hi ↦ hω1 i (by lia)) fun i a hi ↦ hω2 i a (hi.trans_le ?_)
      exact pullCount_mono _ (by lia) _
    have h_action : action alg n ω = action alg n ω' := by
      simp only [action, h_hist, hω1 n (by lia)]
    have h_reward : reward alg n ω = reward alg n ω' := by
      rw [reward_eq', reward_eq', ← h_hist, ← h_action]
      refine hω2 _ _ ?_
      rw [pullCount_action_eq_pullCount_add_one, pullCount_action_eq]
      exact Nat.lt_succ_self _
    rw [hist_succ, hist_succ, h_hist, h_action, h_reward]

lemma action_eq_and_pullCount_eq_congr_aux (alg : Algorithm 𝓐 𝓡)
    (a : 𝓐) (m n : ℕ) {ω ω' : probSpace 𝓐 𝓡}
    (hω1 : ∀ i, ω.1 i = ω'.1 i) (hω2_ne : ∀ i b, b ≠ a → ω.2 i b = ω'.2 i b)
    (hω2_eq : ∀ i, i + 1 ≤ m → ω.2 i a = ω'.2 i a)
    (h_eq : action alg n ω = a ∧ pullCount (action alg) a n ω = m) :
    action alg n ω' = a ∧ pullCount (action alg) a n ω' = m := by
  obtain ⟨h_action, h_pc⟩ := h_eq
  have h_hist : hist alg ω n = hist alg ω' n := by
    refine hist_congr alg n (fun i _ ↦ hω1 i) fun i b hi ↦ ?_
    rcases eq_or_ne b a with (rfl | hba)
    · rw [h_pc] at hi
      exact hω2_eq i hi
    · exact hω2_ne i b hba
  constructor
  · rw [← h_action]
    simp only [action, h_hist, hω1]
  · rw [← h_pc, pullCount_action_eq, pullCount_action_eq, h_hist]

lemma action_eq_and_pullCount_eq_congr (alg : Algorithm 𝓐 𝓡) (a : 𝓐) (m n : ℕ)
    {ω ω' : probSpace 𝓐 𝓡}
    (hω1 : ∀ i, ω.1 i = ω'.1 i) (hω2_ne : ∀ i b, b ≠ a → ω.2 i b = ω'.2 i b)
    (hω2_eq : ∀ i, i + 1 ≤ m → ω.2 i a = ω'.2 i a) :
    (action alg n ω = a ∧ pullCount (action alg) a n ω = m) ↔
      (action alg n ω' = a ∧ pullCount (action alg) a n ω' = m) :=
  ⟨action_eq_and_pullCount_eq_congr_aux alg a m n hω1 hω2_ne hω2_eq,
    action_eq_and_pullCount_eq_congr_aux alg a m n (by grind) (by grind) (by grind)⟩

lemma indicator_action_eq_and_pullCount_eq_congr (alg : Algorithm 𝓐 𝓡) (a : 𝓐) (m n : ℕ)
    {ω ω' : probSpace 𝓐 𝓡}
    (hω1 : ∀ i, ω.1 i = ω'.1 i) (hω2_ne : ∀ i b, b ≠ a → ω.2 i b = ω'.2 i b)
    (hω2_eq : ∀ i, i + 1 ≤ m → ω.2 i a = ω'.2 i a) :
    {ω | action alg n ω = a ∧ pullCount (action alg) a n ω = m}.indicator (fun _ ↦ 1) ω =
      {ω | action alg n ω = a ∧ pullCount (action alg) a n ω = m}.indicator (fun _ ↦ 1) ω' := by
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  simp_rw [action_eq_and_pullCount_eq_congr alg a m n hω1 hω2_ne hω2_eq]

end Congruence

section MeasurabilityAdvanced

lemma measurable_hist_comap [Countable 𝓐] (alg : Algorithm 𝓐 𝓡) (n : ℕ) :
    Measurable[MeasurableSpace.comap (fun ω ↦ (fun (i : Fin n) ↦ ω.1 i, ω.2)) inferInstance]
      (hist alg · n) := by
  have h_eq : (hist alg · n) =
      ((hist alg · n) ∘ (fun p ↦ (fun i : ℕ ↦ if hi : i < n then p.1 ⟨i, hi⟩ else 0, p.2))) ∘
        (fun ω ↦ (fun (i : Fin n) ↦ ω.1 i, ω.2)) := by
    ext ω : 1
    exact hist_congr alg n (fun i hi ↦ by simp [hi]) (fun _ _ _ ↦ rfl)
  rw [h_eq]
  refine measurable_comp_comap _ (Measurable.comp (by fun_prop) ?_)
  refine Measurable.prodMk ?_ (by fun_prop)
  rw [measurable_pi_iff]
  intro i
  by_cases hi : i < n
  · simp only [hi, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [hi, ↓reduceDIte]
    exact measurable_const

/-- `truncRow` at the number of pulls of `a` before time `n`: the rewards of action `a` that have
not been observed before time `n` are replaced. The history before time `n` is measurable with
respect to this function (see `measurable_hist_truncRowPullCount`), and on the event
`pullCount (action alg) a n = m` it coincides with `truncRow a m`. -/
noncomputable
def truncRowPullCount (alg : Algorithm 𝓐 𝓡) (a : 𝓐) (n : ℕ) (ω : probSpace 𝓐 𝓡) :
    probSpace 𝓐 𝓡 :=
  truncRow a (pullCount (action alg) a n ω) ω

lemma measurable_hist_truncRowPullCount [Countable 𝓐] (alg : Algorithm 𝓐 𝓡) (a : 𝓐) (n : ℕ) :
    Measurable[MeasurableSpace.comap (truncRowPullCount alg a n) inferInstance] (hist alg · n) := by
  have h_eq : (hist alg · n) = (hist alg · n) ∘ (truncRowPullCount alg a n) := by
    ext ω : 1
    refine hist_congr alg n (fun _ _ ↦ rfl) fun i b hi ↦ ?_
    by_cases hb : b = a
    · subst hb
      simp [truncRowPullCount, truncRow, hi]
    · simp [truncRowPullCount, truncRow, hb]
  rw [h_eq]
  exact (measurable_hist alg n).comp (Measurable.of_comap_le le_rfl)

lemma measurableSet_action_eq_and_pullCount_eq [Countable 𝓐] (alg : Algorithm 𝓐 𝓡) (a : 𝓐)
    (n m : ℕ) :
    MeasurableSet {ω | action alg n ω = a ∧ pullCount (action alg) a n ω = m} :=
  MeasurableSet.inter ((measurableSet_singleton _).preimage (by fun_prop))
    ((measurableSet_singleton _).preimage (by fun_prop))

lemma preimage_action_pullCount_eq (alg : Algorithm 𝓐 𝓡) (a : 𝓐) (n m : ℕ) :
    (fun ω ↦ (action alg n ω, pullCount (action alg) (action alg n ω) n ω)) ⁻¹' {(a, m)} =
      {ω | action alg n ω = a ∧ pullCount (action alg) a n ω = m}.indicator (fun _ ↦ 1)
        ⁻¹' {1} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.indicator_apply,
    Set.mem_ofPred_eq, ite_eq_left_iff, not_and, zero_ne_one, imp_false, Classical.not_imp,
    Decidable.not_not, and_congr_right_iff]
  intro ha
  simp [ha]

lemma measurable_indicator_action_eq_and_pullCount_eq [Countable 𝓐] (alg : Algorithm 𝓐 𝓡)
    (a : 𝓐) (m n : ℕ) :
    Measurable[MeasurableSpace.comap (truncRow a m) inferInstance]
      (({ω | action alg n ω = a ∧ pullCount (action alg) a n ω = m}).indicator (fun _ ↦ 1)) := by
  let f := ({ω | action alg n ω = a ∧ pullCount (action alg) a n ω = m}).indicator (fun _ ↦ 1)
  have h_eq : f = f ∘ truncRow a m := by
    ext ω
    exact indicator_action_eq_and_pullCount_eq_congr alg a m n (fun _ ↦ rfl)
      (fun _ _ hb ↦ by simp [truncRow, hb]) (fun i hi ↦ by simp [truncRow, show i < m by omega])
  change Measurable[MeasurableSpace.comap (truncRow a m) inferInstance] f
  rw [h_eq]
  exact (Measurable.indicator (by fun_prop)
    (measurableSet_action_eq_and_pullCount_eq alg a n m)).comp (Measurable.of_comap_le le_rfl)

lemma measurable_pullCount_action_hist (alg : Algorithm 𝓐 𝓡) (n : ℕ) :
    Measurable[MeasurableSpace.comap (fun ω ↦ (hist alg ω n, action alg n ω)) inferInstance]
      (fun ω ↦ pullCount (action alg) (action alg n ω) n ω) := by
  simp_rw [pullCount_action_eq]
  change Measurable[MeasurableSpace.comap (fun ω ↦ (hist alg ω n, action alg n ω)) inferInstance]
    ((fun p : (Fin n → 𝓐 × 𝓡) × 𝓐 ↦ pullCount' n p.1 p.2) ∘
      (fun ω ↦ (hist alg ω n, action alg n ω)))
  exact measurable_comp_comap _ (measurable_uncurry_pullCount' n)

end MeasurabilityAdvanced

section Independence

omit [Nonempty 𝓐] [StandardBorelSpace 𝓐] [DecidableEq 𝓐] in
lemma indepFun_fst_snd (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] :
    IndepFun Prod.fst Prod.snd (arrayMeasure ν) :=
  indepFun_prod measurable_id measurable_id

omit [Nonempty 𝓐] [StandardBorelSpace 𝓐] [DecidableEq 𝓐] in
lemma indepFun_fst_zero_snd_zero_action (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (a : 𝓐) :
    IndepFun (fun ω ↦ ω.1 0) (fun ω ↦ ω.2 0 a) (arrayMeasure ν) :=
  indepFun_prod (X := fun ω : ℕ → I ↦ ω 0) (Y := fun ω : ℕ → 𝓐 → 𝓡 ↦ ω 0 a)
    (by fun_prop) (by fun_prop)

omit [Nonempty 𝓐] [StandardBorelSpace 𝓐] [DecidableEq 𝓐] in
lemma indepFun_fst_aux (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (n : ℕ) :
    (fun ω ↦ ω.1 n) ⟂ᵢ[arrayMeasure ν] (fun ω ↦ (fun (i : Fin n) ↦ ω.1 i, ω.2)) := by
  have h : IndepFun (fun ω : ℕ → I ↦ ω n) (fun ω (i : Fin n) ↦ ω i)
      (Measure.infinitePi fun _ ↦ volume) := by
    refine (iIndepFun_infinitePi fun _ ↦ measurable_id).indepFun_of_measurable_iSup_comap
      (fun _ ↦ measurable_pi_apply _) (S := Set.Iio n) (by simp) ?_
    rw [measurable_iff_comap_le, MeasurableSpace.comap_pi]
    exact iSup_le fun i ↦ le_iSup₂_of_le (i : ℕ) (Set.mem_Iio.2 i.2) le_rfl
  exact h.fst_prod (ν := streamMeasure ν) (by fun_prop) (by fun_prop)

variable [StandardBorelSpace 𝓡] [Nonempty 𝓡]

lemma indepFun_fst_hist [Countable 𝓐] (alg : Algorithm 𝓐 𝓡)
    (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (n : ℕ) :
    IndepFun (fun ω ↦ ω.1 n) (hist alg · n) (arrayMeasure ν) :=
  (indepFun_fst_aux ν n).of_measurable_right (measurable_hist_comap alg n)

omit [Nonempty 𝓐] [StandardBorelSpace 𝓐] [StandardBorelSpace 𝓡] [Nonempty 𝓡] in
/-- The reward `ω.2 m a` is independent of `truncRow a m`, which reads only other coordinates. -/
lemma indepFun_snd_apply_truncRow (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (a : 𝓐) (m : ℕ) :
    (fun ω ↦ ω.2 m a) ⟂ᵢ[arrayMeasure ν] (truncRow a m) := by
  let T : (ℕ → 𝓐 → 𝓡) → (ℕ → 𝓐 → 𝓡) :=
    fun ω k b ↦ if b = a then ω (if k < m then k else m + 1 + k) b else ω k b
  have hT : Measurable[⨆ p ∈ {p : ℕ × 𝓐 | p ≠ (m, a)},
      MeasurableSpace.comap (fun ω : ℕ → 𝓐 → 𝓡 ↦ ω p.1 p.2) inferInstance] T := by
    rw [measurable_iff_comap_le, MeasurableSpace.comap_pi]
    refine iSup_le fun k ↦ ?_
    rw [MeasurableSpace.comap_pi]
    refine iSup_le fun b ↦ ?_
    by_cases hb : b = a
    · simp only [T, hb, ↓reduceIte]
      refine le_iSup₂_of_le (if k < m then k else m + 1 + k, a) ?_ (le_of_eq rfl)
      simp only [Set.mem_ofPred_eq, ne_eq, Prod.mk.injEq, and_true]
      split_ifs <;> omega
    · simp only [T, hb, ↓reduceIte]
      exact le_iSup₂_of_le (k, b) (by simp [hb]) (le_of_eq rfl)
  have hTm : Measurable T :=
    hT.mono (iSup₂_le fun p _ ↦ Measurable.comap_le (by fun_prop)) le_rfl
  have h := (iIndepFun_eval_streamMeasure ν).indepFun_of_measurable_iSup_comap
    (fun _ ↦ by fun_prop) (i := (m, a)) (by simp) hT
  exact h.snd_prod (μ := Measure.infinitePi fun _ ↦ volume) (by fun_prop) hTm

omit [StandardBorelSpace 𝓡] [Nonempty 𝓡] in
lemma indepFun_snd_apply_pullCount_action [Countable 𝓐] (alg : Algorithm 𝓐 𝓡)
    (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (a : 𝓐) (m n : ℕ) :
    (fun ω ↦ ω.2 m a) ⟂ᵢ[arrayMeasure ν]
      ({ω | action alg n ω = a ∧ pullCount (action alg) a n ω = m}).indicator (fun _ ↦ 1) :=
  (indepFun_snd_apply_truncRow ν a m).of_measurable_right
    (measurable_indicator_action_eq_and_pullCount_eq alg a m n)

lemma indepFun_snd_hist_cond [Countable 𝓐] (alg : Algorithm 𝓐 𝓡)
    (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (a : 𝓐) (n m : ℕ) :
    (fun ω ↦ ω.2 m a) ⟂ᵢ[(arrayMeasure ν)[|(fun ω ↦ (action alg n ω,
      pullCount (action alg) (action alg n ω) n ω)) ⁻¹' {(a, m)}]]
    (hist alg · n) := by
  refine IndepFun.of_measurable_right ?_ (measurable_hist_truncRowPullCount alg a n)
  have h_ae_eq : truncRowPullCount alg a n =ᵐ[(arrayMeasure ν)[|(fun ω ↦ (action alg n ω,
        pullCount (action alg) (action alg n ω) n ω)) ⁻¹' {(a, m)}]]
      truncRow a m := by
    refine ae_cond_of_forall_mem ((measurableSet_singleton _).preimage (by fun_prop))
      fun x hx ↦ ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨hxa, hxm⟩ := hx
    rw [hxa] at hxm
    simp only [truncRowPullCount, hxm]
  refine IndepFun.congr ?_ EventuallyEq.rfl h_ae_eq.symm
  rw [preimage_action_pullCount_eq]
  obtain ⟨f, hf, hf_eq⟩ :=
    (measurable_indicator_action_eq_and_pullCount_eq alg a m n).exists_eq_measurable_comp
  simp_rw [hf_eq]
  exact indepFun_cond_comp (Z := f) (z := 1) (indepFun_snd_apply_truncRow ν a m)
    (measurable_truncRow a m) hf

end Independence

section Laws

variable [Countable 𝓐] [StandardBorelSpace 𝓡] [Nonempty 𝓡]

lemma hasCondDistrib_action' (alg : Algorithm 𝓐 𝓡) (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (n : ℕ) :
    HasCondDistrib (action alg n) (hist alg · n) (alg.policy n) (arrayMeasure ν) := by
  have hU : HasCondDistrib (fun ω ↦ ω.1 n) (fun ω ↦ (hist alg ω n, hist alg ω n))
      (Kernel.const _ volume) (arrayMeasure ν) :=
    ((indepFun_fst_hist alg ν n).symm.comp (measurable_id.prodMk measurable_id)
      measurable_id).hasCondDistrib_const (by fun_prop) (hasLaw_fst_apply_arrayMeasure ν n)
  have h := ((hasCondDistrib_self (X := (hist alg · n)) (by fun_prop)).prod hU).comp_left
    (measurable_algFunction alg n)
  have h_ker : alg.policy n = (Kernel.id ⊗ₖ Kernel.const _ volume).map
      (Function.uncurry (algFunction alg n)) := by
    ext h s hs
    rw [Kernel.map_apply' _ (measurable_algFunction alg n) _ hs,
      Kernel.compProd_apply (measurable_algFunction alg n hs), Kernel.id_apply]
    simp only [Kernel.const_apply]
    rw [lintegral_dirac' _ (measurable_measure_prodMk_left (measurable_algFunction alg n hs)),
      ← algFunction_map alg n h, Measure.map_apply (by fun_prop) hs]
    rfl
  rw [action_eq, h_ker]
  exact h

omit [StandardBorelSpace 𝓡] [Nonempty 𝓡] in
lemma reward_ae_eq_cond (alg : Algorithm 𝓐 𝓡) (ν : Kernel 𝓐 𝓡) (a : 𝓐) (n m : ℕ) :
    reward alg n =ᵐ[(arrayMeasure ν)[|(fun ω ↦ (action alg n ω,
        pullCount (action alg) (action alg n ω) n ω)) ⁻¹' {(a, m)}]]
      (fun ω ↦ ω.2 m a) := by
  rw [reward_eq]
  refine ae_cond_of_forall_mem ((measurableSet_singleton _).preimage (by fun_prop)) fun ω hω ↦ ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hω
  simp only [hω.2]
  simp [hω.1]

/-- The conditional distribution of the reward at time `n`, given the history before time `n`,
the action at time `n`, and the number of times that action has been pulled before time `n`,
is equal to the kernel `ν`. -/
lemma hasCondDistrib_reward_hist_action_pullCount
    (alg : Algorithm 𝓐 𝓡) (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (n : ℕ) :
    HasCondDistrib (reward alg n)
      (fun ω ↦ (hist alg ω n, action alg n ω, pullCount (action alg) (action alg n ω) n ω))
      ((ν.prodMkRight _).prodMkLeft _) (arrayMeasure ν) := by
  refine hasCondDistrib_of_condDistrib_eq (by fun_prop) (by fun_prop) ?_
  refine condDistrib_prod_of_forall_condDistrib_cond (by fun_prop) (by fun_prop) (by fun_prop) _ ?_
  intro (a, m) ham
  have h_eq : ((ν.prodMkRight _).prodMkLeft _).comap (fun ω : (Fin n → 𝓐 × 𝓡) ↦ (ω, a, m))
        (by fun_prop) =
      Kernel.const _ (ν a) := by ext; simp
  rw [h_eq, condDistrib_congr_left (reward_ae_eq_cond alg ν a n m)]
  refine (condDistrib_of_indepFun ?_ (by fun_prop) (by fun_prop)).trans (ae_of_all _ fun ω ↦ ?_)
  · exact (indepFun_snd_hist_cond alg ν a n m).symm
  · simp only [Kernel.const_apply]
    rw [preimage_action_pullCount_eq, cond_of_indepFun, map_snd_apply_arrayMeasure m a]
    · exact (indepFun_snd_apply_pullCount_action alg ν a m n).symm
    · exact Measurable.indicator (by fun_prop) (measurableSet_action_eq_and_pullCount_eq alg a n m)
    · fun_prop
    · simp
    · rwa [preimage_action_pullCount_eq] at ham

/-- The reward at time `n` is conditionally independent of the history before time `n`,
given the action at time `n` and the number of times that action has been pulled before
time `n`. -/
lemma condIndepFun_reward_hist (alg : Algorithm 𝓐 𝓡) (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (n : ℕ) :
    (reward alg n) ⟂ᵢ[(fun ω ↦ (action alg n ω, pullCount (action alg) (action alg n ω) n ω)),
        Measurable.prodMk (by fun_prop) (measurable_pullCount_action alg n);
        arrayMeasure ν]
      (hist alg · n) := by
  have h_cond := hasCondDistrib_reward_hist_action_pullCount alg ν n
  refine condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft (by fun_prop) (by fun_prop) ?_
    h_cond.condDistrib_eq
  exact Measurable.prodMk (by fun_prop) (measurable_pullCount_action alg n)

/-- The conditional distribution of the reward at time `n`, given the history before time `n`
and the action at time `n`, is equal to the kernel `ν`. -/
lemma hasCondDistrib_reward' (alg : Algorithm 𝓐 𝓡) (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (n : ℕ) :
    HasCondDistrib (reward alg n) (fun ω ↦ (hist alg ω n, action alg n ω))
      (ν.prodMkLeft _) (arrayMeasure ν) := by
  have h := (hasCondDistrib_reward_hist_action_pullCount alg ν n).measurableEquiv_comp_right
    MeasurableEquiv.prodAssoc.symm
  obtain ⟨f, hf, hf_eq⟩ := (measurable_pullCount_action_hist alg n).exists_eq_measurable_comp
  have h_eq : (MeasurableEquiv.prodAssoc.symm ∘ fun ω ↦ (hist alg ω n, action alg n ω,
      pullCount (action alg) (action alg n ω) n ω)) =
      fun ω ↦ ((hist alg ω n, action alg n ω), f (hist alg ω n, action alg n ω)) := by
    funext ω
    exact Prod.ext rfl (congrFun hf_eq ω)
  have h_ker : ((ν.prodMkRight ℕ).prodMkLeft (Fin n → 𝓐 × 𝓡)).comap
      MeasurableEquiv.prodAssoc.symm.symm MeasurableEquiv.prodAssoc.symm.symm.measurable =
      (ν.prodMkLeft _).prodMkRight ℕ := by
    ext p : 1
    rfl
  rw [h_eq, h_ker] at h
  exact (hasCondDistrib_prod_right_iff _ _ hf).1 h

lemma hasCondDistrib_action (alg : Algorithm 𝓐 𝓡) (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] (n : ℕ) :
    HasCondDistrib (action alg n) (history (action alg) (reward alg) n) (alg.policy n)
      (arrayMeasure ν) := by
  simpa only [hist_eq_history] using hasCondDistrib_action' alg ν n

lemma hasCondDistrib_reward (alg : Algorithm 𝓐 𝓡) (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν]
    (n : ℕ) :
    HasCondDistrib (reward alg n)
      (fun ω ↦ (history (action alg) (reward alg) n ω, action alg n ω))
      ((stationaryEnv ν).feedback n) (arrayMeasure ν) := by
  simpa only [hist_eq_history, feedback_stationaryEnv] using hasCondDistrib_reward' alg ν n

lemma isAlgEnvSeq_arrayMeasure (alg : Algorithm 𝓐 𝓡) (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] :
    IsAlgEnvSeq (action alg) (reward alg) alg (stationaryEnv ν) (arrayMeasure ν) where
  hasCondDistrib_action := hasCondDistrib_action alg ν
  hasCondDistrib_feedback := hasCondDistrib_reward alg ν

lemma hasLaw_action_zero (alg : Algorithm 𝓐 𝓡) (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] :
    HasLaw (action alg 0) alg.p0 (arrayMeasure ν) :=
  (isAlgEnvSeq_arrayMeasure alg ν).hasLaw_action_zero

lemma hasCondDistrib_reward_zero (alg : Algorithm 𝓐 𝓡) (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] :
    HasCondDistrib (reward alg 0) (action alg 0) ν (arrayMeasure ν) := by
  have h := (isAlgEnvSeq_arrayMeasure alg ν).hasCondDistrib_feedback_zero
  rwa [ν0_stationaryEnv] at h

end Laws

end ArrayModel

end MeasureSpace

end Bandits
