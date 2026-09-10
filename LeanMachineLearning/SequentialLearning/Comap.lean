/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Algorithm

/-!
# Transport of algorithms and environments

## Main definitions

* `Round.map fo fa fy`, `Hist.map fo fa fy`: round-wise transport of a round and a history
  along maps of the observation, the action and the feedback, with the
  special cases `mapObs`, `mapAction` and `mapFeedback` that transport a single component.
* `Algorithm.comap alg F hF`: the algorithm that transforms the pair (past rounds, current
  observation) by the measurable map `F n` at round `n` before applying the policy of `alg`.
* `Algorithm.comapObs alg f`: the algorithm that sees `f o` when the observation is `o`, both in
  the current round and in the past rounds.
* `Algorithm.comapFeedback alg g`: the algorithm that sees `g y` when the feedback of a past round
  is `y`.
* `Environment.comap env F hF f hf`: the environment that reads the summary `F n` of the past
  rounds and reads `f a` when the algorithm plays `a` in the current round.
* `Environment.comapAction env f`: the environment that reads `f a` when the algorithm plays `a`,
  both in the current round and in the past rounds.
* `Algorithm.congr alg e𝓞 e𝓐 e𝓨`, `Environment.congr env e𝓞 e𝓐 e𝓨`: relabelling of the
  observations, the actions and the feedbacks of a player along measurable equivalences.

## Main statements

* `IsAlgEnvSeq.hasCondDistrib_action_comapObs`, `IsAlgEnvSeq.hasCondDistrib_action_comapFeedback`:
  in a run of `alg.comapObs f` (resp. `alg.comapFeedback g`) against any environment, the
  conditional distribution of the action given the transported history and the transported
  observation is `alg.policy n`.
* `IsAlgEnvSeq.hasCondDistrib_obs_comapAction`, `IsAlgEnvSeq.hasCondDistrib_feedback_comapAction`:
  in a run against `env.comapAction f`, the observations and feedbacks have the conditional
  distributions of a run of `env` on the transported actions.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓞' 𝓞'' 𝓐 𝓐' 𝓐'' 𝓨 𝓨' 𝓨'' Ω : Type*}
  {m𝓞 : MeasurableSpace 𝓞} {m𝓞' : MeasurableSpace 𝓞'} {m𝓞'' : MeasurableSpace 𝓞''}
  {m𝓐 : MeasurableSpace 𝓐} {m𝓐' : MeasurableSpace 𝓐'} {m𝓐'' : MeasurableSpace 𝓐''}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓨' : MeasurableSpace 𝓨'} {m𝓨'' : MeasurableSpace 𝓨''}
  {mΩ : MeasurableSpace Ω}
  {fo : 𝓞 → 𝓞'} {fa : 𝓐 → 𝓐'} {fy : 𝓨 → 𝓨'} {go : 𝓞' → 𝓞''} {ga : 𝓐' → 𝓐''} {gy : 𝓨' → 𝓨''}

section Map

/-- Transport a round along maps of the observation, the action and the feedback. -/
def Round.map (fo : 𝓞 → 𝓞') (fa : 𝓐 → 𝓐') (fy : 𝓨 → 𝓨') (r : Round 𝓞 𝓐 𝓨) : Round 𝓞' 𝓐' 𝓨' :=
  (fo r.obs, fa r.action, fy r.feedback)

/-- Transport a history round-wise. -/
def Hist.map (fo : 𝓞 → 𝓞') (fa : 𝓐 → 𝓐') (fy : 𝓨 → 𝓨') {n : ℕ} (h : Hist 𝓞 𝓐 𝓨 n) :
    Hist 𝓞' 𝓐' 𝓨' n :=
  fun i ↦ Round.map fo fa fy (h i)

@[simp] lemma Round.obs_map (r : Round 𝓞 𝓐 𝓨) : (Round.map fo fa fy r).obs = fo r.obs := rfl
@[simp] lemma Round.action_map (r : Round 𝓞 𝓐 𝓨) :
    (Round.map fo fa fy r).action = fa r.action := rfl
@[simp] lemma Round.feedback_map (r : Round 𝓞 𝓐 𝓨) :
    (Round.map fo fa fy r).feedback = fy r.feedback := rfl

@[simp] lemma Hist.map_apply {n : ℕ} (h : Hist 𝓞 𝓐 𝓨 n) (i : Fin n) :
    Hist.map fo fa fy h i = Round.map fo fa fy (h i) := rfl

@[simp] lemma Round.map_id : Round.map (id : 𝓞 → 𝓞) (id : 𝓐 → 𝓐) (id : 𝓨 → 𝓨) = id := rfl

@[simp] lemma Hist.map_id {n : ℕ} :
    Hist.map (id : 𝓞 → 𝓞) (id : 𝓐 → 𝓐) (id : 𝓨 → 𝓨) (n := n) = id := rfl

lemma Round.map_comp (r : Round 𝓞 𝓐 𝓨) :
    Round.map go ga gy (Round.map fo fa fy r) = Round.map (go ∘ fo) (ga ∘ fa) (gy ∘ fy) r := rfl

lemma Hist.map_comp {n : ℕ} (h : Hist 𝓞 𝓐 𝓨 n) :
    Hist.map go ga gy (Hist.map fo fa fy h) = Hist.map (go ∘ fo) (ga ∘ fa) (gy ∘ fy) h := rfl

@[fun_prop]
lemma Round.measurable_map (hfo : Measurable fo) (hfa : Measurable fa) (hfy : Measurable fy) :
    Measurable (Round.map fo fa fy) := by unfold Round.map; fun_prop

@[fun_prop]
lemma Hist.measurable_map (hfo : Measurable fo) (hfa : Measurable fa) (hfy : Measurable fy)
    (n : ℕ) :
    Measurable (Hist.map fo fa fy (n := n)) := by unfold Hist.map; fun_prop

/-- Transport the observations of a round. -/
abbrev Round.mapObs (f : 𝓞 → 𝓞') (r : Round 𝓞 𝓐 𝓨) : Round 𝓞' 𝓐 𝓨 := Round.map f id id r

/-- Transport the observations of a history. -/
abbrev Hist.mapObs (f : 𝓞 → 𝓞') {n : ℕ} (h : Hist 𝓞 𝓐 𝓨 n) : Hist 𝓞' 𝓐 𝓨 n :=
  Hist.map f id id h

/-- Transport the actions of a round. -/
abbrev Round.mapAction (f : 𝓐 → 𝓐') (r : Round 𝓞 𝓐 𝓨) : Round 𝓞 𝓐' 𝓨 := Round.map id f id r

/-- Transport the actions of a history. -/
abbrev Hist.mapAction (f : 𝓐 → 𝓐') {n : ℕ} (h : Hist 𝓞 𝓐 𝓨 n) : Hist 𝓞 𝓐' 𝓨 n :=
  Hist.map id f id h

/-- Transport the feedback of a round. -/
abbrev Round.mapFeedback (f : 𝓨 → 𝓨') (r : Round 𝓞 𝓐 𝓨) : Round 𝓞 𝓐 𝓨' := Round.map id id f r

/-- Transport the feedback of a history. -/
abbrev Hist.mapFeedback (f : 𝓨 → 𝓨') {n : ℕ} (h : Hist 𝓞 𝓐 𝓨 n) : Hist 𝓞 𝓐 𝓨' n :=
  Hist.map id id f h

end Map

section Comap

/-- The algorithm with observations in `𝓞'` and feedbacks in `𝓨'` obtained from
`alg : Algorithm 𝓞 𝓐 𝓨` by transforming the pair (past rounds, current observation) by `F n` at
each round `n` before applying the policy of `alg`.

This is the primitive transport operation on algorithms: `Algorithm.comapObs` and
`Algorithm.comapFeedback` are the special cases in which `F n` is a round-wise map of the
observation and of the feedback. -/
def Algorithm.comap (alg : Algorithm 𝓞 𝓐 𝓨)
    (F : (n : ℕ) → Hist 𝓞' 𝓐 𝓨' n × 𝓞' → Hist 𝓞 𝓐 𝓨 n × 𝓞) (hF : ∀ n, Measurable (F n)) :
    Algorithm 𝓞' 𝓐 𝓨' where
  policy n := (alg.policy n).comap (F n) (hF n)

@[simp]
lemma Algorithm.policy_comap (alg : Algorithm 𝓞 𝓐 𝓨)
    {F : (n : ℕ) → Hist 𝓞' 𝓐 𝓨' n × 𝓞' → Hist 𝓞 𝓐 𝓨 n × 𝓞} (hF : ∀ n, Measurable (F n)) (n : ℕ) :
    (alg.comap F hF).policy n = (alg.policy n).comap (F n) (hF n) := rfl

@[simp]
lemma Algorithm.p0_comap (alg : Algorithm 𝓞 𝓐 𝓨)
    {F : (n : ℕ) → Hist 𝓞' 𝓐 𝓨' n × 𝓞' → Hist 𝓞 𝓐 𝓨 n × 𝓞} (hF : ∀ n, Measurable (F n)) :
    (alg.comap F hF).p0
      = alg.p0.comap (fun o ↦ (F 0 (default, o)).2) (((hF 0).comp measurable_prodMk_left).snd) := by
  ext o : 1
  rw [p0_apply, policy_comap, Kernel.comap_apply, alg.policy_zero, Kernel.comap_apply]

@[simp]
lemma Algorithm.comap_id (alg : Algorithm 𝓞 𝓐 𝓨) :
    alg.comap (fun _ ↦ id) (fun _ ↦ measurable_id) = alg := rfl

lemma Algorithm.comap_comap (alg : Algorithm 𝓞 𝓐 𝓨)
    {F : (n : ℕ) → Hist 𝓞' 𝓐 𝓨' n × 𝓞' → Hist 𝓞 𝓐 𝓨 n × 𝓞} (hF : ∀ n, Measurable (F n))
    {G : (n : ℕ) → Hist 𝓞'' 𝓐 𝓨'' n × 𝓞'' → Hist 𝓞' 𝓐 𝓨' n × 𝓞'} (hG : ∀ n, Measurable (G n)) :
    (alg.comap F hF).comap G hG =
      alg.comap (fun n ↦ F n ∘ G n) fun n ↦ (hF n).comp (hG n) := rfl

section ComapObs

variable {f : 𝓞' → 𝓞}

/-- The algorithm that sees `f o` when the observation is `o`, both in the current round and in the
past rounds. -/
def Algorithm.comapObs (alg : Algorithm 𝓞 𝓐 𝓨) (f : 𝓞' → 𝓞)
    (hf : Measurable f := by fun_prop) : Algorithm 𝓞' 𝓐 𝓨 :=
  alg.comap (fun _ p ↦ (Hist.mapObs f p.1, f p.2)) fun _ ↦ by fun_prop

lemma Algorithm.comapObs_def (alg : Algorithm 𝓞 𝓐 𝓨) (hf : Measurable f) :
    alg.comapObs f hf = alg.comap (fun _ p ↦ (Hist.mapObs f p.1, f p.2)) fun _ ↦ by fun_prop := rfl

@[simp]
lemma Algorithm.policy_comapObs (alg : Algorithm 𝓞 𝓐 𝓨) (hf : Measurable f) (n : ℕ) :
    (alg.comapObs f hf).policy n
      = (alg.policy n).comap (fun p ↦ (Hist.mapObs f p.1, f p.2)) (by fun_prop) := rfl

@[simp]
lemma Algorithm.p0_comapObs (alg : Algorithm 𝓞 𝓐 𝓨) (hf : Measurable f) :
    (alg.comapObs f hf).p0 = alg.p0.comap f hf := by
  ext o : 1
  rw [p0_apply, policy_comapObs, Kernel.comap_apply, alg.policy_zero, Kernel.comap_apply]

@[simp]
lemma Algorithm.comapObs_id (alg : Algorithm 𝓞 𝓐 𝓨) : alg.comapObs id measurable_id = alg := rfl

lemma Algorithm.comapObs_comapObs (alg : Algorithm 𝓞 𝓐 𝓨) (hf : Measurable f)
    {g : 𝓞'' → 𝓞'} (hg : Measurable g) :
    (alg.comapObs f hf).comapObs g hg = alg.comapObs (f ∘ g) (hf.comp hg) := rfl

end ComapObs

section ComapFeedback

variable {g : 𝓨' → 𝓨}

/-- The algorithm that sees `g y` when the feedback of a past round is `y`. -/
def Algorithm.comapFeedback (alg : Algorithm 𝓞 𝓐 𝓨) (g : 𝓨' → 𝓨)
    (hg : Measurable g := by fun_prop) : Algorithm 𝓞 𝓐 𝓨' :=
  alg.comap (fun _ p ↦ (Hist.mapFeedback g p.1, p.2)) fun _ ↦ by fun_prop

lemma Algorithm.comapFeedback_def (alg : Algorithm 𝓞 𝓐 𝓨) (hg : Measurable g) :
    alg.comapFeedback g hg
      = alg.comap (fun _ p ↦ (Hist.mapFeedback g p.1, p.2)) fun _ ↦ by fun_prop := rfl

@[simp]
lemma Algorithm.policy_comapFeedback (alg : Algorithm 𝓞 𝓐 𝓨) (hg : Measurable g) (n : ℕ) :
    (alg.comapFeedback g hg).policy n
      = (alg.policy n).comap (fun p ↦ (Hist.mapFeedback g p.1, p.2)) (by fun_prop) := rfl

@[simp]
lemma Algorithm.p0_comapFeedback (alg : Algorithm 𝓞 𝓐 𝓨) (hg : Measurable g) :
    (alg.comapFeedback g hg).p0 = alg.p0 := by
  ext o : 1
  rw [p0_apply, policy_comapFeedback, Kernel.comap_apply, alg.policy_zero, p0_apply]

@[simp]
lemma Algorithm.comapFeedback_id (alg : Algorithm 𝓞 𝓐 𝓨) :
    alg.comapFeedback id measurable_id = alg := rfl

lemma Algorithm.comapFeedback_comapFeedback (alg : Algorithm 𝓞 𝓐 𝓨)
    {g : 𝓨' → 𝓨} (hg : Measurable g) {g' : 𝓨'' → 𝓨'} (hg' : Measurable g') :
    (alg.comapFeedback g hg).comapFeedback g' hg' = alg.comapFeedback (g ∘ g') (hg.comp hg') := rfl

end ComapFeedback

/-- Transporting the observations and the feedbacks of an algorithm are independent operations. -/
lemma Algorithm.comapObs_comapFeedback_comm (alg : Algorithm 𝓞 𝓐 𝓨)
    {f : 𝓞' → 𝓞} (hf : Measurable f) {g : 𝓨' → 𝓨} (hg : Measurable g) :
    (alg.comapFeedback g hg).comapObs f hf = (alg.comapObs f hf).comapFeedback g hg := rfl

section ComapAction

variable {F : (n : ℕ) → Hist 𝓞 𝓐' 𝓨 n → Hist 𝓞 𝓐 𝓨 n} {f : 𝓐' → 𝓐}

/-- The environment that reads the summary `F n` of the past rounds and reads `f a` when the
algorithm plays `a` in the current round.

This is the primitive transport operation on environments, dual to `Algorithm.comap`:
`Environment.comapAction` is the special case in which `F n` is the round-wise map of the actions.
Only the action can change type, since the observations and the feedbacks are outputs of the
environment; `F n` can nonetheless forget or summarize the past rounds, as an environment that
reads only the last round does. -/
def Environment.comap (env : Environment 𝓞 𝓐 𝓨)
    (F : (n : ℕ) → Hist 𝓞 𝓐' 𝓨 n → Hist 𝓞 𝓐 𝓨 n) (hF : ∀ n, Measurable (F n))
    (f : 𝓐' → 𝓐) (hf : Measurable f) : Environment 𝓞 𝓐' 𝓨 where
  obs n := (env.obs n).comap (F n) (hF n)
  feedback n := (env.feedback n).comap (fun p ↦ ((F n p.1.1, p.1.2), f p.2)) (by fun_prop)

@[simp]
lemma Environment.obs_comap (env : Environment 𝓞 𝓐 𝓨)
    (hF : ∀ n, Measurable (F n)) (hf : Measurable f) (n : ℕ) :
    (env.comap F hF f hf).obs n = (env.obs n).comap (F n) (hF n) := rfl

@[simp]
lemma Environment.feedback_comap (env : Environment 𝓞 𝓐 𝓨) (hF : ∀ n, Measurable (F n))
    (hf : Measurable f) (n : ℕ) :
    (env.comap F hF f hf).feedback n
      = (env.feedback n).comap (fun p ↦ ((F n p.1.1, p.1.2), f p.2)) (by fun_prop) := rfl

@[simp]
lemma Environment.obs0_comap (env : Environment 𝓞 𝓐 𝓨) (hF : ∀ n, Measurable (F n))
    (hf : Measurable f) :
    (env.comap F hF f hf).obs0 = env.obs0 := by
  rw [Environment.obs0_def, obs_comap, Kernel.comap_apply, env.obs_zero]

@[simp]
lemma Environment.ν0_comap (env : Environment 𝓞 𝓐 𝓨) (hF : ∀ n, Measurable (F n))
    (hf : Measurable f) :
    (env.comap F hF f hf).ν0 = env.ν0.comap (fun p ↦ (p.1, f p.2)) (by fun_prop) := by
  ext p : 1
  rw [Environment.ν0_apply, feedback_comap, Kernel.comap_apply, env.feedback_zero,
    Kernel.comap_apply]

@[simp]
lemma Environment.comap_id (env : Environment 𝓞 𝓐 𝓨) :
    env.comap (fun _ ↦ id) (fun _ ↦ measurable_id) id measurable_id = env := rfl

lemma Environment.comap_comp (env : Environment 𝓞 𝓐 𝓨) (hF : ∀ n, Measurable (F n))
    (hf : Measurable f)
    {G : (n : ℕ) → Hist 𝓞 𝓐'' 𝓨 n → Hist 𝓞 𝓐' 𝓨 n} (hG : ∀ n, Measurable (G n))
    {g : 𝓐'' → 𝓐'} (hg : Measurable g) :
    (env.comap F hF f hf).comap G hG g hg
      = env.comap (fun n ↦ F n ∘ G n) (fun n ↦ (hF n).comp (hG n)) (f ∘ g) (hf.comp hg) := rfl

/-- The environment that reads `f a` when the algorithm plays `a`, both in the current round and in
the past rounds. -/
def Environment.comapAction (env : Environment 𝓞 𝓐 𝓨) (f : 𝓐' → 𝓐)
    (hf : Measurable f := by fun_prop) : Environment 𝓞 𝓐' 𝓨 :=
  env.comap (fun _ ↦ Hist.mapAction f) (fun _ ↦ by fun_prop) f hf

lemma Environment.comapAction_def (env : Environment 𝓞 𝓐 𝓨) (f : 𝓐' → 𝓐) (hf : Measurable f) :
    env.comapAction f hf = env.comap (fun _ ↦ Hist.mapAction f) (fun _ ↦ by fun_prop) f hf := rfl

@[simp]
lemma Environment.obs_comapAction (env : Environment 𝓞 𝓐 𝓨) (hf : Measurable f)
    (n : ℕ) :
    (env.comapAction f hf).obs n = (env.obs n).comap (Hist.mapAction f) (by fun_prop) := rfl

@[simp]
lemma Environment.feedback_comapAction (env : Environment 𝓞 𝓐 𝓨) (hf : Measurable f) (n : ℕ) :
    (env.comapAction f hf).feedback n = (env.feedback n).comap
      (fun p ↦ ((Hist.mapAction f p.1.1, p.1.2), f p.2)) (by fun_prop) := rfl

@[simp]
lemma Environment.obs0_comapAction (env : Environment 𝓞 𝓐 𝓨) (hf : Measurable f) :
    (env.comapAction f hf).obs0 = env.obs0 := by
  rw [Environment.obs0_def, obs_comapAction, Kernel.comap_apply, env.obs_zero]

@[simp]
lemma Environment.ν0_comapAction (env : Environment 𝓞 𝓐 𝓨) (hf : Measurable f) :
    (env.comapAction f hf).ν0 = env.ν0.comap (fun p ↦ (p.1, f p.2)) (by fun_prop) := by
  ext p : 1
  rw [Environment.ν0_apply, feedback_comapAction, Kernel.comap_apply, env.feedback_zero,
    Kernel.comap_apply]

@[simp]
lemma Environment.comapAction_id (env : Environment 𝓞 𝓐 𝓨) :
    env.comapAction id measurable_id = env := rfl

lemma Environment.comapAction_comp (env : Environment 𝓞 𝓐 𝓨) (hf : Measurable f)
    (g : 𝓐'' → 𝓐') (hg : Measurable g) :
    (env.comapAction f hf).comapAction g hg = env.comapAction (f ∘ g) (hf.comp hg) := rfl

end ComapAction

end Comap

section Congr

/-- Relabelling of the observations, the actions and the feedbacks of an algorithm along measurable
equivalences. -/
noncomputable def Algorithm.congr (alg : Algorithm 𝓞 𝓐 𝓨) (e𝓞 : 𝓞 ≃ᵐ 𝓞') (e𝓐 : 𝓐 ≃ᵐ 𝓐')
    (e𝓨 : 𝓨 ≃ᵐ 𝓨') : Algorithm 𝓞' 𝓐' 𝓨' where
  policy n := ((alg.policy n).map e𝓐).comap
    (fun p ↦ (Hist.map e𝓞.symm e𝓐.symm e𝓨.symm p.1, e𝓞.symm p.2)) (by fun_prop)
  isMarkovKernel_policy n := by
    have : IsMarkovKernel ((alg.policy n).map e𝓐) := Kernel.IsMarkovKernel.map _ e𝓐.measurable
    infer_instance

@[simp]
lemma Algorithm.policy_congr (alg : Algorithm 𝓞 𝓐 𝓨) (e𝓞 : 𝓞 ≃ᵐ 𝓞') (e𝓐 : 𝓐 ≃ᵐ 𝓐')
    (e𝓨 : 𝓨 ≃ᵐ 𝓨') (n : ℕ) :
    (alg.congr e𝓞 e𝓐 e𝓨).policy n = ((alg.policy n).map e𝓐).comap
      (fun p ↦ (Hist.map e𝓞.symm e𝓐.symm e𝓨.symm p.1, e𝓞.symm p.2)) (by fun_prop) := rfl

@[simp]
lemma Algorithm.p0_congr (alg : Algorithm 𝓞 𝓐 𝓨) (e𝓞 : 𝓞 ≃ᵐ 𝓞') (e𝓐 : 𝓐 ≃ᵐ 𝓐')
    (e𝓨 : 𝓨 ≃ᵐ 𝓨') :
    (alg.congr e𝓞 e𝓐 e𝓨).p0 = (alg.p0.map e𝓐).comap e𝓞.symm e𝓞.symm.measurable := by
  ext o : 1
  rw [p0_apply, policy_congr, Kernel.comap_apply, Kernel.map_apply _ e𝓐.measurable,
    alg.policy_zero, Kernel.comap_apply, Kernel.map_apply _ e𝓐.measurable]

@[simp]
lemma Algorithm.congr_refl (alg : Algorithm 𝓞 𝓐 𝓨) :
    alg.congr (.refl 𝓞) (.refl 𝓐) (.refl 𝓨) = alg := by
  ext n : 2
  simp [MeasurableEquiv.symm_refl, MeasurableEquiv.coe_refl]

lemma Algorithm.congr_congr (alg : Algorithm 𝓞 𝓐 𝓨) (e𝓞 : 𝓞 ≃ᵐ 𝓞') (e𝓐 : 𝓐 ≃ᵐ 𝓐')
    (e𝓨 : 𝓨 ≃ᵐ 𝓨') (f𝓞 : 𝓞' ≃ᵐ 𝓞'') (f𝓐 : 𝓐' ≃ᵐ 𝓐'') (f𝓨 : 𝓨' ≃ᵐ 𝓨'') :
    (alg.congr e𝓞 e𝓐 e𝓨).congr f𝓞 f𝓐 f𝓨
      = alg.congr (e𝓞.trans f𝓞) (e𝓐.trans f𝓐) (e𝓨.trans f𝓨) := by
  ext n : 2
  ext p : 1
  rw [policy_congr, Kernel.comap_apply, Kernel.map_apply _ f𝓐.measurable, policy_congr,
    Kernel.comap_apply, Kernel.map_apply _ e𝓐.measurable,
    Measure.map_map f𝓐.measurable e𝓐.measurable, policy_congr, Kernel.comap_apply,
    Kernel.map_apply _ (e𝓐.trans f𝓐).measurable]
  rfl

@[simp]
lemma Algorithm.congr_symm (alg : Algorithm 𝓞 𝓐 𝓨) (e𝓞 : 𝓞 ≃ᵐ 𝓞') (e𝓐 : 𝓐 ≃ᵐ 𝓐')
    (e𝓨 : 𝓨 ≃ᵐ 𝓨') :
    (alg.congr e𝓞 e𝓐 e𝓨).congr e𝓞.symm e𝓐.symm e𝓨.symm = alg := by
  rw [congr_congr, MeasurableEquiv.self_trans_symm, MeasurableEquiv.self_trans_symm,
    MeasurableEquiv.self_trans_symm, congr_refl]

/-- Relabelling of the observations, the actions and the feedbacks of an environment along
measurable equivalences. See also `Algorithm.congr`. -/
noncomputable def Environment.congr (env : Environment 𝓞 𝓐 𝓨) (e𝓞 : 𝓞 ≃ᵐ 𝓞') (e𝓐 : 𝓐 ≃ᵐ 𝓐')
    (e𝓨 : 𝓨 ≃ᵐ 𝓨') :
    Environment 𝓞' 𝓐' 𝓨' where
  obs n := ((env.obs n).map e𝓞).comap (Hist.map e𝓞.symm e𝓐.symm e𝓨.symm) (by fun_prop)
  feedback n := ((env.feedback n).map e𝓨).comap
    (fun p ↦ ((Hist.map e𝓞.symm e𝓐.symm e𝓨.symm p.1.1, e𝓞.symm p.1.2), e𝓐.symm p.2)) (by fun_prop)
  isMarkovKernel_obs n := by
    have : IsMarkovKernel ((env.obs n).map e𝓞) := Kernel.IsMarkovKernel.map _ e𝓞.measurable
    infer_instance
  isMarkovKernel_feedback n := by
    have : IsMarkovKernel ((env.feedback n).map e𝓨) := Kernel.IsMarkovKernel.map _ e𝓨.measurable
    infer_instance

@[simp]
lemma Environment.obs_congr (env : Environment 𝓞 𝓐 𝓨) (e𝓞 : 𝓞 ≃ᵐ 𝓞') (e𝓐 : 𝓐 ≃ᵐ 𝓐')
    (e𝓨 : 𝓨 ≃ᵐ 𝓨') (n : ℕ) :
    (env.congr e𝓞 e𝓐 e𝓨).obs n
      = ((env.obs n).map e𝓞).comap (Hist.map e𝓞.symm e𝓐.symm e𝓨.symm) (by fun_prop) := rfl

@[simp]
lemma Environment.feedback_congr (env : Environment 𝓞 𝓐 𝓨) (e𝓞 : 𝓞 ≃ᵐ 𝓞') (e𝓐 : 𝓐 ≃ᵐ 𝓐')
    (e𝓨 : 𝓨 ≃ᵐ 𝓨') (n : ℕ) :
    (env.congr e𝓞 e𝓐 e𝓨).feedback n = ((env.feedback n).map e𝓨).comap
      (fun p ↦ ((Hist.map e𝓞.symm e𝓐.symm e𝓨.symm p.1.1, e𝓞.symm p.1.2), e𝓐.symm p.2))
      (by fun_prop) := rfl

@[simp]
lemma Environment.obs0_congr (env : Environment 𝓞 𝓐 𝓨) (e𝓞 : 𝓞 ≃ᵐ 𝓞') (e𝓐 : 𝓐 ≃ᵐ 𝓐')
    (e𝓨 : 𝓨 ≃ᵐ 𝓨') :
    (env.congr e𝓞 e𝓐 e𝓨).obs0 = env.obs0.map e𝓞 := by
  rw [Environment.obs0_def, obs_congr, Kernel.comap_apply, Kernel.map_apply _ e𝓞.measurable,
    env.obs_zero]

@[simp]
lemma Environment.ν0_congr (env : Environment 𝓞 𝓐 𝓨) (e𝓞 : 𝓞 ≃ᵐ 𝓞') (e𝓐 : 𝓐 ≃ᵐ 𝓐')
    (e𝓨 : 𝓨 ≃ᵐ 𝓨') :
    (env.congr e𝓞 e𝓐 e𝓨).ν0
      = (env.ν0.map e𝓨).comap (fun p ↦ (e𝓞.symm p.1, e𝓐.symm p.2)) (by fun_prop) := by
  ext p : 1
  rw [Environment.ν0_apply, feedback_congr, Kernel.comap_apply,
    Kernel.map_apply _ e𝓨.measurable, env.feedback_zero, Kernel.comap_apply,
    Kernel.map_apply _ e𝓨.measurable]

@[simp]
lemma Environment.congr_refl (env : Environment 𝓞 𝓐 𝓨) :
    env.congr (.refl 𝓞) (.refl 𝓐) (.refl 𝓨) = env := by
  ext n : 2
  · simp [MeasurableEquiv.symm_refl, MeasurableEquiv.coe_refl]
  · simp [MeasurableEquiv.symm_refl, MeasurableEquiv.coe_refl]

lemma Environment.congr_congr (env : Environment 𝓞 𝓐 𝓨) (e𝓞 : 𝓞 ≃ᵐ 𝓞') (e𝓐 : 𝓐 ≃ᵐ 𝓐')
    (e𝓨 : 𝓨 ≃ᵐ 𝓨') (f𝓞 : 𝓞' ≃ᵐ 𝓞'') (f𝓐 : 𝓐' ≃ᵐ 𝓐'') (f𝓨 : 𝓨' ≃ᵐ 𝓨'') :
    (env.congr e𝓞 e𝓐 e𝓨).congr f𝓞 f𝓐 f𝓨
      = env.congr (e𝓞.trans f𝓞) (e𝓐.trans f𝓐) (e𝓨.trans f𝓨) := by
  ext n : 2
  · ext p : 1
    rw [obs_congr, Kernel.comap_apply, Kernel.map_apply _ f𝓞.measurable, obs_congr,
      Kernel.comap_apply, Kernel.map_apply _ e𝓞.measurable,
      Measure.map_map f𝓞.measurable e𝓞.measurable, obs_congr, Kernel.comap_apply,
      Kernel.map_apply _ (e𝓞.trans f𝓞).measurable]
    rfl
  · ext p : 1
    rw [feedback_congr, Kernel.comap_apply, Kernel.map_apply _ f𝓨.measurable, feedback_congr,
      Kernel.comap_apply, Kernel.map_apply _ e𝓨.measurable,
      Measure.map_map f𝓨.measurable e𝓨.measurable, feedback_congr, Kernel.comap_apply,
      Kernel.map_apply _ (e𝓨.trans f𝓨).measurable]
    rfl

@[simp]
lemma Environment.congr_symm (env : Environment 𝓞 𝓐 𝓨) (e𝓞 : 𝓞 ≃ᵐ 𝓞') (e𝓐 : 𝓐 ≃ᵐ 𝓐')
    (e𝓨 : 𝓨 ≃ᵐ 𝓨') :
    (env.congr e𝓞 e𝓐 e𝓨).congr e𝓞.symm e𝓐.symm e𝓨.symm = env := by
  rw [congr_congr, MeasurableEquiv.self_trans_symm, MeasurableEquiv.self_trans_symm,
    MeasurableEquiv.self_trans_symm, congr_refl]

end Congr

section Runs

variable {alg : Algorithm 𝓞 𝓐 𝓨} {P : Measure Ω} [IsFiniteMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

namespace IsAlgEnvSeq

section ComapObs

variable {env : Environment 𝓞' 𝓐 𝓨} {f : 𝓞' → 𝓞} {hf : Measurable f} {O : ℕ → Ω → 𝓞'}

/-- The algorithm does not use the part of the observation that it ignores: the conditional
distribution of its action given the transported history and observation is its own policy. -/
lemma hasCondDistrib_action_comapObs (h : IsAlgEnvSeq O A Y (alg.comapObs f hf) env P) (n : ℕ) :
    HasCondDistrib (A n)
      (fun ω ↦ (history (fun n ω ↦ f (O n ω)) A Y n ω, f (O n ω))) (alg.policy n) P :=
  HasCondDistrib.comp_right (f := fun p : Hist 𝓞' 𝓐 𝓨 n × 𝓞' ↦ (Hist.mapObs f p.1, f p.2))
    (hf := by fun_prop) (h.hasCondDistrib_action n)

end ComapObs

section ComapFeedback

variable {env : Environment 𝓞 𝓐 𝓨'} {g : 𝓨' → 𝓨} {hg : Measurable g} {O : ℕ → Ω → 𝓞}
  {Y' : ℕ → Ω → 𝓨'}

/-- The algorithm does not use the part of the past feedbacks that it ignores: the conditional
distribution of its action given the transported history and the observation is its own policy. -/
lemma hasCondDistrib_action_comapFeedback
    (h : IsAlgEnvSeq O A Y' (alg.comapFeedback g hg) env P) (n : ℕ) :
    HasCondDistrib (A n)
      (fun ω ↦ (history O A (fun n ω ↦ g (Y' n ω)) n ω, O n ω)) (alg.policy n) P :=
  HasCondDistrib.comp_right (f := fun p : Hist 𝓞 𝓐 𝓨' n × 𝓞 ↦ (Hist.mapFeedback g p.1, p.2))
    (hf := by fun_prop) (h.hasCondDistrib_action n)

end ComapFeedback

section ComapAction

variable {env : Environment 𝓞 𝓐 𝓨} {f : 𝓐' → 𝓐} {hf : Measurable f} {O : ℕ → Ω → 𝓞}
  {A' : ℕ → Ω → 𝓐'}

/-- The environment does not use the part of the action that it ignores: the conditional
distribution of the observation given the transported history is its own observation kernel. -/
lemma hasCondDistrib_obs_comapAction {alg : Algorithm 𝓞 𝓐' 𝓨}
    (h : IsAlgEnvSeq O A' Y alg (env.comapAction f hf) P) (n : ℕ) :
    HasCondDistrib (O n) (history O (fun n ω ↦ f (A' n ω)) Y n) (env.obs n) P :=
  HasCondDistrib.comp_right (f := Hist.mapAction (𝓞 := 𝓞) (𝓨 := 𝓨) f (n := n))
    (hf := by fun_prop) (h.hasCondDistrib_obs n)

/-- The environment does not use the part of the action that it ignores: the conditional
distribution of the feedback given the transported history, the observation and the transported
action is its own feedback kernel. -/
lemma hasCondDistrib_feedback_comapAction {alg : Algorithm 𝓞 𝓐' 𝓨}
    (h : IsAlgEnvSeq O A' Y alg (env.comapAction f hf) P) (n : ℕ) :
    HasCondDistrib (Y n)
      (fun ω ↦ ((history O (fun n ω ↦ f (A' n ω)) Y n ω, O n ω), f (A' n ω))) (env.feedback n) P :=
  HasCondDistrib.comp_right
    (f := fun p : (Hist 𝓞 𝓐' 𝓨 n × 𝓞) × 𝓐' ↦ ((Hist.mapAction f p.1.1, p.1.2), f p.2))
    (hf := by fun_prop) (h.hasCondDistrib_feedback n)

end ComapAction

end IsAlgEnvSeq

end Runs

end Learning
