/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Announce

/-!
# The projection theorem for announcing algorithms

An algorithm `alg : Algorithm 𝓞 (𝓩 × 𝓐) 𝓨` that announces a variable in `𝓩` (a memory, a sampled
index, a mixture component) plays against `env.comapAction Prod.snd`, for an
`env : Environment 𝓞 𝓐 𝓨` that ignores the announcement. This file constructs a *behavioral*
algorithm `alg.project : Algorithm 𝓞 𝓐 𝓨` and shows that, against **every** environment, the
observable part of a run of `alg` is a run of `alg.project`.

The projected policy is the conditional law of the action given the observable history. It does not
depend on `env` because the environment's kernels read only observables, so they cancel in the
posterior over the announced variables: this is Kuhn's theorem in this setting.

## Main definitions

* `Algorithm.liftHist alg n : Kernel (Hist 𝓞 𝓐 𝓨 n) (Hist 𝓞 (𝓩 × 𝓐) 𝓨 n)`: the posterior over
  the announced history given the observable history, defined by recursion on `n` from `alg` alone.
* `Algorithm.liftStep alg n : Kernel (Hist 𝓞 𝓐 𝓨 n × 𝓞) (𝓐 × (Hist 𝓞 (𝓩 × 𝓐) 𝓨 n × 𝓩))`: from the
  observable history and the current observation, the joint law of the action and of the pair
  (announced history, announced variable of the current round).
* `Algorithm.project alg : Algorithm 𝓞 𝓐 𝓨`: the behavioral algorithm, whose policy is the
  `𝓐`-marginal of `liftStep`.

## Main statements

* `Algorithm.isAlgEnvSeq_project`: in a run of `alg` against `env.comapAction Prod.snd`, the
  observations, the played actions and the feedbacks form a run of `alg.project` against `env`.
* `Algorithm.map_trajMeasure_project`: the projection theorem,
  `(trajMeasure alg (env.comapAction Prod.snd)).map (Traj.mapAction Prod.snd)
    = trajMeasure alg.project env`, for every environment `env`.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 𝓩 Ω : Type*}
  [MeasurableSpace 𝓞] [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] [MeasurableSpace 𝓩]
  [MeasurableSpace Ω]

section Snoc

/-- Splitting a history of `n + 1` rounds into its first `n` rounds and its last round. -/
noncomputable def histSucc (𝓞 𝓐 𝓨 : Type*) [MeasurableSpace 𝓞] [MeasurableSpace 𝓐]
    [MeasurableSpace 𝓨] (n : ℕ) : Hist 𝓞 𝓐 𝓨 (n + 1) ≃ᵐ Hist 𝓞 𝓐 𝓨 n × Round 𝓞 𝓐 𝓨 :=
  MeasurableEquiv.finSuccProd (Round 𝓞 𝓐 𝓨) n

/-- Insert an announced variable into a round. -/
def Round.announce (z : 𝓩) (r : Round 𝓞 𝓐 𝓨) : Round 𝓞 (𝓩 × 𝓐) 𝓨 :=
  (r.obs, (z, r.action), r.feedback)

omit [MeasurableSpace 𝓞] [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] [MeasurableSpace 𝓩] in
@[simp]
lemma Round.mapAction_announce (z : 𝓩) (r : Round 𝓞 𝓐 𝓨) :
    Round.mapAction Prod.snd (Round.announce z r) = r := rfl

@[fun_prop]
lemma Round.measurable_announce :
    Measurable (fun p : 𝓩 × Round 𝓞 𝓐 𝓨 ↦ Round.announce p.1 p.2) := by
  unfold Round.announce
  fun_prop

omit [MeasurableSpace Ω] in
lemma history_succ_eq (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (n : ℕ) :
    history O A Y (n + 1)
      = (histSucc 𝓞 𝓐 𝓨 n).symm ∘ fun ω ↦ (history O A Y n ω, step O A Y n ω) :=
  history_succ n

end Snoc

namespace Algorithm

variable (alg : Algorithm 𝓞 (𝓩 × 𝓐) 𝓨)

/-- From the observable history, the current observation and a candidate posterior `L` over the
announced history, the joint law of the announced history and of the announced action. -/
noncomputable def liftPair (n : ℕ) (L : Kernel (Hist 𝓞 𝓐 𝓨 n) (Hist 𝓞 (𝓩 × 𝓐) 𝓨 n)) :
    Kernel (Hist 𝓞 𝓐 𝓨 n × 𝓞) (Hist 𝓞 (𝓩 × 𝓐) 𝓨 n × (𝓩 × 𝓐)) :=
  L.prodMkRight 𝓞 ⊗ₖ (alg.policy n).comap (fun p ↦ (p.2, p.1.2)) (by fun_prop)

instance (n : ℕ) (L : Kernel (Hist 𝓞 𝓐 𝓨 n) (Hist 𝓞 (𝓩 × 𝓐) 𝓨 n)) [IsMarkovKernel L] :
    IsMarkovKernel (liftPair alg n L) := by
  unfold liftPair; infer_instance

/-- The joint law of the action and of the pair (announced history, announced variable of the
current round), given the observable history and the current observation. -/
noncomputable def liftStep (n : ℕ) (L : Kernel (Hist 𝓞 𝓐 𝓨 n) (Hist 𝓞 (𝓩 × 𝓐) 𝓨 n)) :
    Kernel (Hist 𝓞 𝓐 𝓨 n × 𝓞) (𝓐 × (Hist 𝓞 (𝓩 × 𝓐) 𝓨 n × 𝓩)) :=
  (liftPair alg n L).map (fun q ↦ (q.2.2, (q.1, q.2.1)))

instance (n : ℕ) (L : Kernel (Hist 𝓞 𝓐 𝓨 n) (Hist 𝓞 (𝓩 × 𝓐) 𝓨 n)) [IsMarkovKernel L] :
    IsMarkovKernel (liftStep alg n L) := by
  unfold liftStep
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

end Algorithm

section Snoc2

/-- The data that the one-step posterior reads off a history of `n + 1` observable rounds: the
first `n` rounds, the observation of the last round and the action of the last round. -/
noncomputable def stepIn (n : ℕ) (x : Hist 𝓞 𝓐 𝓨 (n + 1)) : (Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐 :=
  (((histSucc 𝓞 𝓐 𝓨 n x).1, (histSucc 𝓞 𝓐 𝓨 n x).2.obs), (histSucc 𝓞 𝓐 𝓨 n x).2.action)

/-- Rebuild an announced history of `n + 1` rounds from the observable history of `n + 1` rounds,
the announced history of the first `n` rounds and the announced variable of the last round. -/
noncomputable def stepOut (n : ℕ) (p : Hist 𝓞 𝓐 𝓨 (n + 1) × (Hist 𝓞 (𝓩 × 𝓐) 𝓨 n × 𝓩)) :
    Hist 𝓞 (𝓩 × 𝓐) 𝓨 (n + 1) :=
  (histSucc 𝓞 (𝓩 × 𝓐) 𝓨 n).symm (p.2.1, Round.announce p.2.2 (histSucc 𝓞 𝓐 𝓨 n p.1).2)

@[fun_prop]
lemma measurable_stepIn (n : ℕ) : Measurable (stepIn (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨) n) := by
  have h := (histSucc 𝓞 𝓐 𝓨 n).measurable
  unfold stepIn
  fun_prop

@[fun_prop]
lemma measurable_stepOut (n : ℕ) :
    Measurable (stepOut (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨) (𝓩 := 𝓩) n) := by
  have h := (histSucc 𝓞 𝓐 𝓨 n).measurable
  have h' := (histSucc 𝓞 (𝓩 × 𝓐) 𝓨 n).symm.measurable
  unfold stepOut
  fun_prop

end Snoc2

namespace Algorithm

section Project

variable [StandardBorelSpace 𝓞] [Nonempty 𝓞] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
  [StandardBorelSpace 𝓨] [Nonempty 𝓨] [StandardBorelSpace 𝓩] [Nonempty 𝓩]

/-- Auxiliary recursion for `Algorithm.liftHist`, carrying the proof that the kernel is Markov:
that proof is needed at the next step, to disintegrate. -/
noncomputable def liftHistAux (alg : Algorithm 𝓞 (𝓩 × 𝓐) 𝓨) :
    (n : ℕ) → {L : Kernel (Hist 𝓞 𝓐 𝓨 n) (Hist 𝓞 (𝓩 × 𝓐) 𝓨 n) // IsMarkovKernel L}
  | 0 => ⟨Kernel.deterministic (fun _ ↦ default) measurable_const, inferInstance⟩
  | n + 1 =>
      haveI := (liftHistAux alg n).2
      ⟨(Kernel.id ×ₖ ((liftStep alg n (liftHistAux alg n).1).condKernel.comap (stepIn n)
          (measurable_stepIn n))).map (stepOut n),
        Kernel.IsMarkovKernel.map _ (measurable_stepOut n)⟩

/-- The posterior over the announced history given the observable history, defined by recursion on
the number of rounds from `alg` alone. -/
noncomputable def liftHist (alg : Algorithm 𝓞 (𝓩 × 𝓐) 𝓨) (n : ℕ) :
    Kernel (Hist 𝓞 𝓐 𝓨 n) (Hist 𝓞 (𝓩 × 𝓐) 𝓨 n) :=
  (liftHistAux alg n).1

variable (alg : Algorithm 𝓞 (𝓩 × 𝓐) 𝓨)

instance instIsMarkovKernelLiftHist (n : ℕ) : IsMarkovKernel (liftHist alg n) :=
  (liftHistAux alg n).2

@[simp]
lemma liftHist_zero :
    liftHist alg 0 = Kernel.deterministic (fun _ ↦ default) measurable_const := rfl

lemma liftHist_succ (n : ℕ) :
    liftHist alg (n + 1) = (Kernel.id ×ₖ
      ((liftStep alg n (liftHist alg n)).condKernel.comap (stepIn n) (measurable_stepIn n))).map
      (stepOut n) := rfl

/-- The behavioral algorithm obtained by forgetting the announced variable: its policy is the law of
the action given the observable history and the current observation, under the posterior over the
announced history. -/
noncomputable def project : Algorithm 𝓞 𝓐 𝓨 where
  policy n := (liftStep alg n (liftHist alg n)).fst

@[simp]
lemma policy_project (n : ℕ) :
    (project alg).policy n = (liftStep alg n (liftHist alg n)).fst := rfl

end Project

end Algorithm

section StepEquiv

/-- A history of `n + 1` rounds, seen as the first `n` rounds together with the observation, the
action and the feedback of the last round. -/
noncomputable def stepEquiv (𝓞 𝓐 𝓨 : Type*) [MeasurableSpace 𝓞] [MeasurableSpace 𝓐]
    [MeasurableSpace 𝓨] (n : ℕ) :
    ((Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐) × 𝓨 ≃ᵐ Hist 𝓞 𝓐 𝓨 (n + 1) where
  toFun p := (histSucc 𝓞 𝓐 𝓨 n).symm (p.1.1.1, (p.1.1.2, p.1.2, p.2))
  invFun x := ((((histSucc 𝓞 𝓐 𝓨 n x).1, (histSucc 𝓞 𝓐 𝓨 n x).2.obs),
    (histSucc 𝓞 𝓐 𝓨 n x).2.action), (histSucc 𝓞 𝓐 𝓨 n x).2.feedback)
  left_inv p := by
    simp only [MeasurableEquiv.apply_symm_apply, Round.obs_mk, Round.action_mk, Round.feedback_mk]
  right_inv x := by
    simp only [Round.mk_obs_action_feedback]
    exact (histSucc 𝓞 𝓐 𝓨 n).symm_apply_apply x
  measurable_toFun := by
    have h := (histSucc 𝓞 𝓐 𝓨 n).symm.measurable
    simp only [Equiv.coe_fn_mk]
    fun_prop
  measurable_invFun := by
    have h := (histSucc 𝓞 𝓐 𝓨 n).measurable
    simp only [Equiv.symm_mk, Equiv.coe_fn_mk]
    fun_prop

@[simp]
lemma stepIn_eq_fst_stepEquiv_symm (n : ℕ) (x : Hist 𝓞 𝓐 𝓨 (n + 1)) :
    stepIn n x = ((stepEquiv 𝓞 𝓐 𝓨 n).symm x).1 := rfl

omit [MeasurableSpace Ω] in
lemma stepEquiv_apply_history (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (n : ℕ) :
    (stepEquiv 𝓞 𝓐 𝓨 n) ∘ (fun ω ↦ (((history O A Y n ω, O n ω), A n ω), Y n ω))
      = history O A Y (n + 1) := (history_succ_eq O A Y n).symm

end StepEquiv

section Run

variable [StandardBorelSpace 𝓞] [Nonempty 𝓞] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
  [StandardBorelSpace 𝓨] [Nonempty 𝓨] [StandardBorelSpace 𝓩] [Nonempty 𝓩]
  {alg : Algorithm 𝓞 (𝓩 × 𝓐) 𝓨} {env : Environment 𝓞 𝓐 𝓨}
  {O : ℕ → Ω → 𝓞} {B : ℕ → Ω → 𝓩 × 𝓐} {Y : ℕ → Ω → 𝓨}
  {P : Measure Ω} [IsProbabilityMeasure P]

namespace IsAlgEnvSeq

/-- One step of the projection: given the conditional law of the announced history, the joint law of
the played action and of the pair (announced history, announced variable of the current round),
conditionally on the observable history and the current observation. This is where the
environment's kernels cancel: the observation depends only on the observable history. -/
lemma hasCondDistrib_liftStep (h : IsAlgEnvSeq O B Y alg (env.comapAction Prod.snd) P) (n : ℕ)
    (ih : HasCondDistrib (history O B Y n) (history O (fun n ω ↦ (B n ω).2) Y n)
      (Algorithm.liftHist alg n) P) :
    HasCondDistrib (fun ω ↦ ((B n ω).2, (history O B Y n ω, (B n ω).1)))
      (fun ω ↦ (history O (fun n ω ↦ (B n ω).2) Y n ω, O n ω))
      (Algorithm.liftStep alg n (Algorithm.liftHist alg n)) P := by
  -- the observation of round `n` depends only on the observable history
  have hObs : HasCondDistrib (O n)
      (fun ω ↦ (history O (fun n ω ↦ (B n ω).2) Y n ω, history O B Y n ω))
      ((env.obs n).prodMkRight (Hist 𝓞 (𝓩 × 𝓐) 𝓨 n)) P :=
    HasCondDistrib.comp_right
      (f := fun X : Hist 𝓞 (𝓩 × 𝓐) 𝓨 n ↦ (Hist.mapAction Prod.snd X, X))
      (hf := by fun_prop) (Z := history O B Y n) (h.hasCondDistrib_obs n)
  -- hence the current observation carries no information about the announced history
  have hLift : HasCondDistrib (history O B Y n)
      (fun ω ↦ (history O (fun n ω ↦ (B n ω).2) Y n ω, O n ω))
      ((Algorithm.liftHist alg n).prodMkRight 𝓞) P :=
    HasCondDistrib.prodMk_right_of_comap_fst ih hObs
  -- the announced action, conditioned on the observable data and the announced history
  have hAct : HasCondDistrib (B n)
      (fun ω ↦ ((history O (fun n ω ↦ (B n ω).2) Y n ω, O n ω), history O B Y n ω))
      ((alg.policy n).comap
        (fun p : (Hist 𝓞 𝓐 𝓨 n × 𝓞) × Hist 𝓞 (𝓩 × 𝓐) 𝓨 n ↦ (p.2, p.1.2)) (by fun_prop)) P :=
    HasCondDistrib.comp_right
      (f := fun p : Hist 𝓞 (𝓩 × 𝓐) 𝓨 n × 𝓞 ↦ ((Hist.mapAction Prod.snd p.1, p.2), p.1))
      (hf := by fun_prop) (Z := fun ω ↦ (history O B Y n ω, O n ω))
      (h.hasCondDistrib_action n)
  exact (hLift.prod hAct).comp_left (f := fun q ↦ (q.2.2, (q.1, q.2.1))) (by fun_prop)

/-- **The invariant of the projection theorem.** In a run of an announcing algorithm against an
environment that ignores the announcements, the conditional law of the announced history given the
observable history is `Algorithm.liftHist alg n`, which does not depend on the environment: the
environment's kernels read only observables, so they cancel in the posterior over the announced
variables. -/
lemma hasCondDistrib_liftHist (h : IsAlgEnvSeq O B Y alg (env.comapAction Prod.snd) P) (n : ℕ) :
    HasCondDistrib (history O B Y n) (history O (fun n ω ↦ (B n ω).2) Y n)
      (Algorithm.liftHist alg n) P := by
  induction n with
  | zero =>
      rw [Algorithm.liftHist_zero, history_zero, history_zero]
      exact hasCondDistrib_deterministic _ (by fun_prop) (ae_of_all _ fun _ ↦ rfl)
  | succ n ih =>
      have hO := h.measurable_obs
      have hB := h.measurable_action
      have hY := h.measurable_feedback
      have hStep := h.hasCondDistrib_liftStep n ih
      -- disintegrate along the played action
      rw [← Kernel.disintegrate (Algorithm.liftStep alg n (Algorithm.liftHist alg n))
        (Algorithm.liftStep alg n (Algorithm.liftHist alg n)).condKernel] at hStep
      have hCond := HasCondDistrib.of_compProd hStep
      -- the feedback depends only on the observable data
      have hFb : HasCondDistrib (Y n)
          (fun ω ↦ (((history O (fun n ω ↦ (B n ω).2) Y n ω, O n ω), (B n ω).2),
            (history O B Y n ω, (B n ω).1)))
          ((env.feedback n).prodMkRight (Hist 𝓞 (𝓩 × 𝓐) 𝓨 n × 𝓩)) P :=
        HasCondDistrib.comp_right
          (f := fun p : (Hist 𝓞 (𝓩 × 𝓐) 𝓨 n × 𝓞) × (𝓩 × 𝓐) ↦
            (((Hist.mapAction Prod.snd p.1.1, p.1.2), p.2.2), (p.1.1, p.2.1)))
          (hf := by fun_prop) (Z := fun ω ↦ ((history O B Y n ω, O n ω), B n ω))
          (h.hasCondDistrib_feedback n)
      -- hence the feedback carries no information about the announced variables
      have hCondY := HasCondDistrib.prodMk_right_of_comap_fst hCond hFb
      -- read the conditioning as the observable history of `n + 1` rounds
      have hCondY' := hCondY.measurableEquiv_comp_right (stepEquiv 𝓞 𝓐 𝓨 n)
      rw [stepEquiv_apply_history] at hCondY'
      -- and rebuild the announced history of `n + 1` rounds
      have hfinal := hCondY'.map_prodMk (measurable_stepOut n)
      rw [Algorithm.liftHist_succ]
      convert hfinal using 2 with ω
      · rw [history_succ_eq (O := O) (A := B) (Y := Y)]
        rfl
      · rfl

/-- The conditional law of the played action given the observable history and the current
observation is the policy of the projected algorithm. -/
lemma hasCondDistrib_action_project (h : IsAlgEnvSeq O B Y alg (env.comapAction Prod.snd) P)
    (n : ℕ) :
    HasCondDistrib (fun ω ↦ (B n ω).2)
      (fun ω ↦ (history O (fun n ω ↦ (B n ω).2) Y n ω, O n ω))
      ((Algorithm.project alg).policy n) P :=
  (h.hasCondDistrib_liftStep n (h.hasCondDistrib_liftHist n)).fst

/-- **The projection theorem, run form.** In a run of an announcing algorithm `alg` against
`env.comapAction Prod.snd`, the observations, the played actions and the feedbacks form a run of the
behavioral algorithm `alg.project` against `env`. The announced variables remain random variables of
that run. -/
lemma isAlgEnvSeq_project (h : IsAlgEnvSeq O B Y alg (env.comapAction Prod.snd) P) :
    IsAlgEnvSeq O (fun n ω ↦ (B n ω).2) Y (Algorithm.project alg) env P where
  measurable_obs := h.measurable_obs
  measurable_action n := (h.measurable_action n).snd
  measurable_feedback := h.measurable_feedback
  hasCondDistrib_obs n := h.hasCondDistrib_obs_comapAction n
  hasCondDistrib_action n := h.hasCondDistrib_action_project n
  hasCondDistrib_feedback n := h.hasCondDistrib_feedback_comapAction n

end IsAlgEnvSeq

/-- **The projection theorem.** For standard Borel spaces and every environment `env`, the law of
the observable trajectory of the announcing algorithm `alg` played against
`env.comapAction Prod.snd` is the trajectory law of the behavioral algorithm `alg.project` played
against `env`. In particular the projected algorithm does not depend on `env`, so any statement
about behavioral algorithms that only involves the observable trajectory transfers to announcing
algorithms. -/
theorem Algorithm.map_trajMeasure_project (alg : Algorithm 𝓞 (𝓩 × 𝓐) 𝓨)
    (env : Environment 𝓞 𝓐 𝓨) :
    (trajMeasure alg (env.comapAction Prod.snd)).map (Traj.mapAction Prod.snd)
      = trajMeasure (Algorithm.project alg) env :=
  (IT.isAlgEnvSeq_trajMeasure alg (env.comapAction Prod.snd)).isAlgEnvSeq_project.map_trajectory

/-- If an announcing algorithm does not read its own past announcements, its projection has the
behavioral algorithm of `Algorithm.IgnoresAnnounced` as trajectory law: the two descriptions of the
observable process agree. -/
lemma Algorithm.trajMeasure_project_of_ignoresAnnounced {alg' : Algorithm 𝓞 𝓐 𝓨}
    (h : alg.IgnoresAnnounced alg') (env : Environment 𝓞 𝓐 𝓨) :
    trajMeasure (Algorithm.project alg) env = trajMeasure alg' env := by
  rw [← Algorithm.map_trajMeasure_project alg env]
  exact ((IT.isAlgEnvSeq_trajMeasure alg
    (env.comapAction Prod.snd)).isAlgEnvSeq_of_ignoresAnnounced h).map_trajectory

end Run

end Learning
