/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Kernel.Composition.MapComap
public import LeanMachineLearning.SequentialLearning.Algorithm

/-!
# Algorithms that depend only on the time and the observation

In general, an algorithm `alg : Algorithm 𝓞 𝓐 𝓨` has a policy
`alg.policy n : Kernel (Hist 𝓞 𝓐 𝓨 n × 𝓞) 𝓐`, which depends on the history before time `n` and on
the observation at time `n`. In some cases, the policy depends only on the time and on the
observation. We say that `alg` is a *Markov algorithm* if there exists a sequence of Markov kernels
`κ : ℕ → Kernel 𝓞 𝓐` such that `alg.policy n = (κ n).prodMkLeft (Hist 𝓞 𝓐 𝓨 n)` for all `n`.

## Main definitions

* `Algorithm.IsMarkov alg`: the policy of `alg` at time `n` depends only on `n` and on the current
  observation, not on the history.
* `Algorithm.policyCondObs alg n`: the kernel representing the conditional distribution of the
  action at time `n` given the observation at time `n` in a Markov algorithm `alg`.
* `Algorithm.markov κ`: the algorithm whose action at time `n` is drawn from the Markov kernel
  `κ n` applied to the observation at time `n`.

## Main statements

* `Algorithm.IsMarkov.hasCondDistrib_action`: in a run of a Markov algorithm, the conditional
  distribution of the action at time `n` given the observation at time `n` is
  `alg.policyCondObs n`.
* `Algorithm.IsMarkov.condIndepFun_action_history`: in a run of a Markov algorithm, the action at
  time `n` is conditionally independent of the history before time `n` given the observation at
  time `n`.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}

/-- The policy of the algorithm at time `n` depends only on `n` and on the current observation,
not on the history. -/
class Algorithm.IsMarkov (alg : Algorithm 𝓞 𝓐 𝓨) : Prop where
  exists_policy_eq_prodMkLeft : ∃ κ : ℕ → Kernel 𝓞 𝓐, (∀ n, IsMarkovKernel (κ n)) ∧
    ∀ n, alg.policy n = (κ n).prodMkLeft (Hist 𝓞 𝓐 𝓨 n)

namespace Algorithm

/-- The kernel representing the conditional distribution of the action at time `n` given the
observation at time `n` in a Markov algorithm. -/
noncomputable
def policyCondObs (alg : Algorithm 𝓞 𝓐 𝓨) [h_markov : alg.IsMarkov] (n : ℕ) : Kernel 𝓞 𝓐 :=
  h_markov.exists_policy_eq_prodMkLeft.choose n

instance (alg : Algorithm 𝓞 𝓐 𝓨) [alg.IsMarkov] (n : ℕ) : IsMarkovKernel (alg.policyCondObs n) :=
  IsMarkov.exists_policy_eq_prodMkLeft.choose_spec.1 n

lemma policy_eq_prodMkLeft_policyCondObs (alg : Algorithm 𝓞 𝓐 𝓨) [alg.IsMarkov] (n : ℕ) :
    alg.policy n = (alg.policyCondObs n).prodMkLeft (Hist 𝓞 𝓐 𝓨 n) :=
  IsMarkov.exists_policy_eq_prodMkLeft.choose_spec.2 n

lemma policy_apply_eq_policyCondObs (alg : Algorithm 𝓞 𝓐 𝓨) [alg.IsMarkov] (n : ℕ)
    (h : Hist 𝓞 𝓐 𝓨 n) (o : 𝓞) :
    alg.policy n (h, o) = alg.policyCondObs n o := by
  rw [policy_eq_prodMkLeft_policyCondObs, Kernel.prodMkLeft_apply]

lemma p0_eq_policyCondObs (alg : Algorithm 𝓞 𝓐 𝓨) [alg.IsMarkov] :
    alg.p0 = alg.policyCondObs 0 := by
  ext o : 1
  rw [p0_apply, policy_apply_eq_policyCondObs]

/-- The kernel `alg.policyCondObs n` is determined by the policy at time `n`. The assumption
`Nonempty 𝓨` ensures that there are histories of every length. -/
lemma policyCondObs_eq_of_policy_eq [Nonempty 𝓨] (alg : Algorithm 𝓞 𝓐 𝓨) [alg.IsMarkov] {n : ℕ}
    {κ : Kernel 𝓞 𝓐} (h : alg.policy n = κ.prodMkLeft (Hist 𝓞 𝓐 𝓨 n)) :
    alg.policyCondObs n = κ := by
  rcases isEmpty_or_nonempty 𝓞 with h𝓞 | h𝓞
  · ext o : 1
    exact h𝓞.elim o
  have : Nonempty 𝓐 := Measure.nonempty_of_neZero (alg.policyCondObs n (Classical.arbitrary 𝓞))
  rw [policy_eq_prodMkLeft_policyCondObs, Kernel.prodMkLeft_inj] at h
  exact h

namespace IsMarkov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨} {P : Measure Ω} [IsFiniteMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {n N : ℕ}

lemma hasCondDistrib_action_history_obs [alg.IsMarkov] (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    HasCondDistrib (A n) (fun ω ↦ (history O A Y n ω, O n ω))
      ((alg.policyCondObs n).prodMkLeft (Hist 𝓞 𝓐 𝓨 n)) P := by
  rw [← alg.policy_eq_prodMkLeft_policyCondObs]
  exact h.hasCondDistrib_action n

lemma hasCondDistrib_action_history_obs_of_isAlgEnvSeqUntil [alg.IsMarkov]
    (h : IsAlgEnvSeqUntil O A Y alg env P N) (hn : n < N) :
    HasCondDistrib (A n) (fun ω ↦ (history O A Y n ω, O n ω))
      ((alg.policyCondObs n).prodMkLeft (Hist 𝓞 𝓐 𝓨 n)) P := by
  rw [← alg.policy_eq_prodMkLeft_policyCondObs]
  exact h.hasCondDistrib_action n hn

/-- The conditional distribution of the action at time `n` given the observation at time `n` is
`alg.policyCondObs n`. -/
lemma hasCondDistrib_action [alg.IsMarkov] (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    HasCondDistrib (A n) (O n) (alg.policyCondObs n) P :=
  (hasCondDistrib_action_history_obs h n).comp_right

/-- The conditional distribution of the action at time `n < N` given the observation at time `n`
is `alg.policyCondObs n`. -/
lemma hasCondDistrib_action_of_isAlgEnvSeqUntil [alg.IsMarkov]
    (h : IsAlgEnvSeqUntil O A Y alg env P N) (hn : n < N) :
    HasCondDistrib (A n) (O n) (alg.policyCondObs n) P :=
  (hasCondDistrib_action_history_obs_of_isAlgEnvSeqUntil h hn).comp_right

/-- The law of the action at time `n` is the law of the observation at time `n` composed with
`alg.policyCondObs n`. -/
lemma hasLaw_action_comp [alg.IsMarkov] (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    HasLaw (A n) (alg.policyCondObs n ∘ₘ (P.map (O n))) P :=
  (hasCondDistrib_action h n).hasLaw_comp

/-- Conditionally on an event determined by the history before time `n` and the observation at
time `n`, on which that observation is equal to `b`, the action at time `n` has law
`alg.policyCondObs n b`. -/
lemma hasLaw_action_cond [alg.IsMarkov] (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ)
    {s : Set (Hist 𝓞 𝓐 𝓨 n × 𝓞)} (hs : MeasurableSet s) {b : 𝓞} (hsb : ∀ u ∈ s, u.2 = b)
    (hP : P ((fun ω ↦ (history O A Y n ω, O n ω)) ⁻¹' s) ≠ 0) :
    HasLaw (A n) (alg.policyCondObs n b) P[|(fun ω ↦ (history O A Y n ω, O n ω)) ⁻¹' s] := by
  refine (hasCondDistrib_action_history_obs h n).hasLaw_cond (h.measurable_action _) hs
    (fun u hu ↦ ?_) hP
  rw [Kernel.prodMkLeft_apply, hsb u hu]

/-- Conditionally on an event determined by the history before time `n` and the observation at
time `n`, on which that observation is constant, the action at time `n` is independent of the
history before time `n` and of the observation at time `n`. -/
lemma indepFun_history_obs_action_cond [alg.IsMarkov] (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ)
    {s : Set (Hist 𝓞 𝓐 𝓨 n × 𝓞)} (hs : MeasurableSet s) {b : 𝓞} (hsb : ∀ u ∈ s, u.2 = b) :
    (fun ω ↦ (history O A Y n ω, O n ω))
      ⟂ᵢ[P[|(fun ω ↦ (history O A Y n ω, O n ω)) ⁻¹' s]] A n := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  refine (hasCondDistrib_action_history_obs h n).indepFun_cond (by fun_prop) hs
    (η := alg.policyCondObs n b) fun u hu ↦ ?_
  rw [Kernel.prodMkLeft_apply, hsb u hu]

variable [StandardBorelSpace 𝓞] [Nonempty 𝓞] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
  [StandardBorelSpace 𝓨] [Nonempty 𝓨]

/-- The action at time `n` is conditionally independent of the history before time `n`, given the
observation at time `n`. -/
lemma condIndepFun_action_history [StandardBorelSpace Ω] [alg.IsMarkov]
    (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    A n ⟂ᵢ[O n, h.measurable_obs n; P] history O A Y n := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  refine condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft (η := alg.policyCondObs n)
    (by fun_prop) (by fun_prop) (by fun_prop) ?_
  exact HasCondDistrib.condDistrib_eq (hasCondDistrib_action_history_obs h n)

/-- The action at time `n` is conditionally independent of the history before time `n` and the
observation at time `n`, given the observation at time `n`. -/
lemma condIndepFun_action_history_obs [StandardBorelSpace Ω] [alg.IsMarkov]
    (h : IsAlgEnvSeq O A Y alg env P) (n : ℕ) :
    A n ⟂ᵢ[O n, h.measurable_obs n; P] (fun ω ↦ (history O A Y n ω, O n ω)) := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  exact (condIndepFun_action_history h n).prod_right (by fun_prop) (by fun_prop) (by fun_prop)

end IsMarkov

section Markov

variable {κ : ℕ → Kernel 𝓞 𝓐} [∀ n, IsMarkovKernel (κ n)]

/-- The algorithm whose action at time `n` is drawn from `κ n` applied to the observation at
time `n`, whatever the history. -/
def markov (κ : ℕ → Kernel 𝓞 𝓐) [∀ n, IsMarkovKernel (κ n)] : Algorithm 𝓞 𝓐 𝓨 where
  policy n := (κ n).prodMkLeft (Hist 𝓞 𝓐 𝓨 n)

@[simp]
lemma policy_markov (n : ℕ) :
    (markov κ : Algorithm 𝓞 𝓐 𝓨).policy n = (κ n).prodMkLeft (Hist 𝓞 𝓐 𝓨 n) := rfl

@[simp]
lemma p0_markov : (markov κ : Algorithm 𝓞 𝓐 𝓨).p0 = κ 0 := by
  ext o : 1
  rw [p0_apply, policy_markov, Kernel.prodMkLeft_apply]

instance : (markov κ : Algorithm 𝓞 𝓐 𝓨).IsMarkov where
  exists_policy_eq_prodMkLeft := ⟨κ, inferInstance, fun _ ↦ rfl⟩

@[simp]
lemma policyCondObs_markov [Nonempty 𝓨] (n : ℕ) :
    (markov κ : Algorithm 𝓞 𝓐 𝓨).policyCondObs n = κ n :=
  policyCondObs_eq_of_policy_eq _ rfl

end Markov

end Algorithm

namespace IsAlgEnvSeq

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {κ : ℕ → Kernel 𝓞 𝓐} [∀ n, IsMarkovKernel (κ n)] {env : Environment 𝓞 𝓐 𝓨}
  {P : Measure Ω} [IsFiniteMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

lemma hasCondDistrib_action_history_obs_markov
    (h : IsAlgEnvSeq O A Y (Algorithm.markov κ) env P) (n : ℕ) :
    HasCondDistrib (A n) (fun ω ↦ (history O A Y n ω, O n ω)) ((κ n).prodMkLeft (Hist 𝓞 𝓐 𝓨 n)) P :=
  h.hasCondDistrib_action n

/-- The conditional distribution of the action at time `n` given the observation at time `n`
is `κ n`. -/
lemma hasCondDistrib_action_markov (h : IsAlgEnvSeq O A Y (Algorithm.markov κ) env P) (n : ℕ) :
    HasCondDistrib (A n) (O n) (κ n) P :=
  (hasCondDistrib_action_history_obs_markov h n).comp_right

/-- The conditional distribution of the action at time `n` given the observation at time `n`
is `κ n`. -/
lemma condDistrib_action_markov [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq O A Y (Algorithm.markov κ) env P) (n : ℕ) :
    condDistrib (A n) (O n) P =ᵐ[P.map (O n)] κ n :=
  (hasCondDistrib_action_markov h n).condDistrib_eq

/-- Conditionally on an event determined by the history before time `n` and the observation at
time `n`, on which that observation is equal to `b`, the action at time `n` has law `κ n b`. -/
lemma hasLaw_action_cond_markov (h : IsAlgEnvSeq O A Y (Algorithm.markov κ) env P) (n : ℕ)
    {s : Set (Hist 𝓞 𝓐 𝓨 n × 𝓞)} (hs : MeasurableSet s) {b : 𝓞} (hsb : ∀ u ∈ s, u.2 = b)
    (hP : P ((fun ω ↦ (history O A Y n ω, O n ω)) ⁻¹' s) ≠ 0) :
    HasLaw (A n) (κ n b) P[|(fun ω ↦ (history O A Y n ω, O n ω)) ⁻¹' s] := by
  refine (hasCondDistrib_action_history_obs_markov h n).hasLaw_cond (h.measurable_action _) hs
    (fun u hu ↦ ?_) hP
  rw [Kernel.prodMkLeft_apply, hsb u hu]

/-- Conditionally on an event determined by the history before time `n` and the observation at
time `n`, on which that observation is constant, the action at time `n` is independent of the
history before time `n` and of the observation at time `n`. -/
lemma indepFun_history_obs_action_cond_markov
    (h : IsAlgEnvSeq O A Y (Algorithm.markov κ) env P) (n : ℕ)
    {s : Set (Hist 𝓞 𝓐 𝓨 n × 𝓞)} (hs : MeasurableSet s) {b : 𝓞} (hsb : ∀ u ∈ s, u.2 = b) :
    (fun ω ↦ (history O A Y n ω, O n ω))
      ⟂ᵢ[P[|(fun ω ↦ (history O A Y n ω, O n ω)) ⁻¹' s]] A n :=
  Algorithm.IsMarkov.indepFun_history_obs_action_cond h n hs hsb

/-- The action at time `n` is conditionally independent of the history before time `n`, given the
observation at time `n`. -/
lemma condIndepFun_action_history_markov [StandardBorelSpace Ω]
    [StandardBorelSpace 𝓞] [Nonempty 𝓞] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (h : IsAlgEnvSeq O A Y (Algorithm.markov κ) env P) (n : ℕ) :
    A n ⟂ᵢ[O n, h.measurable_obs n; P] history O A Y n :=
  Algorithm.IsMarkov.condIndepFun_action_history h n

end IsAlgEnvSeq

end Learning
