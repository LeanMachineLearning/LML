/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.Probability.Kernel.Composition.MapComap
public import LeanMachineLearning.SequentialLearning.Algorithm

/-!
# Oblivious and stationary environments

An oblivious environment is an environment in which the distribution of the next feedback depends
only on the last action (and not on the past history).
If the kernel that gives the distribution of the next feedback given the last action is the same at
every time step, then we say that the environment is stationary.

## Main definitions

We define a `Prop`-valued typeclass `IsObliviousEnv` to express that an environment is oblivious,
and we define two constructors for oblivious environments.

Typeclass and related definitions:
* `IsObliviousEnv env`: the environment `env` is oblivious.
* `feedbackCondAction env n`: the kernel representing the conditional distribution of the feedback
  given the action at time `n` in an oblivious environment `env`.

Constructors for oblivious environments:
* `obliviousEnv ν`: an oblivious environment, in which the distribution of the next feedback depends
  only on the last action, but in a possibly time-dependent manner, and is given by a sequence of
  Markov kernels `ν : ℕ → Kernel 𝓐 𝓨`.
* `stationaryEnv ν`: a stationary environment, in which the distribution of the next feedback
  depends only on the last action (and not on the past history), and is given by a Markov kernel
  `ν : Kernel 𝓐 𝓨`.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Learning

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}

/-- An environment is oblivious if the distribution of the next feedback depends only on
the last action and not on the past history. -/
class IsObliviousEnv (env : Environment 𝓐 𝓨) : Prop where
  exists_eq_prodMkLeft : ∃ ν : ℕ → Kernel 𝓐 𝓨, (∀ n, IsMarkovKernel (ν n)) ∧
    (env.ν0 = ν 0) ∧ (∀ n, env.feedback n = (ν (n + 1)).prodMkLeft _)

/-- The kernel representing the conditional distribution of the feedback given the action
at time `n` in an oblivious environment. -/
noncomputable
def feedbackCondAction (env : Environment 𝓐 𝓨) [h_obl : IsObliviousEnv env] (n : ℕ) : Kernel 𝓐 𝓨 :=
  h_obl.exists_eq_prodMkLeft.choose n

instance (env : Environment 𝓐 𝓨) [IsObliviousEnv env] (n : ℕ) :
    IsMarkovKernel (feedbackCondAction env n) :=
  IsObliviousEnv.exists_eq_prodMkLeft.choose_spec.1 n

lemma ν0_eq_feedbackCondAction (env : Environment 𝓐 𝓨) [IsObliviousEnv env] :
    env.ν0 = feedbackCondAction env 0 :=
  IsObliviousEnv.exists_eq_prodMkLeft.choose_spec.2.1

lemma feedback_eq_feedbackCondAction (env : Environment 𝓐 𝓨) [IsObliviousEnv env] (n : ℕ) :
    env.feedback n = (feedbackCondAction env (n + 1)).prodMkLeft _ :=
  IsObliviousEnv.exists_eq_prodMkLeft.choose_spec.2.2 n

namespace IsObliviousEnv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace 𝓐] [Nonempty 𝓐] [StandardBorelSpace 𝓨] [Nonempty 𝓨]
  {alg : Algorithm 𝓐 𝓨} {env : Environment 𝓐 𝓨} {P : Measure Ω} [IsFiniteMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {n N : ℕ}
  {ν : ℕ → Kernel 𝓐 𝓨} [∀ n, IsMarkovKernel (ν n)]

lemma hasCondDistrib_feedback_hist_action [IsObliviousEnv env]
    (h : IsAlgEnvSeq A Y alg env P) (n : ℕ) :
    HasCondDistrib (Y (n + 1)) (fun ω ↦ (IsAlgEnvSeq.hist A Y n ω, A (n + 1) ω))
      ((feedbackCondAction env (n + 1)).prodMkLeft _) P := by
  have hA := h.measurable_action
  have hR' := h.measurable_feedback
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  have h_eq := (h.hasCondDistrib_feedback n).condDistrib_eq
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)] at h_eq ⊢
  simpa only [feedback_eq_feedbackCondAction] using h_eq

lemma hasCondDistrib_feedback [IsObliviousEnv env] (h : IsAlgEnvSeq A Y alg env P) (n : ℕ) :
    HasCondDistrib (Y n) (A n) (feedbackCondAction env n) P := by
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  cases n with
  | zero => rw [← ν0_eq_feedbackCondAction]; exact h.hasCondDistrib_feedback_zero
  | succ n =>
    refine ⟨by fun_prop, by fun_prop, ?_⟩
    have h_eq := (h.hasCondDistrib_feedback n).condDistrib_eq
    rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)] at h_eq ⊢
    have : P.map (A (n + 1)) =
        (P.map (fun x ↦ (IsAlgEnvSeq.hist A Y n x, A (n + 1) x))).snd := by
      rw [Measure.snd_map_prodMk (by fun_prop)]
    simp only [feedback_eq_feedbackCondAction] at h_eq
    rw [this, ← Measure.snd_prodAssoc_compProd_prodMkLeft, ← h_eq,
      Measure.snd_map_prodMk (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    congr

/-- The feedback at time `n + 1` is conditionally independent of the history up to time `n`
given the action at time `n + 1`. -/
lemma condIndepFun_feedback_hist_action [StandardBorelSpace Ω]
        [IsObliviousEnv env] (h : IsAlgEnvSeq A Y alg env P) (n : ℕ) :
    Y (n + 1) ⟂ᵢ[A (n + 1), h.measurable_action _ ; P] IsAlgEnvSeq.hist A Y n := by
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  refine condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    (η := feedbackCondAction env (n + 1))
    (by fun_prop) (by fun_prop) (by fun_prop) ?_
  refine HasCondDistrib.condDistrib_eq ?_
  rw [← feedback_eq_feedbackCondAction]
  exact h.hasCondDistrib_feedback n

lemma condIndepFun_feedback_hist_action_action [StandardBorelSpace Ω]
    [IsObliviousEnv env] (h : IsAlgEnvSeq A Y alg env P) (n : ℕ) :
    Y (n + 1) ⟂ᵢ[A (n + 1), h.measurable_action (n + 1); P]
      (fun ω ↦ (IsAlgEnvSeq.hist A Y n ω, A (n + 1) ω)) := by
  have h_indep : Y (n + 1) ⟂ᵢ[A (n + 1), h.measurable_action (n + 1); P] IsAlgEnvSeq.hist A Y n :=
    condIndepFun_feedback_hist_action h n
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  exact h_indep.prod_right (by fun_prop) (by fun_prop) (by fun_prop)

lemma condIndepFun_feedback_hist_action_action' [StandardBorelSpace Ω]
        [IsObliviousEnv env] (h : IsAlgEnvSeq A Y alg env P) (n : ℕ) (hn : n ≠ 0) :
    Y n ⟂ᵢ[A n, h.measurable_action n; P] (fun ω ↦ (IsAlgEnvSeq.hist A Y (n - 1) ω, A n ω)) := by
  have := condIndepFun_feedback_hist_action_action h (n - 1)
  grind

end IsObliviousEnv

/-- An oblivious environment, in which the distribution of the next feedback depends only on
the last action, but in a possibly time-dependent manner. -/
@[simps]
-- ANCHOR: obliviousEnv
def obliviousEnv (ν : ℕ → Kernel 𝓐 𝓨) [∀ n, IsMarkovKernel (ν n)] : Environment 𝓐 𝓨 where
  feedback n := (ν (n + 1)).prodMkLeft _
  ν0 := ν 0
-- ANCHOR_END: obliviousEnv

@[simp]
lemma feedback_obliviousEnv (ν : ℕ → Kernel 𝓐 𝓨) [∀ n, IsMarkovKernel (ν n)] (n : ℕ) :
    (obliviousEnv ν).feedback n = (ν (n + 1)).prodMkLeft _ := by simp [obliviousEnv]

@[simp]
lemma ν0_obliviousEnv (ν : ℕ → Kernel 𝓐 𝓨) [∀ n, IsMarkovKernel (ν n)] :
    (obliviousEnv ν).ν0 = ν 0 := by simp [obliviousEnv]

instance (ν : ℕ → Kernel 𝓐 𝓨) [∀ n, IsMarkovKernel (ν n)] :
    IsObliviousEnv (obliviousEnv ν) where
  exists_eq_prodMkLeft := ⟨fun n ↦ ν n, inferInstance,rfl, fun _ ↦ rfl⟩

@[simp]
lemma feedbackCondAction_obliviousEnv (ν : ℕ → Kernel 𝓐 𝓨) [hν : ∀ n, IsMarkovKernel (ν n)]
    (n : ℕ) :
    feedbackCondAction (obliviousEnv ν) n = ν n := by
  rcases isEmpty_or_nonempty 𝓐 with h𝓐 | h𝓐
  · ext a : 1
    exact h𝓐.elim a
  rcases isEmpty_or_nonempty 𝓨 with hR | hR
  · refine absurd (hν 0) ?_
    simp only [Subsingleton.eq_zero ν, Pi.zero_apply]
    exact Kernel.not_isMarkovKernel_zero
  have : Nonempty (Iic n → 𝓐 × 𝓨) := ⟨fun _ ↦ (h𝓐.some, hR.some)⟩
  have h_eq_zero := ν0_eq_feedbackCondAction (obliviousEnv ν)
  have h_eq := feedback_eq_feedbackCondAction (obliviousEnv ν) (n - 1)
  cases n with
  | zero => exact h_eq_zero.symm
  | succ n =>
    simp only [Nat.add_one_sub_one, obliviousEnv_feedback, add_tsub_cancel_right] at h_eq
    rw [← Kernel.prodMkLeft_inj (γ := Iic n → 𝓐 × 𝓨)]
    exact h_eq.symm

/-- A stationary environment, in which the distribution of the next feedback depends only on the
last action. -/
-- ANCHOR: stationaryEnv
def stationaryEnv (ν : Kernel 𝓐 𝓨) [IsMarkovKernel ν] : Environment 𝓐 𝓨 := obliviousEnv fun _ ↦ ν
-- ANCHOR_END: stationaryEnv

@[simp]
lemma feedback_stationaryEnv (ν : Kernel 𝓐 𝓨) [IsMarkovKernel ν] (n : ℕ) :
    (stationaryEnv ν).feedback n = ν.prodMkLeft _ := by simp [stationaryEnv]

@[simp]
lemma ν0_stationaryEnv (ν : Kernel 𝓐 𝓨) [IsMarkovKernel ν] : (stationaryEnv ν).ν0 = ν := by
  simp [stationaryEnv]

instance (ν : Kernel 𝓐 𝓨) [IsMarkovKernel ν] : IsObliviousEnv (stationaryEnv ν) where
  exists_eq_prodMkLeft := ⟨fun _ ↦ ν, inferInstance, rfl, fun _ ↦ rfl⟩

@[simp]
lemma feedbackCondAction_stationaryEnv (ν : Kernel 𝓐 𝓨) [hν : IsMarkovKernel ν] (n : ℕ) :
    feedbackCondAction (stationaryEnv ν) n = ν := feedbackCondAction_obliviousEnv _ _

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace 𝓐] [Nonempty 𝓐] [StandardBorelSpace 𝓨] [Nonempty 𝓨]
  {alg : Algorithm 𝓐 𝓨} {ν : Kernel 𝓐 𝓨} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

namespace IsAlgEnvSeq

/-- The conditional distribution of the feedback at time `n` given the action at time `n` is `ν`. -/
lemma hasCondDistrib_feedback_obliviousEnv {ν : ℕ → Kernel 𝓐 𝓨} [∀ n, IsMarkovKernel (ν n)]
    (h : IsAlgEnvSeq A Y alg (obliviousEnv ν) P) (n : ℕ) :
    HasCondDistrib (Y n) (A n) (ν n) P := by
  simpa using IsObliviousEnv.hasCondDistrib_feedback h n

/-- The conditional distribution of the feedback at time `n` given the action at time `n` is `ν`. -/
lemma hasCondDistrib_feedback_stationaryEnv
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ) :
    HasCondDistrib (Y n) (A n) ν P := by
  simpa using IsObliviousEnv.hasCondDistrib_feedback h n

/-- The conditional distribution of the feedback at time `n` given the action at time `n` is `ν`. -/
lemma condDistrib_feedback_stationaryEnv
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ) :
    condDistrib (Y n) (A n) P =ᵐ[P.map (A n)] ν :=
  (hasCondDistrib_feedback_stationaryEnv h n).condDistrib_eq

-- todo: generalize to IsObliviousEnv
lemma condExp_feedback_obliviousEnv_ae_eq_integral_id {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E]
    {mE : MeasurableSpace E} [BorelSpace E]
    {alg : Algorithm 𝓐 E} {Y : ℕ → Ω → E}
    {ν : ℕ → Kernel 𝓐 E} [∀ n, IsMarkovKernel (ν n)]
    (h : IsAlgEnvSeq A Y alg (obliviousEnv ν) P) (n : ℕ) (h_int : Integrable (Y n) P) :
    P[Y n | m𝓐.comap (A n)] =ᵐ[P] fun ω ↦ (ν n (A n ω))[id] := by
  have h_obl : HasCondDistrib (Y n) (A n) (ν n) P := h.hasCondDistrib_feedback_obliviousEnv n
  have h_ae : ∀ᵐ ω ∂P, 𝓛[Y n | A n; P] (A n ω) = ν n (A n ω) :=
    ae_of_ae_map (h.measurable_action n).aemeasurable h_obl.condDistrib_eq
  have h_ae' : P[Y n | m𝓐.comap (A n)] =ᵐ[P] fun ω ↦ ∫ y, y ∂𝓛[Y n | A n; P] (A n ω) :=
    condExp_ae_eq_integral_condDistrib' (h.measurable_action n) h_int
  filter_upwards [h_ae, h_ae'] with ω hω hω' using by simp [hω', hω]

/-- The feedback at time `n + 1` is conditionally independent of the history up to time `n`
given the action at time `n + 1`. -/
lemma condIndepFun_feedback_hist_action [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ) :
    Y (n + 1) ⟂ᵢ[A (n + 1), h.measurable_action _ ; P] hist A Y n :=
  IsObliviousEnv.condIndepFun_feedback_hist_action h n

lemma condIndepFun_feedback_hist_action_action [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ) :
    Y (n + 1) ⟂ᵢ[A (n + 1), h.measurable_action (n + 1); P]
      (fun ω ↦ (hist A Y n ω, A (n + 1) ω)) :=
  IsObliviousEnv.condIndepFun_feedback_hist_action_action h n

lemma condIndepFun_feedback_hist_action_action' [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A Y alg (stationaryEnv ν) P) (n : ℕ) (hn : n ≠ 0) :
    Y n ⟂ᵢ[A n, h.measurable_action n; P] (fun ω ↦ (hist A Y (n - 1) ω, A n ω)) :=
  IsObliviousEnv.condIndepFun_feedback_hist_action_action' h n hn

end IsAlgEnvSeq

end Learning
