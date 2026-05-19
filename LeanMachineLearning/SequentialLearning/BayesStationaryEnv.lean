/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.MeasureTheory.Constructions.BorelSpace.MeasurableArgMax
public import LeanMachineLearning.Online.Bandit.Regret
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
public import LeanMachineLearning.SequentialLearning.StationaryEnv

/-! # Bayesian stationary environments -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Learning

variable {𝓔 𝓐 𝓨 Ω : Type*}
variable [MeasurableSpace 𝓔] [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] [MeasurableSpace Ω]

structure IsBayesAlgEnvSeq
    [StandardBorelSpace 𝓐] [Nonempty 𝓐] [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (Q : Measure 𝓔) (κ : Kernel (𝓔 × 𝓐) 𝓨) (alg : Algorithm 𝓐 𝓨)
    (E : Ω → 𝓔) (A : ℕ → Ω → 𝓐) (R' : ℕ → Ω → 𝓨)
    (P : Measure Ω) [IsFiniteMeasure P] : Prop where
  measurable_E : Measurable E := by fun_prop -- todo rename
  measurable_action n : Measurable (A n) := by fun_prop
  measurable_feedback n : Measurable (R' n) := by fun_prop
  hasLaw_env : HasLaw E Q P
  hasCondDistrib_action_zero : HasCondDistrib (A 0) E (Kernel.const _ alg.p0) P
  hasCondDistrib_feedback_zero : HasCondDistrib (R' 0) (fun ω ↦ (E ω, A 0 ω)) κ P
  hasCondDistrib_action n :
    HasCondDistrib (A (n + 1)) (fun ω ↦ (E ω, IsAlgEnvSeq.hist A R' n ω))
      ((alg.policy n).prodMkLeft _) P
  hasCondDistrib_feedback n :
    HasCondDistrib (R' (n + 1)) (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, E ω, A (n + 1) ω))
      (κ.prodMkLeft _) P

namespace IsBayesAlgEnvSeq

def trajectory (A : ℕ → Ω → 𝓐) (R' : ℕ → Ω → 𝓨) (ω : Ω) : ℕ → 𝓐 × 𝓨 := fun n ↦ (A n ω, R' n ω)

@[fun_prop]
lemma measurable_trajectory {A : ℕ → Ω → 𝓐} {R' : ℕ → Ω → 𝓨} (hA : ∀ n, Measurable (A n))
    (hR : ∀ n, Measurable (R' n)) : Measurable (trajectory A R') := by
  unfold trajectory
  fun_prop

section Real

noncomputable
def actionMean (κ : Kernel (𝓔 × 𝓐) ℝ) (E : Ω → 𝓔) (a : 𝓐) (ω : Ω) : ℝ := (κ (E ω, a))[id]

@[fun_prop]
lemma measurable_actionMean {κ : Kernel (𝓔 × 𝓐) ℝ} {E : Ω → 𝓔} {a : 𝓐} (hE : Measurable E) :
    Measurable (actionMean κ E a) :=
  stronglyMeasurable_id.integral_kernel.measurable.comp (by fun_prop)

@[fun_prop]
lemma measurable_uncurry_actionMean_comp [Countable 𝓐] [MeasurableSingletonClass 𝓐]
    {κ : Kernel (𝓔 × 𝓐) ℝ} {E : Ω → 𝓔} (hE : Measurable E) {f : Ω → 𝓐} (hf : Measurable f) :
    Measurable (fun ω ↦ actionMean κ E (f ω) ω) := by
  change Measurable ((fun aω ↦ actionMean κ E aω.1 aω.2) ∘ fun ω ↦ (f ω, ω))
  apply Measurable.comp _ (by fun_prop)
  exact measurable_from_prod_countable_right (fun _ ↦ measurable_actionMean hE)

lemma integrable_uncurry_actionMean_comp [Countable 𝓐] [MeasurableSingletonClass 𝓐]
    {κ : Kernel (𝓔 × 𝓐) ℝ} {E : Ω → 𝓔} (hE : Measurable E) {f : Ω → 𝓐} (hf : Measurable f)
    {P : Measure Ω} [IsFiniteMeasure P] {l u : ℝ} (hm : ∀ e a, (κ (e, a))[id] ∈ (Set.Icc l u)) :
    Integrable (fun ω ↦ actionMean κ E (f ω) ω) P := by
  refine ⟨(measurable_uncurry_actionMean_comp hE hf).aestronglyMeasurable, ?_⟩
  apply HasFiniteIntegral.of_bounded
  filter_upwards with ω using abs_le_max_abs_abs (hm (E ω) (f ω)).1 (hm (E ω) (f ω)).2

noncomputable
def bestAction [Nonempty 𝓐] [Fintype 𝓐] [Encodable 𝓐] [MeasurableSingletonClass 𝓐]
    (κ : Kernel (𝓔 × 𝓐) ℝ) (E : Ω → 𝓔) (ω : Ω) : 𝓐 :=
  measurableArgmax (fun ω' a ↦ actionMean κ E a ω') ω

@[fun_prop]
lemma measurable_bestAction [Nonempty 𝓐] [Fintype 𝓐] [Encodable 𝓐] [MeasurableSingletonClass 𝓐]
    {κ : Kernel (𝓔 × 𝓐) ℝ} {E : Ω → 𝓔} (hE : Measurable E) : Measurable (bestAction κ E) :=
  measurable_measurableArgmax (by fun_prop)

/-- The gap at time `n`. -/
noncomputable
def gap (κ : Kernel (𝓔 × 𝓐) ℝ) (E : Ω → 𝓔) (A : ℕ → Ω → 𝓐) (n : ℕ) (ω : Ω) : ℝ :=
  Bandits.gap (κ.sectR (E ω)) (A n ω)

omit [MeasurableSpace Ω] in
/-- The gap is non-negative if the means are bounded by `u : ℝ` (even if `𝓐` is not `Finite`). -/
lemma gap_nonneg_of_le {κ : Kernel (𝓔 × 𝓐) ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → 𝓐} {n : ℕ} {ω : Ω} {u : ℝ}
    (h : ∀ e a, (κ (e, a))[id] ≤ u) : 0 ≤ gap κ E A n ω := by
  simp_rw [gap, Bandits.gap, Kernel.sectR_apply]
  linarith [le_ciSup ⟨u, Set.forall_mem_range.2 fun a ↦ (h (E ω) a)⟩ (A n ω)]

omit [MeasurableSpace Ω] in
lemma gap_le_of_mem_Icc [Nonempty 𝓐] {κ : Kernel (𝓔 × 𝓐) ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → 𝓐} {n : ℕ}
    {ω : Ω} {l u : ℝ} (h : ∀ e a, (κ (e, a))[id] ∈ Set.Icc l u) : gap κ E A n ω ≤ u - l := by
  simp_rw [gap, Bandits.gap, Kernel.sectR_apply]
  grind [ciSup_le (fun a ↦ (h (E ω) a).2)]

omit [MeasurableSpace Ω] in
lemma gap_eq_sub [Nonempty 𝓐] [Fintype 𝓐] [Encodable 𝓐] [MeasurableSingletonClass 𝓐]
    {κ : Kernel (𝓔 × 𝓐) ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → 𝓐} {n : ℕ} {ω : Ω} :
    gap κ E A n ω = actionMean κ E (bestAction κ E ω) ω - actionMean κ E (A n ω) ω := by
  rw [gap, Bandits.gap]
  congr
  apply le_antisymm
  · exact ciSup_le (isMaxOn_measurableArgmax (fun ω' a ↦ actionMean κ E a ω') ω)
  · exact Finite.le_ciSup (fun a ↦ actionMean κ E a ω) _

@[fun_prop]
lemma measurable_gap [Countable 𝓐] {κ : Kernel (𝓔 × 𝓐) ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → 𝓐} {n : ℕ}
    (hE : Measurable E) (hA : ∀ t, Measurable (A t)) : Measurable (gap κ E A n) :=
  (Measurable.iSup fun _ ↦ stronglyMeasurable_id.integral_kernel.measurable.comp (by fun_prop)).sub
    (stronglyMeasurable_id.integral_kernel.measurable.comp (by fun_prop))

lemma integrable_gap [Countable 𝓐] [Nonempty 𝓐] {κ : Kernel (𝓔 × 𝓐) ℝ} {E : Ω → 𝓔}
    {A : ℕ → Ω → 𝓐} {n : ℕ} {P : Measure Ω} [IsFiniteMeasure P] (hE : Measurable E)
    (hA : ∀ t, Measurable (A t)) {l u : ℝ} (h : ∀ e a, (κ (e, a))[id] ∈ Set.Icc l u) :
    Integrable (gap κ E A n) P := by
  apply Integrable.of_bound (by fun_prop) (u - l)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (gap_nonneg_of_le (fun e a ↦ (h e a).2))]
  exact gap_le_of_mem_Icc h

noncomputable
def regret (κ : Kernel (𝓔 × 𝓐) ℝ) (E : Ω → 𝓔) (A : ℕ → Ω → 𝓐) (n : ℕ) (ω : Ω) : ℝ :=
  Bandits.regret (κ.sectR (E ω)) A n ω

omit [MeasurableSpace Ω] in
lemma regret_eq_sum_gap {κ : Kernel (𝓔 × 𝓐) ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → 𝓐} {n : ℕ} {ω : Ω} :
    regret κ E A n ω = ∑ s ∈ range n, gap κ E A s ω := by
  simp [regret, Bandits.regret, gap, Bandits.gap]

omit [MeasurableSpace Ω] in
lemma regret_eq_sum_gap' {κ : Kernel (𝓔 × 𝓐) ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → 𝓐} {n : ℕ} :
    regret κ E A n = fun ω ↦ ∑ s ∈ range n, gap κ E A s ω := funext fun _ ↦ regret_eq_sum_gap

@[fun_prop]
lemma measurable_regret [Countable 𝓐] {κ : Kernel (𝓔 × 𝓐) ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → 𝓐} {n : ℕ}
    (hE : Measurable E) (hA : ∀ t, Measurable (A t)) : Measurable (regret κ E A n) := by
  rw [regret_eq_sum_gap']
  fun_prop

lemma integrable_regret [Countable 𝓐] [Nonempty 𝓐] {κ : Kernel (𝓔 × 𝓐) ℝ} {E : Ω → 𝓔}
    {A : ℕ → Ω → 𝓐} {n : ℕ} {P : Measure Ω} [IsFiniteMeasure P] (hE : Measurable E)
    (hA : ∀ t, Measurable (A t)) {l u : ℝ} (h : ∀ e a, (κ (e, a))[id] ∈ Set.Icc l u) :
    Integrable (regret κ E A n) P := by
  rw [regret_eq_sum_gap']
  exact integrable_finset_sum _ (fun _ _ ↦ integrable_gap hE hA h)

end Real

variable [StandardBorelSpace 𝓐] [Nonempty 𝓐] [StandardBorelSpace 𝓨] [Nonempty 𝓨]
variable {Q : Measure 𝓔} {κ : Kernel (𝓔 × 𝓐) 𝓨} {alg : Algorithm 𝓐 𝓨}
variable {E : Ω → 𝓔} {A : ℕ → Ω → 𝓐} {R' : ℕ → Ω → 𝓨}
variable {P : Measure Ω} [IsFiniteMeasure P]

section Laws

lemma hasLaw_action_zero [IsProbabilityMeasure P] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    HasLaw (A 0) alg.p0 P := h.hasCondDistrib_action_zero.hasLaw_of_const

lemma hasCondDistrib_action' (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    HasCondDistrib (A (n + 1)) (IsAlgEnvSeq.hist A R' n) (alg.policy n) P :=
  (h.hasCondDistrib_action n).comp_right' (by fun_prop)

lemma hasCondDistrib_feedback' [IsFiniteKernel κ] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    HasCondDistrib (R' (n + 1)) (fun ω ↦ (E ω, A (n + 1) ω)) κ P :=
  (h.hasCondDistrib_feedback n).comp_right' (by fun_prop)

end Laws

section CondDistribIsAlgEnvSeq

lemma hasLaw_IT_action_zero (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    ∀ᵐ e ∂Q, HasLaw (IT.action 0) alg.p0 (condDistrib (trajectory A R') E P e) := by
  rw [← h.hasLaw_env.map_eq]
  filter_upwards [condDistrib_comp E
      ((measurable_trajectory h.measurable_action h.measurable_feedback).aemeasurable)
      (IT.measurable_action (𝓐 := 𝓐) (𝓨 := 𝓨) 0),
    h.hasCondDistrib_action_zero.condDistrib_eq] with _ hc hcd
  exact ⟨(IT.measurable_action 0).aemeasurable, by
    rw [← Kernel.map_apply _ (IT.measurable_action 0), ← hc,
      show IT.action 0 ∘ trajectory A R' = A 0 from rfl, hcd, Kernel.const_apply]⟩

lemma hasCondDistrib_IT_feedback_zero (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    ∀ᵐ e ∂Q, HasCondDistrib (IT.feedback 0) (IT.action 0) (κ.sectR e)
      (condDistrib (trajectory A R') E P e) := by
  rw [← h.hasLaw_env.map_eq]
  exact h.hasCondDistrib_feedback_zero.hasCondDistrib_sectR
    (IT.measurable_action 0) (IT.measurable_feedback 0)
    (measurable_trajectory h.measurable_action h.measurable_feedback).aemeasurable

lemma hasCondDistrib_IT_action (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    ∀ᵐ e ∂Q, HasCondDistrib (IT.action (n + 1)) (IT.hist n) (alg.policy n)
      (condDistrib (trajectory A R') E P e) := by
  rw [← h.hasLaw_env.map_eq]
  filter_upwards [(h.hasCondDistrib_action n).hasCondDistrib_sectR
    (IT.measurable_hist n) (IT.measurable_action (n + 1))
    (measurable_trajectory h.measurable_action h.measurable_feedback).aemeasurable] with _ he
  rwa [Kernel.sectR_prodMkLeft] at he

lemma hasCondDistrib_IT_feedback [IsFiniteKernel κ] (h : IsBayesAlgEnvSeq Q κ alg E A R' P)
    (n : ℕ) :
    ∀ᵐ e ∂Q, HasCondDistrib (IT.feedback (n + 1)) (fun τ ↦ (IT.hist n τ, IT.action (n + 1) τ))
      ((κ.sectR e).prodMkLeft _) (condDistrib (trajectory A R') E P e) := by
  rw [← h.hasLaw_env.map_eq]
  have hc : HasCondDistrib (R' (n + 1))
      (fun ω ↦ (E ω, IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω))
      (κ.comap (fun (e, _, a) ↦ (e, a)) (by fun_prop)) P :=
    (h.hasCondDistrib_feedback n).comp_right (MeasurableEquiv.prodAssoc.symm.trans
      ((MeasurableEquiv.prodCongr .prodComm (.refl _)).trans .prodAssoc))
  exact hc.hasCondDistrib_sectR ((IT.measurable_hist n).prodMk
    (IT.measurable_action (n + 1))) (IT.measurable_feedback (n + 1))
    (measurable_trajectory h.measurable_action h.measurable_feedback).aemeasurable

lemma hasLaw_IT_hist (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    ∀ᵐ e ∂Q, HasLaw (IT.hist n) (condDistrib (IsAlgEnvSeq.hist A R' n) E P e)
      (condDistrib (trajectory A R') E P e) := by
  rw [← h.hasLaw_env.map_eq, show IsAlgEnvSeq.hist A R' n = IT.hist n ∘ trajectory A R' from rfl]
  filter_upwards [condDistrib_comp E
    (measurable_trajectory h.measurable_action h.measurable_feedback).aemeasurable
    (IT.measurable_hist n)] with _ he
  exact ⟨(IT.measurable_hist n).aemeasurable, by
    rw [← Kernel.map_apply _ (IT.measurable_hist n), he]⟩

lemma ae_IsAlgEnvSeq [IsMarkovKernel κ] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    ∀ᵐ e ∂Q, IsAlgEnvSeq IT.action IT.feedback alg (stationaryEnv (κ.sectR e))
      (condDistrib (trajectory A R') E P e) := by
  filter_upwards [hasLaw_IT_action_zero h, hasCondDistrib_IT_feedback_zero h,
    ae_all_iff.2 (hasCondDistrib_IT_action h), ae_all_iff.2 (hasCondDistrib_IT_feedback h)]
    with _ ha0 hr0 hA hR
  exact ⟨IT.measurable_action, IT.measurable_feedback, ha0, hr0, hA, hR⟩

end CondDistribIsAlgEnvSeq

end IsBayesAlgEnvSeq

section IsAlgEnvSeq

noncomputable
def bayesStationaryEnv (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × 𝓐) 𝓨)
    [IsMarkovKernel κ] : Environment 𝓐 (𝓔 × 𝓨) where
  feedback n :=
    let g : (Iic n → 𝓐 × 𝓔 × 𝓨) × 𝓐 → 𝓔 × 𝓐 := fun (h, a) => ((h ⟨0, by simp⟩).2.1, a)
    (Kernel.deterministic (Prod.fst ∘ g) (by fun_prop)) ×ₖ (κ.comap g (by fun_prop))
  ν0 := (Kernel.const _ Q) ⊗ₖ κ.swapLeft

variable [Nonempty 𝓐] [Nonempty 𝓔] [Nonempty 𝓨]
variable [StandardBorelSpace 𝓐] [StandardBorelSpace 𝓔] [StandardBorelSpace 𝓨]
variable {Q : Measure 𝓔} [IsProbabilityMeasure Q] {κ : Kernel (𝓔 × 𝓐) 𝓨} [IsMarkovKernel κ]
variable {alg : Algorithm 𝓐 𝓨} {A : ℕ → Ω → 𝓐} {R' : ℕ → Ω → 𝓔 × 𝓨}
variable {P : Measure Ω} [IsProbabilityMeasure P]

lemma IsAlgEnvSeq.isBayesAlgEnvSeq
    (h : IsAlgEnvSeq A R' (alg.prod_left 𝓔) (bayesStationaryEnv Q κ) P) :
    IsBayesAlgEnvSeq Q κ alg (fun ω ↦ (R' 0 ω).1) A (fun n ω ↦ (R' n ω).2) P where
  measurable_E := (h.measurable_feedback 0).fst
  measurable_action := h.measurable_action
  measurable_feedback n := (h.measurable_feedback n).snd
  hasLaw_env := by
    apply HasCondDistrib.hasLaw_of_const
    simpa [bayesStationaryEnv] using h.hasCondDistrib_feedback_zero.fst
  hasCondDistrib_action_zero := by
    have hc : HasCondDistrib (fun ω ↦ (R' 0 ω).1) (A 0) (Kernel.const _ Q) P := by
      simpa [bayesStationaryEnv] using h.hasCondDistrib_feedback_zero.fst
    simpa [h.hasLaw_action_zero.map_eq, Algorithm.prod_left] using hc.const_map_of_const
  hasCondDistrib_feedback_zero :=
    h.hasCondDistrib_feedback_zero.of_compProd.comp_right MeasurableEquiv.prodComm
  hasCondDistrib_action n := by
    let f : (Iic n → 𝓐 × 𝓔 × 𝓨) → 𝓔 × (Iic n → 𝓐 × 𝓨) :=
      fun h ↦ ((h ⟨0, by simp⟩).2.1, fun i ↦ ((h i).1, (h i).2.2))
    have hc : HasCondDistrib (A (n + 1)) (IsAlgEnvSeq.hist A R' n)
        (((alg.policy n).comap Prod.snd (by fun_prop)).comap f (by fun_prop)) P :=
      h.hasCondDistrib_action n
    exact hc.comp_right' (f := f)
  hasCondDistrib_feedback n := by
    let f : (Iic n → 𝓐 × 𝓔 × 𝓨) × 𝓐 → (Iic n → 𝓐 × 𝓨) × 𝓔 × 𝓐 :=
      fun p ↦ ((fun i ↦ ((p.1 i).1, (p.1 i).2.2)), (p.1 ⟨0, by simp⟩).2.1, p.2)
    have hc : HasCondDistrib (fun ω ↦ (R' (n + 1) ω).2)
        (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω))
        ((Kernel.prodMkLeft ((Iic n) → 𝓐 × 𝓨) κ).comap f (by fun_prop)) P := by
      simpa [bayesStationaryEnv, Kernel.snd_prod] using (h.hasCondDistrib_feedback n).snd
    exact hc.comp_right' (by fun_prop)

end IsAlgEnvSeq

namespace IT

noncomputable
def bayesTrajMeasure (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × 𝓐) 𝓨)
    [IsMarkovKernel κ] (alg : Algorithm 𝓐 𝓨) : Measure (ℕ → 𝓐 × 𝓔 × 𝓨) :=
  trajMeasure (alg.prod_left 𝓔) (bayesStationaryEnv Q κ)
deriving IsProbabilityMeasure

lemma isBayesAlgEnvSeq_bayesTrajMeasure
    [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    [StandardBorelSpace 𝓔] [Nonempty 𝓔]
    [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × 𝓐) 𝓨) [IsMarkovKernel κ]
    (alg : Algorithm 𝓐 𝓨) :
    IsBayesAlgEnvSeq Q κ alg (fun ω ↦ (ω 0).2.1) action (fun n ω ↦ (ω n).2.2)
       (bayesTrajMeasure Q κ alg) := (isAlgEnvSeq_trajMeasure _ _).isBayesAlgEnvSeq

noncomputable
def bayesTrajMeasurePosterior [StandardBorelSpace 𝓔] [Nonempty 𝓔]
    (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × 𝓐) 𝓨) [IsMarkovKernel κ]
    (alg : Algorithm 𝓐 𝓨) (n : ℕ) : Kernel (Iic n → 𝓐 × 𝓨) 𝓔 :=
  condDistrib (fun ω ↦ (ω 0).2.1) (IsAlgEnvSeq.hist action (fun n ω ↦ (ω n).2.2) n)
    (bayesTrajMeasure Q κ alg)
deriving IsMarkovKernel

end IT

end Learning
