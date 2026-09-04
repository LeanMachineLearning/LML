/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Probability.ConditionalProbability
public import LeanMachineLearning.ForMathlib.Probability.HasLaw
public import LeanMachineLearning.Online.Bandit.ArrayProbSpace

/-! # Laws of `stepsUntil` and `rewardByCount`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning
open scoped ENNReal NNReal

namespace Bandits

variable {𝓐 Ω : Type*} {m𝓐 : MeasurableSpace 𝓐} {mΩ : MeasurableSpace Ω} [DecidableEq 𝓐]
  {A : ℕ → Ω → 𝓐} {R : ℕ → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
  {alg : Algorithm 𝓐 ℝ} {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {h_inter : IsAlgEnvSeq A R alg (stationaryEnv ν) P}

local notation "𝔓" => P.prod (streamMeasure ν)

/-- Law of `Y` conditioned on the event `s`.-/
notation "𝓛[" Y " | " s "; " μ "]" => Measure.map Y (μ[|s])
/-- Law of `Y` conditioned on the event that `X` is in `s`. -/
notation "𝓛[" Y " | " X " in " s "; " μ "]" => Measure.map Y (μ[|X ⁻¹' s])
/-- Law of `Y` conditioned on the event that `X` equals `x`. -/
notation "𝓛[" Y " | " X " ← " x "; " μ "]" => Measure.map Y (μ[|X ⁻¹' {x}])

omit [DecidableEq 𝓐] in
lemma condDistrib_reward'' [Countable 𝓐]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (n : ℕ) :
    𝓛[fun ω ↦ R n ω.1 | fun ω ↦ A n ω.1; 𝔓] =ᵐ[(𝔓).map (fun ω ↦ A n ω.1)] ν := by
  have hA := h.measurable_action
  have hR := h.measurable_feedback
  have h_ra' : 𝓛[R n | A n; P] =ᵐ[P.map (A n)] ν := h.condDistrib_feedback_stationaryEnv n
  have h_law : (𝔓).map (fun ω ↦ A n ω.1) = P.map (A n) := by
    change ((𝔓).map (A n ∘ Prod.fst)) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.fst, Measure.fst_prod]
  rw [h_law]
  have h_prod : 𝓛[fun ω ↦ R n ω.1 | fun ω ↦ A n ω.1; 𝔓]
      =ᵐ[P.map (A n)] 𝓛[R n | A n; P] :=
    condDistrib_fst_prod _ (by fun_prop) _
  filter_upwards [h_ra', h_prod] with ω h_eq h_prod
  rw [h_prod, h_eq]

section CondIndep

variable [StandardBorelSpace 𝓐]

omit [DecidableEq 𝓐] in
lemma reward_cond_action [Countable 𝓐]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : 𝓐) (n : ℕ)
    (hμa : (𝔓).map (fun ω ↦ A n ω.1) {a} ≠ 0) :
    𝓛[fun ω ↦ R n ω.1 | fun ω ↦ A n ω.1 ← a; 𝔓] = ν a := by
  have hA := h.measurable_action
  have hR := h.measurable_feedback
  have h_ra : 𝓛[fun ω ↦ R n ω.1 | fun ω ↦ A n ω.1; 𝔓] =ᵐ[(𝔓).map (fun ω ↦ A n ω.1)] ν :=
    condDistrib_reward'' h n
  have h_eq := condDistrib_ae_eq_cond (μ := 𝔓)
    (X := fun ω ↦ A n ω.1) (Y := fun ω ↦ R n ω.1) (by fun_prop) (by fun_prop)
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h_ra h_eq
  specialize h_ra a hμa
  specialize h_eq a hμa
  rw [h_ra] at h_eq
  exact h_eq.symm

variable [Nonempty 𝓐]

lemma condIndepFun_reward_stepsUntil_action' [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : 𝓐) (m n : ℕ) :
    R n ⟂ᵢ[A n, h.measurable_action n; P] {ω | stepsUntil A a m ω = ↑n}.indicator (fun _ ↦ 1) := by
  -- the indicator of `stepsUntil ... = n` is a function of `hist (n-1)` and `action n`.
  -- It thus suffices to use the independence of `reward n` and `hist (n-1)` conditionally
  -- on `action n`.
  have hA := h.measurable_action
  have hR := h.measurable_feedback
  by_cases hn : n = 0
  · have h_indep : R 0 ⟂ᵢ[A 0, hA 0; P] A 0 :=
      condIndepFun_self_right (by fun_prop) (by fun_prop)
    simp only [hn]
    refine h_indep.of_measurable_right (hX := hA 0) ?_
    exact measurable_comap_indicator_stepsUntil_eq_zero a m
  · have h_indep : R n ⟂ᵢ[A n, hA n; P] fun ω ↦ (history A R (n - 1) ω, A n ω) :=
      IsAlgEnvSeq.condIndepFun_feedback_history_action_action' h n (by grind)
    refine h_indep.of_measurable_right (hX := hA n) ?_
    exact measurable_comap_indicator_stepsUntil_eq h a m n

lemma condIndepFun_reward_stepsUntil_action [StandardBorelSpace Ω] [Countable 𝓐]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (a : 𝓐) (m n : ℕ) :
    CondIndepFun (m𝓐.comap (fun ω ↦ A n ω.1)) ((h.measurable_action n).comp measurable_fst).comap_le
      (fun ω ↦ R n ω.1) ({ω | stepsUntil A a m ω.1 = ↑n}.indicator (fun _ ↦ 1)) 𝔓 := by
  have hA := h.measurable_action
  have hR := h.measurable_feedback
  exact condIndepFun_fst_prod (ν := streamMeasure ν)
    (measurable_indicator_stepsUntil_eq h a m n) (by fun_prop) (by fun_prop)
    (condIndepFun_reward_stepsUntil_action' h a m n)

lemma reward_cond_stepsUntil [StandardBorelSpace Ω] [Countable 𝓐]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : 𝓐) (m n : ℕ)
    (hm : m ≠ 0) (hμn : 𝔓 ((fun ω ↦ stepsUntil A a m ω.1) ⁻¹' {↑n}) ≠ 0) :
    𝓛[fun ω ↦ R n ω.1 | fun ω ↦ stepsUntil A a m ω.1 ← ↑n; 𝔓] = ν a := by
  have hA := h.measurable_action
  have hR := h.measurable_feedback
  have hμna :
      𝔓 ((fun ω ↦ stepsUntil A a m ω.1) ⁻¹' {↑n} ∩ (fun ω ↦ A n ω.1) ⁻¹' {a}) ≠ 0 := by
    suffices ((fun ω : Ω × (ℕ → 𝓐 → ℝ) ↦
          stepsUntil A a m ω.1) ⁻¹' {↑n} ∩ (fun ω ↦ A n ω.1) ⁻¹' {a})
        = (fun ω ↦ stepsUntil A a m ω.1) ⁻¹' {↑n} by simpa [this] using hμn
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, and_iff_left_iff_imp]
    exact action_eq_of_stepsUntil_eq_coe hm
  have hμa : (𝔓).map (fun ω ↦ A n ω.1) {a} ≠ 0 := by
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    refine fun h_zero ↦ hμn (measure_mono_null (fun ω ↦ ?_) h_zero)
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact action_eq_of_stepsUntil_eq_coe hm
  calc 𝓛[fun ω ↦ R n ω.1 | fun ω ↦ stepsUntil A a m ω.1 ← (n : ℕ∞); 𝔓]
  _ = (𝔓[|(fun ω ↦ stepsUntil A a m ω.1) ⁻¹' {↑n} ∩ (fun ω ↦ A n ω.1) ⁻¹' {a}]).map
      (fun ω ↦ R n ω.1) := by
    congr with ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, iff_self_and]
    exact action_eq_of_stepsUntil_eq_coe hm
  _ = (𝔓[|(fun ω ↦ A n ω.1) ⁻¹' {a}
      ∩ {ω : Ω × (ℕ → 𝓐 → ℝ) | stepsUntil A a m ω.1 = ↑n}.indicator 1 ⁻¹' {1} ]).map
      (fun ω ↦ R n ω.1) := by
    congr 2 with ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.indicator_apply,
      Set.mem_ofPred_eq, Pi.one_apply, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    rw [and_comm]
  _ = 𝓛[fun ω ↦ R n ω.1 | fun ω ↦ A n ω.1 ← a; 𝔓] := by
    rw [cond_of_condIndepFun (by fun_prop)]
    · exact condIndepFun_reward_stepsUntil_action h a m n
    · refine measurable_one.indicator ?_
      exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
    · fun_prop
    · convert hμna using 2
      rw [Set.inter_comm]
      congr 1 with ω
      simp [Set.indicator_apply]
  _ = ν a := reward_cond_action h a n hμa

/-- The conditional distribution of the reward received at the `m`-th pull of action `a`
given the time at which number of pulls is `m` is the constant kernel with value `ν a`. -/
lemma condDistrib_rewardByCount_stepsUntil [StandardBorelSpace Ω] [Countable 𝓐]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : 𝓐) (m : ℕ) (hm : m ≠ 0) :
    condDistrib (rewardByCount A R a m) (fun ω ↦ stepsUntil A a m ω.1) 𝔓
      =ᵐ[(𝔓).map (fun ω ↦ stepsUntil A a m ω.1)] Kernel.const _ (ν a) := by
  have hA := h.measurable_action
  have hR := h.measurable_feedback
  refine (condDistrib_ae_eq_cond (μ := 𝔓)
    (X := fun ω ↦ stepsUntil A a m ω.1) (by fun_prop) (by fun_prop)).trans ?_
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro n hn
  simp only [Kernel.const_apply]
  cases n with
  | top =>
    rw [Measure.map_congr (g := fun ω ↦ ω.2 m a)]
    swap
    · refine ae_cond_of_forall_mem ((measurableSet_singleton _).preimage (by fun_prop)) ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact fun ω ↦ rewardByCount_of_stepsUntil_eq_top
    rw [cond_of_indepFun _ (by fun_prop) (by fun_prop) (measurableSet_singleton _)]
    · exact (hasLaw_snd_apply_prod_streamMeasure P ν m a).map_eq
    · rwa [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hn
    · exact indepFun_prod (X := fun ω : Ω ↦ stepsUntil A a m ω)
        (Y := fun ω : ℕ → 𝓐 → ℝ ↦ ω m a) (by fun_prop) (by fun_prop)
  | coe n =>
    rw [Measure.map_congr (g := fun ω ↦ R n ω.1)]
    swap
    · refine ae_cond_of_forall_mem ((measurableSet_singleton _).preimage (by fun_prop)) ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact fun ω ↦ rewardByCount_of_stepsUntil_eq_coe
    refine reward_cond_stepsUntil h a m n hm ?_
    rwa [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hn

/-- The reward received at the `m`-th pull of action `a` has law `ν a`. -/
lemma hasLaw_rewardByCount [StandardBorelSpace Ω] [Countable 𝓐]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : 𝓐) (m : ℕ) (hm : m ≠ 0) :
    HasLaw (rewardByCount A R a m) (ν a) 𝔓 where
  aemeasurable :=
    (measurable_rewardByCount h.measurable_action h.measurable_feedback a m).aemeasurable
  map_eq := by
    have hA := h.measurable_action
    have hR := h.measurable_feedback
    have h_condDistrib :
        condDistrib (rewardByCount A R a m) (fun ω ↦ stepsUntil A a m ω.1) 𝔓
        =ᵐ[(𝔓).map (fun ω ↦ stepsUntil A a m ω.1)]
          Kernel.const _ (ν a) := condDistrib_rewardByCount_stepsUntil h a m hm
    calc (𝔓).map (rewardByCount A R a m)
    _ = (condDistrib (rewardByCount A R a m) (fun ω ↦ stepsUntil A a m ω.1) 𝔓)
        ∘ₘ ((𝔓).map (fun ω ↦ stepsUntil A a m ω.1)) := by
      rw [condDistrib_comp_map (by fun_prop) (by fun_prop)]
    _ = (Kernel.const _ (ν a)) ∘ₘ ((𝔓).map (fun ω ↦ stepsUntil A a m ω.1)) :=
      Measure.comp_congr h_condDistrib
    _ = ν a := by
      have : IsProbabilityMeasure ((𝔓).map (fun ω ↦ stepsUntil A a m ω.1)) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      simp

lemma identDistrib_rewardByCount [StandardBorelSpace Ω] [Countable 𝓐]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : 𝓐) (n m : ℕ)
    (hn : n ≠ 0) (hm : m ≠ 0) :
    IdentDistrib (rewardByCount A R a n) (rewardByCount A R a m) 𝔓 𝔓 where
  aemeasurable_fst :=
    (measurable_rewardByCount h.measurable_action h.measurable_feedback a n).aemeasurable
  aemeasurable_snd :=
    (measurable_rewardByCount h.measurable_action h.measurable_feedback a m).aemeasurable
  map_eq := by rw [(hasLaw_rewardByCount h a n hn).map_eq, (hasLaw_rewardByCount h a m hm).map_eq]

lemma identDistrib_rewardByCount_id [StandardBorelSpace Ω] [Countable 𝓐]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : 𝓐) (n : ℕ) (hn : n ≠ 0) :
    IdentDistrib (rewardByCount A R a n) id 𝔓 (ν a) where
  aemeasurable_fst :=
    (measurable_rewardByCount h.measurable_action h.measurable_feedback a n).aemeasurable
  aemeasurable_snd := Measurable.aemeasurable <| by fun_prop
  map_eq := by rw [(hasLaw_rewardByCount h a n hn).map_eq, Measure.map_id]

lemma identDistrib_rewardByCount_eval [StandardBorelSpace Ω] [Countable 𝓐]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : 𝓐) (n m : ℕ) (hn : n ≠ 0) :
    IdentDistrib (rewardByCount A R a n) (fun ω ↦ ω m a) 𝔓 (streamMeasure ν) :=
  (identDistrib_rewardByCount_id h a n hn).trans
    (identDistrib_eval_eval_id_streamMeasure ν m a).symm

end CondIndep

section Independence

/-! ### Independence of the rewards by count

We prove that the family `(rewardByCount A R a (m + 1))_{(a, m)}` is independent, with
`rewardByCount A R a (m + 1)` distributed according to `ν a`.

The proof goes through the time-truncated arrays `rewardByCountUntil A R t`, in which the entries
corresponding to pulls that happen at time `t` or later are replaced by the auxiliary array. Under
the product measure `𝔓`, the law of `rewardByCountUntil A R t` does not depend on `t`: going from
`t` to `t + 1` replaces the entry `(A t, pullCount A (A t) t)`, which was an auxiliary reward with
law `ν (A t)` independent of everything else, by the reward `R t`, which conditionally on the
history and on `A t` also has law `ν (A t)`. For `t = 0` the array is a sub-array of the auxiliary
array, whose law is the product measure. Finally `rewardByCountUntil A R t` converges to
`rewardByCount` entrywise as `t → ∞`, which gives the law of the latter. -/


/-- The law of the array `rewardByCountUntil A R 0`, which is a sub-array of the auxiliary array,
is the product measure `⨂ (a, m), ν a`. -/
lemma hasLaw_rewardByCountUntil_zero (μ : Measure Ω) [IsProbabilityMeasure μ] :
    HasLaw (rewardByCountUntil A R 0) (Measure.infinitePi fun p : 𝓐 × ℕ ↦ ν p.1)
      (μ.prod (streamMeasure ν)) :=
  have h_indep : iIndepFun (fun (p : 𝓐 × ℕ) (ω : Ω × (ℕ → 𝓐 → ℝ)) ↦ ω.2 (p.2 + 1) p.1)
      (μ.prod (streamMeasure ν)) :=
    (iIndepFun_snd_apply_prod_streamMeasure μ ν).precomp (g := fun p : 𝓐 × ℕ ↦ (p.2 + 1, p.1))
      fun p q hpq ↦ Prod.ext (Prod.mk.inj hpq).2 (by have := (Prod.mk.inj hpq).1; omega)
  h_indep.hasLaw_infinitePi (fun p ↦ hasLaw_snd_apply_prod_streamMeasure μ ν _ _)
    (by fun_prop : Measurable fun (ω : Ω × (ℕ → 𝓐 → ℝ)) (p : 𝓐 × ℕ) ↦
      ω.2 (p.2 + 1) p.1).aemeasurable

variable [MeasurableSingletonClass 𝓐]

/-- The array `rewardByCountUntil A R t` with the entry `(b, k)` erased is independent of the
entry `(k + 1, b)` of the auxiliary array. -/
lemma indepFun_update_rewardByCountUntil_eval [Countable 𝓐] (hA : ∀ n, Measurable (A n))
    (hR : ∀ n, Measurable (R n)) (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℕ) (b : 𝓐) (k : ℕ) :
    (fun ω ↦ Function.update (rewardByCountUntil A R t ω) (b, k) 0)
      ⟂ᵢ[μ.prod (streamMeasure ν)] (fun ω ↦ ω.2 (k + 1) b) := by
  refine ((indepFun_snd_apply_prod_streamMeasure_update μ ν (k + 1) b 0).of_measurable_right
    ?_).symm
  have h_eq : (fun ω : Ω × (ℕ → 𝓐 → ℝ) ↦ Function.update (rewardByCountUntil A R t ω) (b, k) 0)
      = (fun ω ↦ Function.update (rewardByCountUntil A R t ω) (b, k) 0)
        ∘ (fun ω ↦ (ω.1, fun i c ↦ if i = k + 1 ∧ c = b then 0 else ω.2 i c)) := by
    ext ⟨x, z⟩ p
    simp only [Function.comp_apply]
    by_cases hp : p = (b, k)
    · rw [hp, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hp, Function.update_of_ne hp]
      refine rewardByCountUntil_congr t p ?_
      split_ifs with hc
      · exact absurd (Prod.ext hc.2 (by have := hc.1; omega)) hp
      · rfl
  rw [h_eq]
  exact measurable_comp_comap _
    (measurable_update_left.comp (measurable_rewardByCountUntil hA hR t))

/-- Conditionally on the event that the action at time `n + 1` is `b` and that `b` was pulled `k`
times before, the reward at time `n + 1` is independent of the history up to time `n` and of the
action at time `n + 1`. -/
lemma indepFun_history_reward_cond (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (n : ℕ) (b : 𝓐) (k : ℕ) :
    (fun x ↦ (history A R n x, A (n + 1) x))
      ⟂ᵢ[P[|{x | A (n + 1) x = b ∧ pullCount A b (n + 1) x = k}]] R (n + 1) := by
  rw [setOf_action_eq_and_pullCount_eq_eq_preimage (R' := R)]
  exact h.indepFun_history_action_feedback_cond_stationaryEnv n
    (measurableSet_snd_eq_and_pullCount'_eq n b k) fun u hu ↦ hu.1

lemma indepFun_action_zero_reward_zero_cond (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (b : 𝓐) (k : ℕ) :
    A 0 ⟂ᵢ[P[|{x | A 0 x = b ∧ pullCount A b 0 x = k}]] R 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · have h_eq : {x | A 0 x = b ∧ pullCount A b 0 x = 0} = A 0 ⁻¹' {b} := by ext; simp
    rw [h_eq]
    exact indepFun_cond_preimage_singleton_left (h.measurable_action 0) b _
  · have h_eq : {x | A 0 x = b ∧ pullCount A b 0 x = k} = ∅ := by ext; simp [hk.symm]
    rw [h_eq]
    simp

/-- Conditionally on the event that the action at time `t` is `b` and that `b` was pulled `k`
times before, the reward at time `t` has law `ν b`. -/
lemma hasLaw_reward_cond (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (t : ℕ) (b : 𝓐) (k : ℕ)
    (hP : P {x | A t x = b ∧ pullCount A b t x = k} ≠ 0) :
    HasLaw (R t) (ν b) (P[|{x | A t x = b ∧ pullCount A b t x = k}]) := by
  cases t with
  | zero =>
    rcases eq_or_ne k 0 with rfl | hk
    · have h_eq : {x | A 0 x = b ∧ pullCount A b 0 x = 0} = A 0 ⁻¹' {b} := by ext; simp
      rw [h_eq] at hP ⊢
      exact h.hasLaw_feedback_zero_cond_stationaryEnv hP
    · refine absurd ?_ hP
      have h_eq : {x | A 0 x = b ∧ pullCount A b 0 x = k} = ∅ := by ext; simp [hk.symm]
      rw [h_eq, measure_empty]
  | succ n =>
    rw [setOf_action_eq_and_pullCount_eq_eq_preimage (R' := R)] at hP ⊢
    exact h.hasLaw_feedback_cond_stationaryEnv n (measurableSet_snd_eq_and_pullCount'_eq n b k)
      (fun u hu ↦ hu.1) hP

lemma hasLaw_reward_cond_prod (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (t : ℕ) (b : 𝓐)
    (k : ℕ) (hP : P {x | A t x = b ∧ pullCount A b t x = k} ≠ 0) :
    HasLaw (fun ω ↦ R t ω.1) (ν b)
      ((P[|{x | A t x = b ∧ pullCount A b t x = k}]).prod (streamMeasure ν)) :=
  (hasLaw_reward_cond h t b k hP).comp (hasLaw_fst_prod _ _)

variable [Countable 𝓐]

/-- Conditionally on the event that the action at time `t` is `b` and that `b` was pulled `k`
times before, the array `rewardByCountUntil A R t` with the entry `(b, k)` erased is independent of
the reward at time `t`. -/
lemma indepFun_update_rewardByCountUntil_reward (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (t : ℕ) (b : 𝓐) (k : ℕ) :
    (fun ω ↦ Function.update (rewardByCountUntil A R t ω) (b, k) 0)
      ⟂ᵢ[(P[|{x | A t x = b ∧ pullCount A b t x = k}]).prod (streamMeasure ν)]
      (fun ω ↦ R t ω.1) := by
  have hA := h.measurable_action
  have hR := h.measurable_feedback
  by_cases hP : P {x | A t x = b ∧ pullCount A b t x = k} = 0
  · rw [cond_eq_zero.2 (Or.inr hP), Measure.zero_prod]
    exact indepFun_zero_measure _ _
  have : IsProbabilityMeasure (P[|{x | A t x = b ∧ pullCount A b t x = k}]) :=
    cond_isProbabilityMeasure hP
  cases t with
  | zero =>
    have h_indep := (indepFun_action_zero_reward_zero_cond h b k).symm.fst_prod
      (ν := streamMeasure ν) (hR 0) (hA 0)
    refine (h_indep.of_measurable_right ?_).symm
    refine Measurable.comp measurable_update_left ?_
    refine measurable_rewardByCountUntil_of 0 (fun i hi ↦ absurd hi (Nat.not_lt_zero i))
      (fun i hi ↦ absurd hi (Nat.not_lt_zero i)) ?_
    exact measurable_comp_comap (fun ω : Ω × (ℕ → 𝓐 → ℝ) ↦ (A 0 ω.1, ω.2)) measurable_snd
  | succ n =>
    have h_indep := (indepFun_history_reward_cond h n b k).symm.fst_prod
      (ν := streamMeasure ν) (hR _) (by fun_prop)
    refine (h_indep.of_measurable_right ?_).symm
    refine Measurable.comp measurable_update_left ?_
    refine measurable_rewardByCountUntil_of (n + 1) (fun i hi ↦ ?_) (fun i hi ↦ ?_) ?_
    · exact measurable_comp_comap
        (fun ω : Ω × (ℕ → 𝓐 → ℝ) ↦ ((history A R n ω.1, A (n + 1) ω.1), ω.2))
        (g := fun v : ((Iic n → 𝓐 × ℝ) × 𝓐) × (ℕ → 𝓐 → ℝ) ↦
          (v.1.1 ⟨i, mem_Iic.2 (Nat.lt_succ_iff.1 hi)⟩).1) (by fun_prop)
    · exact measurable_comp_comap
        (fun ω : Ω × (ℕ → 𝓐 → ℝ) ↦ ((history A R n ω.1, A (n + 1) ω.1), ω.2))
        (g := fun v : ((Iic n → 𝓐 × ℝ) × 𝓐) × (ℕ → 𝓐 → ℝ) ↦
          (v.1.1 ⟨i, mem_Iic.2 (Nat.lt_succ_iff.1 hi)⟩).2) (by fun_prop)
    · exact measurable_comp_comap
        (fun ω : Ω × (ℕ → 𝓐 → ℝ) ↦ ((history A R n ω.1, A (n + 1) ω.1), ω.2))
        (g := fun v : ((Iic n → 𝓐 × ℝ) × 𝓐) × (ℕ → 𝓐 → ℝ) ↦ v.2) measurable_snd

/-- Conditionally on the event that the action at time `t` is `b` and that `b` was pulled `k`
times before, the arrays `rewardByCountUntil A R (t + 1)` and `rewardByCountUntil A R t` have the
same law: they differ only in the entry `(b, k)`, which is `R t` in the first and an auxiliary
reward in the second, and both are independent of the rest of the array with law `ν b`. -/
lemma identDistrib_rewardByCountUntil_add_one_cond (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (t : ℕ) (b : 𝓐) (k : ℕ) :
    IdentDistrib (rewardByCountUntil A R (t + 1)) (rewardByCountUntil A R t)
      ((P[|{x | A t x = b ∧ pullCount A b t x = k}]).prod (streamMeasure ν))
      ((P[|{x | A t x = b ∧ pullCount A b t x = k}]).prod (streamMeasure ν)) := by
  have hA := h.measurable_action
  have hR := h.measurable_feedback
  set E₁ := {x | A t x = b ∧ pullCount A b t x = k} with hE₁
  have hE₁_meas : MeasurableSet E₁ := measurableSet_action_eq_and_pullCount_eq hA t b k
  by_cases hP : P E₁ = 0
  · rw [cond_eq_zero.2 (Or.inr hP), Measure.zero_prod]
    exact ⟨(measurable_rewardByCountUntil hA hR _).aemeasurable,
      (measurable_rewardByCountUntil hA hR _).aemeasurable, by simp⟩
  have : IsProbabilityMeasure (P[|E₁]) := cond_isProbabilityMeasure hP
  set μ' := (P[|E₁]).prod (streamMeasure ν) with hμ'
  have h_ae : ∀ᵐ ω ∂μ', A t ω.1 = b ∧ pullCount A b t ω.1 = k := by
    rw [ae_iff]
    have h_set : {ω : Ω × (ℕ → 𝓐 → ℝ) | ¬ (A t ω.1 = b ∧ pullCount A b t ω.1 = k)}
        = E₁ᶜ ×ˢ Set.univ := by
      ext ω
      simp [hE₁]
    rw [h_set, hμ', Measure.prod_prod, cond_apply hE₁_meas, Set.inter_compl_self, measure_empty,
      mul_zero, zero_mul]
  set W : Ω × (ℕ → 𝓐 → ℝ) → 𝓐 × ℕ → ℝ :=
    fun ω ↦ Function.update (rewardByCountUntil A R t ω) (b, k) 0 with hW
  have hWm : Measurable W := measurable_update_left.comp (measurable_rewardByCountUntil hA hR t)
  have h1 : rewardByCountUntil A R (t + 1)
      =ᵐ[μ'] fun ω ↦ Function.update (W ω) (b, k) (R t ω.1) := by
    filter_upwards [h_ae] with ω hω
    obtain ⟨hb, hk⟩ := hω
    simp only [hW, rewardByCountUntil_add_one, Function.update_idem, hb, hk]
  have h2 : rewardByCountUntil A R t
      =ᵐ[μ'] fun ω ↦ Function.update (W ω) (b, k) (ω.2 (k + 1) b) := by
    filter_upwards [h_ae] with ω hω
    obtain ⟨hb, hk⟩ := hω
    simp only [hW, Function.update_idem]
    rw [← rewardByCountUntil_apply_of_pullCount_le hk.le, Function.update_eq_self]
  -- both `(W, R t)` and `(W, ω.2 (k + 1) b)` have law `(μ'.map W).prod (ν b)`
  have hW : HasLaw W (μ'.map W) μ' := hWm.hasLaw_map μ'
  have h1' : HasLaw (fun ω ↦ Function.update (W ω) (b, k) (R t ω.1))
      (((μ'.map W).prod (ν b)).map
        fun q : (𝓐 × ℕ → ℝ) × ℝ ↦ Function.update q.1 (b, k) q.2) μ' :=
    ((measurable_update' (a := (b, k))).hasLaw_map _).comp
      ((indepFun_update_rewardByCountUntil_reward h t b k).hasLaw_prod hW
        (hasLaw_reward_cond_prod h t b k hP))
  have h2' : HasLaw (fun ω : Ω × (ℕ → 𝓐 → ℝ) ↦ Function.update (W ω) (b, k) (ω.2 (k + 1) b))
      (((μ'.map W).prod (ν b)).map
        fun q : (𝓐 × ℕ → ℝ) × ℝ ↦ Function.update q.1 (b, k) q.2) μ' :=
    ((measurable_update' (a := (b, k))).hasLaw_map _).comp
      ((indepFun_update_rewardByCountUntil_eval hA hR _ t b k).hasLaw_prod hW
        (hasLaw_snd_apply_prod_streamMeasure _ _ _ _))
  exact ((IdentDistrib.of_ae_eq (measurable_rewardByCountUntil hA hR _).aemeasurable h1).trans
    (h1'.identDistrib h2')).trans
    (IdentDistrib.of_ae_eq (measurable_rewardByCountUntil hA hR _).aemeasurable h2).symm

/-- The law of `rewardByCountUntil A R t` under `𝔓` does not depend on `t`. -/
lemma identDistrib_rewardByCountUntil_add_one (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (t : ℕ) :
    IdentDistrib (rewardByCountUntil A R (t + 1)) (rewardByCountUntil A R t) 𝔓 𝔓 := by
  have hA := h.measurable_action
  have hR := h.measurable_feedback
  -- condition on the value of `(A t, pullCount A (A t) t)`
  refine identDistrib_of_forall_identDistrib_cond
    (g := fun ω : Ω × (ℕ → 𝓐 → ℝ) ↦ (A t ω.1, pullCount A (A t ω.1) t ω.1))
    (((hA t).comp measurable_fst).prodMk
      ((measurable_uncurry_pullCount_comp hA (hA t) measurable_const).comp measurable_fst))
    (measurable_rewardByCountUntil hA hR _) (measurable_rewardByCountUntil hA hR _) fun p ↦ ?_
  have h_eq : (fun ω : Ω × (ℕ → 𝓐 → ℝ) ↦ (A t ω.1, pullCount A (A t ω.1) t ω.1)) ⁻¹' {p}
      = {x | A t x = p.1 ∧ pullCount A p.1 t x = p.2} ×ˢ Set.univ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.ext_iff, Set.mem_prod,
      Set.mem_ofPred_eq, Set.mem_univ, and_true]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← h1]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [h1]; exact h2⟩
  rw [h_eq, cond_prod_univ]
  exact identDistrib_rewardByCountUntil_add_one_cond h t p.1 p.2

/-- The law of `rewardByCountUntil A R t` under `𝔓` is `⨂ (a, m), ν a`, for all `t`. -/
lemma hasLaw_rewardByCountUntil (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (t : ℕ) :
    HasLaw (rewardByCountUntil A R t) (Measure.infinitePi fun p : 𝓐 × ℕ ↦ ν p.1) 𝔓 := by
  induction t with
  | zero => exact hasLaw_rewardByCountUntil_zero P
  | succ t ih => exact (identDistrib_rewardByCountUntil_add_one h t).symm.hasLaw ih

/-- The array of rewards by count `(a, m) ↦ rewardByCount A R a (m + 1)` has law
`⨂ (a, m), ν a`: its entries are independent, and the entry `(a, m)` has law `ν a`. -/
lemma hasLaw_rewardByCount_infinitePi (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) :
    HasLaw (fun ω (p : 𝓐 × ℕ) ↦ rewardByCount A R p.1 (p.2 + 1) ω)
      (Measure.infinitePi fun p : 𝓐 × ℕ ↦ ν p.1) 𝔓 := by
  have hY : Measurable fun ω (p : 𝓐 × ℕ) ↦ rewardByCount A R p.1 (p.2 + 1) ω :=
    measurable_pi_lambda _ fun p ↦
      measurable_rewardByCount h.measurable_action h.measurable_feedback p.1 (p.2 + 1)
  -- `rewardByCountUntil A R t` has that law for all `t` and converges entrywise to the array
  exact hasLaw_of_forall_eventually_eq (L := Filter.atTop)
    (measurable_rewardByCountUntil h.measurable_action h.measurable_feedback) hY.aemeasurable
    (hasLaw_rewardByCountUntil h) eventually_rewardByCountUntil_eq

/-- The reward received at the `(m + 1)`-th pull of action `a` has law `ν a`. -/
lemma hasLaw_rewardByCount_add_one (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (a : 𝓐) (m : ℕ) :
    HasLaw (rewardByCount A R a (m + 1)) (ν a) 𝔓 :=
  (hasLaw_eval_infinitePi (fun p : 𝓐 × ℕ ↦ ν p.1) (a, m)).comp (hasLaw_rewardByCount_infinitePi h)

/-- The rewards by count `rewardByCount A R a (m + 1)` are independent over all actions `a` and
all counts `m`. -/
lemma iIndepFun_rewardByCount_add_one (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) :
    iIndepFun (fun (p : 𝓐 × ℕ) ω ↦ rewardByCount A R p.1 (p.2 + 1) ω) 𝔓 :=
  (iIndepFun_iff_hasLaw_Pi_infinitePi
    (X := fun (p : 𝓐 × ℕ) ω ↦ rewardByCount A R p.1 (p.2 + 1) ω) (μ := fun p : 𝓐 × ℕ ↦ ν p.1)
    (fun p ↦ hasLaw_rewardByCount_add_one h p.1 p.2)
    (hasLaw_rewardByCount_infinitePi h).aemeasurable).2 (hasLaw_rewardByCount_infinitePi h)

/-- The rewards by count `rewardByCount A R a m` for `m ≠ 0` are independent over all actions `a`
and all counts `m`. -/
lemma iIndepFun_rewardByCount (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) :
    iIndepFun (fun (p : {p : 𝓐 × ℕ // p.2 ≠ 0}) ω ↦ rewardByCount A R p.1.1 p.1.2 ω) 𝔓 := by
  have h_eq : (fun (p : {p : 𝓐 × ℕ // p.2 ≠ 0}) ω ↦ rewardByCount A R p.1.1 p.1.2 ω)
      = fun p ω ↦ rewardByCount A R p.1.1 (p.1.2 - 1 + 1) ω := by
    ext p ω
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero p.2)]
  rw [h_eq]
  exact (iIndepFun_rewardByCount_add_one h).precomp
    (g := fun p : {p : 𝓐 × ℕ // p.2 ≠ 0} ↦ (p.1.1, p.1.2 - 1)) fun p q hpq ↦ by
      simp only [Prod.mk.injEq] at hpq
      exact Subtype.ext (Prod.ext hpq.1 (by have := p.2; have := q.2; omega))

/-- For each action `a`, the rewards by count `(rewardByCount A R a (m + 1))_m` are independent
(and by `hasLaw_rewardByCount_add_one` identically distributed with law `ν a`). -/
lemma iIndepFun_rewardByCount_add_one_action (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (a : 𝓐) :
    iIndepFun (fun m ω ↦ rewardByCount A R a (m + 1) ω) 𝔓 :=
  (iIndepFun_rewardByCount_add_one h).precomp (g := fun m ↦ (a, m))
    fun _ _ hmn ↦ (Prod.mk.inj hmn).2

/-- Two distinct rewards by count are independent. -/
lemma indepFun_rewardByCount (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {a b : 𝓐} {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hne : (a, m) ≠ (b, n)) :
    rewardByCount A R a m ⟂ᵢ[𝔓] rewardByCount A R b n :=
  (iIndepFun_rewardByCount h).indepFun (i := ⟨(a, m), hm⟩) (j := ⟨(b, n), hn⟩)
    fun h_eq ↦ hne (congrArg Subtype.val h_eq)

end Independence

end Bandits
