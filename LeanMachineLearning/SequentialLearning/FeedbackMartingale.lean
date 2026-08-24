/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.ActionIndicator
public import LeanMachineLearning.SequentialLearning.StationaryEnv

/-!
# TODO
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω β 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β}
  {m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace 𝓨] [Nonempty 𝓨]
  {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → β} {Y : Ω → 𝓨}
  {κ : Kernel β 𝓨} [IsFiniteKernel κ]

lemma HasCondDistrib.condExp_comp_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (h : HasCondDistrib Y X κ P) (hX : Measurable X)
    {g : 𝓨 → F} (hg : StronglyMeasurable g) (hint : Integrable (fun ω ↦ g (Y ω)) P) :
    P[fun ω ↦ g (Y ω) | mβ.comap X] =ᵐ[P] fun ω ↦ ∫ y, g y ∂(κ (X ω)) := by
  refine (condExp_ae_eq_integral_condDistrib hX h.aemeasurable_snd hg hint).trans ?_
  filter_upwards [ae_of_ae_map hX.aemeasurable h.condDistrib_eq] with ω hω
  rw [hω]

end ProbabilityTheory

namespace Learning

variable {Ω 𝓐 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  [NormedAddCommGroup 𝓨] [NormedSpace ℝ 𝓨]
  {ν : ℕ → Kernel 𝓐 𝓨}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {alg : Algorithm 𝓐 𝓨}

omit [NormedSpace ℝ 𝓨] in
lemma IsAlgEnvSeq.condExp_feedback_comp {𝓩 : Type*} [NormedAddCommGroup 𝓩] [NormedSpace ℝ 𝓩]
    [CompleteSpace 𝓩] [StandardBorelSpace 𝓨] [∀ n, IsMarkovKernel (ν n)]
    (h : IsAlgEnvSeq A Y alg (obliviousEnv ν) P) (n : ℕ)
    {g : 𝓨 → 𝓩} (hg : StronglyMeasurable g) (hint : Integrable (fun ω ↦ g (Y n ω)) P) :
    P[fun ω ↦ g (Y n ω) | h.filtrationAction n] =ᵐ[P] fun ω ↦ (ν n (A n ω))[g] := by
  cases n with
  | zero =>
    have hcd : HasCondDistrib (Y 0) (A 0) (ν 0) P := by
      have hf := h.hasCondDistrib_feedback_zero
      rwa [ν0_obliviousEnv] at hf
    rw [IsAlgEnvSeq.filtrationAction_zero_eq_comap]
    exact hcd.condExp_comp_eq (h.measurable_action 0) hg hint
  | succ m =>
    have hX : Measurable (fun ω ↦ (history A Y m ω, A (m + 1) ω)) :=
      (h.measurable_history m).prodMk (h.measurable_action (m + 1))
    have hcd : HasCondDistrib (Y (m + 1)) (fun ω ↦ (history A Y m ω, A (m + 1) ω))
        ((ν (m + 1)).prodMkLeft _) P := by
      simpa using IsObliviousEnv.hasCondDistrib_feedback_history_action h m
    rw [h.filtrationAction_eq_comap (m + 1) (Nat.succ_ne_zero m)]
    exact hcd.condExp_comp_eq hX hg hint

lemma IsAlgEnvSeq.condExp_feedback [BorelSpace 𝓨] [SecondCountableTopology 𝓨] [CompleteSpace 𝓨]
    [∀ n, IsMarkovKernel (ν n)]
    (h : IsAlgEnvSeq A Y alg (obliviousEnv ν) P) (n : ℕ)
    (hint : Integrable (Y n) P) :
    P[Y n | h.filtrationAction n] =ᵐ[P] fun ω ↦ (ν n (A n ω))[id] :=
  condExp_feedback_comp h n stronglyMeasurable_id hint

noncomputable def respMart
    (ν : ℕ → Kernel 𝓐 𝓨) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (k : 𝓐) (n : ℕ) (ω : Ω) : 𝓨 :=
    ∑ m ∈ Finset.range n, {ω | A m ω = k}.indicator (fun ω ↦ Y m ω - (ν m k)[id]) ω

lemma respMart_succ (k : 𝓐) (n : ℕ) :
    respMart ν A Y k (n + 1) = respMart ν A Y k n +
      {ω | A n ω = k}.indicator (fun ω ↦ Y n ω - (ν n k)[id]) := by
  ext ω
  simp [respMart, Finset.sum_range_succ]

lemma respMart_succ_sub (k : 𝓐) (n : ℕ) (ω : Ω) :
    respMart ν A Y k (n + 1) ω - respMart ν A Y k n ω
      = {ω | A n ω = k}.indicator (fun ω ↦ Y n ω - (ν n k)[id]) ω := by simp [respMart_succ]

variable [MeasurableSingletonClass 𝓐]

@[fun_prop]
lemma integrable_respMart_increment {m : ℕ} (hAmeas : Measurable (A m))
    (hint : Integrable (Y m) P) (k : 𝓐) :
    Integrable (fun ω ↦ {ω | A m ω = k}.indicator (fun ω ↦ Y m ω - (ν m k)[id]) ω) P :=
  (hint.sub (integrable_const _)).indicator (hAmeas (measurableSet_singleton k))

@[fun_prop]
lemma integrable_respMart (hA : ∀ n, Measurable (A n)) (hint : ∀ n, Integrable (Y n) P)
    (k : 𝓐) (n : ℕ) :
    Integrable (respMart ν A Y k n) P :=
  integrable_finsetSum _ fun m _ ↦ integrable_respMart_increment (hA m) (hint m) k

lemma memLp_respMart_increment {m : ℕ} (k : 𝓐) (hAmeas : Measurable (A m)) {p : ℝ≥0∞}
    (hY2 : MemLp (Y m) p P) :
    MemLp ({ω | A m ω = k}.indicator (fun ω ↦ Y m ω - (ν m k)[id])) p P :=
  (hY2.sub (memLp_const _)).indicator (hAmeas (measurableSet_singleton k))

lemma memLp_respMart {p : ℝ≥0∞}
    (hA : ∀ n, Measurable (A n)) (hY2 : ∀ n, MemLp (Y n) p P) (k : 𝓐) (n : ℕ) :
    MemLp (respMart ν A Y k n) p P :=
  memLp_finsetSum _ fun m _ ↦ memLp_respMart_increment k (hA m) (hY2 m)

lemma adapted_respMart [MeasurableAdd₂ 𝓨] [MeasurableSub₂ 𝓨] [∀ n, IsMarkovKernel (ν n)]
    (h : IsAlgEnvSeq A Y alg (obliviousEnv ν) P) (k : 𝓐) :
    Adapted h.filtrationAction (respMart ν A Y k) := by
  refine fun n ↦ Finset.measurable_fun_sum _ fun m hm ↦ ?_
  have hAm : Measurable[h.filtrationAction n] (A m) :=
    h.adapted_action_filtrationAction.measurable_le (by grind)
  have hYm : Measurable[h.filtrationAction n] (Y m) :=
    h.measurable_feedback_filtrationAction_of_lt (by grind)
  exact (hYm.sub measurable_const).indicator (hAm (measurableSet_singleton k))

section Martingale

variable [SecondCountableTopology 𝓨]

lemma stronglyAdapted_respMart [OpensMeasurableSpace 𝓨] [∀ n, IsMarkovKernel (ν n)]
    (h : IsAlgEnvSeq A Y alg (obliviousEnv ν) P) (k : 𝓐) :
    StronglyAdapted h.filtrationAction (respMart ν A Y k) := by
  refine fun n ↦ Finset.stronglyMeasurable_fun_sum _ fun m hm ↦ ?_
  rw [Finset.mem_range] at hm
  have hAm : Measurable[h.filtrationAction n] (A m) :=
    h.adapted_action_filtrationAction.measurable_le (by grind)
  have hYm : Measurable[h.filtrationAction n] (Y m) :=
    h.measurable_feedback_filtrationAction_of_lt hm
  exact StronglyMeasurable.indicator (hYm.stronglyMeasurable.sub stronglyMeasurable_const)
    (hAm (measurableSet_singleton k))

lemma condExp_respMart_increment [CompleteSpace 𝓨] [BorelSpace 𝓨] [∀ n, IsMarkovKernel (ν n)]
    (h : IsAlgEnvSeq A Y alg (obliviousEnv ν) P) (k : 𝓐) (i : ℕ)
    (hint : Integrable (Y i) P) :
    P[{ω | A i ω = k}.indicator (fun ω ↦ Y i ω - (ν i k)[id]) | h.filtrationAction i] =ᵐ[P] 0 := by
  let c : Ω → ℝ := actionIndicator A k i
  let g : Ω → 𝓨 := fun ω ↦ Y i ω - (ν i k)[id]
  have h_smul : c • g = {ω | A i ω = k}.indicator (fun ω ↦ Y i ω - (ν i k)[id]) := by
    ext ω
    by_cases hω : A i ω = k <;> simp [c, g, actionIndicator, hω]
  have hAG : Measurable[h.filtrationAction i] (A i) := h.adapted_action_filtrationAction i
  have hcG : StronglyMeasurable[h.filtrationAction i] c :=
    (h.adapted_actionIndicator_filtrationAction k i).stronglyMeasurable
  have hgint : Integrable g P := hint.sub (integrable_const _)
  have hcint : Integrable (c • g) P := by
    rw [h_smul]
    exact integrable_respMart_increment (ν := ν) (h.measurable_action i) hint k
  have hcondg : P[g | h.filtrationAction i] =ᵐ[P] fun ω ↦ (ν i (A i ω))[id] - (ν i k)[id] := by
    refine (condExp_sub hint (integrable_const _) _).trans ?_
    rw [condExp_const (h.filtrationAction.le i)]
    exact (h.condExp_feedback i hint).sub (Filter.EventuallyEq.refl _ _)
  have hpull := condExp_smul_of_aestronglyMeasurable_left hcG.aestronglyMeasurable hcint hgint
  filter_upwards [hpull, hcondg] with ω hp hcg
  rw [← h_smul, hp]
  simp only [Pi.smul_apply', hcg, id_eq, Pi.ofNat_apply, smul_eq_zero]
  rcases eq_or_ne (A i ω) k with hak | hak
  · simp [hak]
  · simp [c, actionIndicator, hak]

lemma martingale_respMart [CompleteSpace 𝓨] [BorelSpace 𝓨] [∀ n, IsMarkovKernel (ν n)]
    (h : IsAlgEnvSeq A Y alg (obliviousEnv ν) P)
    (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) :
    Martingale (respMart ν A Y k) h.filtrationAction P := by
  have hInt : ∀ n, Integrable (respMart ν A Y k n) P :=
    integrable_respMart h.measurable_action hint k
  refine martingale_nat (stronglyAdapted_respMart h k) hInt fun i ↦ ?_
  rw [respMart_succ]
  symm
  have hadd := condExp_add (hInt i)
    (integrable_respMart_increment (ν := ν) (h.measurable_action i) (hint i) k)
    (h.filtrationAction i)
  have hself : P[respMart ν A Y k i | h.filtrationAction i] = respMart ν A Y k i :=
    condExp_of_stronglyMeasurable (h.filtrationAction.le i) (stronglyAdapted_respMart h k i)
      (hInt i)
  have hincr := condExp_respMart_increment h k i (hint i)
  filter_upwards [hadd, hincr] with ω ha hin
  rw [ha, Pi.add_apply, congrFun hself ω, hin, Pi.zero_apply, add_zero]

end Martingale

end Learning
