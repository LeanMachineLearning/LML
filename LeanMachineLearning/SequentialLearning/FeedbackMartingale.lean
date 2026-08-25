/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.ActionIndicator
public import LeanMachineLearning.SequentialLearning.Means
public import LeanMachineLearning.SequentialLearning.StationaryEnv

/-!
# TODO

TODO: extend beyond oblivious environments, to general environments?
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning

open scoped ENNReal

namespace Learning

variable {Ω 𝓐 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  [NormedAddCommGroup 𝓨] [NormedSpace ℝ 𝓨]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {alg : Algorithm 𝓐 𝓨} {env : Environment 𝓐 𝓨}

-- todo: use range instead of Iic? It would become a martingale with respect to filtrationAction
-- without the shiftUp
noncomputable def respMart
    (env : Environment 𝓐 𝓨) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (k : 𝓐) (n : ℕ) (ω : Ω) : 𝓨 :=
  ∑ m ∈ Iic n, {ω | A m ω = k}.indicator (fun ω ↦ Y m ω - env.means A Y (A m ω) m ω) ω

lemma respMart_succ (k : 𝓐) (n : ℕ) :
    respMart env A Y k (n + 1) = respMart env A Y k n +
      {ω | A (n + 1) ω = k}.indicator
        (fun ω ↦ Y (n + 1) ω - env.means A Y (A (n + 1) ω) (n + 1) ω) := by
  ext ω
  simp [respMart]

lemma respMart_succ_sub (k : 𝓐) (n : ℕ) (ω : Ω) :
    respMart env A Y k (n + 1) ω - respMart env A Y k n ω
      = {ω | A (n + 1) ω = k}.indicator
        (fun ω ↦ Y (n + 1) ω - env.means A Y (A (n + 1) ω) (n + 1) ω) ω := by
  simp [respMart_succ]

variable [MeasurableSingletonClass 𝓐]

@[fun_prop]
lemma integrable_respMart_increment [SecondCountableTopology 𝓨] [OpensMeasurableSpace 𝓨]
    {m : ℕ} (h : IsAlgEnvSeq A Y alg env P) (hint : Integrable (Y m) P) (k : 𝓐) :
    Integrable (fun ω ↦ {ω | A m ω = k}.indicator
      (fun ω ↦ Y m ω - env.means A Y (A m ω) m ω) ω) P := by
  exact (hint.sub (h.integrable_means_action hint)).indicator
    (h.measurable_action _ (measurableSet_singleton k))

@[fun_prop]
lemma integrable_respMart [SecondCountableTopology 𝓨] [OpensMeasurableSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) (n : ℕ) :
    Integrable (respMart env A Y k n) P :=
  integrable_finsetSum _ fun m _ ↦ integrable_respMart_increment h (hint m) k

lemma memLp_respMart_increment [SecondCountableTopology 𝓨] [BorelSpace 𝓨]
    {m : ℕ} (k : 𝓐) (h : IsAlgEnvSeq A Y alg env P) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ∞)
    (hY : MemLp (Y m) p P) :
    MemLp ({ω | A m ω = k}.indicator (fun ω ↦ Y m ω - env.means A Y (A m ω) m ω)) p P := by
  refine (hY.sub ?_).indicator (h.measurable_action _ (measurableSet_singleton k))
  exact h.memLp_means_action hp1 hp_top hY

lemma memLp_respMart [SecondCountableTopology 𝓨] [BorelSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ∞)
    (hY : ∀ n, MemLp (Y n) p P) (k : 𝓐) (n : ℕ) :
    MemLp (respMart env A Y k n) p P :=
  memLp_finsetSum _ fun m _ ↦ memLp_respMart_increment k h hp1 hp_top (hY m)

section Martingale

variable [SecondCountableTopology 𝓨]

lemma IsAlgEnvSeq.adapted_respMart [BorelSpace 𝓨] (h : IsAlgEnvSeq A Y alg env P) (k : 𝓐) :
    Adapted h.filtration (respMart env A Y k) := by
  refine fun n ↦ Finset.measurable_fun_sum _ fun m hm ↦ ?_
  have hAm : Measurable[h.filtration n] (A m) := h.adapted_action.measurable_le (by grind)
  have hYm : Measurable[h.filtration n] (Y m) := h.adapted_feedback.measurable_le (by grind)
  refine (hYm.sub ?_).indicator (hAm (measurableSet_singleton k))
  exact h.adapted_means.measurable_le (by grind)

lemma IsAlgEnvSeq.stronglyAdapted_respMart [BorelSpace 𝓨] (h : IsAlgEnvSeq A Y alg env P) (k : 𝓐) :
    StronglyAdapted h.filtration (respMart env A Y k) := (adapted_respMart h k).stronglyAdapted

lemma IsAlgEnvSeq.stronglyAdapted_respMart_filtrationAction [BorelSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) (k : 𝓐) :
    StronglyAdapted (h.filtrationAction.shiftUp 1) (respMart env A Y k) := by
  intro n
  refine (h.stronglyAdapted_respMart k n).mono ?_
  simp only [Filtration.shiftUp]
  exact h.filtration_le_filtrationAction_succ n

lemma condExp_respMart_increment_filtrationAction [CompleteSpace 𝓨] [BorelSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P) (k : 𝓐) (i : ℕ) (hint : Integrable (Y i) P) :
    P[{ω | A i ω = k}.indicator (fun ω ↦ Y i ω - env.means A Y (A i ω) i ω) | h.filtrationAction i]
      =ᵐ[P] 0 := by
  let c : Ω → ℝ := actionIndicator A k i
  let g : Ω → 𝓨 := fun ω ↦ Y i ω - env.means A Y (A i ω) i ω
  have h_smul : c • g = {ω | A i ω = k}.indicator (fun ω ↦ Y i ω - env.means A Y (A i ω) i ω) := by
    ext ω
    by_cases hω : A i ω = k <;> simp [c, g, actionIndicator, hω]
  have hAG : Measurable[h.filtrationAction i] (A i) := h.adapted_action_filtrationAction i
  have hcG : StronglyMeasurable[h.filtrationAction i] c :=
    (h.adapted_actionIndicator_filtrationAction k i).stronglyMeasurable
  have hgint : Integrable g P := hint.sub (h.integrable_means_action hint)
  have hcint : Integrable (c • g) P := by
    rw [h_smul]
    exact integrable_respMart_increment h hint k
  have hcondg : P[g | h.filtrationAction i] =ᵐ[P] 0 := by
    refine (condExp_sub hint (h.integrable_means_action hint) _).trans ?_
    have h1 := h.condExp_feedback i hint
    grw [h1]
    rw [condExp_of_stronglyMeasurable]
    · simp
    · exact h.adapted_means_filtrationAction.stronglyAdapted i
    · exact h.integrable_means_action hint
  have hpull := condExp_smul_of_aestronglyMeasurable_left hcG.aestronglyMeasurable hcint hgint
  filter_upwards [hpull, hcondg] with ω hp hcg
  rw [← h_smul, hp]
  simp only [Pi.smul_apply', hcg, Pi.ofNat_apply, smul_eq_zero]
  rcases eq_or_ne (A i ω) k with hak | hak
  · simp
  · simp [c, actionIndicator, hak]

lemma martingale_respMart [CompleteSpace 𝓨] [BorelSpace 𝓨]
    (h : IsAlgEnvSeq A Y alg env P)
    (hint : ∀ n, Integrable (Y n) P) (k : 𝓐) :
    Martingale (respMart env A Y k) (h.filtrationAction.shiftUp 1) P := by
  have hInt : ∀ n, Integrable (respMart env A Y k n) P := integrable_respMart h hint k
  refine martingale_nat (h.stronglyAdapted_respMart_filtrationAction k) hInt fun i ↦ ?_
  rw [respMart_succ]
  symm
  have hadd := condExp_add (hInt i)
    (integrable_respMart_increment h (hint (i + 1)) k) (h.filtrationAction.shiftUp 1 i)
  have hself : P[respMart env A Y k i | h.filtrationAction.shiftUp 1 i] = respMart env A Y k i :=
    condExp_of_stronglyMeasurable ((h.filtrationAction.shiftUp 1).le i)
      (h.stronglyAdapted_respMart_filtrationAction k i) (hInt i)
  have hincr := condExp_respMart_increment_filtrationAction h k (i + 1) (hint (i + 1))
  filter_upwards [hadd, hincr] with ω ha hin
  rw [ha, Pi.add_apply, congrFun hself ω]
  simp only [Filtration.shiftUp, add_eq_left]
  rw [hin, Pi.zero_apply]

end Martingale

end Learning
