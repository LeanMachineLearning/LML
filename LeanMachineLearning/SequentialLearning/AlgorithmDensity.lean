/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.Probability.Kernel.Composition.MeasureCompProd
public import LeanMachineLearning.Probability.WithDensity
public import LeanMachineLearning.SequentialLearning.BayesStationaryEnv

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

open scoped ENNReal

namespace Learning

variable {α R : Type*} [MeasurableSpace α] [MeasurableSpace R]

namespace Algorithm

noncomputable
def density [MeasurableSpace.CountablyGenerated α] (alg alg₀ : Algorithm α R) :
    (n : ℕ) → (Iic n → α × R) → ℝ≥0∞
  | 0, h => (alg.p0.rnDeriv alg₀.p0 (h ⟨0, by simp⟩).1)
  | n + 1, h =>
    let p := MeasurableEquiv.IicSuccProd (fun _ ↦ α × R) n h
    alg.density alg₀ n p.1 * (alg.policy n).rnDeriv (alg₀.policy n) p.1 p.2.1

@[fun_prop]
lemma measurable_density [MeasurableSpace.CountablyGenerated α] (alg alg₀ : Algorithm α R) (n : ℕ) :
    Measurable (alg.density alg₀ n) := by
  induction n with
  | zero =>
    simp_rw [density]
    fun_prop
  | succ n ih =>
    simp_rw [density]
    fun_prop

end Algorithm

namespace IsAlgEnvSeq

variable {Ω : Type*} [MeasurableSpace Ω]
variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
variable {alg : Algorithm α R} {env : Environment α R}
variable {A : ℕ → Ω → α} {R' : ℕ → Ω → R}
variable {P : Measure Ω} [IsFiniteMeasure P]

lemma hasLaw_hist_zero (h : IsAlgEnvSeq A R' alg env P) : HasLaw (hist A R' 0)
    ((P.map (step A R' 0)).map (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ α × R)).symm) P where
  aemeasurable := (measurable_hist h.measurable_A h.measurable_R 0).aemeasurable
  map_eq := by
    have he : (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ α × R)).symm ∘ step A R' 0 =
        hist A R' 0 := by
      funext _ ⟨0, _⟩
      rfl
    rw [← he]
    have hA := h.measurable_A
    have hR := h.measurable_R
    exact (Measure.map_map (by fun_prop) (by fun_prop)).symm

lemma hasLaw_hist_succ (h : IsAlgEnvSeq A R' alg env P) (n : ℕ) : HasLaw (hist A R' (n + 1))
    ((P.map (hist A R' n) ⊗ₘ condDistrib (step A R' (n + 1)) (hist A R' n) P).map
        (MeasurableEquiv.IicSuccProd (fun _ ↦ α × R) n).symm) P where
  aemeasurable := (measurable_hist h.measurable_A h.measurable_R (n + 1)).aemeasurable
  map_eq := by
    have he : (MeasurableEquiv.IicSuccProd (fun _ ↦ α × R) n).symm ∘
        (fun ω ↦ (hist A R' n ω, step A R' (n + 1) ω)) = hist A R' (n + 1) := by
      funext ω
      exact (MeasurableEquiv.IicSuccProd (fun _ ↦ α × R) n).symm_apply_apply (hist A R' (n + 1) ω)
    have hA := h.measurable_A
    have hR := h.measurable_R
    rw [← he, ← Measure.map_map (by fun_prop) (by fun_prop)]
    congr
    exact (compProd_map_condDistrib (by fun_prop)).symm

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]
variable {alg₀ : Algorithm α R}
variable {A₀ : ℕ → Ω₀ → α} {R₀ : ℕ → Ω₀ → R}
variable {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]

lemma absolutelyContinuous_map_hist (h : IsAlgEnvSeq A R' alg env P)
    (h₀ : IsAlgEnvSeq A₀ R₀ alg₀ env P₀) (hc : alg ≪ₐ alg₀) (n : ℕ) :
    P.map (IsAlgEnvSeq.hist A R' n) ≪ P₀.map (IsAlgEnvSeq.hist A₀ R₀ n) := by
  induction n with
  | zero =>
    rw [h.hasLaw_hist_zero.map_eq, h₀.hasLaw_hist_zero.map_eq]
    apply Measure.AbsolutelyContinuous.map _ (by fun_prop)
    rw [h.hasLaw_step_zero.map_eq, h₀.hasLaw_step_zero.map_eq]
    exact Measure.AbsolutelyContinuous.compProd_left hc.p0 _
  | succ n ih =>
    rw [(h.hasLaw_hist_succ n).map_eq, (h₀.hasLaw_hist_succ n).map_eq]
    apply Measure.AbsolutelyContinuous.map _ (by fun_prop)
    rw [Measure.compProd_congr (h.hasCondDistrib_step n).condDistrib_eq,
        Measure.compProd_congr (h₀.hasCondDistrib_step n).condDistrib_eq]
    apply Measure.AbsolutelyContinuous.compProd ih
    filter_upwards with h' using Measure.AbsolutelyContinuous.compProd_left_apply (hc.policy n h') _

lemma hasLaw_hist_withDensity (h : IsAlgEnvSeq A R' alg env P) (h₀ : IsAlgEnvSeq A₀ R₀ alg₀ env P₀)
   (hc : alg ≪ₐ alg₀) (n : ℕ) : HasLaw (IsAlgEnvSeq.hist A R' n)
      ((P₀.map (IsAlgEnvSeq.hist A₀ R₀ n)).withDensity (alg.density alg₀ n)) P where
  aemeasurable := (IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n).aemeasurable
  map_eq := by
    induction n with
    | zero =>
      rw [h.hasLaw_hist_zero.map_eq, h₀.hasLaw_hist_zero.map_eq, h.hasLaw_step_zero.map_eq,
        h₀.hasLaw_step_zero.map_eq]
      rw [← Measure.withDensity_rnDeriv_eq _ _ hc.p0,
        Measure.withDensity_compProd_left (by fun_prop)]
      exact Measure.withDensity_map_equiv (by fun_prop)
    | succ n ih =>
      let ρ h' (ar : α × R) := Kernel.rnDeriv (alg.policy n) (alg₀.policy n) h' ar.1
      have hs : stepKernel alg env n = (stepKernel alg₀ env n).withDensity ρ := by
        rw [stepKernel, ← Kernel.withDensity_rnDeriv_eq' (hc.policy n)]
        exact Kernel.withDensity_compProd_left (Kernel.measurable_rnDeriv _ _)
      have : IsMarkovKernel ((stepKernel alg₀ env n).withDensity ρ) := by
        rw [← hs]
        infer_instance
      rw [(h.hasLaw_hist_succ n).map_eq, (h₀.hasLaw_hist_succ n).map_eq,
          Measure.compProd_congr (h.hasCondDistrib_step n).condDistrib_eq,
          Measure.compProd_congr (h₀.hasCondDistrib_step n).condDistrib_eq, ih, hs,
          Measure.withDensity_compProd_withDensity (by fun_prop) (by fun_prop)]
      exact Measure.withDensity_map_equiv (by fun_prop)

end IsAlgEnvSeq

namespace IsBayesAlgEnvSeq

variable {𝓔 : Type*} [MeasurableSpace 𝓔]
variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
variable {Q : Measure 𝓔}
variable {κ : Kernel (𝓔 × α) R} [IsMarkovKernel κ]

variable {Ω : Type*} [MeasurableSpace Ω]
variable {E : Ω → 𝓔} {A : ℕ → Ω → α} {R' : ℕ → Ω → R}
variable {alg : Algorithm α R}
variable {P : Measure Ω} [IsProbabilityMeasure P]

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]
variable {E₀ : Ω₀ → 𝓔} {A₀ : ℕ → Ω₀ → α} {R₀ : ℕ → Ω₀ → R}
variable {alg₀ : Algorithm α R}
variable {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]

lemma condDistrib_hist_eq_condDistrib_hist_withDensity (h : IsBayesAlgEnvSeq Q κ alg E A R' P)
    (h₀ : IsBayesAlgEnvSeq Q κ alg₀ E₀ A₀ R₀ P₀) (hc : alg ≪ₐ alg₀) (n : ℕ) :
    condDistrib (IsAlgEnvSeq.hist A R' n) E P =ᵐ[Q]
      ((condDistrib (IsAlgEnvSeq.hist A₀ R₀ n) E₀ P₀).withDensity
        (fun _ ↦ alg.density alg₀ n)) := by
    filter_upwards [h.ae_IsAlgEnvSeq, h₀.ae_IsAlgEnvSeq, h.hasLaw_IT_hist n, h₀.hasLaw_IT_hist n]
      with _ hae hae₀ he he₀
    rw [Kernel.withDensity_apply _ (by fun_prop), ← he.map_eq, ← he₀.map_eq]
    exact (hae.hasLaw_hist_withDensity hae₀ hc n).map_eq

lemma hasLaw_hist_withDensity (h : IsBayesAlgEnvSeq Q κ alg E A R' P)
    (h₀ : IsBayesAlgEnvSeq Q κ alg₀ E₀ A₀ R₀ P₀) (hc : alg ≪ₐ alg₀) (n : ℕ) :
    HasLaw (IsAlgEnvSeq.hist A R' n)
      ((P₀.map (IsAlgEnvSeq.hist A₀ R₀ n)).withDensity (alg.density alg₀ n)) P where
  aemeasurable := (IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n).aemeasurable
  map_eq := by
    have hA := h.measurable_A
    have hR := h.measurable_R
    have hA₀ := h₀.measurable_A
    have hR₀ := h₀.measurable_R
    have hE := h.measurable_E
    have hE₀ := h₀.measurable_E
    rw [← condDistrib_comp_map hE.aemeasurable (by fun_prop), h.hasLaw_env.map_eq,
          Measure.bind_congr_right (h.condDistrib_hist_eq_condDistrib_hist_withDensity h₀ hc n),
          Kernel.comp_withDensity_const (by fun_prop),
          ← h₀.hasLaw_env.map_eq, condDistrib_comp_map hE₀.aemeasurable (by fun_prop)]

variable [StandardBorelSpace 𝓔] [Nonempty 𝓔]
variable [IsProbabilityMeasure Q]

lemma hasCondDistrib_env_hist (h : IsBayesAlgEnvSeq Q κ alg E A R' P)
    (h₀ : IsBayesAlgEnvSeq Q κ alg₀ E₀ A₀ R₀ P₀) (hc : alg ≪ₐ alg₀) (n : ℕ) :
    HasCondDistrib E (IsAlgEnvSeq.hist A R' n)
      (condDistrib E₀ (IsAlgEnvSeq.hist A₀ R₀ n) P₀) P where
  aemeasurable_fst := h.measurable_E.aemeasurable
  aemeasurable_snd := (IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n).aemeasurable
  condDistrib_eq := by
    have hA := h.measurable_A
    have hR := h.measurable_R
    have hA₀ := h₀.measurable_A
    have hR₀ := h₀.measurable_R
    have hE := h.measurable_E
    have hE₀ := h₀.measurable_E
    rw [condDistrib_ae_eq_iff_measure_eq_compProd _ h.measurable_E.aemeasurable,
      ← compProd_map_condDistrib_swap hE (by fun_prop), h.hasLaw_env.map_eq,
      Measure.compProd_eq_compProd_withDensity (by fun_prop)
        (h.condDistrib_hist_eq_condDistrib_hist_withDensity h₀ hc n),
      Measure.map_swap_withDensity_fst (by fun_prop),
      ← h₀.hasLaw_env.map_eq, compProd_map_condDistrib_swap hE₀ (by fun_prop),
      ← compProd_map_condDistrib (by fun_prop),
      ← Measure.withDensity_compProd_left (by fun_prop),
      ← (hasLaw_hist_withDensity h h₀ hc n).map_eq]

end IsBayesAlgEnvSeq

end Learning
