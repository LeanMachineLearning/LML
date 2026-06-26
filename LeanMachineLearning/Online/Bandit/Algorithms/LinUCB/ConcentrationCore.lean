/-
Copyright (c) 2026 OpenAI, Fawad Haider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Fawad Haider
-/
module

public import LeanMachineLearning.Online.Bandit.Algorithms.LinUCB.ConfidenceEvents
public import Mathlib.Probability.ConditionalExpectation

/-!
# LinUCB Scalar And Projected Concentration Core

Reward-noise kernels, scalar projected-noise concentration, and fixed-direction
exponential-process lemmas for finite-action LinUCB.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset Learning

open scoped ENNReal NNReal Matrix MatrixOrder

namespace Bandits

variable {K d : ℕ}

namespace LinUCB

variable {hK : 0 < K} {reg : ℝ} {β : ℕ → ℝ} {x : Fin K → Feature d}
  {ν : Kernel (Fin K) ℝ} [IsMarkovKernel ν]
  {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}
  {n : ℕ} {ω : Ω}

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A pointwise-equal presentation of a real-valued supermartingale is again a supermartingale.

This small helper keeps later textbook-facing concentration lemmas from repeating the three
definition fields of `Supermartingale`: adaptedness, conditional expectation monotonicity, and
integrability. -/
lemma supermartingale_congr_eq
    {f g : ℕ → Ω → ℝ} {ℱ : Filtration ℕ mΩ}
    (hf : Supermartingale f ℱ P) (hfg : ∀ n, f n = g n) :
    Supermartingale g ℱ P := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa [← hfg i] using hf.stronglyAdapted i
  · intro i j hij
    have h_cond_eq : P[g j | ℱ i] =ᵐ[P] P[f j | ℱ i] := by
      exact condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦ by
        rw [← hfg j])
    filter_upwards [h_cond_eq, hf.condExp_ae_le hij] with ω h_eq h_le
    rw [h_eq]
    simpa [hfg i] using h_le
  · intro i
    exact (hf.integrable i).congr (Filter.Eventually.of_forall fun ω ↦ by
      rw [hfg i])

section AlgorithmBehavior



omit [IsMarkovKernel ν] in
/-- Project the arm-wise reward-noise subgaussian assumption to a single arm. -/
lemma RewardNoiseSubgaussian.apply
    {σ2 : ℝ≥0}
    (hν : RewardNoiseSubgaussian (K := K) ν σ2) (a : Fin K) :
    HasSubgaussianMGF (fun r ↦ r - (ν a)[id]) σ2 (ν a) :=
  hν a

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A subgaussian MGF bound remains true when the variance proxy is enlarged. -/
lemma hasSubgaussianMGF_mono_varianceProxy
    {X : Ω → ℝ} {c c' : ℝ≥0}
    (hX : HasSubgaussianMGF X c P) (hc : c ≤ c') :
    HasSubgaussianMGF X c' P where
  integrable_exp_mul := hX.integrable_exp_mul
  mgf_le t := by
    refine (hX.mgf_le t).trans ?_
    exact Real.exp_le_exp.mpr (by
      have hc' : (c : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hc
      gcongr)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A scalar subgaussian MGF bound gives the normalized exponential-process bound at one time. -/
lemma hasSubgaussianMGF_integral_exp_sub_le_one
    {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c P) (u : ℝ) :
    ∫ ω, Real.exp (u * X ω - (c : ℝ) * u ^ 2 / 2) ∂P ≤ 1 := by
  let b : ℝ := (c : ℝ) * u ^ 2 / 2
  have h_eq :
      (∫ ω, Real.exp (u * X ω - (c : ℝ) * u ^ 2 / 2) ∂P) =
        (∫ ω, Real.exp (u * X ω) ∂P) / Real.exp b := by
    simp only [b]
    simp_rw [Real.exp_sub]
    rw [MeasureTheory.integral_div]
  have h_mgf_le :
      (∫ ω, Real.exp (u * X ω) ∂P) ≤ Real.exp b := by
    simpa [mgf, b] using hX.mgf_le u
  calc
    (∫ ω, Real.exp (u * X ω - (c : ℝ) * u ^ 2 / 2) ∂P)
        = (∫ ω, Real.exp (u * X ω) ∂P) / Real.exp b := h_eq
    _ ≤ Real.exp b / Real.exp b :=
        div_le_div_of_nonneg_right h_mgf_le (le_of_lt (Real.exp_pos b))
    _ = 1 := div_self (Real.exp_ne_zero b)

omit [IsMarkovKernel ν] in
/-- Measurability of the arm-mean map on the finite action space. -/
lemma measurable_rewardMean (ν : Kernel (Fin K) ℝ) :
    Measurable fun a : Fin K ↦ (ν a)[id] :=
  measurable_of_countable _

omit [IsMarkovKernel ν] in
/-- Deterministic centering map sending `(a, r)` to the reward noise `r - μ(a)`. -/
noncomputable def centerReward (ν : Kernel (Fin K) ℝ) (p : Fin K × ℝ) : ℝ :=
  p.2 - (ν p.1)[id]

omit [IsMarkovKernel ν] in
/-- The centered-reward map is measurable. -/
lemma measurable_centerReward (ν : Kernel (Fin K) ℝ) :
    Measurable (centerReward ν) :=
  measurable_snd.sub ((measurable_rewardMean ν).comp measurable_fst)

omit [IsMarkovKernel ν] in
/-- Conditional kernel of centered reward noise given the selected action.

For action `a`, this is the reward law `ν a` pushed forward by `r ↦ r - μ(a)`. It is the
Markov-kernel form of the scalar martingale noise process used by the future self-normalized
concentration theorem. -/
noncomputable def rewardNoiseKernel (ν : Kernel (Fin K) ℝ) : Kernel (Fin K) ℝ :=
  ⟨fun a ↦ (ν a).map (fun r ↦ r - (ν a)[id]), measurable_of_countable _⟩

instance rewardNoiseKernel.instIsMarkovKernel :
    IsMarkovKernel (rewardNoiseKernel (K := K) ν) := by
  constructor
  intro a
  simpa [rewardNoiseKernel] using
    Measure.isProbabilityMeasure_map (μ := ν a) (measurable_id.sub measurable_const).aemeasurable

omit [IsMarkovKernel ν] in
/-- At a fixed action, `rewardNoiseKernel` is exactly the reward law pushed forward by centering at
that action's mean. -/
lemma rewardNoiseKernel_apply (ν : Kernel (Fin K) ℝ) (a : Fin K) :
    rewardNoiseKernel ν a = (ν a).map (fun r ↦ r - (ν a)[id]) :=
  rfl

omit [IsMarkovKernel ν] in
/-- Arm-wise subgaussianity stated on the centered-noise kernel itself. -/
def RewardNoiseKernelSubgaussian (ν : Kernel (Fin K) ℝ) (σ2 : ℝ≥0) : Prop :=
  ∀ a, HasSubgaussianMGF id σ2 (rewardNoiseKernel ν a)

omit [IsMarkovKernel ν] in
/-- The UCB-style arm-wise centered reward assumption implies subgaussianity of the centered-noise
kernel. -/
lemma RewardNoiseKernelSubgaussian.of_rewardNoiseSubgaussian
    {σ2 : ℝ≥0}
    (hν : RewardNoiseSubgaussian (K := K) ν σ2) :
    RewardNoiseKernelSubgaussian (K := K) ν σ2 := by
  intro a
  rw [rewardNoiseKernel_apply (ν := ν) a]
  exact (HasSubgaussianMGF.id_map_iff
    ((measurable_id.sub measurable_const).aemeasurable)).mpr (hν a)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Arm-wise subgaussianity of the centered-noise kernel packages into Mathlib's kernel-level
subgaussian MGF predicate over any finite action law. -/
lemma RewardNoiseKernelSubgaussian.hasKernelSubgaussian
    {σ2 : ℝ≥0}
    (hν : RewardNoiseKernelSubgaussian (K := K) ν σ2)
    (μ : Measure (Fin K)) [IsFiniteMeasure μ] :
    Kernel.HasSubgaussianMGF id σ2 (rewardNoiseKernel ν) μ := by
  constructor
  · intro t
    have hf :
        AEStronglyMeasurable (fun η : ℝ ↦ Real.exp (t * η)) ((rewardNoiseKernel ν) ∘ₘ μ) := by
      fun_prop
    change Integrable (fun η : ℝ ↦ Real.exp (t * η)) ((rewardNoiseKernel ν) ∘ₘ μ)
    rw [Measure.integrable_comp_iff hf]
    constructor
    · exact Filter.Eventually.of_forall fun a ↦ (hν a).integrable_exp_mul t
    · have h_meas :
          AEStronglyMeasurable
            (fun a : Fin K ↦ ∫ η, ‖Real.exp (t * η)‖ ∂rewardNoiseKernel ν a) μ := by
        exact (measurable_of_countable _).aestronglyMeasurable
      refine integrable_of_le_of_le h_meas ?_ ?_ (integrable_const 0)
        (integrable_const (Real.exp (σ2 * t ^ 2 / 2)))
      · exact Filter.Eventually.of_forall fun a ↦ integral_nonneg fun η ↦ norm_nonneg _
      · refine Filter.Eventually.of_forall fun a ↦ ?_
        have h_int := (hν a).integrable_exp_mul t
        have h_mgf := (hν a).mgf_le t
        simpa [mgf, Real.norm_of_nonneg (Real.exp_nonneg _)] using h_mgf
  · exact Filter.Eventually.of_forall fun a t ↦ (hν a).mgf_le t

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The history-action version of `RewardNoiseKernelSubgaussian.hasKernelSubgaussian`: adding an
ignored history coordinate to the conditioning variable preserves the kernel-level subgaussian MGF
property. -/
lemma RewardNoiseKernelSubgaussian.hasKernelSubgaussian_prodMkLeft
    {γ : Type*} [MeasurableSpace γ] {σ2 : ℝ≥0}
    (hν : RewardNoiseKernelSubgaussian (K := K) ν σ2)
    (μ : Measure (γ × Fin K)) [IsFiniteMeasure μ] :
    Kernel.HasSubgaussianMGF id σ2 ((rewardNoiseKernel ν).prodMkLeft γ) μ := by
  constructor
  · intro t
    have hf :
        AEStronglyMeasurable (fun η : ℝ ↦ Real.exp (t * η))
          (((rewardNoiseKernel ν).prodMkLeft γ) ∘ₘ μ) := by
      fun_prop
    change Integrable (fun η : ℝ ↦ Real.exp (t * η))
      (((rewardNoiseKernel ν).prodMkLeft γ) ∘ₘ μ)
    rw [Measure.integrable_comp_iff hf]
    constructor
    · exact Filter.Eventually.of_forall fun z ↦ by
        simpa [Kernel.prodMkLeft_apply] using (hν z.2).integrable_exp_mul t
    · have h_meas :
          AEStronglyMeasurable
            (fun z : γ × Fin K ↦
              ∫ η, ‖Real.exp (t * η)‖ ∂(rewardNoiseKernel ν).prodMkLeft γ z) μ := by
        refine ((measurable_of_countable
          (fun a : Fin K ↦ ∫ η, ‖Real.exp (t * η)‖ ∂rewardNoiseKernel ν a)).comp
          measurable_snd).aestronglyMeasurable.congr ?_
        exact Filter.Eventually.of_forall fun z ↦ by simp [Kernel.prodMkLeft_apply]
      refine integrable_of_le_of_le h_meas ?_ ?_ (integrable_const 0)
        (integrable_const (Real.exp (σ2 * t ^ 2 / 2)))
      · exact Filter.Eventually.of_forall fun z ↦ integral_nonneg fun η ↦ norm_nonneg _
      · refine Filter.Eventually.of_forall fun z ↦ ?_
        have h_mgf := (hν z.2).mgf_le t
        simpa [Kernel.prodMkLeft_apply, mgf, Real.norm_of_nonneg (Real.exp_nonneg _)] using h_mgf
  · exact Filter.Eventually.of_forall fun z t ↦ by
      simpa [Kernel.prodMkLeft_apply] using (hν z.2).mgf_le t

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The UCB-style arm-wise reward-noise assumption gives the kernel-level subgaussian MGF package
for `rewardNoiseKernel`. -/
lemma RewardNoiseSubgaussian.hasKernelSubgaussian
    {σ2 : ℝ≥0}
    (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (μ : Measure (Fin K)) [IsFiniteMeasure μ] :
    Kernel.HasSubgaussianMGF id σ2 (rewardNoiseKernel ν) μ :=
  RewardNoiseKernelSubgaussian.hasKernelSubgaussian
    (ν := ν) (σ2 := σ2)
    (RewardNoiseKernelSubgaussian.of_rewardNoiseSubgaussian (K := K) (ν := ν) hν) μ

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The UCB-style arm-wise reward-noise assumption gives the kernel-level subgaussian MGF package
after adding an ignored history coordinate. -/
lemma RewardNoiseSubgaussian.hasKernelSubgaussian_prodMkLeft
    {γ : Type*} [MeasurableSpace γ] {σ2 : ℝ≥0}
    (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (μ : Measure (γ × Fin K)) [IsFiniteMeasure μ] :
    Kernel.HasSubgaussianMGF id σ2 ((rewardNoiseKernel ν).prodMkLeft γ) μ :=
  RewardNoiseKernelSubgaussian.hasKernelSubgaussian_prodMkLeft
    (ν := ν) (σ2 := σ2)
    (RewardNoiseKernelSubgaussian.of_rewardNoiseSubgaussian (K := K) (ν := ν) hν) μ

omit [IsProbabilityMeasure P] in
/-- Mapping an action-reward joint law by reward centering is the same as pairing the action law
with `rewardNoiseKernel`. -/
lemma compProd_map_centerReward_eq_compProd_rewardNoiseKernel
    (μ : Measure (Fin K)) [SFinite μ] :
    (μ ⊗ₘ ν).map (fun p : Fin K × ℝ ↦ (p.1, centerReward ν p)) =
      μ ⊗ₘ rewardNoiseKernel ν := by
  ext s hs
  let g : Fin K × ℝ → Fin K × ℝ := fun p ↦ (p.1, centerReward ν p)
  have hg : Measurable g := by
    dsimp [g]
    exact Measurable.prodMk measurable_fst (measurable_centerReward ν)
  change (Measure.map g (μ ⊗ₘ ν)) s = (μ ⊗ₘ rewardNoiseKernel ν) s
  rw [Measure.map_apply hg hs, Measure.compProd_apply (hg hs), Measure.compProd_apply hs]
  refine lintegral_congr_ae ?_
  refine Filter.Eventually.of_forall fun a ↦ ?_
  change (ν a) (Prod.mk a ⁻¹' (g ⁻¹' s)) =
    (rewardNoiseKernel ν a) (Prod.mk a ⁻¹' s)
  rw [rewardNoiseKernel_apply (ν := ν) a]
  let f : ℝ → ℝ := fun r ↦ r - (ν a)[id]
  have hf : Measurable f := by
    dsimp [f]
    exact measurable_id.sub measurable_const
  change (ν a) (Prod.mk a ⁻¹' (g ⁻¹' s)) = (Measure.map f (ν a)) (Prod.mk a ⁻¹' s)
  rw [Measure.map_apply hf (measurable_prodMk_left hs)]
  congr 1

omit [IsProbabilityMeasure P] in
/-- Mapping a history/action-reward joint law by reward centering is the same as pairing the
history/action law with `rewardNoiseKernel`, ignoring the history coordinate.

This is the history-action version of `compProd_map_centerReward_eq_compProd_rewardNoiseKernel`.
It is the measure identity used to show that reward noise is conditionally centered-subgaussian
given the past history and the current selected action. -/
lemma compProd_map_centerReward_historyAction_eq_compProd_rewardNoiseKernel_prodMkLeft
    {γ : Type*} [MeasurableSpace γ]
    (μ : Measure (γ × Fin K)) [SFinite μ] :
    (μ ⊗ₘ ν.prodMkLeft γ).map
        (fun p : (γ × Fin K) × ℝ ↦ (p.1, p.2 - (ν p.1.2)[id])) =
      μ ⊗ₘ (rewardNoiseKernel ν).prodMkLeft γ := by
  ext s hs
  let g : (γ × Fin K) × ℝ → (γ × Fin K) × ℝ :=
    fun p ↦ (p.1, p.2 - (ν p.1.2)[id])
  have hg : Measurable g := by
    dsimp [g]
    refine Measurable.prodMk measurable_fst ?_
    exact measurable_snd.sub ((measurable_rewardMean ν).comp (measurable_snd.comp measurable_fst))
  change (Measure.map g (μ ⊗ₘ ν.prodMkLeft γ)) s =
    (μ ⊗ₘ (rewardNoiseKernel ν).prodMkLeft γ) s
  rw [Measure.map_apply hg hs, Measure.compProd_apply (hg hs), Measure.compProd_apply hs]
  refine lintegral_congr_ae ?_
  refine Filter.Eventually.of_forall fun ha ↦ ?_
  change (ν.prodMkLeft γ ha) (Prod.mk ha ⁻¹' (g ⁻¹' s)) =
    ((rewardNoiseKernel ν).prodMkLeft γ ha) (Prod.mk ha ⁻¹' s)
  rw [Kernel.prodMkLeft_apply, Kernel.prodMkLeft_apply, rewardNoiseKernel_apply (ν := ν) ha.2]
  let f : ℝ → ℝ := fun r ↦ r - (ν ha.2)[id]
  have hf : Measurable f := by
    dsimp [f]
    exact measurable_id.sub measurable_const
  change (ν ha.2) (Prod.mk ha ⁻¹' (g ⁻¹' s)) =
    (Measure.map f (ν ha.2)) (Prod.mk ha ⁻¹' s)
  rw [Measure.map_apply hf (measurable_prodMk_left hs)]
  congr 1

/-- In a stationary bandit environment, the scalar centered reward noise at time `t`, conditioned
on the selected action, has conditional kernel `rewardNoiseKernel ν`.

This is the formal bridge from the repository's Markov-kernel environment model to the martingale
noise process used in the textbook LinUCB self-normalized concentration proof. -/
lemma hasCondDistrib_rewardNoise_action {alg : Algorithm (Fin K) ℝ}
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (t : ℕ) :
    HasCondDistrib (rewardNoise A R ν t) (A t) (rewardNoiseKernel ν) P := by
  have hR : HasCondDistrib (R t) (A t) ν P :=
    h.hasCondDistrib_feedback_stationaryEnv t
  have h_noise_meas :
      Measurable fun ω ↦ R t ω - (ν (A t ω))[id] :=
    (h.measurable_feedback t).sub ((measurable_rewardMean ν).comp (h.measurable_action t))
  have h_noise_ae : AEMeasurable (rewardNoise A R ν t) P := by
    change AEMeasurable (fun ω ↦ R t ω - (ν (A t ω))[id]) P
    exact h_noise_meas.aemeasurable
  have h_pair_ae : AEMeasurable (fun ω ↦ (A t ω, R t ω)) P :=
    (Measurable.prodMk (h.measurable_action t) (h.measurable_feedback t)).aemeasurable
  have h_center_ae :
      AEMeasurable (fun p : Fin K × ℝ ↦ (p.1, centerReward ν p))
        (P.map fun ω ↦ (A t ω, R t ω)) :=
    (Measurable.prodMk measurable_fst (measurable_centerReward ν)).aemeasurable
  refine ⟨?_, ?_⟩
  · exact (h.measurable_action t).aemeasurable.prodMk h_noise_ae
  · have h_eq := hR.map_eq
    calc P.map (fun ω ↦ (A t ω, rewardNoise A R ν t ω))
      _ = (P.map (fun ω ↦ (A t ω, R t ω))).map
          (fun p : Fin K × ℝ ↦ (p.1, centerReward ν p)) := by
            rw [AEMeasurable.map_map_of_aemeasurable h_center_ae h_pair_ae]
            · rfl
      _ = (P.map (A t) ⊗ₘ ν).map
          (fun p : Fin K × ℝ ↦ (p.1, centerReward ν p)) := by
            rw [h_eq]
      _ = P.map (A t) ⊗ₘ rewardNoiseKernel ν :=
            compProd_map_centerReward_eq_compProd_rewardNoiseKernel (ν := ν) (μ := P.map (A t))

/-- In a stationary bandit environment, the scalar centered reward noise at a positive time,
conditioned on the previous history and the selected action, has conditional kernel
`rewardNoiseKernel ν`, ignoring the history coordinate.

This is the martingale-noise conditional-law statement needed before applying a future
self-normalized concentration theorem: after the algorithm chooses `A t` from the past, the
remaining centered reward noise has the centered law of that selected arm. -/
lemma hasCondDistrib_rewardNoise_history_action {alg : Algorithm (Fin K) ℝ}
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) {t : ℕ} (ht : t ≠ 0) :
    HasCondDistrib (rewardNoise A R ν t)
      (fun ω ↦ (history A R (t - 1) ω, A t ω))
      ((rewardNoiseKernel ν).prodMkLeft (Iic (t - 1) → Fin K × ℝ)) P := by
  cases t with
  | zero => exact (ht rfl).elim
  | succ n =>
      have hR : HasCondDistrib (R (n + 1))
          (fun ω ↦ (history A R n ω, A (n + 1) ω))
          (ν.prodMkLeft (Iic n → Fin K × ℝ)) P := by
        simpa using h.hasCondDistrib_feedback n
      have h_noise_meas :
          Measurable fun ω ↦ R (n + 1) ω - (ν (A (n + 1) ω))[id] :=
        (h.measurable_feedback (n + 1)).sub
          ((measurable_rewardMean ν).comp (h.measurable_action (n + 1)))
      have h_noise_ae : AEMeasurable (rewardNoise A R ν (n + 1)) P := by
        change AEMeasurable
          (fun ω ↦ R (n + 1) ω - (ν (A (n + 1) ω))[id]) P
        exact h_noise_meas.aemeasurable
      have h_pair_ae :
          AEMeasurable
            (fun ω ↦ ((history A R n ω, A (n + 1) ω), R (n + 1) ω)) P :=
        (Measurable.prodMk
          (Measurable.prodMk
            (h.measurable_history n)
            (h.measurable_action (n + 1)))
          (h.measurable_feedback (n + 1))).aemeasurable
      have h_center_ae :
          AEMeasurable
            (fun p : ((Iic n → Fin K × ℝ) × Fin K) × ℝ ↦
              (p.1, p.2 - (ν p.1.2)[id]))
            (P.map fun ω ↦
              ((history A R n ω, A (n + 1) ω), R (n + 1) ω)) := by
        refine (Measurable.prodMk measurable_fst ?_).aemeasurable
        exact measurable_snd.sub
          ((measurable_rewardMean ν).comp (measurable_snd.comp measurable_fst))
      refine ⟨?_, ?_⟩
      · exact ((Measurable.prodMk
          (h.measurable_history n)
          (h.measurable_action (n + 1))).aemeasurable).prodMk h_noise_ae
      · have h_eq := hR.map_eq
        calc
          P.map
              (fun ω ↦
                ((history A R n ω, A (n + 1) ω),
                  rewardNoise A R ν (n + 1) ω))
            = (P.map
              (fun ω ↦
                ((history A R n ω, A (n + 1) ω), R (n + 1) ω))).map
              (fun p : ((Iic n → Fin K × ℝ) × Fin K) × ℝ ↦
                (p.1, p.2 - (ν p.1.2)[id])) := by
                rw [AEMeasurable.map_map_of_aemeasurable h_center_ae h_pair_ae]
                rfl
          _ = (P.map (fun ω ↦ (history A R n ω, A (n + 1) ω)) ⊗ₘ
              ν.prodMkLeft (Iic n → Fin K × ℝ)).map
              (fun p : ((Iic n → Fin K × ℝ) × Fin K) × ℝ ↦
                (p.1, p.2 - (ν p.1.2)[id])) := by
                rw [h_eq]
          _ = P.map (fun ω ↦ (history A R n ω, A (n + 1) ω)) ⊗ₘ
              (rewardNoiseKernel ν).prodMkLeft (Iic n → Fin K × ℝ) :=
                compProd_map_centerReward_historyAction_eq_compProd_rewardNoiseKernel_prodMkLeft
                  (ν := ν)
                  (μ := P.map fun ω ↦ (history A R n ω, A (n + 1) ω))

omit [IsMarkovKernel ν] in
/-- Arm-wise subgaussianity of `rewardNoiseKernel` remains true after adding an ignored history
coordinate to the conditioning variable. -/
lemma RewardNoiseKernelSubgaussian.prodMkLeft
    {γ : Type*} [MeasurableSpace γ] {σ2 : ℝ≥0}
    (hν : RewardNoiseKernelSubgaussian (K := K) ν σ2) :
    ∀ z : γ × Fin K,
      HasSubgaussianMGF id σ2 ((rewardNoiseKernel ν).prodMkLeft γ z) := by
  intro z
  simpa [Kernel.prodMkLeft_apply] using hν z.2

omit [IsMarkovKernel ν] in
/-- Pointwise predictable scalar projections of the centered-noise kernel are subgaussian with the
variance proxy multiplied by the squared scalar.

For a later vector concentration proof, `q z` is the predictable coefficient obtained by projecting
the selected feature vector onto a fixed direction. -/
lemma RewardNoiseKernelSubgaussian.prodMkLeft_constMul
    {γ : Type*} [MeasurableSpace γ] {σ2 : ℝ≥0}
    (hν : RewardNoiseKernelSubgaussian (K := K) ν σ2) (q : γ × Fin K → ℝ) :
    ∀ z : γ × Fin K,
      HasSubgaussianMGF (fun η ↦ q z * η)
        (⟨q z ^ 2, sq_nonneg (q z)⟩ * σ2)
        ((rewardNoiseKernel ν).prodMkLeft γ z) := by
  intro z
  simpa only [id_eq] using (hν.prodMkLeft z).const_mul (q z)

/-- Under the UCB-style arm-wise reward-noise assumption, the conditional law of the positive-time
LinUCB reward noise given history and selected action is subgaussian.

This is the scalar probabilistic input that a future vector self-normalized concentration theorem
should consume for predictable projections of `η_t x_{A_t}`. -/
lemma rewardNoise_condDistrib_history_action_subgaussian {alg : Algorithm (Fin K) ℝ}
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0) :
    ∀ᵐ z ∂P.map (fun ω ↦ (history A R (t - 1) ω, A t ω)),
      HasSubgaussianMGF id σ2
        (condDistrib (rewardNoise A R ν t)
          (fun ω ↦ (history A R (t - 1) ω, A t ω)) P z) := by
  have h_cond := hasCondDistrib_rewardNoise_history_action
    (A := A) (R := R) (ν := ν) h ht
  have h_kernel :
      ∀ z : (Iic (t - 1) → Fin K × ℝ) × Fin K,
        HasSubgaussianMGF id σ2
          ((rewardNoiseKernel ν).prodMkLeft (Iic (t - 1) → Fin K × ℝ) z) :=
    (RewardNoiseKernelSubgaussian.of_rewardNoiseSubgaussian
      (K := K) (ν := ν) hν).prodMkLeft
  filter_upwards [h_cond.condDistrib_eq] with z hz
  rw [hz]
  exact h_kernel z

omit [IsMarkovKernel ν] in
/-- The centered reward-noise kernel, viewed over the realized history/action conditioning law,
satisfies Mathlib's kernel-level subgaussian MGF predicate.

This packages the previous pointwise conditional-law statement with the global exponential
integrability required by `Kernel.HasSubgaussianMGF`. -/
lemma rewardNoise_history_action_kernelSubgaussian
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2) (t : ℕ) :
    Kernel.HasSubgaussianMGF id σ2
      ((rewardNoiseKernel ν).prodMkLeft (Iic (t - 1) → Fin K × ℝ))
      (P.map fun ω ↦ (history A R (t - 1) ω, A t ω)) :=
  hν.hasKernelSubgaussian_prodMkLeft
    (P.map fun ω ↦ (history A R (t - 1) ω, A t ω))

/-- The marginal law of the realized positive-time reward noise is the measure obtained by first
sampling the realized history/action pair and then sampling from the centered reward-noise kernel.

This is the process-level law identity behind the conditional-law statement
`hasCondDistrib_rewardNoise_history_action`. It lets later concentration lemmas move between the
actual random variable `rewardNoise A R ν t` and the Markov-kernel description of its conditional
law. -/
lemma rewardNoise_map_eq_historyAction_kernel_comp {alg : Algorithm (Fin K) ℝ}
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {t : ℕ} (ht : t ≠ 0) :
    P.map (rewardNoise A R ν t) =
      ((rewardNoiseKernel ν).prodMkLeft (Iic (t - 1) → Fin K × ℝ)) ∘ₘ
        P.map (fun ω ↦ (history A R (t - 1) ω, A t ω)) := by
  let X : Ω → (Iic (t - 1) → Fin K × ℝ) × Fin K :=
    fun ω ↦ (history A R (t - 1) ω, A t ω)
  let Y : Ω → ℝ := rewardNoise A R ν t
  let κ : Kernel ((Iic (t - 1) → Fin K × ℝ) × Fin K) ℝ :=
    (rewardNoiseKernel ν).prodMkLeft (Iic (t - 1) → Fin K × ℝ)
  have h_cond : HasCondDistrib Y X κ P := by
    simpa [X, Y, κ] using
      hasCondDistrib_rewardNoise_history_action (A := A) (R := R) (ν := ν) h ht
  have hX_meas : Measurable X := by
    dsimp [X]
    exact Measurable.prodMk
      ((h.measurable_history (t - 1)))
      (h.measurable_action t)
  have hX_law : HasLaw X (P.map X) P := ⟨hX_meas.aemeasurable, rfl⟩
  have h_pair := HasLaw.prod_of_hasCondDistrib hX_law h_cond
  have h_snd := congrArg Measure.snd h_pair.map_eq
  rw [Measure.snd_map_prodMk₀ hX_meas.aemeasurable, Measure.snd_compProd] at h_snd
  simpa [X, Y, κ] using h_snd

/-- Exponential integrability of the realized positive-time reward noise follows from the
arm-wise subgaussian reward-noise assumption.

The proof first packages the centered reward-noise law as a kernel-level subgaussian MGF statement,
then uses `rewardNoise_map_eq_historyAction_kernel_comp` to transport the resulting integrability
back to the actual process variable. -/
lemma rewardNoise_integrable_exp_mul_history_action {alg : Algorithm (Fin K) ℝ}
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0) (u : ℝ) :
    Integrable (fun ω ↦ Real.exp (u * rewardNoise A R ν t ω)) P := by
  let X : Ω → (Iic (t - 1) → Fin K × ℝ) × Fin K :=
    fun ω ↦ (history A R (t - 1) ω, A t ω)
  let κ : Kernel ((Iic (t - 1) → Fin K × ℝ) × Fin K) ℝ :=
    (rewardNoiseKernel ν).prodMkLeft (Iic (t - 1) → Fin K × ℝ)
  have h_kernel :
      Kernel.HasSubgaussianMGF id σ2 κ (P.map X) := by
    simpa [X, κ] using
      rewardNoise_history_action_kernelSubgaussian (A := A) (R := R) (P := P)
        (ν := ν) hν t
  have h_int := h_kernel.integrable_exp_mul u
  have h_law :
      P.map (rewardNoise A R ν t) = κ ∘ₘ P.map X := by
    simpa [X, κ] using
      rewardNoise_map_eq_historyAction_kernel_comp (A := A) (R := R) (ν := ν) h ht
  rw [← h_law] at h_int
  have hY_ae : AEMeasurable (rewardNoise A R ν t) P :=
    (hasCondDistrib_rewardNoise_history_action (A := A) (R := R) (ν := ν) h ht).aemeasurable_snd
  simpa [Function.comp_def] using
    (integrable_map_measure (by fun_prop) hY_ae).mp h_int

/-- Conditional MGF bound for the realized positive-time LinUCB reward noise.

Given the previous history and the selected action at time `t`, the conditional expectation of
`exp (u * η_t)` is bounded by the arm-wise subgaussian MGF bound
`exp (σ2 * u^2 / 2)`, where `η_t = R_t - μ(A_t)`.

This is the scalar conditional-subgaussian statement that the textbook vector self-normalized
argument uses for predictable projections of the noise process. -/
lemma rewardNoise_ae_condExp_exp_le_history_action {alg : Algorithm (Fin K) ℝ}
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0) (u : ℝ) :
    ∀ᵐ ω ∂P,
      P[fun ω' ↦ Real.exp (u * rewardNoise A R ν t ω') |
        (inferInstance : MeasurableSpace ((Iic (t - 1) → Fin K × ℝ) × Fin K)).comap
          (fun ω ↦ (history A R (t - 1) ω, A t ω))] ω
        ≤ Real.exp (σ2 * u ^ 2 / 2) := by
  let X : Ω → (Iic (t - 1) → Fin K × ℝ) × Fin K :=
    fun ω ↦ (history A R (t - 1) ω, A t ω)
  let Y : Ω → ℝ := rewardNoise A R ν t
  let κ : Kernel ((Iic (t - 1) → Fin K × ℝ) × Fin K) ℝ :=
    (rewardNoiseKernel ν).prodMkLeft (Iic (t - 1) → Fin K × ℝ)
  have h_cond : HasCondDistrib Y X κ P := by
    simpa [X, Y, κ] using
      hasCondDistrib_rewardNoise_history_action (A := A) (R := R) (ν := ν) h ht
  have hX_meas : Measurable X := by
    dsimp [X]
    exact Measurable.prodMk
      ((h.measurable_history (t - 1)))
      (h.measurable_action t)
  have hY_ae : AEMeasurable Y P := h_cond.aemeasurable_snd
  have hf : StronglyMeasurable (fun η : ℝ ↦ Real.exp (u * η)) := by
    fun_prop
  have h_int : Integrable (fun ω ↦ Real.exp (u * Y ω)) P := by
    simpa [Y] using
      rewardNoise_integrable_exp_mul_history_action (A := A) (R := R) (ν := ν) h hν ht u
  have h_ce :
      P[fun ω ↦ Real.exp (u * Y ω) |
        (inferInstance : MeasurableSpace ((Iic (t - 1) → Fin K × ℝ) × Fin K)).comap X]
        =ᵐ[P] fun ω ↦ ∫ η, Real.exp (u * η) ∂condDistrib Y X P (X ω) := by
    exact condExp_ae_eq_integral_condDistrib (μ := P) (X := X) (Y := Y)
      hX_meas hY_ae hf h_int
  have h_kernel_eq : ∀ᵐ ω ∂P, condDistrib Y X P (X ω) = κ (X ω) :=
    ae_of_ae_map hX_meas.aemeasurable h_cond.condDistrib_eq
  have h_kernel_subG :
      ∀ z : (Iic (t - 1) → Fin K × ℝ) × Fin K,
        HasSubgaussianMGF id σ2 (κ z) := by
    intro z
    simpa [κ] using
      (RewardNoiseKernelSubgaussian.of_rewardNoiseSubgaussian
        (K := K) (ν := ν) hν).prodMkLeft z
  filter_upwards [h_ce, h_kernel_eq] with ω h_ceω hκω
  rw [h_ceω, hκω]
  simpa [X, Y, κ, mgf] using (h_kernel_subG (X ω)).mgf_le u

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Variance proxy for multiplying a subgaussian scalar by a deterministic coefficient. -/
def scalarProjectionVariance (σ2 : ℝ≥0) (q : ℝ) : ℝ≥0 :=
  ⟨q ^ 2, sq_nonneg q⟩ * σ2

/-- Conditional MGF bound for predictable scalar projections of positive-time LinUCB reward noise.

If `q` is a measurable function of the previous history and current selected action, then
`q(history, action) * η_t` is conditionally subgaussian given that same history/action information,
with variance proxy multiplied by `q(history, action)^2`.

The explicit integrability hypothesis is needed for this fully general statement because an
unbounded predictable coefficient does not automatically preserve global exponential
integrability. Bounded-coefficient corollaries can discharge that hypothesis separately. -/
lemma rewardNoise_constMul_ae_condExp_exp_le_history_action {alg : Algorithm (Fin K) ℝ}
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0)
    (q : (Iic (t - 1) → Fin K × ℝ) × Fin K → ℝ) (hq : Measurable q) (u : ℝ)
    (h_int :
      Integrable
        (fun ω ↦ Real.exp
          (u * (q (history A R (t - 1) ω, A t ω) *
            rewardNoise A R ν t ω))) P) :
    ∀ᵐ ω ∂P,
      P[fun ω' ↦ Real.exp
          (u * (q (history A R (t - 1) ω', A t ω') *
            rewardNoise A R ν t ω')) |
        (inferInstance : MeasurableSpace ((Iic (t - 1) → Fin K × ℝ) × Fin K)).comap
          (fun ω ↦ (history A R (t - 1) ω, A t ω))] ω
        ≤ Real.exp (scalarProjectionVariance σ2
            (q (history A R (t - 1) ω, A t ω)) * u ^ 2 / 2) := by
  let X : Ω → (Iic (t - 1) → Fin K × ℝ) × Fin K :=
    fun ω ↦ (history A R (t - 1) ω, A t ω)
  let Y : Ω → ℝ := rewardNoise A R ν t
  let κ : Kernel ((Iic (t - 1) → Fin K × ℝ) × Fin K) ℝ :=
    (rewardNoiseKernel ν).prodMkLeft (Iic (t - 1) → Fin K × ℝ)
  let f : ((Iic (t - 1) → Fin K × ℝ) × Fin K) × ℝ → ℝ :=
    fun p ↦ Real.exp (u * (q p.1 * p.2))
  have h_cond : HasCondDistrib Y X κ P := by
    simpa [X, Y, κ] using
      hasCondDistrib_rewardNoise_history_action (A := A) (R := R) (ν := ν) h ht
  have hX_meas : Measurable X := by
    dsimp [X]
    exact Measurable.prodMk
      ((h.measurable_history (t - 1)))
      (h.measurable_action t)
  have hY_ae : AEMeasurable Y P := h_cond.aemeasurable_snd
  have hf : StronglyMeasurable f := by
    dsimp [f]
    fun_prop
  have h_ce :
      P[fun ω ↦ f (X ω, Y ω) |
        (inferInstance : MeasurableSpace ((Iic (t - 1) → Fin K × ℝ) × Fin K)).comap X]
        =ᵐ[P] fun ω ↦ ∫ η, f (X ω, η) ∂condDistrib Y X P (X ω) := by
    exact condExp_prod_ae_eq_integral_condDistrib (μ := P) (X := X) (Y := Y)
      hX_meas hY_ae hf (by simpa [X, Y, f] using h_int)
  have h_kernel_eq : ∀ᵐ ω ∂P, condDistrib Y X P (X ω) = κ (X ω) :=
    ae_of_ae_map hX_meas.aemeasurable h_cond.condDistrib_eq
  have h_kernel_subG :
      ∀ z : (Iic (t - 1) → Fin K × ℝ) × Fin K,
        HasSubgaussianMGF (fun η ↦ q z * η) (scalarProjectionVariance σ2 (q z)) (κ z) := by
    intro z
    simpa [scalarProjectionVariance, κ] using
      (RewardNoiseKernelSubgaussian.of_rewardNoiseSubgaussian
        (K := K) (ν := ν) hν).prodMkLeft_constMul q z
  filter_upwards [h_ce, h_kernel_eq] with ω h_ceω hκω
  rw [h_ceω, hκω]
  simpa [X, Y, κ, f, mgf] using (h_kernel_subG (X ω)).mgf_le u

/-- Conditional exponential-supermartingale one-step bound with the realized predictable variance.

This is the local scalar ingredient needed by the textbook self-normalized LinUCB proof. Unlike
the later `HasCondSubgaussianMGF` wrappers, it does not replace the predictable coefficient
`q(history, action)` by a uniform deterministic bound. The variance penalty remains the realized
quantity `q(history, action)^2 * σ2`. -/
lemma rewardNoise_constMul_ae_condExp_exp_sub_realizedVariance_le_one
    {alg : Algorithm (Fin K) ℝ}
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0)
    (q : (Iic (t - 1) → Fin K × ℝ) × Fin K → ℝ) (hq : Measurable q) (u : ℝ)
    (h_int :
      Integrable
        (fun ω ↦ Real.exp
          (u * (q (history A R (t - 1) ω, A t ω) *
            rewardNoise A R ν t ω))) P) :
    ∀ᵐ ω ∂P,
      P[fun ω' ↦ Real.exp
          (u * (q (history A R (t - 1) ω', A t ω') *
              rewardNoise A R ν t ω') -
            scalarProjectionVariance σ2
              (q (history A R (t - 1) ω', A t ω')) * u ^ 2 / 2) |
        (inferInstance : MeasurableSpace ((Iic (t - 1) → Fin K × ℝ) × Fin K)).comap
          (fun ω ↦ (history A R (t - 1) ω, A t ω))] ω
        ≤ 1 := by
  let X : Ω → (Iic (t - 1) → Fin K × ℝ) × Fin K :=
    fun ω ↦ (history A R (t - 1) ω, A t ω)
  let Y : Ω → ℝ := rewardNoise A R ν t
  let κ : Kernel ((Iic (t - 1) → Fin K × ℝ) × Fin K) ℝ :=
    (rewardNoiseKernel ν).prodMkLeft (Iic (t - 1) → Fin K × ℝ)
  let f : ((Iic (t - 1) → Fin K × ℝ) × Fin K) × ℝ → ℝ :=
    fun p ↦ Real.exp
      (u * (q p.1 * p.2) - scalarProjectionVariance σ2 (q p.1) * u ^ 2 / 2)
  have h_cond : HasCondDistrib Y X κ P := by
    simpa [X, Y, κ] using
      hasCondDistrib_rewardNoise_history_action (A := A) (R := R) (ν := ν) h ht
  have hX_meas : Measurable X := by
    dsimp [X]
    exact Measurable.prodMk
      ((h.measurable_history (t - 1)))
      (h.measurable_action t)
  have hY_ae : AEMeasurable Y P := h_cond.aemeasurable_snd
  have hf_meas : Measurable f := by
    dsimp [f]
    simp only [scalarProjectionVariance, NNReal.coe_mul]
    fun_prop
  have hf : StronglyMeasurable f := hf_meas.stronglyMeasurable
  have h_int_sub : Integrable (fun ω ↦ f (X ω, Y ω)) P := by
    have h_target :
        AEStronglyMeasurable (fun ω ↦ f (X ω, Y ω)) P := by
      exact (hf_meas.comp_aemeasurable (hX_meas.aemeasurable.prodMk hY_ae)).aestronglyMeasurable
    refine Integrable.mono h_int h_target ?_
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    have hvar_nonneg :
        0 ≤ (scalarProjectionVariance σ2 (q (X ω)) : ℝ) * u ^ 2 / 2 := by
      positivity
    simp only [f, X, Y, Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr (by linarith)
  have h_ce :
      P[fun ω ↦ f (X ω, Y ω) |
        (inferInstance : MeasurableSpace ((Iic (t - 1) → Fin K × ℝ) × Fin K)).comap X]
        =ᵐ[P] fun ω ↦ ∫ η, f (X ω, η) ∂condDistrib Y X P (X ω) := by
    exact condExp_prod_ae_eq_integral_condDistrib (μ := P) (X := X) (Y := Y)
      hX_meas hY_ae hf h_int_sub
  have h_kernel_eq : ∀ᵐ ω ∂P, condDistrib Y X P (X ω) = κ (X ω) :=
    ae_of_ae_map hX_meas.aemeasurable h_cond.condDistrib_eq
  have h_kernel_subG :
      ∀ z : (Iic (t - 1) → Fin K × ℝ) × Fin K,
        HasSubgaussianMGF (fun η ↦ q z * η) (scalarProjectionVariance σ2 (q z)) (κ z) := by
    intro z
    simpa [scalarProjectionVariance, κ] using
      (RewardNoiseKernelSubgaussian.of_rewardNoiseSubgaussian
        (K := K) (ν := ν) hν).prodMkLeft_constMul q z
  filter_upwards [h_ce, h_kernel_eq] with ω h_ceω hκω
  rw [h_ceω, hκω]
  let z : (Iic (t - 1) → Fin K × ℝ) × Fin K := X ω
  let c : ℝ := (scalarProjectionVariance σ2 (q z) : ℝ) * u ^ 2 / 2
  have h_int_mgf : Integrable (fun η ↦ Real.exp (u * (q z * η))) (κ z) :=
    (h_kernel_subG z).integrable_exp_mul u
  have h_integral_eq :
      (∫ η, f (X ω, η) ∂κ (X ω)) =
        (∫ η, Real.exp (u * (q z * η)) ∂κ z) / Real.exp c := by
    simp only [z, c, f]
    simp_rw [Real.exp_sub]
    rw [MeasureTheory.integral_div]
  have h_mgf_le :
      (∫ η, Real.exp (u * (q z * η)) ∂κ z) ≤ Real.exp c := by
    simpa [mgf, c] using (h_kernel_subG z).mgf_le u
  calc
    (∫ η, f (X ω, η) ∂κ (X ω))
        = (∫ η, Real.exp (u * (q z * η)) ∂κ z) / Real.exp c := h_integral_eq
    _ ≤ Real.exp c / Real.exp c :=
        div_le_div_of_nonneg_right h_mgf_le (le_of_lt (Real.exp_pos c))
    _ = 1 := by
        exact div_self (Real.exp_ne_zero c)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If an event is measurable in a smaller sigma-algebra, then a `μ`-a.e. proof of the event can
be viewed as a `μ.trim hm`-a.e. proof.

This is a small measure-theory bridge used below to package conditional expectation bounds into
Mathlib's `HasCondSubgaussianMGF`, whose MGF bound is stated over the trimmed conditioning
measure. -/
lemma ae_trim_of_ae_of_measurableSet (μ : Measure Ω) {m' : MeasurableSpace Ω} (hm' : m' ≤ mΩ)
    {p : Ω → Prop} (hp : @MeasurableSet Ω m' {ω | p ω}) (hμ : ∀ᵐ ω ∂μ, p ω) :
    ∀ᵐ ω ∂μ.trim hm', p ω := by
  rw [ae_iff] at hμ ⊢
  have hp_compl : @MeasurableSet Ω m' {ω | ¬ p ω} := by
    simpa only [Set.compl_setOf] using hp.compl
  rw [trim_measurableSet_eq hm' hp_compl]
  exact hμ

/-- Positive-time LinUCB reward noise is conditionally subgaussian with respect to the filtration
generated by the previous history and the current selected action.

This repackages `rewardNoise_ae_condExp_exp_le_history_action` into Mathlib's
`HasCondSubgaussianMGF` API, which is the API used by the existing martingale-sum concentration
lemmas. -/
lemma rewardNoise_hasCondSubgaussianMGF_filtrationAction {alg : Algorithm (Fin K) ℝ}
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0) :
    HasCondSubgaussianMGF
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback t)
      ((IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback).le t)
      (rewardNoise A R ν t) σ2 P := by
  let ℱ := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback
  let mX : MeasurableSpace Ω := ℱ t
  have hmX : mX ≤ mΩ := ℱ.le t
  let Y : Ω → ℝ := rewardNoise A R ν t
  change Kernel.HasSubgaussianMGF Y σ2
    (@condExpKernel Ω mΩ _ P _ mX) (@Measure.trim Ω mX mΩ P hmX)
  refine Kernel.HasSubgaussianMGF.of_rat (X := Y) (c := σ2)
    (κ := @condExpKernel Ω mΩ _ P _ mX) (ν := @Measure.trim Ω mX mΩ P hmX) ?_ ?_
  · intro u
    rw [condExpKernel_comp_trim (Ω := Ω) (m := mX) (mΩ := mΩ) (μ := P) hmX]
    simpa [Y] using
      rewardNoise_integrable_exp_mul_history_action (A := A) (R := R) (ν := ν) h hν ht u
  · intro q
    let u : ℝ := q
    have h_int : Integrable (fun ω ↦ Real.exp (u * Y ω)) P := by
      simpa [Y] using
        rewardNoise_integrable_exp_mul_history_action (A := A) (R := R) (ν := ν) h hν ht u
    have h_condExp_eq :
        P[fun ω ↦ Real.exp (u * Y ω) | mX]
          =ᵐ[P.trim hmX] fun ω ↦
            ∫ y, Real.exp (u * Y y) ∂(@condExpKernel Ω mΩ _ P _ mX) ω := by
      exact condExp_ae_eq_trim_integral_condExpKernel (Ω := Ω) (m := mX)
        (mΩ := mΩ) (μ := P) hmX h_int
    have h_condExp_le_P :
        ∀ᵐ ω ∂P,
          P[fun ω' ↦ Real.exp (u * Y ω') | mX] ω ≤ Real.exp (σ2 * u ^ 2 / 2) := by
      have h_le := rewardNoise_ae_condExp_exp_le_history_action (A := A) (R := R)
        (ν := ν) h hν ht u
      simpa [Y, mX, ℱ, u, IsAlgEnvSeq.filtrationAction_eq_comap
        (A := A) (Y := R) t ht] using h_le
    have h_event_meas :
        @MeasurableSet Ω mX
          {ω | P[fun ω' ↦ Real.exp (u * Y ω') | mX] ω ≤ Real.exp (σ2 * u ^ 2 / 2)} := by
      exact measurableSet_le stronglyMeasurable_condExp.measurable measurable_const
    have h_condExp_le_trim :
        ∀ᵐ ω ∂P.trim hmX,
          P[fun ω' ↦ Real.exp (u * Y ω') | mX] ω ≤ Real.exp (σ2 * u ^ 2 / 2) :=
      ae_trim_of_ae_of_measurableSet P hmX h_event_meas h_condExp_le_P
    filter_upwards [h_condExp_eq, h_condExp_le_trim] with ω h_eq h_le
    change (∫ y, Real.exp (u * Y y) ∂(@condExpKernel Ω mΩ _ P _ mX) ω) ≤
      Real.exp (σ2 * u ^ 2 / 2)
    rw [← h_eq]
    exact h_le

/-- Bounded predictable scalar coefficients preserve exponential integrability of the projected
reward noise.

If `|q(history, action)| ≤ Q`, then `exp (u * q_t * η_t)` is dominated by
`exp (|u| Q * η_t) + exp (-|u| Q * η_t)`, and both endpoint exponentials are integrable by the
arm-wise reward-noise subgaussian assumption. -/
lemma rewardNoise_constMul_integrable_exp_mul_history_action_of_abs_le
    {alg : Algorithm (Fin K) ℝ}
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0)
    (q : (Iic (t - 1) → Fin K × ℝ) × Fin K → ℝ) (hq : Measurable q)
    (Q : ℝ) (hQ : 0 ≤ Q) (hq_bound : ∀ z, |q z| ≤ Q) (u : ℝ) :
    Integrable
      (fun ω ↦ Real.exp
        (u * (q (history A R (t - 1) ω, A t ω) *
          rewardNoise A R ν t ω))) P := by
  let X : Ω → (Iic (t - 1) → Fin K × ℝ) × Fin K :=
    fun ω ↦ (history A R (t - 1) ω, A t ω)
  let Y : Ω → ℝ := rewardNoise A R ν t
  let c : ℝ := |u| * Q
  have hX_meas : Measurable X := by
    dsimp [X]
    exact Measurable.prodMk
      ((h.measurable_history (t - 1)))
      (h.measurable_action t)
  have hY_meas : Measurable Y := by
    dsimp [Y, rewardNoise]
    exact (h.measurable_feedback t).sub ((measurable_rewardMean ν).comp (h.measurable_action t))
  have h_target :
      AEStronglyMeasurable
        (fun ω ↦ Real.exp (u * (q (X ω) * Y ω))) P := by
    exact (measurable_exp.comp
      (measurable_const.mul (((hq.comp hX_meas).mul hY_meas)))).aestronglyMeasurable
  have h_pos : Integrable (fun ω ↦ Real.exp (c * Y ω)) P := by
    simpa [Y, c] using
      rewardNoise_integrable_exp_mul_history_action (A := A) (R := R) (ν := ν) h hν ht c
  have h_neg : Integrable (fun ω ↦ Real.exp ((-c) * Y ω)) P := by
    simpa [Y, c] using
      rewardNoise_integrable_exp_mul_history_action (A := A) (R := R) (ν := ν) h hν ht (-c)
  refine Integrable.mono (h_pos.add h_neg) h_target ?_
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  have hc_nonneg : 0 ≤ c := mul_nonneg (abs_nonneg u) hQ
  have harg_abs :
      |u * (q (X ω) * Y ω)| ≤ |c * Y ω| := by
    calc
      |u * (q (X ω) * Y ω)|
          = |u| * |q (X ω)| * |Y ω| := by
              rw [abs_mul, abs_mul, mul_assoc]
      _ ≤ |u| * Q * |Y ω| := by
              gcongr
              exact hq_bound (X ω)
      _ = |c * Y ω| := by
              rw [abs_mul, abs_of_nonneg hc_nonneg]
  have harg_le_abs : u * (q (X ω) * Y ω) ≤ |c * Y ω| :=
    (le_abs_self _).trans harg_abs
  calc
    ‖Real.exp (u * (q (X ω) * Y ω))‖
        = Real.exp (u * (q (X ω) * Y ω)) := Real.norm_of_nonneg (Real.exp_nonneg _)
    _ ≤ Real.exp |c * Y ω| := Real.exp_le_exp.mpr harg_le_abs
    _ ≤ Real.exp (c * Y ω) + Real.exp ((-c) * Y ω) := by
        simpa [neg_mul] using Real.exp_abs_le (c * Y ω)
    _ = ‖((fun ω ↦ Real.exp (c * Y ω)) + fun ω ↦ Real.exp ((-c) * Y ω)) ω‖ := by
        rw [Pi.add_apply, Real.norm_of_nonneg]
        positivity

/-- Bounded predictable scalar projections of positive-time LinUCB reward noise are conditionally
subgaussian in Mathlib's standard `HasCondSubgaussianMGF` API.

The coefficient `q` may depend on the previous history and current selected action. If its scaled
variance proxy `q^2 * σ2` is bounded by a deterministic `c`, and the projected exponentials are
integrable, then the projected noise process is conditionally subgaussian with parameter `c`.

The remaining explicit integrability assumption is the only extra analytic side condition in this
wrapper. It is unavoidable at this level of generality for unbounded predictable coefficients. -/
lemma rewardNoise_constMul_hasCondSubgaussianMGF_filtrationAction_of_integrable
    {alg : Algorithm (Fin K) ℝ}
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 c : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0)
    (q : (Iic (t - 1) → Fin K × ℝ) × Fin K → ℝ) (hq : Measurable q)
    (hc : ∀ z, scalarProjectionVariance σ2 (q z) ≤ c)
    (h_int : ∀ u : ℝ,
      Integrable
        (fun ω ↦ Real.exp
          (u * (q (history A R (t - 1) ω, A t ω) *
            rewardNoise A R ν t ω))) P) :
    HasCondSubgaussianMGF
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback t)
      ((IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback).le t)
      (fun ω ↦ q (history A R (t - 1) ω, A t ω) *
        rewardNoise A R ν t ω)
      c P := by
  let ℱ := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback
  let mX : MeasurableSpace Ω := ℱ t
  have hmX : mX ≤ mΩ := ℱ.le t
  let X : Ω → (Iic (t - 1) → Fin K × ℝ) × Fin K :=
    fun ω ↦ (history A R (t - 1) ω, A t ω)
  let Z : Ω → ℝ := fun ω ↦ q (X ω) * rewardNoise A R ν t ω
  change Kernel.HasSubgaussianMGF Z c
    (@condExpKernel Ω mΩ _ P _ mX) (@Measure.trim Ω mX mΩ P hmX)
  refine Kernel.HasSubgaussianMGF.of_rat (X := Z) (c := c)
    (κ := @condExpKernel Ω mΩ _ P _ mX) (ν := @Measure.trim Ω mX mΩ P hmX) ?_ ?_
  · intro u
    rw [condExpKernel_comp_trim (Ω := Ω) (m := mX) (mΩ := mΩ) (μ := P) hmX]
    simpa [X, Z] using h_int u
  · intro r
    let u : ℝ := r
    have h_int_u : Integrable (fun ω ↦ Real.exp (u * Z ω)) P := by
      simpa [X, Z] using h_int u
    have h_condExp_eq :
        P[fun ω ↦ Real.exp (u * Z ω) | mX]
          =ᵐ[P.trim hmX] fun ω ↦
            ∫ y, Real.exp (u * Z y) ∂(@condExpKernel Ω mΩ _ P _ mX) ω := by
      exact condExp_ae_eq_trim_integral_condExpKernel (Ω := Ω) (m := mX)
        (mΩ := mΩ) (μ := P) hmX h_int_u
    have h_condExp_le_P :
        ∀ᵐ ω ∂P,
          P[fun ω' ↦ Real.exp (u * Z ω') | mX] ω ≤ Real.exp (c * u ^ 2 / 2) := by
      have h_le :
          ∀ᵐ ω ∂P,
            P[fun ω' ↦ Real.exp (u * Z ω') | mX] ω ≤
              Real.exp (scalarProjectionVariance σ2 (q (X ω)) * u ^ 2 / 2) := by
        simpa [X, Z, mX, ℱ, IsAlgEnvSeq.filtrationAction_eq_comap
          (A := A) (Y := R) t ht] using
          rewardNoise_constMul_ae_condExp_exp_le_history_action
            (A := A) (R := R) (ν := ν) h hν ht q hq u (by simpa [X, Z] using h_int_u)
      filter_upwards [h_le] with ω hω
      refine hω.trans ?_
      have hcω : (scalarProjectionVariance σ2 (q (X ω)) : ℝ) ≤ (c : ℝ) := by
        exact_mod_cast hc (X ω)
      gcongr
    have h_event_meas :
        @MeasurableSet Ω mX
          {ω | P[fun ω' ↦ Real.exp (u * Z ω') | mX] ω ≤ Real.exp (c * u ^ 2 / 2)} := by
      exact measurableSet_le stronglyMeasurable_condExp.measurable measurable_const
    have h_condExp_le_trim :
        ∀ᵐ ω ∂P.trim hmX,
          P[fun ω' ↦ Real.exp (u * Z ω') | mX] ω ≤ Real.exp (c * u ^ 2 / 2) :=
      ae_trim_of_ae_of_measurableSet P hmX h_event_meas h_condExp_le_P
    filter_upwards [h_condExp_eq, h_condExp_le_trim] with ω h_eq h_le
    change (∫ y, Real.exp (u * Z y) ∂(@condExpKernel Ω mΩ _ P _ mX) ω) ≤
      Real.exp (c * u ^ 2 / 2)
    rw [← h_eq]
    exact h_le

/-- Bounded predictable scalar projections of positive-time LinUCB reward noise are conditionally
subgaussian without any separate integrability hypothesis.

This is the bounded-coefficient version of
`rewardNoise_constMul_hasCondSubgaussianMGF_filtrationAction_of_integrable`. If
`|q(history, action)| ≤ Q`, then the variance proxy is bounded by `Q^2 * σ2`, and exponential
integrability follows from the arm-wise reward-noise subgaussian assumption. -/
lemma rewardNoise_constMul_hasCondSubgaussianMGF_filtrationAction_of_abs_le
    {alg : Algorithm (Fin K) ℝ}
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0)
    (q : (Iic (t - 1) → Fin K × ℝ) × Fin K → ℝ) (hq : Measurable q)
    (Q : ℝ) (hQ : 0 ≤ Q) (hq_bound : ∀ z, |q z| ≤ Q) :
    HasCondSubgaussianMGF
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback t)
      ((IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback).le t)
      (fun ω ↦ q (history A R (t - 1) ω, A t ω) *
        rewardNoise A R ν t ω)
      (⟨Q ^ 2, sq_nonneg Q⟩ * σ2) P := by
  refine rewardNoise_constMul_hasCondSubgaussianMGF_filtrationAction_of_integrable
    (A := A) (R := R) (ν := ν) h hν ht q hq ?_ ?_
  · intro z
    dsimp [scalarProjectionVariance]
    gcongr
    have hQ_le_abs : Q ≤ |Q| := by
      rw [abs_of_nonneg hQ]
    exact sq_le_sq.2 ((hq_bound z).trans hQ_le_abs)
  · intro u
    exact rewardNoise_constMul_integrable_exp_mul_history_action_of_abs_le
      (A := A) (R := R) (ν := ν) h hν ht q hq Q hQ hq_bound u

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A fixed-direction scalar projection of the LinUCB reward-feature noise.

For positive time `t`, this is
`⟪v, x_{A_t}⟫ * η_t`, where `η_t = R_t - μ(A_t)`. The `t = 0` value is set to zero because the
repository's algorithm/environment sequence gives the clean history/action conditional law for
positive times. -/
noncomputable def projectedRewardFeatureNoise
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (ν : Kernel (Fin K) ℝ)
    (x : Fin K → Feature d) (v : Feature d) (t : ℕ) (ω : Ω) : ℝ :=
  if t = 0 then 0 else dotProduct v (x (A t ω)) * rewardNoise A R ν t ω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Realized variance proxy of the fixed-direction positive-time reward-feature noise.

At positive time `t`, this is `σ2 * ⟪v, x_{A_t}⟫²`. The time-zero value is set to zero to match
`projectedRewardFeatureNoise`, which also omits time zero from the positive-time martingale route.
-/
noncomputable def projectedRewardFeatureNoiseRealizedVariance
    (A : ℕ → Ω → Fin K) (σ2 : ℝ≥0)
    (x : Fin K → Feature d) (v : Feature d) (t : ℕ) (ω : Ω) : ℝ :=
  if t = 0 then 0 else (scalarProjectionVariance σ2 (dotProduct v (x (A t ω))) : ℝ)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Exponential-supermartingale increment for a fixed direction of LinUCB reward-feature noise.

This is `exp(u Y_t - u² V_t / 2)`, where `Y_t` is the fixed-direction projected noise and `V_t`
is its realized subgaussian variance proxy. -/
noncomputable def projectedRewardFeatureNoiseExpIncrement
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (ν : Kernel (Fin K) ℝ)
    (σ2 : ℝ≥0) (x : Fin K → Feature d) (v : Feature d) (u : ℝ)
    (t : ℕ) (ω : Ω) : ℝ :=
  Real.exp
    (u * projectedRewardFeatureNoise A R ν x v t ω -
      projectedRewardFeatureNoiseRealizedVariance A σ2 x v t ω * u ^ 2 / 2)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Cumulative realized variance proxy for a fixed direction of LinUCB reward-feature noise. -/
noncomputable def projectedRewardFeatureNoiseRealizedVarianceSum
    (A : ℕ → Ω → Fin K) (σ2 : ℝ≥0)
    (x : Fin K → Feature d) (v : Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ range n, projectedRewardFeatureNoiseRealizedVariance A σ2 x v t ω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Finite-horizon fixed-direction exponential process with realized variance.

This is the scalar process
`exp(u * ∑_{t<n} Y_t - u² / 2 * ∑_{t<n} V_t)` that the textbook self-normalized proof later
mixes over Gaussian directions. -/
noncomputable def projectedRewardFeatureNoiseExpProcess
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (ν : Kernel (Fin K) ℝ)
    (σ2 : ℝ≥0) (x : Fin K → Feature d) (v : Feature d) (u : ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp
    (u * (∑ t ∈ range n, projectedRewardFeatureNoise A R ν x v t ω) -
      projectedRewardFeatureNoiseRealizedVarianceSum A σ2 x v n ω * u ^ 2 / 2)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Filtration used to view positive-time projected reward-feature noises as a scalar martingale
difference sequence.

At index `i`, this is the repository's `filtrationAction` at time `i + 1`: it contains the full
history through time `i` and the already selected action at time `i + 1`. Therefore the random
variable at time `i + 1` is conditionally subgaussian with respect to this sigma-algebra. -/
def postActionFiltration
    (hA : ∀ n, Measurable (A n)) (hR : ∀ n, Measurable (R n)) :
    Filtration ℕ mΩ where
  seq i := IsAlgEnvSeq.filtrationAction hA hR (i + 1)
  mono' i j hij := by
    exact (IsAlgEnvSeq.filtrationAction hA hR).mono (Nat.succ_le_succ hij)
  le' i := (IsAlgEnvSeq.filtrationAction hA hR).le (i + 1)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The usual history filtration through time `i` is contained in `postActionFiltration i`. -/
lemma filtration_le_postActionFiltration
    (hA : ∀ n, Measurable (A n)) (hR : ∀ n, Measurable (R n)) (i : ℕ) :
    IsAlgEnvSeq.filtration hA hR i ≤ postActionFiltration (A := A) (R := R) hA hR i := by
  simp [postActionFiltration, IsAlgEnvSeq.filtrationAction]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The fixed-direction projected reward-feature noise is zero at time zero. -/
lemma projectedRewardFeatureNoise_zero (v : Feature d) :
    projectedRewardFeatureNoise A R ν x v 0 ω = 0 := by
  simp [projectedRewardFeatureNoise]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The realized variance proxy is zero at time zero. -/
lemma projectedRewardFeatureNoiseRealizedVariance_zero (σ2 : ℝ≥0) (v : Feature d) :
    projectedRewardFeatureNoiseRealizedVariance A σ2 x v 0 ω = 0 := by
  simp [projectedRewardFeatureNoiseRealizedVariance]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The fixed-direction realized variance proxy is nonnegative. -/
lemma projectedRewardFeatureNoiseRealizedVariance_nonneg (σ2 : ℝ≥0) (v : Feature d)
    (t : ℕ) :
    0 ≤ projectedRewardFeatureNoiseRealizedVariance A σ2 x v t ω := by
  by_cases ht : t = 0
  · simp [projectedRewardFeatureNoiseRealizedVariance, ht]
  · simp [projectedRewardFeatureNoiseRealizedVariance, ht]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The cumulative fixed-direction realized variance proxy is nonnegative. -/
lemma projectedRewardFeatureNoiseRealizedVarianceSum_nonneg (σ2 : ℝ≥0) (v : Feature d)
    (n : ℕ) :
    0 ≤ projectedRewardFeatureNoiseRealizedVarianceSum A σ2 x v n ω := by
  rw [projectedRewardFeatureNoiseRealizedVarianceSum]
  exact sum_nonneg fun t _ht ↦
    projectedRewardFeatureNoiseRealizedVariance_nonneg (A := A) (σ2 := σ2)
      (x := x) (v := v) (t := t) (ω := ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The fixed-direction exponential increment is one at time zero. -/
lemma projectedRewardFeatureNoiseExpIncrement_zero (σ2 : ℝ≥0) (v : Feature d) (u : ℝ) :
    projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u 0 ω = 1 := by
  simp [projectedRewardFeatureNoiseExpIncrement, projectedRewardFeatureNoise_zero,
    projectedRewardFeatureNoiseRealizedVariance_zero]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Exponential increments are nonnegative. -/
lemma projectedRewardFeatureNoiseExpIncrement_nonneg (σ2 : ℝ≥0) (v : Feature d) (u : ℝ)
    (t : ℕ) :
    0 ≤ projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω := by
  exact Real.exp_nonneg _

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The finite-horizon exponential process starts at one. -/
lemma projectedRewardFeatureNoiseExpProcess_zero (σ2 : ℝ≥0) (v : Feature d) (u : ℝ) :
    projectedRewardFeatureNoiseExpProcess A R ν σ2 x v u 0 ω = 1 := by
  simp [projectedRewardFeatureNoiseExpProcess, projectedRewardFeatureNoiseRealizedVarianceSum]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The finite-horizon exponential process is nonnegative. -/
lemma projectedRewardFeatureNoiseExpProcess_nonneg (σ2 : ℝ≥0) (v : Feature d) (u : ℝ)
    (n : ℕ) :
    0 ≤ projectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω := by
  exact Real.exp_nonneg _

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The fixed-direction exponential process factors into the previous process times the next
realized-variance exponential increment. -/
lemma projectedRewardFeatureNoiseExpProcess_succ (σ2 : ℝ≥0) (v : Feature d) (u : ℝ)
    (n : ℕ) :
    projectedRewardFeatureNoiseExpProcess A R ν σ2 x v u (n + 1) ω =
      projectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω *
        projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω := by
  simp only [projectedRewardFeatureNoiseExpProcess, projectedRewardFeatureNoiseExpIncrement,
    projectedRewardFeatureNoiseRealizedVarianceSum, sum_range_succ]
  rw [← Real.exp_add]
  congr 1
  ring

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The finite-horizon exponential process is still one at horizon one, because the positive-time
process deliberately sets the time-zero reward-feature noise and variance to zero. -/
lemma projectedRewardFeatureNoiseExpProcess_one (σ2 : ℝ≥0) (v : Feature d) (u : ℝ) :
    projectedRewardFeatureNoiseExpProcess A R ν σ2 x v u 1 ω = 1 := by
  simpa [projectedRewardFeatureNoiseExpProcess_zero, projectedRewardFeatureNoiseExpIncrement_zero]
    using projectedRewardFeatureNoiseExpProcess_succ (A := A) (R := R) (ν := ν)
      (σ2 := σ2) (x := x) (v := v) (u := u) (n := 0) (ω := ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- At positive times, the fixed-direction projected reward-feature noise is the predictable
coefficient `⟪v, x_{A_t}⟫` times the centered reward noise. -/
lemma projectedRewardFeatureNoise_eq_of_ne_zero (v : Feature d) {t : ℕ} (ht : t ≠ 0) :
    projectedRewardFeatureNoise A R ν x v t ω =
      dotProduct v (x (A t ω)) * rewardNoise A R ν t ω := by
  simp [projectedRewardFeatureNoise, ht]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- At positive times, the realized variance proxy is the squared predictable projection times the
reward-noise variance proxy. -/
lemma projectedRewardFeatureNoiseRealizedVariance_eq_of_ne_zero
    (σ2 : ℝ≥0) (v : Feature d) {t : ℕ} (ht : t ≠ 0) :
    projectedRewardFeatureNoiseRealizedVariance A σ2 x v t ω =
      (scalarProjectionVariance σ2 (dotProduct v (x (A t ω))) : ℝ) := by
  simp [projectedRewardFeatureNoiseRealizedVariance, ht]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The predictable coefficient for a fixed feature direction is measurable as a function of the
history/action conditioning variable. -/
lemma measurable_projectedRewardFeatureCoeff
    (v : Feature d) {t : ℕ} :
    Measurable
      (fun z : (Iic (t - 1) → Fin K × ℝ) × Fin K ↦ dotProduct v (x z.2)) :=
  (measurable_of_countable (fun a : Fin K ↦ dotProduct v (x a))).comp measurable_snd

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The fixed-direction projected reward-feature noise is adapted to `postActionFiltration`. -/
lemma stronglyAdapted_projectedRewardFeatureNoise_postActionFiltration
    (hA : ∀ n, Measurable (A n)) (hR : ∀ n, Measurable (R n))
    (v : Feature d) :
    StronglyAdapted (postActionFiltration (A := A) (R := R) hA hR)
      (projectedRewardFeatureNoise A R ν x v) := by
  intro t
  by_cases ht : t = 0
  · have hY0 : projectedRewardFeatureNoise A R ν x v t = fun _ : Ω ↦ (0 : ℝ) := by
      funext ω
      simp [projectedRewardFeatureNoise, ht]
    rw [hY0]
    exact
      (stronglyMeasurable_const :
        StronglyMeasurable[postActionFiltration (A := A) (R := R) hA hR t]
          (fun _ : Ω ↦ (0 : ℝ)))
  · have hfil_le :
        IsAlgEnvSeq.filtration hA hR t ≤ postActionFiltration (A := A) (R := R) hA hR t :=
      filtration_le_postActionFiltration (A := A) (R := R) hA hR t
    have hA_t : Measurable[postActionFiltration (A := A) (R := R) hA hR t] (A t) :=
      (IsAlgEnvSeq.adapted_action hA hR t).mono hfil_le le_rfl
    have hR_t : Measurable[postActionFiltration (A := A) (R := R) hA hR t] (R t) :=
      (IsAlgEnvSeq.adapted_feedback hA hR t).mono hfil_le le_rfl
    have hη_t :
        Measurable[postActionFiltration (A := A) (R := R) hA hR t]
          (rewardNoise A R ν t) := by
      change Measurable[postActionFiltration (A := A) (R := R) hA hR t]
        (fun ω ↦ R t ω - (ν (A t ω))[id])
      exact hR_t.sub ((measurable_rewardMean ν).comp hA_t)
    have hq_t :
        Measurable[postActionFiltration (A := A) (R := R) hA hR t]
          (fun ω ↦ dotProduct v (x (A t ω))) :=
      (measurable_of_countable (fun a : Fin K ↦ dotProduct v (x a))).comp hA_t
    rw [show projectedRewardFeatureNoise A R ν x v t =
        fun ω ↦ dotProduct v (x (A t ω)) * rewardNoise A R ν t ω by
      funext ω
      simp [projectedRewardFeatureNoise, ht]]
    exact (hq_t.mul hη_t).stronglyMeasurable

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The fixed-direction realized variance proxy is adapted to `postActionFiltration`. -/
lemma stronglyAdapted_projectedRewardFeatureNoiseRealizedVariance_postActionFiltration
    (hA : ∀ n, Measurable (A n)) (hR : ∀ n, Measurable (R n))
    (σ2 : ℝ≥0) (v : Feature d) :
    StronglyAdapted (postActionFiltration (A := A) (R := R) hA hR)
      (projectedRewardFeatureNoiseRealizedVariance A σ2 x v) := by
  intro t
  by_cases ht : t = 0
  · have hV0 :
        projectedRewardFeatureNoiseRealizedVariance A σ2 x v t = fun _ : Ω ↦ (0 : ℝ) := by
      funext ω
      simp [projectedRewardFeatureNoiseRealizedVariance, ht]
    rw [hV0]
    exact
      (stronglyMeasurable_const :
        StronglyMeasurable[postActionFiltration (A := A) (R := R) hA hR t]
          (fun _ : Ω ↦ (0 : ℝ)))
  · have hfil_le :
        IsAlgEnvSeq.filtration hA hR t ≤ postActionFiltration (A := A) (R := R) hA hR t :=
      filtration_le_postActionFiltration (A := A) (R := R) hA hR t
    have hA_t : Measurable[postActionFiltration (A := A) (R := R) hA hR t] (A t) :=
      (IsAlgEnvSeq.adapted_action hA hR t).mono hfil_le le_rfl
    have hvar_t :
        Measurable[postActionFiltration (A := A) (R := R) hA hR t]
          (fun ω ↦ (scalarProjectionVariance σ2 (dotProduct v (x (A t ω))) : ℝ)) :=
      (measurable_of_countable
        (fun a : Fin K ↦ (scalarProjectionVariance σ2 (dotProduct v (x a)) : ℝ))).comp hA_t
    rw [show projectedRewardFeatureNoiseRealizedVariance A σ2 x v t =
        fun ω ↦ (scalarProjectionVariance σ2 (dotProduct v (x (A t ω))) : ℝ) by
      funext ω
      simp [projectedRewardFeatureNoiseRealizedVariance, ht]]
    exact hvar_t.stronglyMeasurable

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The fixed-direction exponential process up to a positive horizon is measurable with respect to
the post-action sigma-algebra at the previous time. -/
lemma stronglyMeasurable_projectedRewardFeatureNoiseExpProcess_postActionFiltration_pred
    (hA : ∀ n, Measurable (A n)) (hR : ∀ n, Measurable (R n))
    (σ2 : ℝ≥0) (v : Feature d) (u : ℝ) (n : ℕ) :
    StronglyMeasurable[postActionFiltration (A := A) (R := R) hA hR (n - 1)]
      (fun ω ↦ projectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω) := by
  let ℱ := postActionFiltration (A := A) (R := R) hA hR
  have hY_adapt : StronglyAdapted ℱ (projectedRewardFeatureNoise A R ν x v) := by
    simpa [ℱ] using
      stronglyAdapted_projectedRewardFeatureNoise_postActionFiltration
        (A := A) (R := R) (ν := ν) (x := x) hA hR v
  have hV_adapt : StronglyAdapted ℱ (projectedRewardFeatureNoiseRealizedVariance A σ2 x v) := by
    simpa [ℱ] using
      stronglyAdapted_projectedRewardFeatureNoiseRealizedVariance_postActionFiltration
        (A := A) (R := R) (x := x) hA hR σ2 v
  have hY_sum :
      Measurable[ℱ (n - 1)]
        (fun ω ↦ ∑ t ∈ range n, projectedRewardFeatureNoise A R ν x v t ω) := by
    refine Finset.measurable_fun_sum (range n) ?_
    intro t ht
    have ht_le : t ≤ n - 1 := by
      exact Nat.le_pred_of_lt (by simpa using ht)
    exact ((hY_adapt t).mono (ℱ.mono ht_le)).measurable
  have hV_sum :
      Measurable[ℱ (n - 1)]
        (fun ω ↦ projectedRewardFeatureNoiseRealizedVarianceSum A σ2 x v n ω) := by
    simp only [projectedRewardFeatureNoiseRealizedVarianceSum]
    refine Finset.measurable_fun_sum (range n) ?_
    intro t ht
    have ht_le : t ≤ n - 1 := by
      exact Nat.le_pred_of_lt (by simpa using ht)
    exact ((hV_adapt t).mono (ℱ.mono ht_le)).measurable
  refine (measurable_exp.comp ?_).stronglyMeasurable
  exact (measurable_const.mul hY_sum).sub ((hV_sum.mul measurable_const).div_const 2)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The fixed-direction exponential process is adapted to the unshifted action filtration at its
horizon.

The existing `postActionFiltration` lemmas are indexed for increments: index `i` contains the
history through `i` and the action at `i + 1`. A process value at horizon `n`, however, contains
increments strictly before `n`, so for `n > 0` it is measurable with respect to
`filtrationAction n`. The `n = 0` case is constant. -/
lemma stronglyAdapted_projectedRewardFeatureNoiseExpProcess_filtrationAction
    (hA : ∀ n, Measurable (A n)) (hR : ∀ n, Measurable (R n))
    (σ2 : ℝ≥0) (v : Feature d) (u : ℝ) :
    StronglyAdapted (IsAlgEnvSeq.filtrationAction hA hR)
      (fun n ω ↦ projectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω) := by
  intro n
  by_cases hn : n = 0
  · subst n
    simpa [projectedRewardFeatureNoiseExpProcess_zero] using
      (stronglyMeasurable_const :
        StronglyMeasurable[IsAlgEnvSeq.filtrationAction hA hR 0]
          (fun _ : Ω ↦ (1 : ℝ)))
  · have hsm :=
      stronglyMeasurable_projectedRewardFeatureNoiseExpProcess_postActionFiltration_pred
        (A := A) (R := R) (ν := ν) (x := x) hA hR σ2 v u n
    have hpost :
        postActionFiltration (A := A) (R := R) hA hR (n - 1) =
          IsAlgEnvSeq.filtrationAction hA hR n := by
      simp [postActionFiltration, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
    rw [← hpost]
    exact hsm

/-- A bounded fixed-direction projection of LinUCB reward-feature noise is conditionally
subgaussian.

This is the scalar concentration input immediately before a vector self-normalized theorem. For a
fixed direction `v`, if `|⟪v, x_a⟫| ≤ Q` for every finite action `a`, then the positive-time
projected noise `⟪v, x_{A_t}⟫η_t` is conditionally subgaussian with variance proxy `Q^2 σ2`. -/
lemma projectedRewardFeatureNoise_hasCondSubgaussianMGF_filtrationAction_of_abs_le
    {alg : Algorithm (Fin K) ℝ}
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0) (v : Feature d)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) :
    HasCondSubgaussianMGF
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback t)
      ((IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback).le t)
      (projectedRewardFeatureNoise A R ν x v t)
      (⟨Q ^ 2, sq_nonneg Q⟩ * σ2) P := by
  rw [show projectedRewardFeatureNoise A R ν x v t =
      fun ω ↦ dotProduct v (x (A t ω)) * rewardNoise A R ν t ω by
    funext ω
    simp [projectedRewardFeatureNoise, ht]]
  exact rewardNoise_constMul_hasCondSubgaussianMGF_filtrationAction_of_abs_le
    (A := A) (R := R) (ν := ν) h hν ht
    (fun z : (Iic (t - 1) → Fin K × ℝ) × Fin K ↦ dotProduct v (x z.2))
    (measurable_projectedRewardFeatureCoeff (x := x) v)
    Q hQ (fun z ↦ hQ_bound z.2)

/-- One-step fixed-direction exponential bound with realized variance.

For a fixed direction `v`, the positive-time projected noise
`⟪v, x_{A_t}⟫η_t` satisfies the exponential-supermartingale increment inequality with the
realized variance proxy `σ2 * ⟪v, x_{A_t}⟫²`. This is the fixed-direction form of the adaptive
variance step used before the Gaussian-mixture/self-normalized argument in the textbook proof. -/
lemma projectedRewardFeatureNoise_ae_condExp_exp_sub_realizedVariance_le_one_of_abs_le
    {alg : Algorithm (Fin K) ℝ}
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0) (v : Feature d)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ) :
    ∀ᵐ ω ∂P,
      P[fun ω' ↦ Real.exp
          (u * projectedRewardFeatureNoise A R ν x v t ω' -
            scalarProjectionVariance σ2 (dotProduct v (x (A t ω'))) * u ^ 2 / 2) |
        IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback t] ω
        ≤ 1 := by
  let q : (Iic (t - 1) → Fin K × ℝ) × Fin K → ℝ :=
    fun z ↦ dotProduct v (x z.2)
  have hq : Measurable q := measurable_projectedRewardFeatureCoeff (x := x) v
  have h_int :
      Integrable
        (fun ω ↦ Real.exp
          (u * (q (history A R (t - 1) ω, A t ω) *
            rewardNoise A R ν t ω))) P :=
    rewardNoise_constMul_integrable_exp_mul_history_action_of_abs_le
      (A := A) (R := R) (ν := ν) h hν ht q hq Q hQ (fun z ↦ hQ_bound z.2) u
  have h_step :=
    rewardNoise_constMul_ae_condExp_exp_sub_realizedVariance_le_one
      (A := A) (R := R) (ν := ν) h hν ht q hq u h_int
  simpa [q, projectedRewardFeatureNoise, ht,
    IsAlgEnvSeq.filtrationAction_eq_comap (A := A) (Y := R) t ht] using h_step

/-- Integrability of a fixed-direction exponential-supermartingale increment under a bounded
predictable projection. -/
lemma projectedRewardFeatureNoiseExpIncrement_integrable_of_abs_le
    {alg : Algorithm (Fin K) ℝ}
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0) (v : Feature d)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ) :
    Integrable
      (fun ω ↦ projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω) P := by
  let q : (Iic (t - 1) → Fin K × ℝ) × Fin K → ℝ :=
    fun z ↦ dotProduct v (x z.2)
  have hq : Measurable q := measurable_projectedRewardFeatureCoeff (x := x) v
  have h_base :
      Integrable
        (fun ω ↦ Real.exp
          (u * (q (history A R (t - 1) ω, A t ω) *
            rewardNoise A R ν t ω))) P :=
    rewardNoise_constMul_integrable_exp_mul_history_action_of_abs_le
      (A := A) (R := R) (ν := ν) h hν ht q hq Q hQ (fun z ↦ hQ_bound z.2) u
  have h_coeff_meas : Measurable fun ω ↦ dotProduct v (x (A t ω)) :=
    (measurable_of_countable (fun a : Fin K ↦ dotProduct v (x a))).comp
      (h.measurable_action t)
  have h_noise_meas : Measurable (rewardNoise A R ν t) := by
    change Measurable (fun ω ↦ R t ω - (ν (A t ω))[id])
    exact (h.measurable_feedback t).sub ((measurable_rewardMean ν).comp (h.measurable_action t))
  have h_proj_meas :
      Measurable fun ω ↦ projectedRewardFeatureNoise A R ν x v t ω := by
    simpa [projectedRewardFeatureNoise, ht] using h_coeff_meas.mul h_noise_meas
  have h_var_meas :
      Measurable fun ω ↦ projectedRewardFeatureNoiseRealizedVariance A σ2 x v t ω := by
    simpa [projectedRewardFeatureNoiseRealizedVariance, ht, Function.comp_def] using
      (measurable_of_countable
        (fun a : Fin K ↦ (scalarProjectionVariance σ2 (dotProduct v (x a)) : ℝ))).comp
        (h.measurable_action t)
  have h_target :
      AEStronglyMeasurable
        (fun ω ↦ projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω) P := by
    refine (measurable_exp.comp ?_).aestronglyMeasurable
    exact (measurable_const.mul h_proj_meas).sub
      ((h_var_meas.mul measurable_const).div_const 2)
  refine Integrable.mono h_base h_target ?_
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  have hpenalty_nonneg :
      0 ≤ (scalarProjectionVariance σ2 (dotProduct v (x (A t ω))) : ℝ) * u ^ 2 / 2 := by
    positivity
  simp only [projectedRewardFeatureNoiseExpIncrement, projectedRewardFeatureNoise,
    projectedRewardFeatureNoiseRealizedVariance, ht, if_false, q,
    Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp.mpr (by linarith [hpenalty_nonneg])

/-- One-step conditional expectation bound for the named fixed-direction exponential increment. -/
lemma projectedRewardFeatureNoiseExpIncrement_ae_condExp_le_one_of_abs_le
    {alg : Algorithm (Fin K) ℝ}
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0) (v : Feature d)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ) :
    ∀ᵐ ω ∂P,
      P[fun ω' ↦ projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω' |
        IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback t] ω
        ≤ 1 := by
  simpa [projectedRewardFeatureNoiseExpIncrement,
    projectedRewardFeatureNoiseRealizedVariance, ht] using
    projectedRewardFeatureNoise_ae_condExp_exp_sub_realizedVariance_le_one_of_abs_le
      (A := A) (R := R) (ν := ν) (x := x) h hν ht v Q hQ hQ_bound u

/-- Predictable-multiplier form of the one-step exponential-supermartingale bound.

This is the induction step needed for a finite-horizon fixed-direction exponential process. If
`M` is nonnegative and measurable at the current post-action sigma-algebra, then multiplying the
next realized-variance exponential increment by `M` keeps conditional expectation bounded by `M`.
-/
lemma projectedRewardFeatureNoiseExpIncrement_ae_condExp_mul_le_of_abs_le
    {alg : Algorithm (Fin K) ℝ}
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0) (v : Feature d)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ)
    (M : Ω → ℝ)
    (hM_meas : AEStronglyMeasurable[IsAlgEnvSeq.filtrationAction
      h.measurable_action h.measurable_feedback t] M P)
    (hM_nonneg : 0 ≤ᵐ[P] M)
    (hM_mul_int :
      Integrable
        (fun ω ↦ M ω * projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω) P) :
    ∀ᵐ ω ∂P,
      P[fun ω' ↦ M ω' *
          projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω' |
        IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback t] ω
        ≤ M ω := by
  let ℱt := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback t
  have h_inc_int :
      Integrable
        (fun ω ↦ projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω) P :=
    projectedRewardFeatureNoiseExpIncrement_integrable_of_abs_le
      (A := A) (R := R) (ν := ν) (x := x) h hν ht v Q hQ hQ_bound u
  have h_pull :
      P[fun ω ↦ M ω *
          projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω | ℱt]
        =ᵐ[P] fun ω ↦
          M ω *
            P[fun ω' ↦ projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω' |
              ℱt] ω := by
    exact condExp_mul_of_aestronglyMeasurable_left hM_meas hM_mul_int h_inc_int
  have h_step :
      ∀ᵐ ω ∂P,
        P[fun ω' ↦ projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω' | ℱt] ω
          ≤ 1 := by
    simpa [ℱt] using
      projectedRewardFeatureNoiseExpIncrement_ae_condExp_le_one_of_abs_le
        (A := A) (R := R) (ν := ν) (x := x) h hν ht v Q hQ hQ_bound u
  filter_upwards [h_pull, h_step, hM_nonneg] with ω h_pullω h_stepω hMω
  rw [h_pullω]
  calc
    M ω *
        P[fun ω' ↦ projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω' | ℱt] ω
        ≤ M ω * 1 := mul_le_mul_of_nonneg_left h_stepω hMω
    _ = M ω := by simp

/-- A bounded fixed-direction projection of the accumulated LinUCB reward-feature noise is
subgaussian by Mathlib's scalar martingale-sum theorem.

This is not the full vector self-normalized concentration theorem. It is the scalar fixed-direction
ingredient: after choosing a direction `v`, the sum of
`⟪v, x_{A_t}⟫η_t` is subgaussian with variance proxy equal to the sum of the per-time proxy bounds.
-/
lemma projectedRewardFeatureNoise_sum_hasSubgaussianMGF_of_abs_le
    {alg : Algorithm (Fin K) ℝ}
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (n : ℕ) :
    HasSubgaussianMGF
      (fun ω ↦ ∑ t ∈ range n, projectedRewardFeatureNoise A R ν x v t ω)
      (∑ t ∈ range n, if t = 0 then 0 else (⟨Q ^ 2, sq_nonneg Q⟩ * σ2 : ℝ≥0)) P := by
  let ℱ := postActionFiltration (A := A) (R := R) h.measurable_action h.measurable_feedback
  let Y : ℕ → Ω → ℝ := projectedRewardFeatureNoise A R ν x v
  let cY : ℕ → ℝ≥0 :=
    fun t ↦ if t = 0 then 0 else ⟨Q ^ 2, sq_nonneg Q⟩ * σ2
  have h_adapted : StronglyAdapted ℱ Y := by
    simpa [ℱ, Y] using
      stronglyAdapted_projectedRewardFeatureNoise_postActionFiltration
        (A := A) (R := R) (ν := ν) (x := x) h.measurable_action h.measurable_feedback v
  have h0 : HasSubgaussianMGF (Y 0) (cY 0) P := by
    have hY0 : Y 0 = (0 : Ω → ℝ) := by
      funext ω
      simp [Y, projectedRewardFeatureNoise]
    have hcY0 : cY 0 = 0 := by
      simp [cY]
    rw [hY0, hcY0]
    exact HasSubgaussianMGF.zero
  have h_subG :
      ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) P := by
    intro i _hi
    simpa [ℱ, Y, cY, postActionFiltration] using
      projectedRewardFeatureNoise_hasCondSubgaussianMGF_filtrationAction_of_abs_le
        (A := A) (R := R) (ν := ν) (x := x) h hν (Nat.succ_ne_zero i)
        v Q hQ hQ_bound
  simpa [Y, cY] using
    HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF (μ := P) (ℱ := ℱ) (Y := Y) (cY := cY)
      h_adapted h0 n h_subG

/-- Integrability of the finite-horizon fixed-direction exponential process.

The realized-variance penalty is nonnegative, so this process is pointwise bounded by
`exp(u * ∑ projectedRewardFeatureNoise)`, whose integrability follows from the existing scalar
subgaussian martingale-sum theorem. -/
lemma projectedRewardFeatureNoiseExpProcess_integrable_of_abs_le
    {alg : Algorithm (Fin K) ℝ}
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ) (n : ℕ) :
    Integrable
      (fun ω ↦ projectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω) P := by
  have h_base :
      Integrable
        (fun ω ↦ Real.exp
          (u * (∑ t ∈ range n, projectedRewardFeatureNoise A R ν x v t ω))) P :=
    (projectedRewardFeatureNoise_sum_hasSubgaussianMGF_of_abs_le
      (A := A) (R := R) (ν := ν) (x := x) h hν v Q hQ hQ_bound n).integrable_exp_mul u
  have h_target :
      AEStronglyMeasurable
        (fun ω ↦ projectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω) P :=
    ((stronglyMeasurable_projectedRewardFeatureNoiseExpProcess_postActionFiltration_pred
      (A := A) (R := R) (ν := ν) (x := x) h.measurable_action h.measurable_feedback
      σ2 v u n).mono
      ((postActionFiltration (A := A) (R := R) h.measurable_action h.measurable_feedback).le
        (n - 1))).aestronglyMeasurable
  refine Integrable.mono h_base h_target ?_
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  have hpenalty_nonneg :
      0 ≤ projectedRewardFeatureNoiseRealizedVarianceSum A σ2 x v n ω * u ^ 2 / 2 := by
    have hsum_nonneg :
        0 ≤ projectedRewardFeatureNoiseRealizedVarianceSum A σ2 x v n ω :=
      projectedRewardFeatureNoiseRealizedVarianceSum_nonneg (A := A) (σ2 := σ2)
        (x := x) (v := v) (n := n) (ω := ω)
    positivity
  simp only [projectedRewardFeatureNoiseExpProcess, Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp.mpr (by linarith [hpenalty_nonneg])

/-- Finite-horizon fixed-direction exponential-supermartingale bound.

For every fixed direction `v` and scalar `u`, the realized-variance exponential process has
expectation at most one:
`E exp(u ∑ Y_t - u²/2 ∑ V_t) ≤ 1`.

This is still scalar. The remaining textbook self-normalized LinUCB step is the Gaussian-mixture
argument that integrates this inequality over directions and converts it into the determinant
self-normalized confidence radius. -/
lemma integral_projectedRewardFeatureNoiseExpProcess_le_one_of_abs_le
    {alg : Algorithm (Fin K) ℝ}
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ) :
    ∫ ω, projectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω ∂P ≤ 1 := by
  induction n with
  | zero =>
      simp [projectedRewardFeatureNoiseExpProcess_zero]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp [projectedRewardFeatureNoiseExpProcess_succ,
          projectedRewardFeatureNoiseExpProcess_zero,
          projectedRewardFeatureNoiseExpIncrement_zero]
      · let ℱ := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback
        let M : Ω → ℝ := fun ω ↦ projectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω
        have hM_meas : AEStronglyMeasurable[ℱ n] M P := by
          have hsm :=
            stronglyMeasurable_projectedRewardFeatureNoiseExpProcess_postActionFiltration_pred
              (A := A) (R := R) (ν := ν) (x := x) h.measurable_action h.measurable_feedback
              σ2 v u n
          have hpost :
              postActionFiltration (A := A) (R := R) h.measurable_action h.measurable_feedback
                  (n - 1) = ℱ n := by
            simp [postActionFiltration, ℱ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
          have hsm_F : StronglyMeasurable[ℱ n] M := by
            rw [← hpost]
            simpa [M] using hsm
          exact hsm_F.aestronglyMeasurable
        have hM_nonneg : 0 ≤ᵐ[P] M :=
          Filter.Eventually.of_forall fun ω ↦
            projectedRewardFeatureNoiseExpProcess_nonneg (A := A) (R := R) (ν := ν)
              (σ2 := σ2) (x := x) (v := v) (u := u) (n := n) (ω := ω)
        have hM_int : Integrable M P :=
          projectedRewardFeatureNoiseExpProcess_integrable_of_abs_le
            (A := A) (R := R) (ν := ν) (x := x) h hν v Q hQ hQ_bound u n
        have hM_mul_int :
            Integrable
              (fun ω ↦ M ω *
                projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω) P := by
          have hnext :
              Integrable
                (fun ω ↦ projectedRewardFeatureNoiseExpProcess A R ν σ2 x v u (n + 1) ω)
                P :=
            projectedRewardFeatureNoiseExpProcess_integrable_of_abs_le
              (A := A) (R := R) (ν := ν) (x := x) h hν v Q hQ hQ_bound u (n + 1)
          refine hnext.congr ?_
          exact Filter.Eventually.of_forall fun ω ↦ by
            simpa [M] using
              projectedRewardFeatureNoiseExpProcess_succ (A := A) (R := R) (ν := ν)
              (σ2 := σ2) (x := x) (v := v) (u := u) (n := n) (ω := ω)
        have h_cond :
            ∀ᵐ ω ∂P,
              P[fun ω' ↦ M ω' *
                  projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω' | ℱ n] ω
                ≤ M ω := by
          simpa [ℱ] using
            projectedRewardFeatureNoiseExpIncrement_ae_condExp_mul_le_of_abs_le
              (A := A) (R := R) (ν := ν) (x := x) h hν hn v Q hQ hQ_bound u
              M hM_meas hM_nonneg hM_mul_int
        have h_cond_int :
            Integrable
              (fun ω ↦
                P[fun ω' ↦ M ω' *
                    projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω' | ℱ n] ω)
              P := by
          exact integrable_condExp
        have h_cond_integral_le :
            (∫ ω,
              P[fun ω' ↦ M ω' *
                  projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω' | ℱ n] ω ∂P)
              ≤ ∫ ω, M ω ∂P :=
          integral_mono_ae h_cond_int hM_int h_cond
        calc
          ∫ ω, projectedRewardFeatureNoiseExpProcess A R ν σ2 x v u (n + 1) ω ∂P
              = ∫ ω, M ω *
                  projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω ∂P := by
                refine integral_congr_ae ?_
                exact Filter.Eventually.of_forall fun ω ↦ by
                  simpa [M] using
                    projectedRewardFeatureNoiseExpProcess_succ (A := A) (R := R)
                    (ν := ν) (σ2 := σ2) (x := x) (v := v) (u := u) (n := n)
                    (ω := ω)
          _ = ∫ ω,
                P[fun ω' ↦ M ω' *
                    projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω' | ℱ n] ω ∂P := by
                rw [integral_condExp (μ := P) (m := ℱ n) (hm := ℱ.le n)
                  (f := fun ω ↦ M ω *
                    projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω)]
          _ ≤ ∫ ω, M ω ∂P := h_cond_integral_le
          _ ≤ 1 := ih

/-- Fixed-direction exponential process as a Mathlib `Supermartingale`.

This is the process-level form of
`integral_projectedRewardFeatureNoiseExpProcess_le_one_of_abs_le`. It keeps the same bounded
projection assumption and packages the existing one-step conditional bound into the interface used
by optional-stopping/Ville arguments. The statement is still scalar and fixed-direction; the
remaining textbook step is to integrate these scalar exponentials over Gaussian directions to
obtain the self-normalized determinant confidence event. -/
lemma supermartingale_projectedRewardFeatureNoiseExpProcess_of_abs_le
    {alg : Algorithm (Fin K) ℝ}
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ) :
    Supermartingale
      (fun n ω ↦ projectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω)
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) P := by
  let ℱ := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback
  let Mproc : ℕ → Ω → ℝ :=
    fun n ω ↦ projectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω
  have h_adapted : StronglyAdapted ℱ Mproc := by
    simpa [ℱ, Mproc] using
      stronglyAdapted_projectedRewardFeatureNoiseExpProcess_filtrationAction
        (A := A) (R := R) (ν := ν) (x := x)
        h.measurable_action h.measurable_feedback σ2 v u
  have h_integrable : ∀ i, Integrable (Mproc i) P := by
    intro i
    simpa [Mproc] using
      projectedRewardFeatureNoiseExpProcess_integrable_of_abs_le
        (A := A) (R := R) (ν := ν) (x := x) h hν v Q hQ hQ_bound u i
  refine supermartingale_nat (𝒢 := ℱ) (μ := P) h_adapted h_integrable ?_
  intro i
  by_cases hi : i = 0
  · subst i
    change P[Mproc 1 | ℱ 0] ≤ᵐ[P] Mproc 0
    have hM0 : Mproc 0 = fun _ : Ω ↦ (1 : ℝ) := by
      funext ω
      simp [Mproc, projectedRewardFeatureNoiseExpProcess_zero]
    have hM1 : Mproc 1 = fun _ : Ω ↦ (1 : ℝ) := by
      funext ω
      simp [Mproc, projectedRewardFeatureNoiseExpProcess_one]
    rw [hM0, hM1, condExp_const (ℱ.le 0)]
  · let M : Ω → ℝ := Mproc i
    have hM_meas : AEStronglyMeasurable[ℱ i] M P :=
      (h_adapted i).aestronglyMeasurable
    have hM_nonneg : 0 ≤ᵐ[P] M :=
      Filter.Eventually.of_forall fun ω ↦ by
        exact projectedRewardFeatureNoiseExpProcess_nonneg (A := A) (R := R) (ν := ν)
          (σ2 := σ2) (x := x) (v := v) (u := u) (n := i) (ω := ω)
    have hM_mul_int :
        Integrable
          (fun ω ↦ M ω *
            projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u i ω) P := by
      have hnext : Integrable (Mproc (i + 1)) P := h_integrable (i + 1)
      refine hnext.congr ?_
      exact Filter.Eventually.of_forall fun ω ↦ by
        simpa [Mproc, M] using
          projectedRewardFeatureNoiseExpProcess_succ (A := A) (R := R) (ν := ν)
            (σ2 := σ2) (x := x) (v := v) (u := u) (n := i) (ω := ω)
    have h_cond :
        ∀ᵐ ω ∂P,
          P[fun ω' ↦ M ω' *
              projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u i ω' | ℱ i] ω
            ≤ M ω := by
      simpa [ℱ] using
        projectedRewardFeatureNoiseExpIncrement_ae_condExp_mul_le_of_abs_le
          (A := A) (R := R) (ν := ν) (x := x) h hν hi v Q hQ hQ_bound u
          M hM_meas hM_nonneg hM_mul_int
    have h_succ_eq :
        (fun ω ↦ Mproc (i + 1) ω) =ᵐ[P]
          fun ω ↦ M ω *
            projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u i ω :=
      Filter.Eventually.of_forall fun ω ↦ by
        simpa [Mproc, M] using
          projectedRewardFeatureNoiseExpProcess_succ (A := A) (R := R) (ν := ν)
            (σ2 := σ2) (x := x) (v := v) (u := u) (n := i) (ω := ω)
    have h_cond_eq :
        P[Mproc (i + 1) | ℱ i] =ᵐ[P]
          P[fun ω ↦ M ω *
            projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u i ω | ℱ i] :=
      condExp_congr_ae h_succ_eq
    filter_upwards [h_cond_eq, h_cond] with ω h_eq h_le
    rw [h_eq]
    exact h_le

/-- One-sided tail bound for a bounded fixed-direction projection of the accumulated LinUCB
reward-feature noise.

This is the direct probability form of
`projectedRewardFeatureNoise_sum_hasSubgaussianMGF_of_abs_le`, matching the way `UCB.lean` exposes
its scalar concentration facts. -/
lemma probReal_projectedRewardFeatureNoise_sum_ge_le_of_abs_le
    {alg : Algorithm (Fin K) ℝ}
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (n : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real
        {ω |
          ε ≤ ∑ t ∈ range n, projectedRewardFeatureNoise A R ν x v t ω}
      ≤ Real.exp
        (-ε ^ 2 /
          (2 * (∑ t ∈ range n,
            if t = 0 then 0 else (⟨Q ^ 2, sq_nonneg Q⟩ * σ2 : ℝ≥0)))) :=
  (projectedRewardFeatureNoise_sum_hasSubgaussianMGF_of_abs_le
    (A := A) (R := R) (ν := ν) (x := x) h hν v Q hQ hQ_bound n).measure_ge_le hε

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Positive-time centered response vector.

This is the vector martingale term that the scalar projected-noise concentration lemmas above
control directly:
`∑_{1 ≤ t < n} η_t x_{A_t}`. The full `centeredResponseVector` also contains the time-zero
centered reward term, whose law is handled separately by the initial distribution in the
algorithm/environment model. -/
noncomputable def positiveTimeCenteredResponseVector
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (ν : Kernel (Fin K) ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : Feature d :=
  ∑ t ∈ range n, if t = 0 then 0 else rewardNoise A R ν t ω • x (A t ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- No positive-time centered response has accumulated at horizon zero. -/
lemma positiveTimeCenteredResponseVector_zero :
    positiveTimeCenteredResponseVector A R ν x 0 ω = 0 := by
  simp [positiveTimeCenteredResponseVector]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Advancing the horizon adds the next positive-time centered reward-feature vector. -/
lemma positiveTimeCenteredResponseVector_succ :
    positiveTimeCenteredResponseVector A R ν x (n + 1) ω =
      positiveTimeCenteredResponseVector A R ν x n ω +
        if n = 0 then 0 else rewardNoise A R ν n ω • x (A n ω) := by
  simp [positiveTimeCenteredResponseVector, sum_range_succ]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Time-zero contribution to the centered response vector, present exactly when the horizon is
positive. -/
noncomputable def initialCenteredResponseVector
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (ν : Kernel (Fin K) ℝ)
    (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : Feature d :=
  if n = 0 then 0 else rewardNoise A R ν 0 ω • x (A 0 ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Projecting the time-zero centered response vector gives the scalar time-zero projected noise. -/
lemma dotProduct_initialCenteredResponseVector
    (v : Feature d) :
    dotProduct v (initialCenteredResponseVector A R ν x n ω) =
      if n = 0 then 0 else dotProduct v (x (A 0 ω)) * rewardNoise A R ν 0 ω := by
  by_cases hn : n = 0
  · simp [initialCenteredResponseVector, hn]
  · simp only [initialCenteredResponseVector, hn, if_false, Pi.smul_apply, smul_eq_mul,
      dotProduct]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    ring

/-- The initial scalar reward noise is subgaussian for the deterministic initial LinUCB arm. -/
lemma initialRewardNoise_hasSubgaussianMGF
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2) :
    HasSubgaussianMGF (rewardNoise A R ν 0) σ2 P := by
  let a0 : Fin K := ⟨0, hK⟩
  have h_pair :
      HasLaw (fun ω ↦ (A 0 ω, R 0 ω)) (Measure.dirac a0 ⊗ₘ ν) P := by
    have h_step_pair : (fun ω ↦ (A 0 ω, R 0 ω)) =ᵐ[P] Learning.step A R 0 :=
      Filter.Eventually.of_forall fun _ ↦ rfl
    simpa [linUCBAlgorithm, a0] using
      h.hasLaw_step_zero.congr h_step_pair
  have h_snd :
      HasLaw (fun p : Fin K × ℝ ↦ p.2) (ν a0) (Measure.dirac a0 ⊗ₘ ν) := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    ext s hs
    rw [Measure.map_apply measurable_snd hs, Measure.dirac_compProd_apply (measurable_snd hs)]
    change ν a0 s = ν a0 s
    rfl
  have hR_law : HasLaw (R 0) (ν a0) P := by
    simpa [Function.comp_def] using h_snd.comp h_pair
  have h_ident :
      IdentDistrib (fun r : ℝ ↦ r - (ν a0)[id])
        (fun ω ↦ R 0 ω - (ν a0)[id]) (ν a0) P := by
    exact ((hR_law.identDistrib HasLaw.id).comp
      (measurable_id.sub measurable_const)).symm
  have h_subG :
      HasSubgaussianMGF (fun ω ↦ R 0 ω - (ν a0)[id]) σ2 P :=
    (hν a0).congr_identDistrib h_ident
  refine h_subG.congr ?_
  filter_upwards [arm_zero (A := A) (R := R) (reg := reg) (β := β) (x := x)
    (ν := ν) h] with ω hA0
  simp [rewardNoise, a0, hA0]

/-- The time-zero fixed-direction projected reward-feature noise is subgaussian. -/
lemma initialProjectedRewardFeatureNoise_hasSubgaussianMGF
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) :
    HasSubgaussianMGF
      (fun ω ↦ dotProduct v (x (A 0 ω)) * rewardNoise A R ν 0 ω)
      (scalarProjectionVariance σ2 (dotProduct v (x ⟨0, hK⟩))) P := by
  let a0 : Fin K := ⟨0, hK⟩
  let q0 : ℝ := dotProduct v (x a0)
  have h_exact :
      HasSubgaussianMGF (fun ω ↦ q0 * rewardNoise A R ν 0 ω)
        (⟨q0 ^ 2, sq_nonneg q0⟩ * σ2) P :=
    (initialRewardNoise_hasSubgaussianMGF (A := A) (R := R) (reg := reg)
      (β := β) (x := x) (ν := ν) h hν).const_mul q0
  have h_congr :
      (fun ω ↦ q0 * rewardNoise A R ν 0 ω) =ᵐ[P]
        fun ω ↦ dotProduct v (x (A 0 ω)) * rewardNoise A R ν 0 ω := by
    filter_upwards [arm_zero (A := A) (R := R) (reg := reg) (β := β) (x := x)
      (ν := ν) h] with ω hA0
    simp [q0, a0, hA0]
  simpa [scalarProjectionVariance, q0, a0] using h_exact.congr h_congr

/-- The time-zero fixed-direction projected reward-feature noise is subgaussian under a uniform
projection bound. -/
lemma initialProjectedRewardFeatureNoise_hasSubgaussianMGF_of_abs_le
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) :
    HasSubgaussianMGF
      (fun ω ↦ dotProduct v (x (A 0 ω)) * rewardNoise A R ν 0 ω)
      (⟨Q ^ 2, sq_nonneg Q⟩ * σ2) P := by
  let a0 : Fin K := ⟨0, hK⟩
  let q0 : ℝ := dotProduct v (x a0)
  have hq0_sq_le : (⟨q0 ^ 2, sq_nonneg q0⟩ : ℝ≥0) ≤ ⟨Q ^ 2, sq_nonneg Q⟩ := by
    exact_mod_cast sq_le_sq.2 ((hQ_bound a0).trans (by simp [abs_of_nonneg hQ]))
  have h_exact :
      HasSubgaussianMGF
        (fun ω ↦ dotProduct v (x (A 0 ω)) * rewardNoise A R ν 0 ω)
        (⟨q0 ^ 2, sq_nonneg q0⟩ * σ2) P := by
    simpa [scalarProjectionVariance, q0, a0] using
      initialProjectedRewardFeatureNoise_hasSubgaussianMGF
        (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) h hν v
  have h_bound :
    HasSubgaussianMGF
        (fun ω ↦ dotProduct v (x (A 0 ω)) * rewardNoise A R ν 0 ω)
        (⟨Q ^ 2, sq_nonneg Q⟩ * σ2) P :=
    hasSubgaussianMGF_mono_varianceProxy (P := P) h_exact
      (mul_le_mul_left hq0_sq_le σ2)
  exact h_bound

/-- The initial centered response vector has the expected fixed-direction scalar subgaussian
bound. At horizon zero the vector is zero; at every positive horizon it is the time-zero projected
reward-feature noise. -/
lemma dotProduct_initialCenteredResponseVector_hasSubgaussianMGF_of_abs_le
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (n : ℕ) :
    HasSubgaussianMGF
      (fun ω ↦ dotProduct v (initialCenteredResponseVector A R ν x n ω))
      (if n = 0 then 0 else (⟨Q ^ 2, sq_nonneg Q⟩ * σ2 : ℝ≥0)) P := by
  by_cases hn : n = 0
  · rw [if_pos hn]
    have h_zero :
        (fun ω ↦ dotProduct v (initialCenteredResponseVector A R ν x n ω)) =
          (0 : Ω → ℝ) := by
      funext ω
      simp [dotProduct_initialCenteredResponseVector, hn]
    rw [h_zero]
    exact HasSubgaussianMGF.zero
  · rw [if_neg hn]
    exact (initialProjectedRewardFeatureNoise_hasSubgaussianMGF_of_abs_le
      (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) h hν
      v Q hQ hQ_bound).congr
      (Filter.Eventually.of_forall fun ω ↦ by
        simp [dotProduct_initialCenteredResponseVector, hn])

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A fixed-direction scalar projection of the full LinUCB centered reward-feature noise. -/
noncomputable def fullProjectedRewardFeatureNoise
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (ν : Kernel (Fin K) ℝ)
    (x : Fin K → Feature d) (v : Feature d) (t : ℕ) (ω : Ω) : ℝ :=
  dotProduct v (x (A t ω)) * rewardNoise A R ν t ω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- At positive times, the full projected reward-feature noise agrees with the positive-time
projected-noise process. -/
lemma fullProjectedRewardFeatureNoise_eq_projectedRewardFeatureNoise_of_ne_zero
    (v : Feature d) {t : ℕ} (ht : t ≠ 0) :
    fullProjectedRewardFeatureNoise A R ν x v t ω =
      projectedRewardFeatureNoise A R ν x v t ω := by
  simp [fullProjectedRewardFeatureNoise, projectedRewardFeatureNoise, ht]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Realized variance proxy for the full fixed-direction reward-feature noise. -/
noncomputable def fullProjectedRewardFeatureNoiseRealizedVariance
    (A : ℕ → Ω → Fin K) (σ2 : ℝ≥0)
    (x : Fin K → Feature d) (v : Feature d) (t : ℕ) (ω : Ω) : ℝ :=
  (scalarProjectionVariance σ2 (dotProduct v (x (A t ω))) : ℝ)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- At positive times, the full realized variance agrees with the positive-time realized variance
used by the conditional-law exponential step. -/
lemma fullProjectedRewardFeatureNoiseRealizedVariance_eq_projected_of_ne_zero
    (σ2 : ℝ≥0) (v : Feature d) {t : ℕ} (ht : t ≠ 0) :
    fullProjectedRewardFeatureNoiseRealizedVariance A σ2 x v t ω =
      projectedRewardFeatureNoiseRealizedVariance A σ2 x v t ω := by
  simp [fullProjectedRewardFeatureNoiseRealizedVariance,
    projectedRewardFeatureNoiseRealizedVariance, ht]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Exponential-supermartingale increment for the full fixed-direction reward-feature noise. -/
noncomputable def fullProjectedRewardFeatureNoiseExpIncrement
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (ν : Kernel (Fin K) ℝ)
    (σ2 : ℝ≥0) (x : Fin K → Feature d) (v : Feature d) (u : ℝ)
    (t : ℕ) (ω : Ω) : ℝ :=
  Real.exp
    (u * fullProjectedRewardFeatureNoise A R ν x v t ω -
      fullProjectedRewardFeatureNoiseRealizedVariance A σ2 x v t ω * u ^ 2 / 2)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- At positive times, the full exponential increment agrees with the positive-time increment. -/
lemma fullProjectedRewardFeatureNoiseExpIncrement_eq_projected_of_ne_zero
    (σ2 : ℝ≥0) (v : Feature d) (u : ℝ) {t : ℕ} (ht : t ≠ 0) :
    fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω =
      projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω := by
  simp [fullProjectedRewardFeatureNoiseExpIncrement, projectedRewardFeatureNoiseExpIncrement,
    fullProjectedRewardFeatureNoise, projectedRewardFeatureNoise,
    fullProjectedRewardFeatureNoiseRealizedVariance, projectedRewardFeatureNoiseRealizedVariance,
    ht]

/-- At time zero, the full fixed-direction exponential increment has conditional expectation at
most one given the initial action.

The only extra point compared with positive times is conditioning on `filtrationAction 0`, which is
generated by `A 0`. For `linUCBAlgorithm`, `A 0` is deterministic almost surely, so this
conditioning sigma-algebra is independent of the initial exponential increment. The proof then
reduces the conditional expectation to the ordinary expectation and applies the initial
subgaussian MGF bound. -/
lemma fullProjectedRewardFeatureNoiseExpIncrement_zero_ae_condExp_le_one
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (u : ℝ) :
    ∀ᵐ ω ∂P,
      P[fun ω' ↦ fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u 0 ω' |
        IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback 0] ω
        ≤ 1 := by
  let a0 : Fin K := ⟨0, hK⟩
  let F : Ω → ℝ :=
    fun ω ↦ fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u 0 ω
  let X : Ω → ℝ :=
    fun ω ↦ dotProduct v (x (A 0 ω)) * rewardNoise A R ν 0 ω
  let X0 : Ω → ℝ :=
    fun ω ↦ dotProduct v (x a0) * rewardNoise A R ν 0 ω
  let c0 : ℝ := (scalarProjectionVariance σ2 (dotProduct v (x a0)) : ℝ)
  let G : Ω → ℝ := fun ω ↦ Real.exp (u * X0 ω - c0 * u ^ 2 / 2)
  have hcoeff_meas : Measurable fun ω ↦ dotProduct v (x (A 0 ω)) :=
    (measurable_of_countable fun a : Fin K ↦ dotProduct v (x a)).comp
      (h.measurable_action 0)
  have hnoise_meas : Measurable (rewardNoise A R ν 0) := by
    change Measurable (fun ω ↦ R 0 ω - (ν (A 0 ω))[id])
    exact (h.measurable_feedback 0).sub
      ((measurable_rewardMean ν).comp (h.measurable_action 0))
  have hproj_meas : Measurable X := hcoeff_meas.mul hnoise_meas
  have hvar_meas :
      Measurable fun ω ↦ fullProjectedRewardFeatureNoiseRealizedVariance A σ2 x v 0 ω :=
    (measurable_of_countable
      (fun a : Fin K ↦ (scalarProjectionVariance σ2 (dotProduct v (x a)) : ℝ))).comp
      (h.measurable_action 0)
  have hF_meas : Measurable F := by
    dsimp [F, fullProjectedRewardFeatureNoiseExpIncrement]
    exact Real.measurable_exp.comp
      ((measurable_const.mul hproj_meas).sub ((hvar_meas.mul measurable_const).div_const 2))
  have h_initial :
      HasSubgaussianMGF X0 (scalarProjectionVariance σ2 (dotProduct v (x a0))) P := by
    simpa [X0, scalarProjectionVariance, a0] using
      (initialRewardNoise_hasSubgaussianMGF
        (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) h hν
        ).const_mul (dotProduct v (x a0))
  have hG_integral_le : (∫ ω, G ω ∂P) ≤ 1 := by
    simpa [G, X0, c0] using hasSubgaussianMGF_integral_exp_sub_le_one h_initial u
  have hF_eq_G : F =ᵐ[P] G := by
    filter_upwards [arm_zero (A := A) (R := R) (reg := reg) (β := β) (x := x)
      (ν := ν) h] with ω hA0
    simp [F, G, X0, c0, fullProjectedRewardFeatureNoiseExpIncrement,
      fullProjectedRewardFeatureNoise, fullProjectedRewardFeatureNoiseRealizedVariance,
      a0, hA0]
  have hF_integral_le : (∫ ω, F ω ∂P) ≤ 1 := by
    calc
      (∫ ω, F ω ∂P) = ∫ ω, G ω ∂P := integral_congr_ae hF_eq_G
      _ ≤ 1 := hG_integral_le
  let ℱ := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback
  have hA0_const : A 0 =ᵐ[P] fun _ : Ω ↦ a0 :=
    arm_zero (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) h
  have h_indep_fun : F ⟂ᵢ[P] A 0 := by
    exact (indepFun_const_right F a0).congr EventuallyEq.rfl hA0_const.symm
  have h_indep :
      Indep (MeasurableSpace.comap F inferInstance) (ℱ 0) P := by
    rw [IsAlgEnvSeq.filtrationAction_zero_eq_comap]
    simpa [ProbabilityTheory.IndepFun, ProbabilityTheory.Kernel.IndepFun,
      ProbabilityTheory.Indep] using h_indep_fun
  have h_cond_eq :
      P[F | ℱ 0] =ᵐ[P] fun _ : Ω ↦ ∫ ω, F ω ∂P := by
    exact condExp_indep_eq (m₁ := MeasurableSpace.comap F inferInstance)
      (m₂ := ℱ 0) (μ := P)
      hF_meas.comap_le (ℱ.le 0)
      (Measurable.of_comap_le le_rfl).stronglyMeasurable h_indep
  filter_upwards [h_cond_eq] with ω hω
  rw [hω]
  exact hF_integral_le

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Cumulative realized variance proxy for the full fixed-direction reward-feature noise. -/
noncomputable def fullProjectedRewardFeatureNoiseRealizedVarianceSum
    (A : ℕ → Ω → Fin K) (σ2 : ℝ≥0)
    (x : Fin K → Feature d) (v : Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ range n, fullProjectedRewardFeatureNoiseRealizedVariance A σ2 x v t ω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Full finite-horizon fixed-direction exponential process with realized variance. -/
noncomputable def fullProjectedRewardFeatureNoiseExpProcess
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (ν : Kernel (Fin K) ℝ)
    (σ2 : ℝ≥0) (x : Fin K → Feature d) (v : Feature d) (u : ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp
    (u * (∑ t ∈ range n, fullProjectedRewardFeatureNoise A R ν x v t ω) -
      fullProjectedRewardFeatureNoiseRealizedVarianceSum A σ2 x v n ω * u ^ 2 / 2)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Full realized variance proxies are nonnegative. -/
lemma fullProjectedRewardFeatureNoiseRealizedVariance_nonneg
    (σ2 : ℝ≥0) (v : Feature d) (t : ℕ) :
    0 ≤ fullProjectedRewardFeatureNoiseRealizedVariance A σ2 x v t ω := by
  simp [fullProjectedRewardFeatureNoiseRealizedVariance]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The cumulative full realized variance proxy is nonnegative. -/
lemma fullProjectedRewardFeatureNoiseRealizedVarianceSum_nonneg
    (σ2 : ℝ≥0) (v : Feature d) (n : ℕ) :
    0 ≤ fullProjectedRewardFeatureNoiseRealizedVarianceSum A σ2 x v n ω := by
  rw [fullProjectedRewardFeatureNoiseRealizedVarianceSum]
  exact sum_nonneg fun t _ht ↦
    fullProjectedRewardFeatureNoiseRealizedVariance_nonneg (A := A) (σ2 := σ2)
      (x := x) (v := v) (t := t) (ω := ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A rank-one feature matrix contributes the square of the projected feature to the corresponding
quadratic form. -/
lemma dotProduct_vecMulVec_mulVec_eq_sq (v y : Feature d) :
    dotProduct v (Matrix.mulVec (Matrix.vecMulVec y y) v) = (dotProduct v y) ^ 2 := by
  simp [Matrix.vecMulVec_mulVec, dotProduct, pow_two, Finset.sum_mul, mul_assoc,
    mul_comm]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The observed rank-one feature-matrix sum has quadratic form
`∑ (vᵀx_{A_t})²`. -/
lemma dotProduct_sum_vecMulVec_mulVec_eq_sum_sq (v : Feature d) :
    dotProduct v
        (Matrix.mulVec
          (∑ t ∈ range n, Matrix.vecMulVec (x (A t ω)) (x (A t ω))) v) =
      ∑ t ∈ range n, (dotProduct v (x (A t ω))) ^ 2 := by
  simp only [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl ?_
  intro t _ht
  exact dotProduct_vecMulVec_mulVec_eq_sq (v := v) (y := x (A t ω))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The design-matrix quadratic form decomposes into the ridge part plus the observed projected
feature squares. -/
lemma dotProduct_designMatrix_mulVec_eq_reg_add_sum_sq (v : Feature d) :
    dotProduct v (Matrix.mulVec (designMatrix A reg x n ω) v) =
      reg * dotProduct v v + ∑ t ∈ range n, (dotProduct v (x (A t ω))) ^ 2 := by
  simp only [designMatrix, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add]
  rw [dotProduct_sum_vecMulVec_mulVec_eq_sum_sq (A := A) (x := x) (n := n)
    (ω := ω) v]
  simp [dotProduct_smul]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- After removing the ridge part of the design matrix, the quadratic form is exactly the observed
projected feature-square sum. -/
lemma dotProduct_designMatrix_sub_reg_smul_one_mulVec_eq_sum_sq (v : Feature d) :
    dotProduct v
        (Matrix.mulVec
          (designMatrix A reg x n ω - reg • (1 : Matrix (Fin d) (Fin d) ℝ)) v) =
      ∑ t ∈ range n, (dotProduct v (x (A t ω))) ^ 2 := by
  rw [Matrix.sub_mulVec, dotProduct_sub,
    dotProduct_designMatrix_mulVec_eq_reg_add_sum_sq (A := A) (reg := reg)
      (x := x) (n := n) (ω := ω) v]
  simp [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The full realized-variance sum is `σ²` times the observed projected feature-square sum. -/
lemma fullProjectedRewardFeatureNoiseRealizedVarianceSum_eq_sigma_mul_sum_sq
    (σ2 : ℝ≥0) (v : Feature d) :
    fullProjectedRewardFeatureNoiseRealizedVarianceSum A σ2 x v n ω =
      (σ2 : ℝ) * ∑ t ∈ range n, (dotProduct v (x (A t ω))) ^ 2 := by
  rw [fullProjectedRewardFeatureNoiseRealizedVarianceSum]
  calc
    ∑ t ∈ range n, fullProjectedRewardFeatureNoiseRealizedVariance A σ2 x v t ω
        = ∑ t ∈ range n, (σ2 : ℝ) * (dotProduct v (x (A t ω))) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro t _ht
          change ((⟨(dotProduct v (x (A t ω))) ^ 2,
              sq_nonneg (dotProduct v (x (A t ω)))⟩ : ℝ≥0) * σ2 : ℝ) =
            (σ2 : ℝ) * (dotProduct v (x (A t ω))) ^ 2
          change (dotProduct v (x (A t ω))) ^ 2 * (σ2 : ℝ) =
            (σ2 : ℝ) * (dotProduct v (x (A t ω))) ^ 2
          ring
    _ = (σ2 : ℝ) * ∑ t ∈ range n, (dotProduct v (x (A t ω))) ^ 2 := by
          rw [Finset.mul_sum]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The full realized-variance sum is `σ²` times the quadratic form of the non-ridge part of the
design matrix. -/
lemma fullProjectedRewardFeatureNoiseRealizedVarianceSum_eq_sigma_mul_designMatrix_sub_reg
    (σ2 : ℝ≥0) (v : Feature d) :
    fullProjectedRewardFeatureNoiseRealizedVarianceSum A σ2 x v n ω =
      (σ2 : ℝ) *
        dotProduct v
          (Matrix.mulVec
            (designMatrix A reg x n ω - reg • (1 : Matrix (Fin d) (Fin d) ℝ)) v) := by
  rw [fullProjectedRewardFeatureNoiseRealizedVarianceSum_eq_sigma_mul_sum_sq
      (A := A) (σ2 := σ2) (x := x) (v := v) (n := n) (ω := ω),
    dotProduct_designMatrix_sub_reg_smul_one_mulVec_eq_sum_sq (A := A)
      (reg := reg) (x := x) (n := n) (ω := ω) v]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Equivalent design-matrix form of the full realized-variance sum:
`σ² * (vᵀV_n v - reg * vᵀv)`. -/
lemma fullProjectedRewardFeatureNoiseRealizedVarianceSum_eq_sigma_mul_designMatrix_minus_reg_norm
    (σ2 : ℝ≥0) (v : Feature d) :
    fullProjectedRewardFeatureNoiseRealizedVarianceSum A σ2 x v n ω =
      (σ2 : ℝ) *
        (dotProduct v (Matrix.mulVec (designMatrix A reg x n ω) v) -
          reg * dotProduct v v) := by
  rw [fullProjectedRewardFeatureNoiseRealizedVarianceSum_eq_sigma_mul_sum_sq
      (A := A) (σ2 := σ2) (x := x) (v := v) (n := n) (ω := ω),
    dotProduct_designMatrix_mulVec_eq_reg_add_sum_sq (A := A) (reg := reg)
      (x := x) (n := n) (ω := ω) v]
  ring

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Full exponential increments are nonnegative. -/
lemma fullProjectedRewardFeatureNoiseExpIncrement_nonneg
    (σ2 : ℝ≥0) (v : Feature d) (u : ℝ) (t : ℕ) :
    0 ≤ fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω := by
  exact Real.exp_nonneg _

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The full finite-horizon exponential process starts at one. -/
lemma fullProjectedRewardFeatureNoiseExpProcess_zero
    (σ2 : ℝ≥0) (v : Feature d) (u : ℝ) :
    fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u 0 ω = 1 := by
  simp [fullProjectedRewardFeatureNoiseExpProcess,
    fullProjectedRewardFeatureNoiseRealizedVarianceSum]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The full finite-horizon exponential process is nonnegative. -/
lemma fullProjectedRewardFeatureNoiseExpProcess_nonneg
    (σ2 : ℝ≥0) (v : Feature d) (u : ℝ) (n : ℕ) :
    0 ≤ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω := by
  exact Real.exp_nonneg _

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The full exponential process factors into the previous process times the next increment. -/
lemma fullProjectedRewardFeatureNoiseExpProcess_succ
    (σ2 : ℝ≥0) (v : Feature d) (u : ℝ) (n : ℕ) :
    fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u (n + 1) ω =
      fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω *
        fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω := by
  simp only [fullProjectedRewardFeatureNoiseExpProcess,
    fullProjectedRewardFeatureNoiseExpIncrement,
    fullProjectedRewardFeatureNoiseRealizedVarianceSum, sum_range_succ]
  rw [← Real.exp_add]
  congr 1
  ring

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The full fixed-direction projected reward-feature noise is adapted to `postActionFiltration`. -/
lemma stronglyAdapted_fullProjectedRewardFeatureNoise_postActionFiltration
    (hA : ∀ n, Measurable (A n)) (hR : ∀ n, Measurable (R n))
    (v : Feature d) :
    StronglyAdapted (postActionFiltration (A := A) (R := R) hA hR)
      (fullProjectedRewardFeatureNoise A R ν x v) := by
  intro t
  have hfil_le :
      IsAlgEnvSeq.filtration hA hR t ≤ postActionFiltration (A := A) (R := R) hA hR t :=
    filtration_le_postActionFiltration (A := A) (R := R) hA hR t
  have hA_t : Measurable[postActionFiltration (A := A) (R := R) hA hR t] (A t) :=
    (IsAlgEnvSeq.adapted_action hA hR t).mono hfil_le le_rfl
  have hR_t : Measurable[postActionFiltration (A := A) (R := R) hA hR t] (R t) :=
    (IsAlgEnvSeq.adapted_feedback hA hR t).mono hfil_le le_rfl
  have hη_t :
      Measurable[postActionFiltration (A := A) (R := R) hA hR t]
        (rewardNoise A R ν t) := by
    change Measurable[postActionFiltration (A := A) (R := R) hA hR t]
      (fun ω ↦ R t ω - (ν (A t ω))[id])
    exact hR_t.sub ((measurable_rewardMean ν).comp hA_t)
  have hq_t :
      Measurable[postActionFiltration (A := A) (R := R) hA hR t]
        (fun ω ↦ dotProduct v (x (A t ω))) :=
    (measurable_of_countable (fun a : Fin K ↦ dotProduct v (x a))).comp hA_t
  exact (hq_t.mul hη_t).stronglyMeasurable

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The full fixed-direction realized variance proxy is adapted to `postActionFiltration`. -/
lemma stronglyAdapted_fullProjectedRewardFeatureNoiseRealizedVariance_postActionFiltration
    (hA : ∀ n, Measurable (A n)) (hR : ∀ n, Measurable (R n))
    (σ2 : ℝ≥0) (v : Feature d) :
    StronglyAdapted (postActionFiltration (A := A) (R := R) hA hR)
      (fullProjectedRewardFeatureNoiseRealizedVariance A σ2 x v) := by
  intro t
  have hfil_le :
      IsAlgEnvSeq.filtration hA hR t ≤ postActionFiltration (A := A) (R := R) hA hR t :=
    filtration_le_postActionFiltration (A := A) (R := R) hA hR t
  have hA_t : Measurable[postActionFiltration (A := A) (R := R) hA hR t] (A t) :=
    (IsAlgEnvSeq.adapted_action hA hR t).mono hfil_le le_rfl
  have hvar_t :
      Measurable[postActionFiltration (A := A) (R := R) hA hR t]
        (fun ω ↦ (scalarProjectionVariance σ2 (dotProduct v (x (A t ω))) : ℝ)) :=
    (measurable_of_countable
      (fun a : Fin K ↦ (scalarProjectionVariance σ2 (dotProduct v (x a)) : ℝ))).comp hA_t
  change StronglyMeasurable[postActionFiltration (A := A) (R := R) hA hR t]
    (fun ω ↦ (scalarProjectionVariance σ2 (dotProduct v (x (A t ω))) : ℝ))
  exact hvar_t.stronglyMeasurable

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The full fixed-direction exponential process up to a positive horizon is measurable with
respect to the post-action sigma-algebra at the previous time. -/
lemma stronglyMeasurable_fullProjectedRewardFeatureNoiseExpProcess_postActionFiltration_pred
    (hA : ∀ n, Measurable (A n)) (hR : ∀ n, Measurable (R n))
    (σ2 : ℝ≥0) (v : Feature d) (u : ℝ) (n : ℕ) :
    StronglyMeasurable[postActionFiltration (A := A) (R := R) hA hR (n - 1)]
      (fun ω ↦ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω) := by
  let ℱ := postActionFiltration (A := A) (R := R) hA hR
  have hY_adapt : StronglyAdapted ℱ (fullProjectedRewardFeatureNoise A R ν x v) := by
    simpa [ℱ] using
      stronglyAdapted_fullProjectedRewardFeatureNoise_postActionFiltration
        (A := A) (R := R) (ν := ν) (x := x) hA hR v
  have hV_adapt :
      StronglyAdapted ℱ (fullProjectedRewardFeatureNoiseRealizedVariance A σ2 x v) := by
    simpa [ℱ] using
      stronglyAdapted_fullProjectedRewardFeatureNoiseRealizedVariance_postActionFiltration
        (A := A) (R := R) (x := x) hA hR σ2 v
  have hY_sum :
      Measurable[ℱ (n - 1)]
        (fun ω ↦ ∑ t ∈ range n, fullProjectedRewardFeatureNoise A R ν x v t ω) := by
    refine Finset.measurable_fun_sum (range n) ?_
    intro t ht
    have ht_le : t ≤ n - 1 := by
      exact Nat.le_pred_of_lt (by simpa using ht)
    exact ((hY_adapt t).mono (ℱ.mono ht_le)).measurable
  have hV_sum :
      Measurable[ℱ (n - 1)]
        (fun ω ↦ fullProjectedRewardFeatureNoiseRealizedVarianceSum A σ2 x v n ω) := by
    simp only [fullProjectedRewardFeatureNoiseRealizedVarianceSum]
    refine Finset.measurable_fun_sum (range n) ?_
    intro t ht
    have ht_le : t ≤ n - 1 := by
      exact Nat.le_pred_of_lt (by simpa using ht)
    exact ((hV_adapt t).mono (ℱ.mono ht_le)).measurable
  refine (measurable_exp.comp ?_).stronglyMeasurable
  exact (measurable_const.mul hY_sum).sub ((hV_sum.mul measurable_const).div_const 2)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The full fixed-direction exponential process is adapted to the unshifted action filtration at
its horizon. -/
lemma stronglyAdapted_fullProjectedRewardFeatureNoiseExpProcess_filtrationAction
    (hA : ∀ n, Measurable (A n)) (hR : ∀ n, Measurable (R n))
    (σ2 : ℝ≥0) (v : Feature d) (u : ℝ) :
    StronglyAdapted (IsAlgEnvSeq.filtrationAction hA hR)
      (fun n ω ↦ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω) := by
  intro n
  by_cases hn : n = 0
  · subst n
    simpa [fullProjectedRewardFeatureNoiseExpProcess_zero] using
      (stronglyMeasurable_const :
        StronglyMeasurable[IsAlgEnvSeq.filtrationAction hA hR 0]
          (fun _ : Ω ↦ (1 : ℝ)))
  · have hsm :=
      stronglyMeasurable_fullProjectedRewardFeatureNoiseExpProcess_postActionFiltration_pred
        (A := A) (R := R) (ν := ν) (x := x) hA hR σ2 v u n
    have hpost :
        postActionFiltration (A := A) (R := R) hA hR (n - 1) =
          IsAlgEnvSeq.filtrationAction hA hR n := by
      simp [postActionFiltration, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
    rw [← hpost]
    exact hsm

/-- The full fixed-direction projected centered response is a scalar subgaussian martingale sum. -/
lemma fullProjectedRewardFeatureNoise_sum_hasSubgaussianMGF_of_abs_le
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (n : ℕ) :
    HasSubgaussianMGF
      (fun ω ↦ ∑ t ∈ range n, fullProjectedRewardFeatureNoise A R ν x v t ω)
      (∑ _t ∈ range n, (⟨Q ^ 2, sq_nonneg Q⟩ * σ2 : ℝ≥0)) P := by
  let ℱ := postActionFiltration (A := A) (R := R) h.measurable_action h.measurable_feedback
  let Y : ℕ → Ω → ℝ := fullProjectedRewardFeatureNoise A R ν x v
  let cY : ℕ → ℝ≥0 := fun _ ↦ ⟨Q ^ 2, sq_nonneg Q⟩ * σ2
  have h_adapted : StronglyAdapted ℱ Y := by
    simpa [ℱ, Y] using
      stronglyAdapted_fullProjectedRewardFeatureNoise_postActionFiltration
        (A := A) (R := R) (ν := ν) (x := x) h.measurable_action h.measurable_feedback v
  have h0 : HasSubgaussianMGF (Y 0) (cY 0) P := by
    have hY0 :
        Y 0 = fun ω ↦ dotProduct v (x (A 0 ω)) * rewardNoise A R ν 0 ω := by
      funext ω
      simp [Y, fullProjectedRewardFeatureNoise]
    rw [hY0]
    simpa [cY] using
      initialProjectedRewardFeatureNoise_hasSubgaussianMGF_of_abs_le
        (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
        h hν v Q hQ hQ_bound
  have h_subG :
      ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) P := by
    intro i _hi
    have h_eq :
        Y (i + 1) = projectedRewardFeatureNoise A R ν x v (i + 1) := by
      funext ω
      simp [Y, fullProjectedRewardFeatureNoise_eq_projectedRewardFeatureNoise_of_ne_zero
        (A := A) (R := R) (ν := ν) (x := x) (v := v) (t := i + 1)
        (ω := ω) (Nat.succ_ne_zero i)]
    rw [h_eq]
    simpa [ℱ, cY, postActionFiltration] using
      projectedRewardFeatureNoise_hasCondSubgaussianMGF_filtrationAction_of_abs_le
        (A := A) (R := R) (ν := ν) (x := x) h hν (Nat.succ_ne_zero i)
        v Q hQ hQ_bound
  simpa [Y, cY] using
    HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF (μ := P) (ℱ := ℱ) (Y := Y) (cY := cY)
      h_adapted h0 n h_subG

/-- Predictable-multiplier form of the one-step bound for the full fixed-direction exponential
increment at positive times. -/
lemma fullProjectedRewardFeatureNoiseExpIncrement_ae_condExp_mul_le_of_abs_le
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0) (v : Feature d)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ)
    (M : Ω → ℝ)
    (hM_meas : AEStronglyMeasurable[IsAlgEnvSeq.filtrationAction
      h.measurable_action h.measurable_feedback t] M P)
    (hM_nonneg : 0 ≤ᵐ[P] M)
    (hM_mul_int :
      Integrable
        (fun ω ↦ M ω * fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω) P) :
    ∀ᵐ ω ∂P,
      P[fun ω' ↦ M ω' *
          fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω' |
        IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback t] ω
        ≤ M ω := by
  let ℱt := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback t
  have h_mul_eq :
      (fun ω ↦ M ω * fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω) =ᵐ[P]
        fun ω ↦ M ω *
          projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω :=
    Filter.Eventually.of_forall fun ω ↦ by
      change M ω * fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω =
        M ω * projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω
      rw [fullProjectedRewardFeatureNoiseExpIncrement_eq_projected_of_ne_zero
        (A := A) (R := R) (ν := ν) (σ2 := σ2) (x := x) (v := v) (u := u)
        (t := t) (ω := ω) ht]
  have hM_mul_int_projected :
      Integrable
        (fun ω ↦ M ω * projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω) P :=
    hM_mul_int.congr h_mul_eq
  have h_cond_projected :
      ∀ᵐ ω ∂P,
        P[fun ω' ↦ M ω' *
            projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω' | ℱt] ω
          ≤ M ω := by
    simpa [ℱt] using
      projectedRewardFeatureNoiseExpIncrement_ae_condExp_mul_le_of_abs_le
        (A := A) (R := R) (ν := ν) (x := x) h hν ht v Q hQ hQ_bound u
        M hM_meas hM_nonneg hM_mul_int_projected
  have h_cond_eq :
      P[fun ω ↦ M ω *
          fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω | ℱt]
        =ᵐ[P]
        P[fun ω ↦ M ω *
          projectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u t ω | ℱt] :=
    condExp_congr_ae h_mul_eq
  filter_upwards [h_cond_eq, h_cond_projected] with ω h_eq h_le
  rw [h_eq]
  exact h_le

/-- Integrability of the full finite-horizon fixed-direction exponential process.

The realized-variance penalty is nonnegative, so this process is pointwise bounded by the ordinary
exponential of the fixed-direction full centered reward-feature sum. -/
lemma fullProjectedRewardFeatureNoiseExpProcess_integrable_of_abs_le
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ) (n : ℕ) :
    Integrable
      (fun ω ↦ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω) P := by
  have h_base :
      Integrable
        (fun ω ↦ Real.exp
          (u * (∑ t ∈ range n, fullProjectedRewardFeatureNoise A R ν x v t ω))) P :=
    (fullProjectedRewardFeatureNoise_sum_hasSubgaussianMGF_of_abs_le
      (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
      h hν v Q hQ hQ_bound n).integrable_exp_mul u
  have h_target :
      AEStronglyMeasurable
        (fun ω ↦ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω) P :=
    ((stronglyMeasurable_fullProjectedRewardFeatureNoiseExpProcess_postActionFiltration_pred
      (A := A) (R := R) (ν := ν) (x := x) h.measurable_action h.measurable_feedback
      σ2 v u n).mono
      ((postActionFiltration (A := A) (R := R) h.measurable_action h.measurable_feedback).le
        (n - 1))).aestronglyMeasurable
  refine Integrable.mono h_base h_target ?_
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  have hpenalty_nonneg :
      0 ≤ fullProjectedRewardFeatureNoiseRealizedVarianceSum A σ2 x v n ω * u ^ 2 / 2 := by
    have hsum_nonneg :
        0 ≤ fullProjectedRewardFeatureNoiseRealizedVarianceSum A σ2 x v n ω :=
      fullProjectedRewardFeatureNoiseRealizedVarianceSum_nonneg (A := A) (σ2 := σ2)
        (x := x) (v := v) (n := n) (ω := ω)
    positivity
  simp only [fullProjectedRewardFeatureNoiseExpProcess,
    Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp.mpr (by linarith [hpenalty_nonneg])

/-- Finite-horizon fixed-direction exponential-supermartingale bound for the full centered
reward-feature noise.

This is the closest scalar theorem before the vector self-normalized method-of-mixtures step:
for every fixed direction `v` and scalar `u`,
`E exp(u * ⟪v, S_n⟫ - u² / 2 * ∑_{t<n} σ² ⟪v, x_{A_t}⟫²) ≤ 1`, where
`S_n` is the centered response vector. -/
lemma integral_fullProjectedRewardFeatureNoiseExpProcess_le_one_of_abs_le
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ) :
    ∫ ω, fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω ∂P ≤ 1 := by
  induction n with
  | zero =>
      simp [fullProjectedRewardFeatureNoiseExpProcess_zero]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        let a0 : Fin K := ⟨0, hK⟩
        let X : Ω → ℝ :=
          fun ω ↦ dotProduct v (x (A 0 ω)) * rewardNoise A R ν 0 ω
        have h_initial :
            HasSubgaussianMGF X
              (scalarProjectionVariance σ2 (dotProduct v (x a0))) P := by
          simpa [X, a0] using
            initialProjectedRewardFeatureNoise_hasSubgaussianMGF
              (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
              h hν v
        have h_integral_exact :
            ∫ ω, Real.exp
              (u * X ω -
                (scalarProjectionVariance σ2 (dotProduct v (x a0)) : ℝ) * u ^ 2 / 2) ∂P
              ≤ 1 :=
          hasSubgaussianMGF_integral_exp_sub_le_one h_initial u
        have h_process_eq :
            (fun ω ↦ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u 1 ω)
              =ᵐ[P]
            fun ω ↦ Real.exp
              (u * X ω -
                (scalarProjectionVariance σ2 (dotProduct v (x a0)) : ℝ) * u ^ 2 / 2) := by
          filter_upwards [arm_zero (A := A) (R := R) (reg := reg) (β := β) (x := x)
            (ν := ν) h] with ω hA0
          simp [fullProjectedRewardFeatureNoiseExpProcess,
            fullProjectedRewardFeatureNoiseRealizedVarianceSum,
            fullProjectedRewardFeatureNoiseRealizedVariance,
            fullProjectedRewardFeatureNoise, X, a0, hA0]
        calc
          ∫ ω, fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u 1 ω ∂P
              = ∫ ω, Real.exp
                  (u * X ω -
                    (scalarProjectionVariance σ2 (dotProduct v (x a0)) : ℝ) * u ^ 2 / 2) ∂P :=
                integral_congr_ae h_process_eq
          _ ≤ 1 := h_integral_exact
      · let ℱ := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback
        let M : Ω → ℝ := fun ω ↦ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω
        have hM_meas : AEStronglyMeasurable[ℱ n] M P := by
          have hsm :=
            stronglyMeasurable_fullProjectedRewardFeatureNoiseExpProcess_postActionFiltration_pred
              (A := A) (R := R) (ν := ν) (x := x) h.measurable_action h.measurable_feedback
              σ2 v u n
          have hpost :
              postActionFiltration (A := A) (R := R) h.measurable_action h.measurable_feedback
                  (n - 1) = ℱ n := by
            simp [postActionFiltration, ℱ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
          have hsm_F : StronglyMeasurable[ℱ n] M := by
            rw [← hpost]
            simpa [M] using hsm
          exact hsm_F.aestronglyMeasurable
        have hM_nonneg : 0 ≤ᵐ[P] M :=
          Filter.Eventually.of_forall fun ω ↦
            fullProjectedRewardFeatureNoiseExpProcess_nonneg (A := A) (R := R) (ν := ν)
              (σ2 := σ2) (x := x) (v := v) (u := u) (n := n) (ω := ω)
        have hM_int : Integrable M P :=
          fullProjectedRewardFeatureNoiseExpProcess_integrable_of_abs_le
            (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
            h hν v Q hQ hQ_bound u n
        have hM_mul_int :
            Integrable
              (fun ω ↦ M ω *
                fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω) P := by
          have hnext :
              Integrable
                (fun ω ↦ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u (n + 1) ω)
                P :=
            fullProjectedRewardFeatureNoiseExpProcess_integrable_of_abs_le
              (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
              h hν v Q hQ hQ_bound u (n + 1)
          refine hnext.congr ?_
          exact Filter.Eventually.of_forall fun ω ↦ by
            simpa [M] using
              fullProjectedRewardFeatureNoiseExpProcess_succ (A := A) (R := R) (ν := ν)
                (σ2 := σ2) (x := x) (v := v) (u := u) (n := n) (ω := ω)
        have h_cond :
            ∀ᵐ ω ∂P,
              P[fun ω' ↦ M ω' *
                  fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω' | ℱ n] ω
                ≤ M ω := by
          simpa [ℱ] using
            fullProjectedRewardFeatureNoiseExpIncrement_ae_condExp_mul_le_of_abs_le
              (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
              h hν hn v Q hQ hQ_bound u M hM_meas hM_nonneg hM_mul_int
        have h_cond_int :
            Integrable
              (fun ω ↦
                P[fun ω' ↦ M ω' *
                    fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω' | ℱ n] ω)
              P := by
          exact integrable_condExp
        have h_cond_integral_le :
            (∫ ω,
              P[fun ω' ↦ M ω' *
                  fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω' | ℱ n] ω ∂P)
              ≤ ∫ ω, M ω ∂P :=
          integral_mono_ae h_cond_int hM_int h_cond
        calc
          ∫ ω, fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u (n + 1) ω ∂P
              = ∫ ω, M ω *
                  fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω ∂P := by
                refine integral_congr_ae ?_
                exact Filter.Eventually.of_forall fun ω ↦ by
                  simpa [M] using
                    fullProjectedRewardFeatureNoiseExpProcess_succ (A := A) (R := R)
                    (ν := ν) (σ2 := σ2) (x := x) (v := v) (u := u) (n := n)
                    (ω := ω)
          _ = ∫ ω,
                P[fun ω' ↦ M ω' *
                    fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω' |
                  ℱ n] ω ∂P := by
                rw [integral_condExp (μ := P) (m := ℱ n) (hm := ℱ.le n)
                  (f := fun ω ↦ M ω *
                    fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u n ω)]
          _ ≤ ∫ ω, M ω ∂P := h_cond_integral_le
          _ ≤ 1 := ih

/-- Full fixed-direction exponential process as a Mathlib `Supermartingale`.

This is the scalar process used immediately before the textbook Gaussian-mixture argument, now
including the time-zero centered reward-feature contribution. The zero-time conditional step uses
the deterministic initial action of `linUCBAlgorithm`; positive times reuse the standard
history/action conditional-subgaussian increment bound. -/
lemma supermartingale_fullProjectedRewardFeatureNoiseExpProcess_of_abs_le
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ) :
    Supermartingale
      (fun n ω ↦ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω)
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) P := by
  let ℱ := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback
  let Mproc : ℕ → Ω → ℝ :=
    fun n ω ↦ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω
  have h_adapted : StronglyAdapted ℱ Mproc := by
    simpa [ℱ, Mproc] using
      stronglyAdapted_fullProjectedRewardFeatureNoiseExpProcess_filtrationAction
        (A := A) (R := R) (ν := ν) (x := x)
        h.measurable_action h.measurable_feedback σ2 v u
  have h_integrable : ∀ i, Integrable (Mproc i) P := by
    intro i
    simpa [Mproc] using
      fullProjectedRewardFeatureNoiseExpProcess_integrable_of_abs_le
        (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
        h hν v Q hQ hQ_bound u i
  refine supermartingale_nat (𝒢 := ℱ) (μ := P) h_adapted h_integrable ?_
  intro i
  by_cases hi : i = 0
  · subst i
    change P[Mproc 1 | ℱ 0] ≤ᵐ[P] Mproc 0
    let Inc0 : Ω → ℝ :=
      fun ω ↦ fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u 0 ω
    have h_succ_eq : Mproc 1 = Inc0 := by
      funext ω
      simp [Mproc, Inc0, fullProjectedRewardFeatureNoiseExpProcess_succ,
        fullProjectedRewardFeatureNoiseExpProcess_zero]
    have h_cond :
        ∀ᵐ ω ∂P, P[Inc0 | ℱ 0] ω ≤ 1 := by
      simpa [ℱ, Inc0] using
        fullProjectedRewardFeatureNoiseExpIncrement_zero_ae_condExp_le_one
          (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) h hν v u
    have h_cond_eq : P[Mproc 1 | ℱ 0] =ᵐ[P] P[Inc0 | ℱ 0] := by
      exact condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦ by rw [h_succ_eq])
    have hM0 : Mproc 0 = fun _ : Ω ↦ (1 : ℝ) := by
      funext ω
      simp [Mproc, fullProjectedRewardFeatureNoiseExpProcess_zero]
    filter_upwards [h_cond_eq, h_cond] with ω h_eq h_le
    rw [h_eq, hM0]
    exact h_le
  · let M : Ω → ℝ := Mproc i
    have hM_meas : AEStronglyMeasurable[ℱ i] M P :=
      (h_adapted i).aestronglyMeasurable
    have hM_nonneg : 0 ≤ᵐ[P] M :=
      Filter.Eventually.of_forall fun ω ↦ by
        exact fullProjectedRewardFeatureNoiseExpProcess_nonneg (A := A) (R := R) (ν := ν)
          (σ2 := σ2) (x := x) (v := v) (u := u) (n := i) (ω := ω)
    have hM_mul_int :
        Integrable
          (fun ω ↦ M ω *
            fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u i ω) P := by
      have hnext : Integrable (Mproc (i + 1)) P := h_integrable (i + 1)
      refine hnext.congr ?_
      exact Filter.Eventually.of_forall fun ω ↦ by
        simpa [Mproc, M] using
          fullProjectedRewardFeatureNoiseExpProcess_succ (A := A) (R := R) (ν := ν)
            (σ2 := σ2) (x := x) (v := v) (u := u) (n := i) (ω := ω)
    have h_cond :
        ∀ᵐ ω ∂P,
          P[fun ω' ↦ M ω' *
              fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u i ω' | ℱ i] ω
            ≤ M ω := by
      simpa [ℱ] using
        fullProjectedRewardFeatureNoiseExpIncrement_ae_condExp_mul_le_of_abs_le
          (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
          h hν hi v Q hQ hQ_bound u M hM_meas hM_nonneg hM_mul_int
    have h_succ_eq :
        (fun ω ↦ Mproc (i + 1) ω) =ᵐ[P]
          fun ω ↦ M ω *
            fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u i ω :=
      Filter.Eventually.of_forall fun ω ↦ by
        simpa [Mproc, M] using
          fullProjectedRewardFeatureNoiseExpProcess_succ (A := A) (R := R) (ν := ν)
            (σ2 := σ2) (x := x) (v := v) (u := u) (n := i) (ω := ω)
    have h_cond_eq :
        P[Mproc (i + 1) | ℱ i] =ᵐ[P]
          P[fun ω ↦ M ω *
            fullProjectedRewardFeatureNoiseExpIncrement A R ν σ2 x v u i ω | ℱ i] :=
      condExp_congr_ae h_succ_eq
    filter_upwards [h_cond_eq, h_cond] with ω h_eq h_le
    rw [h_eq]
    exact h_le

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Projecting the full centered response vector gives the sum of full projected reward-feature
noise terms. -/
lemma dotProduct_centeredResponseVector_eq_fullProjectedRewardFeatureNoise_sum
    (v : Feature d) :
    dotProduct v (centeredResponseVector A R ν x n ω) =
      ∑ t ∈ range n, fullProjectedRewardFeatureNoise A R ν x v t ω := by
  have hcenter :
      centeredResponseVector A R ν x n ω =
        ∑ t ∈ range n, rewardNoise A R ν t ω • x (A t ω) := by
    ext i
    simp [centeredResponseVector, responseVector, meanResponseVector, rewardNoise,
      Finset.sum_sub_distrib, smul_eq_mul, sub_mul]
  rw [hcenter]
  simp only [fullProjectedRewardFeatureNoise]
  change dotProduct v
      (∑ t ∈ range n, rewardNoise A R ν t ω • x (A t ω)) =
    ∑ t ∈ range n, dotProduct v (x (A t ω)) * rewardNoise A R ν t ω
  simp only [dotProduct, Finset.sum_apply]
  calc
    ∑ i, v i *
        (∑ t ∈ range n, (rewardNoise A R ν t ω • x (A t ω)) i)
        = ∑ i, ∑ t ∈ range n,
            v i * (rewardNoise A R ν t ω • x (A t ω)) i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [Finset.mul_sum]
    _ = ∑ t ∈ range n, ∑ i,
          v i * (rewardNoise A R ν t ω • x (A t ω)) i := by
        rw [Finset.sum_comm]
    _ = ∑ t ∈ range n, dotProduct v (x (A t ω)) * rewardNoise A R ν t ω := by
        refine Finset.sum_congr rfl ?_
        intro t _ht
        simp only [Pi.smul_apply, smul_eq_mul, dotProduct]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i _hi
        ring

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The full fixed-direction exponential process is exactly the normalized exponential of the
projection of the centered response vector. -/
lemma fullProjectedRewardFeatureNoiseExpProcess_eq_centeredResponseVector
    (σ2 : ℝ≥0) (v : Feature d) (u : ℝ) :
    fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω =
      Real.exp
        (u * dotProduct v (centeredResponseVector A R ν x n ω) -
          fullProjectedRewardFeatureNoiseRealizedVarianceSum A σ2 x v n ω * u ^ 2 / 2) := by
  rw [fullProjectedRewardFeatureNoiseExpProcess,
    dotProduct_centeredResponseVector_eq_fullProjectedRewardFeatureNoise_sum
      (A := A) (R := R) (ν := ν) (x := x) (n := n) (ω := ω) v]

/-- Fixed-direction exponential-supermartingale bound stated directly for the centered response
vector. This is the scalar form immediately before the textbook Gaussian-mixture argument. -/
lemma integral_exp_dotProduct_centeredResponseVector_sub_fullRealizedVariance_le_one_of_abs_le
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ) :
    ∫ ω, Real.exp
        (u * dotProduct v (centeredResponseVector A R ν x n ω) -
          fullProjectedRewardFeatureNoiseRealizedVarianceSum A σ2 x v n ω * u ^ 2 / 2) ∂P
      ≤ 1 := by
  simpa [fullProjectedRewardFeatureNoiseExpProcess_eq_centeredResponseVector
    (A := A) (R := R) (ν := ν) (x := x) (n := n) (σ2 := σ2) (v := v) (u := u)] using
    integral_fullProjectedRewardFeatureNoiseExpProcess_le_one_of_abs_le
      (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := n)
      h hν v Q hQ hQ_bound u

/-- Fixed-direction exponential-supermartingale bound with the realized variance written as the
quadratic form of the non-ridge part of the design matrix. -/
lemma integral_exp_dotProduct_centeredResponseVector_sub_designMatrix_sub_reg_le_one_of_abs_le
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ) :
    ∫ ω, Real.exp
        (u * dotProduct v (centeredResponseVector A R ν x n ω) -
          ((σ2 : ℝ) *
            dotProduct v
              (Matrix.mulVec
                (designMatrix A reg x n ω - reg • (1 : Matrix (Fin d) (Fin d) ℝ)) v)) *
              u ^ 2 / 2) ∂P
      ≤ 1 := by
  simpa [fullProjectedRewardFeatureNoiseRealizedVarianceSum_eq_sigma_mul_designMatrix_sub_reg
    (A := A) (reg := reg) (x := x) (σ2 := σ2) (v := v) (n := n)] using
    integral_exp_dotProduct_centeredResponseVector_sub_fullRealizedVariance_le_one_of_abs_le
      (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := n)
      h hν v Q hQ hQ_bound u

/-- Fixed-direction exponential-supermartingale bound with the realized variance written as
`σ² * (vᵀV_n v - reg * vᵀv)`. This is the algebraic form immediately before adding the Gaussian
mixture's ridge term. -/
lemma integral_exp_centeredResponse_sub_designMatrix_minus_reg_norm_le_one_of_abs_le
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ) :
    ∫ ω, Real.exp
        (u * dotProduct v (centeredResponseVector A R ν x n ω) -
          ((σ2 : ℝ) *
            (dotProduct v (Matrix.mulVec (designMatrix A reg x n ω) v) -
              reg * dotProduct v v)) *
              u ^ 2 / 2) ∂P
      ≤ 1 := by
  simpa [fullProjectedRewardFeatureNoiseRealizedVarianceSum_eq_sigma_mul_designMatrix_minus_reg_norm
    (A := A) (reg := reg) (x := x) (σ2 := σ2) (v := v) (n := n)] using
    integral_exp_dotProduct_centeredResponseVector_sub_fullRealizedVariance_le_one_of_abs_le
      (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := n)
      h hν v Q hQ hQ_bound u

/-- Fixed-direction exponential-supermartingale bound with the finite-action projection bound
chosen automatically. This is the scalar theorem used immediately before the textbook
Gaussian-mixture step. -/
lemma integral_exp_centeredResponse_sub_designMatrix_minus_reg_norm_le_one
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (u : ℝ) :
    ∫ ω, Real.exp
        (u * dotProduct v (centeredResponseVector A R ν x n ω) -
          ((σ2 : ℝ) *
            (dotProduct v (Matrix.mulVec (designMatrix A reg x n ω) v) -
              reg * dotProduct v v)) *
              u ^ 2 / 2) ∂P
      ≤ 1 := by
  obtain ⟨Q, hQ, hQ_bound⟩ := exists_abs_dotProduct_feature_bound x v
  exact integral_exp_centeredResponse_sub_designMatrix_minus_reg_norm_le_one_of_abs_le
    (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := n)
    h hν v Q hQ hQ_bound u

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Fixed-vector exponent from the scalar self-normalized proof.

For a fixed direction `λ`, this is
`λᵀ S_t - (σ² / 2) * (λᵀ V_t λ - reg * λᵀλ)`, where `S_t` is the centered
response vector and `V_t` is the regularized design matrix. This is the quantity that the
Gaussian-mixture proof integrates over `λ`. -/
noncomputable def centeredResponseDirectionalExponent
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (ν : Kernel (Fin K) ℝ)
    (reg : ℝ) (σ2 : ℝ≥0) (x : Fin K → Feature d) (n : ℕ) (ω : Ω)
    (lambda : Feature d) : ℝ :=
  dotProduct lambda (centeredResponseVector A R ν x n ω) -
    ((σ2 : ℝ) *
      (dotProduct lambda (Matrix.mulVec (designMatrix A reg x n ω) lambda) -
        reg * dotProduct lambda lambda)) / 2

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The Gaussian prior penalty cancels the ridge-regularization term in the fixed-direction
exponent.

In the textbook method-of-mixtures proof, the fixed-direction supermartingale contributes
`λᵀS_t - (σ² / 2) * λᵀ(V_t - reg I)λ`, while the Gaussian mixing density contributes
`-(σ² * reg / 2) * λᵀλ`.  Adding those two exponents leaves the clean quadratic
`λᵀS_t - (σ² / 2) * λᵀV_tλ`, which is the expression that can be completed into a square. -/
lemma centeredResponseDirectionalExponent_sub_priorPenalty_eq
    (σ2 : ℝ≥0) (lambda : Feature d) :
    centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda -
        ((σ2 : ℝ) * reg * dotProduct lambda lambda) / 2 =
      dotProduct lambda (centeredResponseVector A R ν x n ω) -
        ((σ2 : ℝ) *
          dotProduct lambda (Matrix.mulVec (designMatrix A reg x n ω) lambda)) / 2 := by
  unfold centeredResponseDirectionalExponent
  ring

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The existing full fixed-direction exponential process at multiplier `1` is exactly the
exponential of the named textbook directional exponent. -/
lemma fullProjectedRewardFeatureNoiseExpProcess_one_eq_exp_centeredResponseDirectionalExponent
    (σ2 : ℝ≥0) (lambda : Feature d) :
    fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x lambda (1 : ℝ) n ω =
      Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda) := by
  rw [fullProjectedRewardFeatureNoiseExpProcess_eq_centeredResponseVector]
  simp [centeredResponseDirectionalExponent,
    fullProjectedRewardFeatureNoiseRealizedVarianceSum_eq_sigma_mul_designMatrix_minus_reg_norm
      (A := A) (reg := reg) (x := x) (σ2 := σ2) (v := lambda) (n := n)]

/-- Integrability of the named fixed-vector exponential integrand used by the textbook
Gaussian-mixture proof. -/
lemma integrable_exp_centeredResponseDirectionalExponent
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (lambda : Feature d) :
    Integrable
      (fun ω ↦
        Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda)) P := by
  obtain ⟨Q, hQ, hQ_bound⟩ := exists_abs_dotProduct_feature_bound x lambda
  exact (fullProjectedRewardFeatureNoiseExpProcess_integrable_of_abs_le
    (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := n)
    h hν lambda Q hQ hQ_bound (1 : ℝ)).congr
    (Filter.Eventually.of_forall fun ω ↦ by
      exact fullProjectedRewardFeatureNoiseExpProcess_one_eq_exp_centeredResponseDirectionalExponent
        (A := A) (R := R) (reg := reg) (x := x) (ν := ν) (n := n) (ω := ω)
        σ2 lambda)

/-- Fixed-vector textbook exponential process as a Mathlib `Supermartingale`.

For each fixed direction `λ`, this packages the scalar exponential-supermartingale result in the
notation used by the textbook mixture proof:
`exp(λᵀ S_t - (σ² / 2) * λᵀ(V_t - reg I)λ)`.

The remaining textbook Gaussian-mixture step has to integrate this fixed-`λ` supermartingale over
`λ`; this lemma supplies the pointwise-in-`λ` process without exposing the internal projected-noise
process names. -/
lemma supermartingale_exp_centeredResponseDirectionalExponent
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (lambda : Feature d) :
    Supermartingale
      (fun n ω ↦
        Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda))
      (IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback) P := by
  obtain ⟨Q, hQ, hQ_bound⟩ := exists_abs_dotProduct_feature_bound x lambda
  let ℱ := IsAlgEnvSeq.filtrationAction h.measurable_action h.measurable_feedback
  let M : ℕ → Ω → ℝ :=
    fun n ω ↦ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x lambda (1 : ℝ) n ω
  let G : ℕ → Ω → ℝ :=
    fun n ω ↦
      Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda)
  have hM : Supermartingale M ℱ P := by
    simpa [M, ℱ] using
      supermartingale_fullProjectedRewardFeatureNoiseExpProcess_of_abs_le
        (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
        h hν lambda Q hQ hQ_bound (1 : ℝ)
  have hMG : ∀ n, M n = G n := by
    intro n
    funext ω
    exact fullProjectedRewardFeatureNoiseExpProcess_one_eq_exp_centeredResponseDirectionalExponent
      (A := A) (R := R) (reg := reg) (x := x) (ν := ν) (n := n) (ω := ω)
      σ2 lambda
  simpa [G, ℱ] using supermartingale_congr_eq (P := P) (ℱ := ℱ) hM hMG

/-- Fixed-vector exponential bound in the named form used by the textbook Gaussian-mixture proof.

The scalar concentration core already proves this bound for every fixed direction and scalar
multiplier. This theorem packages the `u = 1` case around
`centeredResponseDirectionalExponent`, which is the exact integrand exponent that the future
Gaussian-mixture theorem must integrate over `λ`. -/
lemma integral_exp_centeredResponseDirectionalExponent_le_one
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (lambda : Feature d) :
    ∫ ω,
      Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda) ∂P ≤ 1 := by
  simpa [centeredResponseDirectionalExponent, mul_assoc] using
    integral_exp_centeredResponse_sub_designMatrix_minus_reg_norm_le_one
      (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := n)
      h hν lambda (1 : ℝ)

/-- Markov tail bound for the fixed-direction exponential process, with an explicit projection
bound.

This is the scalar probability step immediately after the exponential-supermartingale integral
bound and immediately before the textbook Gaussian-mixture argument. -/
lemma probReal_fullProjectedRewardFeatureNoiseExpProcess_ge_le_of_abs_le
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    P.real {ω |
      threshold ≤ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω} ≤
        1 / threshold := by
  have hmarkov :
      threshold *
          P.real {ω |
            threshold ≤ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω} ≤
        ∫ ω, fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω ∂P :=
    mul_meas_ge_le_integral_of_nonneg
      (μ := P)
      (f := fun ω ↦ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω)
      (Filter.Eventually.of_forall fun ω ↦
        fullProjectedRewardFeatureNoiseExpProcess_nonneg (A := A) (R := R)
          (ν := ν) (σ2 := σ2) (x := x) (v := v) (u := u) (n := n) (ω := ω))
      (fullProjectedRewardFeatureNoiseExpProcess_integrable_of_abs_le (A := A)
        (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := n)
        h hν v Q hQ hQ_bound u)
      threshold
  have hmul :
      threshold *
          P.real {ω |
            threshold ≤ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω} ≤
        1 :=
    hmarkov.trans
      (integral_fullProjectedRewardFeatureNoiseExpProcess_le_one_of_abs_le
        (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := n)
        h hν v Q hQ hQ_bound u)
  rw [le_div_iff₀ hthreshold]
  simpa [mul_comm] using hmul

/-- Fixed-direction exponential-process tail bound at threshold `1 / δ`, with an explicit
projection bound. -/
lemma probReal_fullProjectedRewardFeatureNoiseExpProcess_ge_inv_delta_le_of_abs_le
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (u : ℝ)
    {δ : ℝ} (hδ_pos : 0 < δ) :
    P.real {ω |
      1 / δ ≤ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω} ≤ δ := by
  have htail :=
    probReal_fullProjectedRewardFeatureNoiseExpProcess_ge_le_of_abs_le
      (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := n)
      h hν v Q hQ hQ_bound u (one_div_pos.mpr hδ_pos)
  have hinv : 1 / (1 / δ) = δ := by
    field_simp [hδ_pos.ne']
  simpa [hinv] using htail

/-- Fixed-direction exponential-process tail bound with the finite-action projection bound chosen
automatically. -/
lemma probReal_fullProjectedRewardFeatureNoiseExpProcess_ge_inv_delta_le
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (u : ℝ) {δ : ℝ} (hδ_pos : 0 < δ) :
    P.real {ω |
      1 / δ ≤ fullProjectedRewardFeatureNoiseExpProcess A R ν σ2 x v u n ω} ≤ δ := by
  obtain ⟨Q, hQ, hQ_bound⟩ := exists_abs_dotProduct_feature_bound x v
  exact probReal_fullProjectedRewardFeatureNoiseExpProcess_ge_inv_delta_le_of_abs_le
    (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := n)
    h hν v Q hQ hQ_bound u hδ_pos

/-- Fixed-direction exponential-process tail bound in the centered-response/design-matrix form
used by the textbook Gaussian-mixture proof. -/
lemma probReal_exp_centeredResponse_sub_designMatrix_minus_reg_norm_ge_inv_delta_le
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (u : ℝ) {δ : ℝ} (hδ_pos : 0 < δ) :
    P.real {ω |
      1 / δ ≤
        Real.exp
          (u * dotProduct v (centeredResponseVector A R ν x n ω) -
            ((σ2 : ℝ) *
              (dotProduct v (Matrix.mulVec (designMatrix A reg x n ω) v) -
                reg * dotProduct v v)) *
                u ^ 2 / 2)} ≤ δ := by
  simpa [fullProjectedRewardFeatureNoiseExpProcess_eq_centeredResponseVector
    (A := A) (R := R) (ν := ν) (x := x) (n := n) (σ2 := σ2) (v := v) (u := u),
    fullProjectedRewardFeatureNoiseRealizedVarianceSum_eq_sigma_mul_designMatrix_minus_reg_norm
      (A := A) (reg := reg) (x := x) (σ2 := σ2) (v := v) (n := n)] using
    probReal_fullProjectedRewardFeatureNoiseExpProcess_ge_inv_delta_le
      (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν) (n := n)
      h hν v u hδ_pos

/-- Fixed-direction subgaussianity of the full centered response vector. -/
lemma dotProduct_centeredResponseVector_hasSubgaussianMGF_of_abs_le
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (n : ℕ) :
    HasSubgaussianMGF
      (fun ω ↦ dotProduct v (centeredResponseVector A R ν x n ω))
      (∑ _t ∈ range n, (⟨Q ^ 2, sq_nonneg Q⟩ * σ2 : ℝ≥0)) P := by
  exact (fullProjectedRewardFeatureNoise_sum_hasSubgaussianMGF_of_abs_le
    (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
    h hν v Q hQ hQ_bound n).congr
    (Filter.Eventually.of_forall fun ω ↦
      (dotProduct_centeredResponseVector_eq_fullProjectedRewardFeatureNoise_sum
        (A := A) (R := R) (ν := ν) (x := x) (n := n) (ω := ω) v).symm)

/-- One-sided tail bound for a fixed direction of the full centered response vector. -/
lemma probReal_dotProduct_centeredResponseVector_ge_le_of_abs_le
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (linUCBAlgorithm hK reg β x) (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (n : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real
        {ω | ε ≤ dotProduct v (centeredResponseVector A R ν x n ω)}
      ≤ Real.exp
        (-ε ^ 2 /
          (2 * (∑ _t ∈ range n, (⟨Q ^ 2, sq_nonneg Q⟩ * σ2 : ℝ≥0)))) :=
  (dotProduct_centeredResponseVector_hasSubgaussianMGF_of_abs_le
    (A := A) (R := R) (reg := reg) (β := β) (x := x) (ν := ν)
    h hν v Q hQ hQ_bound n).measure_ge_le hε

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The scalar projected-noise sum is exactly the dot product of the direction with the
positive-time centered response vector. -/
lemma dotProduct_positiveTimeCenteredResponseVector_eq_projectedRewardFeatureNoise_sum
    (v : Feature d) :
    dotProduct v (positiveTimeCenteredResponseVector A R ν x n ω) =
      ∑ t ∈ range n, projectedRewardFeatureNoise A R ν x v t ω := by
  change dotProduct v
      (∑ t ∈ range n, if t = 0 then 0 else rewardNoise A R ν t ω • x (A t ω)) =
    ∑ t ∈ range n,
      (if t = 0 then 0 else dotProduct v (x (A t ω)) * rewardNoise A R ν t ω)
  simp only [dotProduct, Finset.sum_apply]
  calc
    ∑ i, v i *
        (∑ t ∈ range n, (if t = 0 then 0 else rewardNoise A R ν t ω • x (A t ω)) i)
        = ∑ i, ∑ t ∈ range n,
            v i * (if t = 0 then 0 else rewardNoise A R ν t ω • x (A t ω)) i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [Finset.mul_sum]
    _ = ∑ t ∈ range n, ∑ i,
          v i * (if t = 0 then 0 else rewardNoise A R ν t ω • x (A t ω)) i := by
        rw [Finset.sum_comm]
    _ = ∑ t ∈ range n,
          if t = 0 then 0 else dotProduct v (x (A t ω)) * rewardNoise A R ν t ω := by
        refine Finset.sum_congr rfl ?_
        intro t _ht
        by_cases ht0 : t = 0
        · simp [ht0]
        · simp only [ht0, if_false, Pi.smul_apply, smul_eq_mul, dotProduct]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The projected-noise sum can be rewritten as a dot product with the positive-time centered
response vector. -/
lemma projectedRewardFeatureNoise_sum_eq_dotProduct_positiveTimeCenteredResponseVector
    (v : Feature d) :
    (∑ t ∈ range n, projectedRewardFeatureNoise A R ν x v t ω) =
      dotProduct v (positiveTimeCenteredResponseVector A R ν x n ω) := by
  rw [dotProduct_positiveTimeCenteredResponseVector_eq_projectedRewardFeatureNoise_sum]

/-- Fixed-direction subgaussianity of the positive-time centered response vector. -/
lemma dotProduct_positiveTimeCenteredResponseVector_hasSubgaussianMGF_of_abs_le
    {alg : Algorithm (Fin K) ℝ}
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (n : ℕ) :
    HasSubgaussianMGF
      (fun ω ↦ dotProduct v (positiveTimeCenteredResponseVector A R ν x n ω))
      (∑ t ∈ range n, if t = 0 then 0 else (⟨Q ^ 2, sq_nonneg Q⟩ * σ2 : ℝ≥0)) P := by
  exact (projectedRewardFeatureNoise_sum_hasSubgaussianMGF_of_abs_le
    (A := A) (R := R) (ν := ν) (x := x) h hν v Q hQ hQ_bound n).congr
    (Filter.Eventually.of_forall fun ω ↦
      projectedRewardFeatureNoise_sum_eq_dotProduct_positiveTimeCenteredResponseVector
        (A := A) (R := R) (ν := ν) (x := x) (n := n) (ω := ω) v)

/-- One-sided tail bound for a fixed direction of the positive-time centered response vector. -/
lemma probReal_dotProduct_positiveTimeCenteredResponseVector_ge_le_of_abs_le
    {alg : Algorithm (Fin K) ℝ}
    [StandardBorelSpace Ω] [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    (v : Feature d) (Q : ℝ) (hQ : 0 ≤ Q)
    (hQ_bound : ∀ a, |dotProduct v (x a)| ≤ Q) (n : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real
        {ω |
          ε ≤ dotProduct v (positiveTimeCenteredResponseVector A R ν x n ω)}
      ≤ Real.exp
        (-ε ^ 2 /
          (2 * (∑ t ∈ range n,
            if t = 0 then 0 else (⟨Q ^ 2, sq_nonneg Q⟩ * σ2 : ℝ≥0)))) :=
  (dotProduct_positiveTimeCenteredResponseVector_hasSubgaussianMGF_of_abs_le
    (A := A) (R := R) (ν := ν) (x := x) h hν v Q hQ hQ_bound n).measure_ge_le hε

/-- Under the UCB-style arm-wise reward-noise assumption, every predictable scalar projection of the
positive-time reward-noise conditional law is subgaussian with the squared projection coefficient.

This is still a conditional-law statement, not yet the final martingale concentration theorem. It
is the local scalar ingredient that the vector self-normalized argument must combine over time and
directions. -/
lemma rewardNoise_condDistrib_history_action_constMul_subgaussian
    {alg : Algorithm (Fin K) ℝ}
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {σ2 : ℝ≥0} (hν : RewardNoiseSubgaussian (K := K) ν σ2)
    {t : ℕ} (ht : t ≠ 0)
    (q : (Iic (t - 1) → Fin K × ℝ) × Fin K → ℝ) :
    ∀ᵐ z ∂P.map (fun ω ↦ (history A R (t - 1) ω, A t ω)),
      HasSubgaussianMGF (fun η ↦ q z * η)
        (⟨q z ^ 2, sq_nonneg (q z)⟩ * σ2)
        (condDistrib (rewardNoise A R ν t)
          (fun ω ↦ (history A R (t - 1) ω, A t ω)) P z) := by
  have h_cond := hasCondDistrib_rewardNoise_history_action
    (A := A) (R := R) (ν := ν) h ht
  have h_kernel :
      ∀ z : (Iic (t - 1) → Fin K × ℝ) × Fin K,
        HasSubgaussianMGF (fun η ↦ q z * η)
          (⟨q z ^ 2, sq_nonneg (q z)⟩ * σ2)
          ((rewardNoiseKernel ν).prodMkLeft (Iic (t - 1) → Fin K × ℝ) z) :=
    (RewardNoiseKernelSubgaussian.of_rewardNoiseSubgaussian
      (K := K) (ν := ν) hν).prodMkLeft_constMul q
  filter_upwards [h_cond.condDistrib_eq] with z hz
  rw [hz]
  exact h_kernel z

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The centered response vector is the accumulated reward noise times the selected feature
vectors: `∑_{s<t} η_s x_{A_s}`. This is the vector martingale term in the textbook
self-normalized concentration proof. -/
lemma centeredResponseVector_eq_sum_rewardNoise_smul :
    centeredResponseVector A R ν x n ω =
      ∑ s ∈ range n, rewardNoise A R ν s ω • x (A s ω) := by
  ext i
  simp [centeredResponseVector, responseVector, meanResponseVector, rewardNoise,
    Finset.sum_sub_distrib, smul_eq_mul, sub_mul]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Before any observations, the centered response vector is zero. -/
lemma centeredResponseVector_zero :
    centeredResponseVector A R ν x 0 ω = 0 := by
  simp [centeredResponseVector, responseVector, meanResponseVector]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Updating the centered response vector adds the next centered reward times its selected feature
vector. -/
lemma centeredResponseVector_succ :
    centeredResponseVector A R ν x (n + 1) ω =
      centeredResponseVector A R ν x n ω + rewardNoise A R ν n ω • x (A n ω) := by
  simp [centeredResponseVector_eq_sum_rewardNoise_smul, sum_range_succ]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The full centered response vector splits into its time-zero contribution plus the positive-time
martingale term. -/
lemma centeredResponseVector_eq_initial_add_positiveTime :
    centeredResponseVector A R ν x n ω =
      initialCenteredResponseVector A R ν x n ω +
        positiveTimeCenteredResponseVector A R ν x n ω := by
  rw [centeredResponseVector_eq_sum_rewardNoise_smul]
  by_cases hn : n = 0
  · simp [hn, initialCenteredResponseVector, positiveTimeCenteredResponseVector]
  · rw [initialCenteredResponseVector, positiveTimeCenteredResponseVector]
    simp only [hn, if_false]
    calc
      ∑ s ∈ range n, rewardNoise A R ν s ω • x (A s ω)
          = ∑ s ∈ range n,
              ((if s = 0 then rewardNoise A R ν 0 ω • x (A 0 ω) else 0) +
                if s = 0 then 0 else rewardNoise A R ν s ω • x (A s ω)) := by
            refine Finset.sum_congr rfl ?_
            intro s _hs
            by_cases hs0 : s = 0
            · simp [hs0]
            · simp [hs0]
      _ = (∑ s ∈ range n,
              if s = 0 then rewardNoise A R ν 0 ω • x (A 0 ω) else 0) +
            ∑ s ∈ range n,
              if s = 0 then 0 else rewardNoise A R ν s ω • x (A s ω) := by
            rw [Finset.sum_add_distrib]
      _ = rewardNoise A R ν 0 ω • x (A 0 ω) +
            ∑ s ∈ range n,
              if s = 0 then 0 else rewardNoise A R ν s ω • x (A s ω) := by
            rw [Finset.sum_ite_eq']
            simp [Nat.pos_of_ne_zero hn]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Projecting the full centered response vector splits into the initial projection plus the
positive-time projected noise sum. -/
lemma dotProduct_centeredResponseVector_eq_initial_add_positiveTime
    (v : Feature d) :
    dotProduct v (centeredResponseVector A R ν x n ω) =
      dotProduct v (initialCenteredResponseVector A R ν x n ω) +
        dotProduct v (positiveTimeCenteredResponseVector A R ν x n ω) := by
  rw [centeredResponseVector_eq_initial_add_positiveTime]
  simp only [dotProduct, Pi.add_apply]
  calc
    ∑ i, v i *
        (initialCenteredResponseVector A R ν x n ω i +
          positiveTimeCenteredResponseVector A R ν x n ω i)
        = ∑ i,
            (v i * initialCenteredResponseVector A R ν x n ω i +
              v i * positiveTimeCenteredResponseVector A R ν x n ω i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
    _ = (∑ i, v i * initialCenteredResponseVector A R ν x n ω i) +
          ∑ i, v i * positiveTimeCenteredResponseVector A R ν x n ω i := by
        rw [Finset.sum_add_distrib]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Projecting the full centered response vector gives the initial projected noise plus the
positive-time projected-noise sum. -/
lemma dotProduct_centeredResponseVector_eq_initial_add_projectedRewardFeatureNoise_sum
    (v : Feature d) :
    dotProduct v (centeredResponseVector A R ν x n ω) =
      (if n = 0 then 0 else dotProduct v (x (A 0 ω)) * rewardNoise A R ν 0 ω) +
        ∑ t ∈ range n, projectedRewardFeatureNoise A R ν x v t ω := by
  rw [dotProduct_centeredResponseVector_eq_initial_add_positiveTime,
    dotProduct_initialCenteredResponseVector,
    dotProduct_positiveTimeCenteredResponseVector_eq_projectedRewardFeatureNoise_sum]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The vector inside the centered-noise-plus-bias quadratic form, written in the textbook
`∑ η_s x_s - reg • θ` form. -/
lemma centeredResponseVector_sub_reg_eq_sum_rewardNoise_smul_sub_reg (θ : Feature d) :
    centeredResponseVector A R ν x n ω - reg • θ =
      (∑ s ∈ range n, rewardNoise A R ν s ω • x (A s ω)) - reg • θ := by
  rw [centeredResponseVector_eq_sum_rewardNoise_smul]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Under linear realizability, multiplying the true parameter by the design matrix gives the
regularization bias plus the mean response vector:
`V_t θ = reg • θ + ∑ μ(A_s) x_{A_s}`. -/
lemma designMatrix_mulVec_linearMeanParameter
    (θ : Feature d)
    (h_linear : LinearMeanModel ν x θ) :
    Matrix.mulVec (designMatrix A reg x n ω) θ =
      reg • θ + meanResponseVector A ν x n ω := by
  ext i
  simp only [designMatrix, meanResponseVector, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.sum_mulVec, Matrix.vecMulVec_mulVec, Matrix.one_mulVec, Finset.sum_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine sum_congr rfl ?_
  intro s _hs
  rw [dotProduct_comm (x (A s ω)) θ, ← h_linear (A s ω)]
  simp [mul_comm]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Deterministic least-squares algebra before using invertibility:
`Y_t - V_t θ = centeredResponse_t - reg • θ`. -/
lemma responseVector_sub_designMatrix_mulVec_linearMeanParameter
    (θ : Feature d)
    (h_linear : LinearMeanModel ν x θ) :
    responseVector A R x n ω - Matrix.mulVec (designMatrix A reg x n ω) θ =
      centeredResponseVector A R ν x n ω - reg • θ := by
  rw [designMatrix_mulVec_linearMeanParameter (A := A) (reg := reg) (x := x)
    (ν := ν) (n := n) (ω := ω) θ h_linear]
  simp [centeredResponseVector, sub_eq_add_neg, add_assoc, add_comm]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Deterministic least-squares error decomposition:
`V_t (θHat_t - θ) = centeredResponse_t - reg • θ`.

This is the algebraic bridge used by the textbook self-normalized proof. The remaining
probabilistic theorem has to control the centered response vector in the `V_t⁻¹` norm. -/
lemma designMatrix_mulVec_thetaHat_sub_linearMeanParameter
    (θ : Feature d)
    (h_linear : LinearMeanModel ν x θ)
    (hreg_pos : 0 < reg) :
    Matrix.mulVec (designMatrix A reg x n ω) (thetaHat A R reg x n ω - θ) =
      centeredResponseVector A R ν x n ω - reg • θ := by
  let V : Matrix (Fin d) (Fin d) ℝ := designMatrix A reg x n ω
  have hV : V.PosDef := designMatrix_posDef (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω) hreg_pos
  have hVdet : IsUnit V.det := by
    exact Matrix.isUnit_iff_isUnit_det (A := V) |>.mp hV.isUnit
  rw [Matrix.mulVec_sub]
  have htheta :
      Matrix.mulVec V (thetaHat A R reg x n ω) = responseVector A R x n ω := by
    simp [thetaHat, V, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hVdet]
  rw [htheta]
  rw [show Matrix.mulVec V θ = reg • θ + meanResponseVector A ν x n ω by
    subst V
    exact designMatrix_mulVec_linearMeanParameter (A := A) (reg := reg) (x := x)
      (ν := ν) (n := n) (ω := ω) θ h_linear]
  simp [centeredResponseVector, sub_eq_add_neg, add_assoc, add_comm]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Squared ellipsoid error of the least-squares estimate around a candidate linear parameter.

This is the process-level quantity `‖θHat_t - θ‖²_{V_t}` from the textbook confidence-set proof,
written as `(θHat_t - θ)ᵀ V_t (θHat_t - θ)`. -/
noncomputable def parameterErrorQuadraticForm
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (θ : Feature d)
    (n : ℕ) (ω : Ω) : ℝ :=
  dotProduct (thetaHat A R reg x n ω - θ)
    (Matrix.mulVec (designMatrix A reg x n ω) (thetaHat A R reg x n ω - θ))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The inverse-design quadratic form of the centered reward-feature vector plus the
regularization bias.

For `z_t = ∑_{s<t} (R_s - μ(A_s)) x_{A_s} - reg • θ`, this is `z_tᵀ V_t⁻¹ z_t`.
The textbook self-normalized concentration step should control this quantity, or a sharper
decomposition implying it. -/
noncomputable def centeredNoiseBiasQuadraticForm
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (ν : Kernel (Fin K) ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (θ : Feature d)
    (n : ℕ) (ω : Ω) : ℝ :=
  dotProduct (centeredResponseVector A R ν x n ω - reg • θ)
    (Matrix.mulVec (designMatrix A reg x n ω)⁻¹
      (centeredResponseVector A R ν x n ω - reg • θ))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Inverse-design norm of the random centered reward-feature vector alone.

This is the martingale/noise term controlled by the self-normalized concentration theorem in the
textbook proof, before adding the deterministic ridge-regularization bias. -/
noncomputable def centeredNoiseQuadraticForm
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ) (ν : Kernel (Fin K) ℝ)
    (reg : ℝ) (x : Fin K → Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  dotProduct (centeredResponseVector A R ν x n ω)
    (Matrix.mulVec (designMatrix A reg x n ω)⁻¹
      (centeredResponseVector A R ν x n ω))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Inverse-design norm of the deterministic ridge-regularization bias `reg • θ`. -/
noncomputable def regularizationBiasQuadraticForm
    (A : ℕ → Ω → Fin K) (reg : ℝ) (x : Fin K → Feature d)
    (θ : Feature d) (n : ℕ) (ω : Ω) : ℝ :=
  dotProduct (reg • θ)
    (Matrix.mulVec (designMatrix A reg x n ω)⁻¹ (reg • θ))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Completion of the square for the exponent that remains after the Gaussian prior penalty has
cancelled the ridge term.

This is the deterministic algebra in the textbook method-of-mixtures proof. With `S_t` the
centered response vector and `V_t` the design matrix, it rewrites

`λᵀS_t - (σ² / 2) λᵀV_tλ`

as

`(1 / (2σ²)) S_tᵀV_t⁻¹S_t
  - (σ² / 2) ‖λ - (1 / σ²) V_t⁻¹S_t‖²_{V_t}`.

After this identity, the remaining analytic step is a translated Gaussian integral whose normalizer
produces `sqrt(det V_t / det(reg I))`. -/
lemma centeredResponseDirectionalExponent_sub_priorPenalty_eq_completedSquare
    (σ2 : ℝ≥0) (lambda : Feature d)
    (hreg_pos : 0 < reg) (hσ2_ne : (σ2 : ℝ) ≠ 0) :
    centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda -
        ((σ2 : ℝ) * reg * dotProduct lambda lambda) / 2 =
      centeredNoiseQuadraticForm A R ν reg x n ω / (2 * (σ2 : ℝ)) -
        ((σ2 : ℝ) / 2) *
          dotProduct
            (lambda - (σ2 : ℝ)⁻¹ •
              Matrix.mulVec (designMatrix A reg x n ω)⁻¹
                (centeredResponseVector A R ν x n ω))
            (Matrix.mulVec (designMatrix A reg x n ω)
              (lambda - (σ2 : ℝ)⁻¹ •
                Matrix.mulVec (designMatrix A reg x n ω)⁻¹
                  (centeredResponseVector A R ν x n ω))) := by
  let σ : ℝ := (σ2 : ℝ)
  let V : Matrix (Fin d) (Fin d) ℝ := designMatrix A reg x n ω
  let S : Feature d := centeredResponseVector A R ν x n ω
  let y : Feature d := Matrix.mulVec V⁻¹ S
  let m : Feature d := σ⁻¹ • y
  have hV : V.PosDef := designMatrix_posDef (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω) hreg_pos
  have hVdet : IsUnit V.det := by
    exact Matrix.isUnit_iff_isUnit_det (A := V) |>.mp hV.isUnit
  have hVy : Matrix.mulVec V y = S := by
    simp [V, y, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hVdet]
  letI : SeminormedAddCommGroup (Feature d) := Matrix.toSeminormedAddCommGroup V hV.posSemidef
  letI : InnerProductSpace ℝ (Feature d) := Matrix.toInnerProductSpace V hV.posSemidef
  have h_dot_lambda :
      dotProduct lambda (Matrix.mulVec V lambda) = inner ℝ lambda lambda := by
    change dotProduct lambda (V *ᵥ lambda) = (V *ᵥ lambda) ⬝ᵥ lambda
    rw [dotProduct_comm]
  have h_dot_shift :
      dotProduct (lambda - m) (Matrix.mulVec V (lambda - m)) =
        inner ℝ (lambda - m) (lambda - m) := by
    change dotProduct (lambda - m) (V *ᵥ (lambda - m)) =
      (V *ᵥ (lambda - m)) ⬝ᵥ (lambda - m)
    rw [dotProduct_comm]
  have h_inner_lambda_y : inner ℝ lambda y = dotProduct lambda S := by
    change (V *ᵥ y) ⬝ᵥ lambda = dotProduct lambda S
    rw [hVy, dotProduct_comm]
  have h_inner_y_y :
      inner ℝ y y = centeredNoiseQuadraticForm A R ν reg x n ω := by
    change (V *ᵥ y) ⬝ᵥ y =
      dotProduct S (Matrix.mulVec V⁻¹ S)
    rw [hVy]
  have h_inner_shift :
      inner ℝ (lambda - m) (lambda - m) =
        inner ℝ lambda lambda - 2 * σ⁻¹ * dotProduct lambda S +
          σ⁻¹ * σ⁻¹ * centeredNoiseQuadraticForm A R ν reg x n ω := by
    rw [show m = σ⁻¹ • y by rfl]
    rw [inner_sub_sub_self]
    have h_left :
        inner ℝ lambda (σ⁻¹ • y) = σ⁻¹ * dotProduct lambda S := by
      rw [real_inner_smul_right, h_inner_lambda_y]
    have h_right :
        inner ℝ (σ⁻¹ • y) lambda = σ⁻¹ * dotProduct lambda S := by
      rw [real_inner_smul_left, real_inner_comm, h_inner_lambda_y]
    have h_self :
        inner ℝ (σ⁻¹ • y) (σ⁻¹ • y) =
          σ⁻¹ * σ⁻¹ * centeredNoiseQuadraticForm A R ν reg x n ω := by
      rw [real_inner_smul_left, real_inner_smul_right, h_inner_y_y]
      ring
    rw [h_left, h_right, h_self]
    ring
  have h_cancel :
      centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda -
          (σ * reg * dotProduct lambda lambda) / 2 =
        dotProduct lambda S -
          (σ * dotProduct lambda (Matrix.mulVec V lambda)) / 2 := by
    simpa [σ, V, S] using
      centeredResponseDirectionalExponent_sub_priorPenalty_eq
        (A := A) (R := R) (ν := ν) (reg := reg) (x := x) (n := n) (ω := ω)
        σ2 lambda
  calc
    centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda -
        ((σ2 : ℝ) * reg * dotProduct lambda lambda) / 2
        = dotProduct lambda S - (σ * dotProduct lambda (Matrix.mulVec V lambda)) / 2 := by
          simpa [σ] using h_cancel
    _ =
      centeredNoiseQuadraticForm A R ν reg x n ω / (2 * σ) -
        (σ / 2) * dotProduct (lambda - m) (Matrix.mulVec V (lambda - m)) := by
          rw [h_dot_lambda, h_dot_shift, h_inner_shift]
          field_simp [hσ2_ne, σ]
          ring
    _ =
      centeredNoiseQuadraticForm A R ν reg x n ω / (2 * (σ2 : ℝ)) -
        ((σ2 : ℝ) / 2) *
          dotProduct
            (lambda - (σ2 : ℝ)⁻¹ •
              Matrix.mulVec (designMatrix A reg x n ω)⁻¹
                (centeredResponseVector A R ν x n ω))
            (Matrix.mulVec (designMatrix A reg x n ω)
              (lambda - (σ2 : ℝ)⁻¹ •
                Matrix.mulVec (designMatrix A reg x n ω)⁻¹
                  (centeredResponseVector A R ν x n ω))) := by
          rfl

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Exponential form of the completed-square identity.

This is the integrand shape needed by the Gaussian-mixture proof: after multiplying the
fixed-direction supermartingale integrand by the Gaussian prior density's ridge penalty, the
dependence on `lambda` is only the translated quadratic kernel, while the
`centeredNoiseQuadraticForm` factor is independent of `lambda`. -/
lemma exp_centeredResponseDirectionalExponent_sub_priorPenalty_eq_completedSquare
    (σ2 : ℝ≥0) (lambda : Feature d)
    (hreg_pos : 0 < reg) (hσ2_ne : (σ2 : ℝ) ≠ 0) :
    Real.exp
        (centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda -
          ((σ2 : ℝ) * reg * dotProduct lambda lambda) / 2) =
      Real.exp (centeredNoiseQuadraticForm A R ν reg x n ω / (2 * (σ2 : ℝ))) *
        Real.exp
          (-(((σ2 : ℝ) / 2) *
            dotProduct
              (lambda - (σ2 : ℝ)⁻¹ •
                Matrix.mulVec (designMatrix A reg x n ω)⁻¹
                  (centeredResponseVector A R ν x n ω))
              (Matrix.mulVec (designMatrix A reg x n ω)
                (lambda - (σ2 : ℝ)⁻¹ •
                  Matrix.mulVec (designMatrix A reg x n ω)⁻¹
                    (centeredResponseVector A R ν x n ω))))) := by
  rw [centeredResponseDirectionalExponent_sub_priorPenalty_eq_completedSquare
    (A := A) (R := R) (ν := ν) (reg := reg) (x := x) (n := n) (ω := ω)
    σ2 lambda hreg_pos hσ2_ne]
  rw [sub_eq_add_neg, Real.exp_add]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Multiplicative form of the completed-square identity used by the Gaussian-mixture proof.

The left-hand side is the product of the fixed-direction supermartingale integrand and the
unnormalized Gaussian prior penalty. The right-hand side separates the `lambda`-independent
self-normalized factor from the translated Gaussian kernel. -/
lemma exp_centeredResponseDirectionalExponent_mul_exp_neg_priorPenalty_eq_completedSquare
    (σ2 : ℝ≥0) (lambda : Feature d)
    (hreg_pos : 0 < reg) (hσ2_ne : (σ2 : ℝ) ≠ 0) :
    Real.exp (centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda) *
        Real.exp (-(((σ2 : ℝ) * reg * dotProduct lambda lambda) / 2)) =
      Real.exp (centeredNoiseQuadraticForm A R ν reg x n ω / (2 * (σ2 : ℝ))) *
        Real.exp
          (-(((σ2 : ℝ) / 2) *
            dotProduct
              (lambda - (σ2 : ℝ)⁻¹ •
                Matrix.mulVec (designMatrix A reg x n ω)⁻¹
                  (centeredResponseVector A R ν x n ω))
              (Matrix.mulVec (designMatrix A reg x n ω)
                (lambda - (σ2 : ℝ)⁻¹ •
                  Matrix.mulVec (designMatrix A reg x n ω)⁻¹
                    (centeredResponseVector A R ν x n ω))))) := by
  rw [← Real.exp_add]
  have h_arg :
      centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda +
          -(((σ2 : ℝ) * reg * dotProduct lambda lambda) / 2) =
        centeredResponseDirectionalExponent A R ν reg σ2 x n ω lambda -
          ((σ2 : ℝ) * reg * dotProduct lambda lambda) / 2 := by
    ring
  rw [h_arg]
  exact exp_centeredResponseDirectionalExponent_sub_priorPenalty_eq_completedSquare
    (A := A) (R := R) (ν := ν) (reg := reg) (x := x) (n := n) (ω := ω)
    σ2 lambda hreg_pos hσ2_ne

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- A coordinate-wise absolute-value bound controls the squared Euclidean norm of a feature
vector. -/
lemma dotProduct_self_le_nat_mul_sq_of_abs_le
    (u : Feature d) {B : ℝ} (hB_nonneg : 0 ≤ B)
    (hu : ∀ i, |u i| ≤ B) :
    dotProduct u u ≤ (d : ℝ) * B ^ 2 := by
  rw [dotProduct]
  calc
    ∑ i, u i * u i ≤ ∑ _i : Fin d, B ^ 2 := by
      refine Finset.sum_le_sum fun i _hi ↦ ?_
      have hsq : u i ^ 2 ≤ B ^ 2 := by
        exact sq_le_sq.2 (by simpa [abs_of_nonneg hB_nonneg] using hu i)
      simpa [pow_two] using hsq
    _ = (d : ℝ) * B ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Positive regularization bounds the centered-noise inverse-design quadratic form by the
ordinary squared Euclidean norm divided by `reg`. -/
lemma centeredNoiseQuadraticForm_le_sqNorm_div_reg
    (hreg_pos : 0 < reg) :
    centeredNoiseQuadraticForm A R ν reg x n ω ≤
      dotProduct (centeredResponseVector A R ν x n ω)
        (centeredResponseVector A R ν x n ω) / reg := by
  calc
    centeredNoiseQuadraticForm A R ν reg x n ω
        ≤ dotProduct (centeredResponseVector A R ν x n ω)
            (Matrix.mulVec (reg • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹
              (centeredResponseVector A R ν x n ω)) :=
          dotProduct_mulVec_le_of_matrix_le
            ((DesignMatrixInvLeRegInv.of_reg_pos (A := A) (reg := reg) (x := x)
              hreg_pos).apply n ω)
            (centeredResponseVector A R ν x n ω)
    _ = dotProduct (centeredResponseVector A R ν x n ω)
          (centeredResponseVector A R ν x n ω) / reg :=
        dotProduct_reg_smul_one_inv_mulVec (reg := reg) hreg_pos.ne'
          (centeredResponseVector A R ν x n ω)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Coordinate-wise control of the centered response vector gives a conservative bound on the
centered-noise inverse-design quadratic form. -/
lemma centeredNoiseQuadraticForm_le_nat_mul_coord_sq_div_reg
    (hreg_pos : 0 < reg) {B : ℝ} (hB_nonneg : 0 ≤ B)
    (hcoord : ∀ i, |centeredResponseVector A R ν x n ω i| ≤ B) :
    centeredNoiseQuadraticForm A R ν reg x n ω ≤ (d : ℝ) * B ^ 2 / reg := by
  refine (centeredNoiseQuadraticForm_le_sqNorm_div_reg (A := A) (R := R)
    (reg := reg) (x := x) (ν := ν) (n := n) (ω := ω) hreg_pos).trans ?_
  exact div_le_div_of_nonneg_right
    (dotProduct_self_le_nat_mul_sq_of_abs_le
      (centeredResponseVector A R ν x n ω) hB_nonneg hcoord)
    hreg_pos.le

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Nonnegative regularization makes the centered-noise inverse-design quadratic form
nonnegative. -/
lemma centeredNoiseQuadraticForm_nonneg_of_reg_nonneg
    (hreg_nonneg : 0 ≤ reg) :
    0 ≤ centeredNoiseQuadraticForm A R ν reg x n ω := by
  simpa [centeredNoiseQuadraticForm] using
    ((designMatrix_posSemidef (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
      hreg_nonneg).inv.dotProduct_mulVec_nonneg (centeredResponseVector A R ν x n ω))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Nonnegative regularization makes the ridge-bias inverse-design quadratic form nonnegative. -/
lemma regularizationBiasQuadraticForm_nonneg_of_reg_nonneg
    (θ : Feature d) (hreg_nonneg : 0 ≤ reg) :
    0 ≤ regularizationBiasQuadraticForm A reg x θ n ω := by
  simpa [regularizationBiasQuadraticForm] using
    ((designMatrix_posSemidef (A := A) (reg := reg) (x := x) (n := n) (ω := ω)
      hreg_nonneg).inv.dotProduct_mulVec_nonneg (reg • θ))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The combined centered-noise-plus-bias quadratic form is bounded by the square of the sum of
the separate noise and ridge-bias inverse-design norms.

This is the deterministic triangle-inequality step in the textbook proof:
`‖S_t - reg θ‖_{V_t⁻¹} ≤ ‖S_t‖_{V_t⁻¹} + ‖reg θ‖_{V_t⁻¹}`. -/
lemma centeredNoiseBiasQuadraticForm_le_sqrt_add_sqrt_sq
    (θ : Feature d)
    (hreg_pos : 0 < reg) :
    centeredNoiseBiasQuadraticForm A R ν reg x θ n ω ≤
      (√(centeredNoiseQuadraticForm A R ν reg x n ω) +
        √(regularizationBiasQuadraticForm A reg x θ n ω)) ^ 2 := by
  let V : Matrix (Fin d) (Fin d) ℝ := designMatrix A reg x n ω
  let M : Matrix (Fin d) (Fin d) ℝ := V⁻¹
  let u : Feature d := centeredResponseVector A R ν x n ω
  let b : Feature d := reg • θ
  have hV : V.PosDef := designMatrix_posDef (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω) hreg_pos
  have hM : M.PosDef := hV.inv
  letI : SeminormedAddCommGroup (Feature d) := Matrix.toSeminormedAddCommGroup M hM.posSemidef
  letI : InnerProductSpace ℝ (Feature d) := Matrix.toInnerProductSpace M hM.posSemidef
  have hq_sub :
      centeredNoiseBiasQuadraticForm A R ν reg x θ n ω =
        inner ℝ (u - b) (u - b) := by
    change dotProduct (u - b) (Matrix.mulVec M (u - b)) = inner ℝ (u - b) (u - b)
    change dotProduct (u - b) (M *ᵥ (u - b)) = (M *ᵥ (u - b)) ⬝ᵥ (u - b)
    rw [dotProduct_comm]
  have hq_u :
      centeredNoiseQuadraticForm A R ν reg x n ω = inner ℝ u u := by
    change dotProduct u (Matrix.mulVec M u) = inner ℝ u u
    change dotProduct u (M *ᵥ u) = (M *ᵥ u) ⬝ᵥ u
    rw [dotProduct_comm]
  have hq_b :
      regularizationBiasQuadraticForm A reg x θ n ω = inner ℝ b b := by
    change dotProduct b (Matrix.mulVec M b) = inner ℝ b b
    change dotProduct b (M *ᵥ b) = (M *ᵥ b) ⬝ᵥ b
    rw [dotProduct_comm]
  have h_cross_sq := real_inner_mul_inner_self_le u b
  have h_cross_sq_pow :
      (inner ℝ u b) ^ 2 ≤ inner ℝ u u * inner ℝ b b := by
    simpa [pow_two] using h_cross_sq
  have h_cross_abs :
      |inner ℝ u b| ≤ √(inner ℝ u u * inner ℝ b b) :=
    Real.abs_le_sqrt h_cross_sq_pow
  have h_sqrt_mul :
      √(inner ℝ u u * inner ℝ b b) =
        √(inner ℝ u u) * √(inner ℝ b b) :=
    Real.sqrt_mul (real_inner_self_nonneg (x := u)) (inner ℝ b b)
  have h_sqrt_u_mul :
      √(inner ℝ u u) * √(inner ℝ u u) = inner ℝ u u := by
    rw [← sq, Real.sq_sqrt (real_inner_self_nonneg (x := u))]
  have h_sqrt_b_mul :
      √(inner ℝ b b) * √(inner ℝ b b) = inner ℝ b b := by
    rw [← sq, Real.sq_sqrt (real_inner_self_nonneg (x := b))]
  have h_neg_cross :
      - inner ℝ u b ≤ √(inner ℝ u u) * √(inner ℝ b b) := by
    exact (neg_le_abs (inner ℝ u b)).trans (h_cross_abs.trans_eq h_sqrt_mul)
  have h_cross_comm : inner ℝ b u = inner ℝ u b := by
    rw [real_inner_comm]
  calc
    centeredNoiseBiasQuadraticForm A R ν reg x θ n ω
        = inner ℝ (u - b) (u - b) := hq_sub
    _ = inner ℝ u u - inner ℝ u b - inner ℝ b u + inner ℝ b b := by
          rw [inner_sub_sub_self]
    _ = inner ℝ u u + inner ℝ b b - 2 * inner ℝ u b := by
          rw [h_cross_comm]
          ring
    _ ≤ inner ℝ u u + inner ℝ b b +
          2 * (√(inner ℝ u u) * √(inner ℝ b b)) := by
          nlinarith [h_neg_cross]
    _ = (√(inner ℝ u u) + √(inner ℝ b b)) ^ 2 := by
          nlinarith [h_sqrt_u_mul, h_sqrt_b_mul]
    _ = (√(centeredNoiseQuadraticForm A R ν reg x n ω) +
          √(regularizationBiasQuadraticForm A reg x θ n ω)) ^ 2 := by
          rw [hq_u, hq_b]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Bound form of `centeredNoiseBiasQuadraticForm_le_sqrt_add_sqrt_sq`: if the random
self-normalized noise term is at most `B` and the ridge-bias term is at most `C`, then the combined
least-squares error term is at most `(√B + √C)²`. -/
lemma centeredNoiseBiasQuadraticForm_le_sqrt_bounds_sq
    (θ : Feature d) (hreg_pos : 0 < reg) (B C : ℝ)
    (hB : centeredNoiseQuadraticForm A R ν reg x n ω ≤ B)
    (hC : regularizationBiasQuadraticForm A reg x θ n ω ≤ C) :
    centeredNoiseBiasQuadraticForm A R ν reg x θ n ω ≤ (√B + √C) ^ 2 := by
  refine (centeredNoiseBiasQuadraticForm_le_sqrt_add_sqrt_sq (A := A) (R := R)
    (reg := reg) (x := x) (ν := ν) (n := n) (ω := ω) θ hreg_pos).trans ?_
  gcongr

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Under linear realizability and positive regularization, the parameter ellipsoid quantity is the
inverse-design quadratic form of the centered reward-feature vector plus the regularization bias.

This is the deterministic algebraic identity immediately before the textbook self-normalized
concentration step: if `z_t = ∑_{s<t} (R_s - μ(A_s)) x_{A_s} - reg • θ`, then
`‖θHat_t - θ‖²_{V_t} = z_tᵀ V_t⁻¹ z_t`. -/
lemma parameterErrorQuadraticForm_eq_centeredResponseVector_sub_reg_inv_designMatrix
    (θ : Feature d)
    (h_linear : LinearMeanModel ν x θ)
    (hreg_pos : 0 < reg) :
    parameterErrorQuadraticForm A R reg x θ n ω =
      dotProduct (centeredResponseVector A R ν x n ω - reg • θ)
        (Matrix.mulVec (designMatrix A reg x n ω)⁻¹
          (centeredResponseVector A R ν x n ω - reg • θ)) := by
  let V : Matrix (Fin d) (Fin d) ℝ := designMatrix A reg x n ω
  let u : Feature d := thetaHat A R reg x n ω - θ
  let z : Feature d := centeredResponseVector A R ν x n ω - reg • θ
  have hV : V.PosDef := designMatrix_posDef (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω) hreg_pos
  have hVdet : IsUnit V.det := by
    exact Matrix.isUnit_iff_isUnit_det (A := V) |>.mp hV.isUnit
  have hz : Matrix.mulVec V u = z := by
    simp only [V, u, z]
    exact designMatrix_mulVec_thetaHat_sub_linearMeanParameter (A := A) (R := R)
      (reg := reg) (x := x) (ν := ν) (n := n) (ω := ω) θ h_linear hreg_pos
  have hu : u = Matrix.mulVec V⁻¹ z := by
    calc
      u = Matrix.mulVec 1 u := by simp
      _ = Matrix.mulVec (V⁻¹ * V) u := by rw [Matrix.nonsing_inv_mul _ hVdet]
      _ = Matrix.mulVec V⁻¹ (Matrix.mulVec V u) := by rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec V⁻¹ z := by rw [hz]
  change dotProduct u (Matrix.mulVec V u) = dotProduct z (Matrix.mulVec V⁻¹ z)
  rw [hz, hu, dotProduct_comm]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Packaged form of
`parameterErrorQuadraticForm_eq_centeredResponseVector_sub_reg_inv_designMatrix` using
`centeredNoiseBiasQuadraticForm`. -/
lemma parameterErrorQuadraticForm_eq_centeredNoiseBiasQuadraticForm
    (θ : Feature d)
    (h_linear : LinearMeanModel ν x θ)
    (hreg_pos : 0 < reg) :
    parameterErrorQuadraticForm A R reg x θ n ω =
      centeredNoiseBiasQuadraticForm A R ν reg x θ n ω := by
  simpa [centeredNoiseBiasQuadraticForm] using
    parameterErrorQuadraticForm_eq_centeredResponseVector_sub_reg_inv_designMatrix
      (A := A) (R := R) (reg := reg) (x := x) (ν := ν) (n := n) (ω := ω)
      θ h_linear hreg_pos

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Positive regularization controls the deterministic regularization-bias term in the
inverse-design norm:
`(reg θ)ᵀ V_t⁻¹ (reg θ) ≤ reg * ‖θ‖²`.

This is the deterministic bias half of the textbook confidence-radius proof, paired later with a
self-normalized concentration bound for the centered reward-feature noise. -/
lemma regularizationBias_invDesign_quadraticForm_le
    (θ : Feature d)
    (hreg_pos : 0 < reg) :
    dotProduct (reg • θ)
        (Matrix.mulVec (designMatrix A reg x n ω)⁻¹ (reg • θ)) ≤
      reg * dotProduct θ θ := by
  calc
    dotProduct (reg • θ)
        (Matrix.mulVec (designMatrix A reg x n ω)⁻¹ (reg • θ))
        ≤ dotProduct (reg • θ)
            (Matrix.mulVec (reg • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ (reg • θ)) :=
          dotProduct_mulVec_le_of_matrix_le
            ((DesignMatrixInvLeRegInv.of_reg_pos (A := A) (reg := reg) (x := x)
              hreg_pos).apply n ω)
            (reg • θ)
    _ = reg * dotProduct θ θ := by
        rw [dotProduct_reg_smul_one_inv_mulVec (reg := reg) hreg_pos.ne' (reg • θ)]
        simp [dotProduct, smul_eq_mul]
        field_simp [hreg_pos.ne']
        rw [← Finset.mul_sum]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Packaged version of `regularizationBias_invDesign_quadraticForm_le` using
`regularizationBiasQuadraticForm`. -/
lemma regularizationBiasQuadraticForm_le
    (θ : Feature d)
    (hreg_pos : 0 < reg) :
    regularizationBiasQuadraticForm A reg x θ n ω ≤ reg * dotProduct θ θ := by
  simpa [regularizationBiasQuadraticForm] using
    regularizationBias_invDesign_quadraticForm_le (A := A) (reg := reg) (x := x)
      (n := n) (ω := ω) θ hreg_pos

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- If `θᵀθ ≤ S2`, then the deterministic ridge-bias contribution is bounded by `reg * S2`. -/
lemma regularizationBiasQuadraticForm_le_of_parameterSqNormBound
    (θ : Feature d) (hreg_pos : 0 < reg) {S2 : ℝ}
    (hθ : ParameterSqNormBound θ S2) :
    regularizationBiasQuadraticForm A reg x θ n ω ≤ reg * S2 :=
  (regularizationBiasQuadraticForm_le (A := A) (reg := reg) (x := x)
    (n := n) (ω := ω) θ hreg_pos).trans
    (mul_le_mul_of_nonneg_left hθ hreg_pos.le)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Matrix Cauchy-Schwarz property for LinUCB prediction errors.

Mathematically, for `V_t = designMatrix A reg x t ω`, this is
`|uᵀ x_a| ≤ sqrt(uᵀ V_t u) * sqrt(x_aᵀ V_t⁻¹ x_a)`.

It is isolated as a named proposition because it is the linear-algebra step that turns the
textbook parameter ellipsoid confidence set into action-wise prediction confidence intervals. The
lemma `linUCBPredictionErrorCauchySchwarz_of_reg_pos` below proves it from positive
regularization. -/
def LinUCBPredictionErrorCauchySchwarz
    (A : ℕ → Ω → Fin K) (reg : ℝ) (x : Fin K → Feature d) : Prop :=
  ∀ (u : Feature d) (a : Fin K) (t : ℕ) (ω : Ω),
    |dotProduct u (x a)| ≤
      √(dotProduct u (Matrix.mulVec (designMatrix A reg x t ω) u)) *
        width A reg x a t ω

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Positive regularization gives the matrix Cauchy-Schwarz property used to pass from the
textbook parameter ellipsoid to arm-wise prediction intervals.

The proof equips the feature space with the inner product induced by
`V_t = designMatrix A reg x t ω`. Cauchy-Schwarz in that inner product gives
`|uᵀ V_t (V_t⁻¹ x_a)|² ≤ (uᵀ V_t u) (x_aᵀ V_t⁻¹ x_a)`, and positive regularization makes
`V_t` positive definite, so `V_t V_t⁻¹ = I`. -/
lemma linUCBPredictionErrorCauchySchwarz_of_reg_pos
    (hreg_pos : 0 < reg) :
    LinUCBPredictionErrorCauchySchwarz A reg x := by
  intro u a t ω
  let V : Matrix (Fin d) (Fin d) ℝ := designMatrix A reg x t ω
  have hV : V.PosDef := designMatrix_posDef (A := A) (reg := reg) (x := x)
    (n := t) (ω := ω) hreg_pos
  have hVdet : IsUnit V.det :=
    (Matrix.isUnit_iff_isUnit_det (A := V)).mp hV.isUnit
  let v : Feature d := Matrix.mulVec V⁻¹ (x a)
  letI : SeminormedAddCommGroup (Feature d) := Matrix.toSeminormedAddCommGroup V hV.posSemidef
  letI : InnerProductSpace ℝ (Feature d) := Matrix.toInnerProductSpace V hV.posSemidef
  have h_inner_uv :
      inner ℝ u v = dotProduct u (Matrix.mulVec V v) := by
    change (V *ᵥ v) ⬝ᵥ u = dotProduct u (Matrix.mulVec V v)
    rw [dotProduct_comm]
  have h_inner_uu :
      inner ℝ u u = dotProduct u (Matrix.mulVec V u) := by
    change (V *ᵥ u) ⬝ᵥ u = dotProduct u (Matrix.mulVec V u)
    rw [dotProduct_comm]
  have h_inner_vv :
      inner ℝ v v = dotProduct v (Matrix.mulVec V v) := by
    change (V *ᵥ v) ⬝ᵥ v = dotProduct v (Matrix.mulVec V v)
    rw [dotProduct_comm]
  have hsq := real_inner_mul_inner_self_le u v
  rw [h_inner_uv, h_inner_uu, h_inner_vv] at hsq
  have hsq' :
      dotProduct u (x a) ^ 2 ≤
        dotProduct u (Matrix.mulVec V u) *
          dotProduct (x a) (Matrix.mulVec V⁻¹ (x a)) := by
    simpa [v, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hVdet, dotProduct_comm, sq] using
      hsq
  have h_abs := Real.abs_le_sqrt hsq'
  calc
    |dotProduct u (x a)|
        ≤ √(dotProduct u (Matrix.mulVec V u) *
            dotProduct (x a) (Matrix.mulVec V⁻¹ (x a))) := h_abs
    _ = √(dotProduct u (Matrix.mulVec V u)) *
          √(dotProduct (x a) (Matrix.mulVec V⁻¹ (x a))) := by
        rw [Real.sqrt_mul (by simpa using hV.posSemidef.dotProduct_mulVec_nonneg u)]
    _ = √(dotProduct u (Matrix.mulVec (designMatrix A reg x t ω) u)) *
          width A reg x a t ω := by
        simp [V, width, widthQuadraticForm]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Textbook-shaped parameter confidence event for finite-action LinUCB.

This is the event that the true linear parameter `θ` lies in every positive-time confidence
ellipsoid: `‖θHat_t - θ‖²_{V_t} ≤ β_{t+1}`. The later self-normalized concentration theorem should
prove this event, or a theorem immediately implying it, with high probability for the textbook
choice of `β`. -/
def LinUCBParameterEllipsoidConfidenceEvent
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d)
    (θ : Feature d) (ω : Ω) : Prop :=
  ∀ t, t ≠ 0 → parameterErrorQuadraticForm A R reg x θ t ω ≤ β (t + 1)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Horizon-local parameter confidence event for finite-action LinUCB. -/
def LinUCBParameterEllipsoidConfidenceEventUpTo
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d)
    (θ : Feature d) (n : ℕ) (ω : Ω) : Prop :=
  ∀ t, t ∈ range n → t ≠ 0 →
    parameterErrorQuadraticForm A R reg x θ t ω ≤ β (t + 1)

omit [IsMarkovKernel ν] in
/-- A global parameter ellipsoid confidence event implies its finite-horizon restriction. -/
lemma LinUCBParameterEllipsoidConfidenceEvent.toUpTo
    (θ : Feature d)
    (h_ellipsoid : LinUCBParameterEllipsoidConfidenceEvent A R reg β x θ ω) :
    LinUCBParameterEllipsoidConfidenceEventUpTo A R reg β x θ n ω := by
  intro t _ht ht0
  exact h_ellipsoid t ht0

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Textbook self-normalized confidence event stated at the centered-noise-plus-bias level.

This is the event naturally exposed by the least-squares decomposition proved above:
`‖θHat_t - θ‖²_{V_t}` is equal to `centeredNoiseBiasQuadraticForm`, so controlling this event is
enough to put the true parameter in every LinUCB confidence ellipsoid. -/
def LinUCBCenteredNoiseBiasConfidenceEvent
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (θ : Feature d) (ω : Ω) : Prop :=
  ∀ t, t ≠ 0 → centeredNoiseBiasQuadraticForm A R ν reg x θ t ω ≤ β (t + 1)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Horizon-local centered-noise-plus-bias confidence event for finite-action LinUCB. -/
def LinUCBCenteredNoiseBiasConfidenceEventUpTo
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (β : ℕ → ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (θ : Feature d) (n : ℕ) (ω : Ω) : Prop :=
  ∀ t, t ∈ range n → t ≠ 0 →
    centeredNoiseBiasQuadraticForm A R ν reg x θ t ω ≤ β (t + 1)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Horizon-local self-normalized event for only the random centered reward-feature vector.

This separates the probabilistic martingale term from the deterministic ridge-bias term. A
textbook self-normalized concentration theorem should prove this event for a concrete
`noiseBudget`; the deterministic lemmas above then add the ridge-bias radius. -/
def LinUCBCenteredNoiseConfidenceEventUpTo
    (A : ℕ → Ω → Fin K) (R : ℕ → Ω → ℝ)
    (reg : ℝ) (noiseBudget : ℕ → ℝ) (x : Fin K → Feature d)
    (ν : Kernel (Fin K) ℝ) (n : ℕ) (ω : Ω) : Prop :=
  ∀ t, t ∈ range n → t ≠ 0 →
    centeredNoiseQuadraticForm A R ν reg x t ω ≤ noiseBudget (t + 1)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Textbook determinant-ratio self-normalized noise bound.

This is the scalar radius appearing before the ridge-bias term in the LinUCB confidence proof:
`2 σ² log(√detRatio / δ)`. The future Gaussian-mixture theorem should prove that the centered
noise quadratic form is bounded by this expression with high probability. -/
noncomputable def textbookSelfNormalizedNoiseBound
    (σ2 : ℝ≥0) (δ : ℝ) (detRatio : ℝ) : ℝ :=
  2 * (σ2 : ℝ) * Real.log (√detRatio / δ)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The textbook self-normalized noise bound is monotone in the determinant ratio. -/
lemma textbookSelfNormalizedNoiseBound_mono_detRatio
    {σ2 : ℝ≥0} {δ ratio D : ℝ}
    (hratio_pos : 0 < ratio) (hratio_le : ratio ≤ D) (hδ_pos : 0 < δ) :
    textbookSelfNormalizedNoiseBound σ2 δ ratio ≤
      textbookSelfNormalizedNoiseBound σ2 δ D := by
  have hsqrt_ratio_pos : 0 < √ratio := Real.sqrt_pos.2 hratio_pos
  have hdiv_pos : 0 < √ratio / δ := div_pos hsqrt_ratio_pos hδ_pos
  have hdiv_le : √ratio / δ ≤ √D / δ :=
    div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hratio_le) hδ_pos.le
  have hlog : Real.log (√ratio / δ) ≤ Real.log (√D / δ) :=
    Real.log_le_log hdiv_pos hdiv_le
  have hcoef_nonneg : 0 ≤ 2 * (σ2 : ℝ) := by positivity
  simpa [textbookSelfNormalizedNoiseBound, mul_assoc] using
    mul_le_mul_of_nonneg_left hlog hcoef_nonneg

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Finite-horizon textbook LinUCB confidence radius, squared.

This is the deterministic radius used by `textbookLinUCBBeta` on the target horizon. -/
noncomputable def textbookLinUCBConfidenceRadius
    (d : ℕ) (reg S2 : ℝ) (σ2 : ℝ≥0) (L2 : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  max 1
    ((√(textbookSelfNormalizedNoiseBound σ2 δ
        (textbookDesignDetRatioTraceBound d reg L2 n)) + √(reg * S2)) ^ 2)

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Finite-horizon textbook LinUCB beta schedule.

The inner expression is the textbook radius
`(sqrt(2 σ² log(sqrt(D_n)/δ)) + sqrt(reg * S²))²`, where
`D_n = (1 + n L² / (reg d))^d` is the terminal determinant-ratio trace budget.
The outer `max 1` packages the schedule assumptions used by the regret proof. The schedule equals
this textbook radius through the target horizon `n` and is extended monotonically after `n`. -/
noncomputable def textbookLinUCBBeta
    (d : ℕ) (reg S2 : ℝ) (σ2 : ℝ≥0) (L2 : ℝ) (n : ℕ) (δ : ℝ) (m : ℕ) : ℝ :=
  textbookLinUCBConfidenceRadius d reg S2 σ2 L2 n δ + max 0 ((m : ℝ) - (n : ℝ))

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- On the target horizon, the finite-horizon textbook beta schedule is exactly the textbook
confidence radius. -/
lemma textbookLinUCBBeta_at_horizon
    (d : ℕ) (reg S2 : ℝ) (σ2 : ℝ≥0) (L2 : ℝ) (n : ℕ) (δ : ℝ) :
    textbookLinUCBBeta d reg S2 σ2 L2 n δ n =
      textbookLinUCBConfidenceRadius d reg S2 σ2 L2 n δ := by
  simp [textbookLinUCBBeta]

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The textbook beta schedule dominates the realized determinant-ratio confidence radius whenever
the realized determinant ratio is below the terminal trace budget. -/
lemma textbookLinUCBBeta_budget_of_designDetRatio_le
    (S2 L2 : ℝ) {σ2 : ℝ≥0} {δ : ℝ} {t m : ℕ}
    (hratio_pos : 0 < designDetRatio A reg x t ω)
    (hratio_le :
      designDetRatio A reg x t ω ≤ textbookDesignDetRatioTraceBound d reg L2 n)
    (hδ_pos : 0 < δ) :
    (√(textbookSelfNormalizedNoiseBound σ2 δ (designDetRatio A reg x t ω)) +
        √(reg * S2)) ^ 2 ≤
      textbookLinUCBBeta d reg S2 σ2 L2 n δ m := by
  have hnoise_le :
      textbookSelfNormalizedNoiseBound σ2 δ (designDetRatio A reg x t ω) ≤
        textbookSelfNormalizedNoiseBound σ2 δ (textbookDesignDetRatioTraceBound d reg L2 n) :=
    textbookSelfNormalizedNoiseBound_mono_detRatio hratio_pos hratio_le hδ_pos
  have hsum_le :
      √(textbookSelfNormalizedNoiseBound σ2 δ (designDetRatio A reg x t ω)) +
          √(reg * S2) ≤
        √(textbookSelfNormalizedNoiseBound σ2 δ
          (textbookDesignDetRatioTraceBound d reg L2 n)) + √(reg * S2) :=
    add_le_add (Real.sqrt_le_sqrt hnoise_le) le_rfl
  have hleft_nonneg :
      0 ≤ √(textbookSelfNormalizedNoiseBound σ2 δ (designDetRatio A reg x t ω)) +
        √(reg * S2) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hright_nonneg :
      0 ≤ √(textbookSelfNormalizedNoiseBound σ2 δ
        (textbookDesignDetRatioTraceBound d reg L2 n)) + √(reg * S2) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hbase :
      (√(textbookSelfNormalizedNoiseBound σ2 δ (designDetRatio A reg x t ω)) +
          √(reg * S2)) ^ 2 ≤
        textbookLinUCBConfidenceRadius d reg S2 σ2 L2 n δ := by
    rw [textbookLinUCBConfidenceRadius]
    exact ((sq_le_sq₀ hleft_nonneg hright_nonneg).mpr hsum_le).trans (le_max_right _ _)
  exact hbase.trans (by simp [textbookLinUCBBeta])

omit [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- Under bounded features, the textbook beta schedule almost surely dominates every realized
finite-horizon determinant-ratio confidence radius. -/
lemma textbookLinUCBBeta_budget_ae_of_featureSqNorm_bound
    [Nonempty (Fin K)]
    (S2 L2 : ℝ) {σ2 : ℝ≥0} {δ : ℝ}
    (hreg_pos : 0 < reg) (hd : d ≠ 0)
    (hL2 : FeatureSqNormBound x L2) (hδ_pos : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ t, t ∈ range n → t ≠ 0 →
      (√(textbookSelfNormalizedNoiseBound σ2 δ (designDetRatio A reg x t ω)) +
        √(reg * S2)) ^ 2 ≤
          textbookLinUCBBeta d reg S2 σ2 L2 n δ (t + 1) := by
  filter_upwards
    [designDetRatio_ae_all_le_textbookTraceBound_of_featureSqNorm_bound
      (A := A) (reg := reg) (x := x) (n := n) (P := P)
      L2 hreg_pos hd hL2 matrixDetLeTraceAveragePow] with ω hratioω
  intro t ht _ht0
  exact textbookLinUCBBeta_budget_of_designDetRatio_le (A := A) (reg := reg)
    (x := x) (n := n) (ω := ω) (S2 := S2) (L2 := L2) (σ2 := σ2)
    (δ := δ) (t := t) (m := t + 1)
    (designDetRatio_pos_of_reg_pos (A := A) (reg := reg) (x := x) (n := t)
      (ω := ω) hreg_pos)
    (hratioω t ht) hδ_pos

end AlgorithmBehavior

end LinUCB

end Bandits
