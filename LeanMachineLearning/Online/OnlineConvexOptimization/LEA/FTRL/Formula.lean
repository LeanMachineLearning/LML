/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.FTRL.RegretDecomposition
public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.Common.Regularizer
import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Deriv
import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.FTRL.Optimality
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Exponential Weights Update Formula for Follow-the-Regularized-Leader (FTRL)

This file defines the explicit closed-form Exponential Weights update for FTRL with cumulative
linearized losses and unnormalized negative entropy regularizer with scale $\alpha_t > 0$:

$$w_{t, i} = \frac{\exp\left(- \frac{1}{\alpha_t} \sum_{k=1}^{t-1} g_{k, i}\right)}
  {\sum_{j=1}^d \exp\left(- \frac{1}{\alpha_t} \sum_{k=1}^{t-1} g_{k, j}\right)}.$$

## Main definitions
* `expWeight`: The standard exponential weight predictor.
* `expWeights`: The full sequence of Exponential Weights (FTRL) iterates.

## Main results
* `expWeight_pos`: Strict positivity in each coordinate.
* `expWeight_mem_stdSimplex`: Membership $w_t \in \Delta^{d-1}$.
* `expWeight_isMinOn`: Minimizer property of $w_t$
  for $F_t$ on $\Delta^{d-1}$.
* `expWeights_optimality_nonneg`: Non-negativity of per-round optimality.
* `expWeights_terminalOptimality_nonpos`: Non-positivity of terminal
  optimality.
-/

open scoped BigOperators Bregman Topology
open Finset

@[expose] public section

namespace Online.OCO.LEA.FTRL

variable {d : ℕ}

/-- Coordinate-wise unnormalized weight for FTRL with cumulative linear losses:
$$\exp\left(- \frac{1}{\alpha} \sum_{k=1}^{t-1} g_{k, i}\right)$$ -/
noncomputable def expWeightUnnorm (α : ℝ) (g_cum : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (i : Fin d) : ℝ :=
  Real.exp (- (g_cum (EuclideanSpace.basisFun (Fin d) ℝ i)) / α)

lemma expWeightUnnorm_pos (α : ℝ) (g_cum : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (i : Fin d) :
    0 < expWeightUnnorm α g_cum i := by
  dsimp [expWeightUnnorm]
  exact Real.exp_pos _

lemma sum_expWeightUnnorm_pos (hd : 0 < d) (α : ℝ)
    (g_cum : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    0 < ∑ i, expWeightUnnorm α g_cum i := by
  have : (univ : Finset (Fin d)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hd)
  exact sum_pos (fun i _ ↦ expWeightUnnorm_pos α g_cum i) this

/-- The normalized exponential weights vector:
$$w_i = \frac{\exp\left(- \frac{1}{\alpha} g_{\mathrm{cum}, i}\right)}
  {\sum_j \exp\left(- \frac{1}{\alpha} g_{\mathrm{cum}, j}\right)}$$ -/
noncomputable def expWeight (_hd : 0 < d) (α : ℝ)
    (g_cum : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i ↦ expWeightUnnorm α g_cum i / ∑ j, expWeightUnnorm α g_cum j)

lemma expWeight_apply (hd : 0 < d) (α : ℝ)
    (g_cum : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (i : Fin d) :
    expWeight hd α g_cum i =
      expWeightUnnorm α g_cum i / ∑ j, expWeightUnnorm α g_cum j :=
  rfl

lemma expWeight_pos (hd : 0 < d) (α : ℝ)
    (g_cum : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (i : Fin d) :
    0 < expWeight hd α g_cum i := by
  rw [expWeight_apply]
  exact div_pos (expWeightUnnorm_pos α g_cum i)
    (sum_expWeightUnnorm_pos hd α g_cum)

lemma expWeight_mem_stdSimplex (hd : 0 < d) (α : ℝ)
    (g_cum : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    expWeight hd α g_cum ∈ stdSimplex (d := d) := by
  rw [mem_stdSimplex_iff]
  refine ⟨fun i ↦ (expWeight_pos hd α g_cum i).le, ?_⟩
  simp_rw [expWeight_apply, ← sum_div]
  exact div_self (sum_expWeightUnnorm_pos hd α g_cum).ne'

lemma expWeight_log_apply (hd : 0 < d) (α : ℝ) (_hα : 0 < α)
    (g_cum : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (i : Fin d) :
    Real.log (expWeight hd α g_cum i) =
      - (g_cum (EuclideanSpace.basisFun (Fin d) ℝ i)) / α -
      Real.log (∑ j, expWeightUnnorm α g_cum j) := by
  rw [expWeight_apply, Real.log_div (expWeightUnnorm_pos α g_cum i).ne'
    (sum_expWeightUnnorm_pos hd α g_cum).ne']
  dsimp [expWeightUnnorm]
  rw [Real.log_exp]

/-- The gradient of the objective $F(x) = \psi_\alpha(x) + g_{\mathrm{cum}}(x)$ at
$w = \mathrm{expWeight}(hd, \alpha, g_{\mathrm{cum}})$ applied to any difference
$(x - w)$ in the affine tangent space of $\Delta^{d-1}$ vanishes identically. -/
lemma ftrl_obj_diff_eq (hd : 0 < d) (α : ℝ) (hα : 0 < α)
    (g_cum : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ stdSimplex (d := d)) :
    (g_cum + unnormEntropyFDeriv α (expWeight hd α g_cum))
      (x - expWeight hd α g_cum) = 0 := by
  let w := expWeight hd α g_cum
  have hw_mem := expWeight_mem_stdSimplex hd α g_cum
  rw [mem_stdSimplex_iff] at hx hw_mem
  have h_basis (y : EuclideanSpace ℝ (Fin d)) :
      g_cum y = ∑ i, y i * g_cum (EuclideanSpace.basisFun (Fin d) ℝ i) := by
    have hy : y = ∑ i, y i • EuclideanSpace.basisFun (Fin d) ℝ i := by
      ext i; simp [EuclideanSpace.basisFun_apply, Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum]
    refine sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]
  simp only [add_apply, unnormEntropyFDeriv_apply]
  have h_w_i (i : Fin d) :
      g_cum (EuclideanSpace.basisFun (Fin d) ℝ i) + α * Real.log (w i) =
        - α * Real.log (∑ j, expWeightUnnorm α g_cum j) := by
    have hlog := expWeight_log_apply hd α hα g_cum i
    dsimp [w]
    rw [hlog]
    have hα_ne : α ≠ 0 := hα.ne'
    field_simp
    ring
  have h_comb : (g_cum (x - w) + α * ∑ i, (x - w) i * Real.log (w i)) =
      ∑ i, (x i - w i) *
        (g_cum (EuclideanSpace.basisFun (Fin d) ℝ i) + α * Real.log (w i)) := by
    rw [h_basis (x - w)]
    simp only [PiLp.sub_apply, mul_sum, ← sum_add_distrib]
    congr 1 with i
    ring
  rw [h_comb]
  simp_rw [h_w_i]
  rw [← sum_mul, sum_sub_distrib, hx.2, hw_mem.2, sub_self, zero_mul]

/-- The vector $w = \mathrm{expWeight}(hd, \alpha, g_{\mathrm{cum}})$ minimizes the
FTRL objective $F(x) = \psi_\alpha(x) + g_{\mathrm{cum}}(x)$ over the standard simplex. -/
lemma isMinOn_expWeight (hd : 0 < d) (α : ℝ) (hα : 0 < α)
    (g_cum : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    IsMinOn (fun x ↦ unnormEntropy α x + g_cum x) (stdSimplex (d := d))
      (expWeight hd α g_cum) := by
  set w := expWeight hd α g_cum
  have hw_mem := expWeight_mem_stdSimplex hd α g_cum
  have hw_pos : ∀ i, 0 < w i := expWeight_pos hd α g_cum
  have h_diff : HasFDerivAt (unnormEntropy α) (unnormEntropyFDeriv α w) w :=
    hasFDerivAt_unnormEntropy α w hw_pos
  have h_conv : ConvexOn ℝ (stdSimplex (d := d)) (unnormEntropy α) :=
    convexOn_unnormEntropy_stdSimplex α hα.le
  have h_obj_conv : ConvexOn ℝ (stdSimplex (d := d)) (unnormEntropy α + ⇑g_cum) :=
    h_conv.add (g_cum.toLinearMap.convexOn h_conv.1)
  have h_obj_diff : HasFDerivAt (unnormEntropy α + ⇑g_cum)
      (unnormEntropyFDeriv α w + g_cum) w :=
    h_diff.add g_cum.hasFDerivAt
  intro x hx
  have h_zero : (unnormEntropyFDeriv α w + g_cum) (x - w) = 0 := by
    have := ftrl_obj_diff_eq hd α hα g_cum x hx
    have h_comm : (unnormEntropyFDeriv α w + g_cum) (x - w) =
        (g_cum + unnormEntropyFDeriv α w) (x - w) := by
      simp only [add_apply]
      ring
    rwa [h_comm]
  have h_subg_base := (hasSubgradientWithinAt_iff_le.mp
      (h_obj_diff.hasSubgradientWithinAt h_obj_conv hw_mem)) x hx
  dsimp [bregDiv] at h_subg_base
  rw [h_zero, add_zero] at h_subg_base
  exact h_subg_base

/-- Full trajectory of Exponential Weights (FTRL) iterates at each round $t \ge 1$:
$$w_t = \mathrm{expWeights}\left(hd, \alpha_t, \sum_{i=1}^{t-1} g_i\right).$$ -/
noncomputable def expWeights (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (t : ℕ) : EuclideanSpace ℝ (Fin d) :=
  expWeight hd (α t) (∑ i ∈ Ico 1 t, g i)

lemma expWeights_pos (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (t : ℕ) (i : Fin d) :
    0 < expWeights hd α g t i :=
  expWeight_pos hd (α t) (∑ i ∈ Ico 1 t, g i) i

@[simp]
lemma expWeights_one (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) :
    expWeights hd α g 1 = uniformSimplex d := by
  ext i
  rw [expWeights, expWeight_apply]
  have h_sum_zero : (∑ i ∈ Ico 1 1, g i) = 0 := by simp
  dsimp [expWeightUnnorm]
  simp only [h_sum_zero, zero_apply, neg_zero, zero_div, Real.exp_zero,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    one_div]

lemma expWeights_mem_stdSimplex (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (t : ℕ) :
    expWeights hd α g t ∈ stdSimplex (d := d) :=
  expWeight_mem_stdSimplex hd (α t) (∑ i ∈ Ico 1 t, g i)

/-- The iterates generated by `expWeights` satisfy the `IsMinOn` condition
at each round $t \ge 1$. -/
theorem expWeights_isMinOn (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (t : ℕ) (hα_pos : 0 < α t) :
    IsMinOn (FObj (fun t x ↦ unnormEntropy (α t) x) g t)
      (stdSimplex (d := d)) (expWeights hd α g t) := by
  have := isMinOn_expWeight hd (α t) hα_pos (∑ i ∈ Ico 1 t, g i)
  have h_eq : (fun x ↦ unnormEntropy (α t) x + (∑ i ∈ Ico 1 t, g i) x) =
      FObj (fun t x ↦ unnormEntropy (α t) x) g t := by
    ext x
    dsimp [FObj]
    rw [_root_.sum_apply]
  rwa [h_eq] at this

/-- The iterates generated by `expWeights` satisfy the terminal `IsMinOn` condition
at horizon $T$. -/
theorem expWeights_terminal_isMinOn (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (T : ℕ) (hα_pos : 0 < α (T + 1)) :
    IsMinOn (FObj (fun t x ↦ unnormEntropy (α t) x) g (T + 1))
      (stdSimplex (d := d)) (expWeights hd α g (T + 1)) := by
  have := isMinOn_expWeight hd (α (T + 1)) hα_pos (∑ i ∈ Ico 1 (T + 1), g i)
  have h_eq : (fun x ↦ unnormEntropy (α (T + 1)) x + (∑ i ∈ Ico 1 (T + 1), g i) x) =
      FObj (fun t x ↦ unnormEntropy (α t) x) g (T + 1) := by
    ext x
    dsimp [FObj]
    rw [_root_.sum_apply]
  rwa [h_eq] at this

/-- Per-round first-order optimality deficit is non-negative for the concrete `expWeights`
trajectory. -/
theorem expWeights_optimality_nonneg (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (t : ℕ) (hα_pos : 0 < α t) :
    0 ≤ optimality (fun t x ↦ unnormEntropyFDeriv (α t) x) (expWeights hd α g) g t := by
  have hw_pos : ∀ i, 0 < expWeights hd α g t i := expWeights_pos hd α g t
  have h_diff := hasFDerivAt_unnormEntropy (α t) (expWeights hd α g t) hw_pos
  have h_conv := convexOn_unnormEntropy_stdSimplex (d := d) (α t) hα_pos.le
  have hwt := expWeights_mem_stdSimplex hd α g t
  have hwt1 := expWeights_mem_stdSimplex hd α g (t + 1)
  have h_min := expWeights_isMinOn hd α g t hα_pos
  exact optimality_nonneg_of_isMinOn (ψ := fun t x ↦ unnormEntropy (α t) x)
    t h_diff h_conv hwt hwt1 h_min

/-- Cumulative first-order optimality deficit is non-negative for the concrete `expWeights`
trajectory. -/
theorem expWeights_sum_optimality_nonneg (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (T : ℕ)
    (hα_pos : ∀ t ∈ Ico 1 (T + 1), 0 < α t) :
    0 ≤ ∑ t ∈ Ico 1 (T + 1),
      optimality (fun t x ↦ unnormEntropyFDeriv (α t) x) (expWeights hd α g) g t :=
  sum_nonneg fun t ht ↦ expWeights_optimality_nonneg hd α g t (hα_pos t ht)

/-- Terminal optimality deficit is non-positive for the concrete `expWeights` trajectory
at any comparator $u \in \Delta^{d-1}$. -/
theorem expWeights_terminalOptimality_nonpos (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (T : ℕ) (hα_pos : 0 < α (T + 1))
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ stdSimplex (d := d)) :
    terminalOptimality (fun t x ↦ unnormEntropy (α t) x) u
      (expWeights hd α g) g T ≤ 0 := by
  have h_min := expWeights_terminal_isMinOn hd α g T hα_pos
  exact terminalOptimality_nonpos_of_isMinOn (ψ := fun t x ↦ unnormEntropy (α t) x)
    T hu h_min

end Online.OCO.LEA.FTRL
