/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.COMD2.RegretDecomposition
public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.Common.Regularizer
import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Deriv
import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.COMD2.Optimality
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Update Formula for Online Mirror Descent in LEA

This file defines the explicit closed-form update for Entropic Online Mirror Descent (OMD)
in Learning with Expert Advice (LEA) with time-varying regularizer weights
$\alpha_t, \alpha_{t+1} > 0$:

$$w_{t+1, i} = \frac{w_{t, i}^{\alpha_t / \alpha_{t+1}} \exp(-g_{t, i}/\alpha_{t+1})}
  {\sum_{j=1}^d w_{t, j}^{\alpha_t / \alpha_{t+1}} \exp(-g_{t, j}/\alpha_{t+1})}.$$

(When $\alpha_t = \alpha_{t+1} = \frac{1}{\eta}$ is constant, this reduces to the standard
multiplicative Exponential Weights / Hedge step $w_{t+1, i} \propto w_{t, i} e^{-\eta g_{t, i}}$.)

## Main definitions

* `omdExpWeightStep`: The one-step update function mapping $w_t \in \Delta^{d-1}$
  to $w_{t+1} \in \Delta^{d-1}$.
* `omdExpWeights`: The full recursive sequence of iterates for Entropic OMD.

## Main results

* `omdExpWeightStep_pos`: Positivity $0 < (w_{t+1})_i$ for all $i$.
* `omdExpWeightStep_mem_stdSimplex`: Membership $w_{t+1} \in \Delta^{d-1}$.
* `omdExpWeights_pos`: Coordinate positivity for all rounds $t \ge 1$.
* `omdExpWeights_mem_stdSimplex`: Simplex membership for all rounds $t \ge 1$.
* `omdExpWeights_isMinOn`: Exact minimizer property of the step.
* `omdExpWeights_optimality_nonneg`: Non-negativity of per-round optimality.
-/

open scoped BigOperators Bregman Topology
open Finset

@[expose] public section

namespace Online.OCO.LEA.COMD2

variable {d : ℕ}

/-- Coordinate-wise unnormalized weight for the exponential update:
$$w_i^{\alpha / \alpha'} \exp(-g_i / \alpha')$$ -/
noncomputable def omdExpWeightUnnorm (α α' : ℝ) (w : EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (i : Fin d) : ℝ :=
  (w i) ^ (α / α') * Real.exp (-(g (EuclideanSpace.basisFun (Fin d) ℝ i)) / α')

lemma omdExpWeightUnnorm_pos (α α' : ℝ) {w : EuclideanSpace ℝ (Fin d)}
    (hw_pos : ∀ i, 0 < w i) (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (i : Fin d) :
    0 < omdExpWeightUnnorm α α' w g i := by
  dsimp [omdExpWeightUnnorm]
  exact mul_pos (Real.rpow_pos_of_pos (hw_pos i) _) (Real.exp_pos _)

lemma sum_omdExpWeightUnnorm_pos (hd : 0 < d) (α α' : ℝ) {w : EuclideanSpace ℝ (Fin d)}
    (hw_pos : ∀ i, 0 < w i) (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    0 < ∑ i, omdExpWeightUnnorm α α' w g i := by
  have : (univ : Finset (Fin d)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hd)
  exact sum_pos (fun i _ ↦ omdExpWeightUnnorm_pos α α' hw_pos g i) this

lemma sum_omdExpWeightUnnorm_ne_zero (hd : 0 < d) (α α' : ℝ) {w : EuclideanSpace ℝ (Fin d)}
    (hw_pos : ∀ i, 0 < w i) (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    ∑ i, omdExpWeightUnnorm α α' w g i ≠ 0 :=
  (sum_omdExpWeightUnnorm_pos hd α α' hw_pos g).ne'

/-- The one-step update for Entropic Online Mirror Descent:
$$w_{t+1, i} = \frac{w_{t, i}^{\alpha_t / \alpha_{t+1}} \exp(-g_{t, i} / \alpha_{t+1})}
  {\sum_j w_{t, j}^{\alpha_t / \alpha_{t+1}} \exp(-g_{t, j} / \alpha_{t+1})}.$$ -/
noncomputable def omdExpWeightStep (_hd : 0 < d) (α α' : ℝ) (w : EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i ↦ omdExpWeightUnnorm α α' w g i / ∑ j, omdExpWeightUnnorm α α' w g j)

lemma omdExpWeightStep_apply (hd : 0 < d) (α α' : ℝ) (w : EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (i : Fin d) :
    omdExpWeightStep hd α α' w g i =
      omdExpWeightUnnorm α α' w g i / ∑ j, omdExpWeightUnnorm α α' w g j :=
  rfl

/-- Positivity of coordinates after an Entropic OMD step. -/
lemma omdExpWeightStep_pos (hd : 0 < d) (α α' : ℝ) (w : EuclideanSpace ℝ (Fin d))
    (hw_pos : ∀ i, 0 < w i) (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (i : Fin d) :
    0 < omdExpWeightStep hd α α' w g i := by
  rw [omdExpWeightStep_apply]
  exact div_pos (omdExpWeightUnnorm_pos α α' hw_pos g i)
    (sum_omdExpWeightUnnorm_pos hd α α' hw_pos g)

/-- The Entropic OMD update always stays within the standard simplex $\Delta^{d-1}$. -/
theorem omdExpWeightStep_mem_stdSimplex (hd : 0 < d) (α α' : ℝ) (w : EuclideanSpace ℝ (Fin d))
    (hw_pos : ∀ i, 0 < w i) (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    omdExpWeightStep hd α α' w g ∈ stdSimplex (d := d) := by
  rw [mem_stdSimplex_iff]
  refine ⟨fun i ↦ (omdExpWeightStep_pos hd α α' w hw_pos g i).le, ?_⟩
  simp_rw [omdExpWeightStep_apply]
  rw [← sum_div, div_self (sum_omdExpWeightUnnorm_ne_zero hd α α' hw_pos g)]

/-- Logarithm of coordinates for the Exponential Weights update. -/
lemma log_omdExpWeightStep_apply (hd : 0 < d) (α α' : ℝ) (_hα' : 0 < α')
    (w : EuclideanSpace ℝ (Fin d)) (hw_pos : ∀ i, 0 < w i)
    (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (i : Fin d) :
    Real.log (omdExpWeightStep hd α α' w g i) =
      (α / α') * Real.log (w i) - (g (EuclideanSpace.basisFun (Fin d) ℝ i)) / α'
        - Real.log (∑ j, omdExpWeightUnnorm α α' w g j) := by
  rw [omdExpWeightStep_apply, Real.log_div (omdExpWeightUnnorm_pos α α' hw_pos g i).ne'
    (sum_omdExpWeightUnnorm_pos hd α α' hw_pos g).ne']
  dsimp [omdExpWeightUnnorm]
  rw [Real.log_mul (Real.rpow_pos_of_pos (hw_pos i) _).ne' (Real.exp_pos _).ne',
    Real.log_rpow (hw_pos i), Real.log_exp]
  ring

/-- The objective function for the mirror descent step:
$$x \mapsto g(x) + \psi_{\alpha'}(x) - \nabla\psi_\alpha(w)(x).$$ -/
noncomputable def mirrorStepObj (α α' : ℝ) (w : EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  g x + unnormEntropy α' x - (unnormEntropyFDeriv α w) x

/-- Linear coordinate expansion of the subgradient and Fréchet derivative on $\mathbb{R}^d$. -/
lemma mirrorStepObj_diff_eq (hd : 0 < d) (α α' : ℝ) (hα' : 0 < α')
    (w : EuclideanSpace ℝ (Fin d)) (hw_pos : ∀ i, 0 < w i)
    (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ stdSimplex) :
    (g + unnormEntropyFDeriv α' (omdExpWeightStep hd α α' w g) - unnormEntropyFDeriv α w)
      (x - omdExpWeightStep hd α α' w g) = 0 := by
  let w_next := omdExpWeightStep hd α α' w g
  have hw_next_mem := omdExpWeightStep_mem_stdSimplex hd α α' w hw_pos g
  rw [mem_stdSimplex_iff] at hx hw_next_mem
  have h_basis (y : EuclideanSpace ℝ (Fin d)) :
      g y = ∑ i, y i * g (EuclideanSpace.basisFun (Fin d) ℝ i) := by
    have hy : y = ∑ i, y i • EuclideanSpace.basisFun (Fin d) ℝ i := by
      ext i; simp [EuclideanSpace.basisFun_apply, Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum]
    refine sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]
  simp only [sub_apply, add_apply, unnormEntropyFDeriv_apply]
  have h_w_next_i (i : Fin d) :
      g (EuclideanSpace.basisFun (Fin d) ℝ i) + α' * Real.log (w_next i) - α * Real.log (w i) =
        - α' * Real.log (∑ j, omdExpWeightUnnorm α α' w g j) := by
    have hlog := log_omdExpWeightStep_apply hd α α' hα' w hw_pos g i
    dsimp [w_next]
    rw [hlog]
    have hα'_ne : α' ≠ 0 := hα'.ne'
    field_simp
    ring
  have h_comb : (g (x - w_next) + α' * ∑ i, (x - w_next) i * Real.log (w_next i)
      - α * ∑ i, (x - w_next) i * Real.log (w i)) =
      ∑ i, (x i - w_next i) *
        (g (EuclideanSpace.basisFun (Fin d) ℝ i) + α' * Real.log (w_next i)
          - α * Real.log (w i)) := by
    rw [h_basis (x - w_next)]
    simp only [PiLp.sub_apply, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    congr 1 with i
    ring
  rw [h_comb]
  simp_rw [h_w_next_i]
  rw [← sum_mul, sum_sub_distrib, hx.2, hw_next_mem.2, sub_self, zero_mul]

/-- The Exponential Weights update is an exact constrained minimizer (`IsMinOn`)
of the linearized mirror descent step objective on the standard simplex $\Delta^{d-1}$. -/
theorem isMinOn_omdExpWeightStep (hd : 0 < d) (α α' : ℝ) (hα' : 0 < α')
    (w : EuclideanSpace ℝ (Fin d)) (hw_pos : ∀ i, 0 < w i)
    (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    IsMinOn (fun x ↦ g x + unnormEntropy α' x - (unnormEntropyFDeriv α w) x)
      (stdSimplex (d := d)) (omdExpWeightStep hd α α' w g) := by
  let w_next := omdExpWeightStep hd α α' w g
  have hw_next_pos := omdExpWeightStep_pos hd α α' w hw_pos g
  have hw_next_mem := omdExpWeightStep_mem_stdSimplex hd α α' w hw_pos g
  have h_diff : HasFDerivAt (unnormEntropy α') (unnormEntropyFDeriv α' w_next) w_next :=
    hasFDerivAt_unnormEntropy α' w_next hw_next_pos
  have h_conv : ConvexOn ℝ (stdSimplex (d := d)) (unnormEntropy α') :=
    convexOn_unnormEntropy_stdSimplex α' hα'.le
  let lin : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := g - unnormEntropyFDeriv α w
  have h_obj_conv : ConvexOn ℝ (stdSimplex (d := d)) (unnormEntropy α' + ⇑lin) :=
    h_conv.add (lin.toLinearMap.convexOn h_conv.1)
  have h_obj_diff : HasFDerivAt (unnormEntropy α' + ⇑lin)
      (unnormEntropyFDeriv α' w_next + lin) w_next :=
    h_diff.add lin.hasFDerivAt
  intro x hx
  have h_zero : (unnormEntropyFDeriv α' w_next + lin) (x - w_next) = 0 := by
    dsimp [lin]
    have := mirrorStepObj_diff_eq hd α α' hα' w hw_pos g x hx
    have h_reorder : (unnormEntropyFDeriv α' w_next + (g - unnormEntropyFDeriv α w)) (x - w_next) =
        (g + unnormEntropyFDeriv α' w_next - unnormEntropyFDeriv α w) (x - w_next) := by
      simp only [add_apply, sub_apply]
      ring
    rwa [h_reorder]
  have h_subg_base := (hasSubgradientWithinAt_iff_le.mp
      (h_obj_diff.hasSubgradientWithinAt h_obj_conv hw_next_mem)) x hx
  dsimp [bregDiv] at h_subg_base
  rw [h_zero, add_zero] at h_subg_base
  dsimp [lin] at h_subg_base ⊢
  simp only [sub_apply] at h_subg_base ⊢
  linarith

/-! ### Whole Trajectory Sequence Construction and Properties -/

/-- Recursive trajectory of iterates generated by the Exponential Weights update, starting from
$w_1 = \mathrm{uniformSimplex}(d)$ at $t = 1$. -/
noncomputable def omdExpWeights (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => uniformSimplex d
  | 1 => uniformSimplex d
  | t + 2 => omdExpWeightStep hd (α (t + 1)) (α (t + 2)) (omdExpWeights hd α g (t + 1)) (g (t + 1))

@[simp]
lemma omdExpWeights_one (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) :
    omdExpWeights hd α g 1 = uniformSimplex d :=
  rfl

lemma omdExpWeights_succ_succ (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (t : ℕ) :
    omdExpWeights hd α g (t + 2) =
      omdExpWeightStep hd (α (t + 1)) (α (t + 2)) (omdExpWeights hd α g (t + 1)) (g (t + 1)) :=
  rfl

/-- Every iterate $w_t$ produced by `omdExpWeights` is strictly positive in all coordinates for
$t \ge 1$. -/
theorem omdExpWeights_pos (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) :
    ∀ t ≥ 1, ∀ i, 0 < omdExpWeights hd α g t i := by
  intro t ht
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := Nat.exists_eq_add_of_le' ht
  clear ht
  induction n with
  | zero =>
    intro i
    rw [omdExpWeights_one]
    exact uniformSimplex_pos hd i
  | succ n ih =>
    intro i
    rw [omdExpWeights_succ_succ]
    exact omdExpWeightStep_pos hd (α (n + 1)) (α (n + 2)) (omdExpWeights hd α g (n + 1))
      (fun j ↦ ih j) (g (n + 1)) i

/-- Every iterate $w_t$ produced by `omdExpWeights` lies in the standard simplex $\Delta^{d-1}$ for
$t \ge 1$. -/
theorem omdExpWeights_mem_stdSimplex (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) :
    ∀ t ≥ 1, omdExpWeights hd α g t ∈ stdSimplex (d := d) := by
  intro t ht
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := Nat.exists_eq_add_of_le' ht
  clear ht
  induction n with
  | zero =>
    rw [omdExpWeights_one]
    exact mem_stdSimplex_uniformSimplex hd
  | succ n _ =>
    rw [omdExpWeights_succ_succ]
    have h_pos : ∀ j, 0 < omdExpWeights hd α g (n + 1) j := by
      have : 1 ≤ n + 1 := by omega
      exact omdExpWeights_pos hd α g (n + 1) this
    exact omdExpWeightStep_mem_stdSimplex hd (α (n + 1)) (α (n + 2))
      (omdExpWeights hd α g (n + 1)) h_pos (g (n + 1))

/-- The iterates generated by `omdExpWeights` satisfy the `IsMinOn` condition at each
round $t \ge 1$. -/
theorem omdExpWeights_isMinOn (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (t : ℕ) (ht : 1 ≤ t)
    (hα'_pos : 0 < α (t + 1)) :
    IsMinOn (fun x ↦ g t x + unnormEntropy (α (t + 1)) x -
      (unnormEntropyFDeriv (α t) (omdExpWeights hd α g t)) x)
      (stdSimplex (d := d)) (omdExpWeights hd α g (t + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := Nat.exists_eq_add_of_le' ht
  rw [omdExpWeights_succ_succ]
  have h_pos := omdExpWeights_pos hd α g (k + 1) (by omega)
  exact isMinOn_omdExpWeightStep hd (α (k + 1)) (α (k + 1 + 1)) hα'_pos
    (omdExpWeights hd α g (k + 1)) h_pos (g (k + 1))

/-- Per-round optimality deficit is non-negative for the concrete `omdExpWeights` trajectory
at any comparator $u \in \Delta^{d-1}$ when $\alpha_{t+1} > 0$. -/
theorem omdExpWeights_optimality_nonneg (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (t : ℕ) (ht : 1 ≤ t) (hα'_pos : 0 < α (t + 1))
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ stdSimplex) :
    0 ≤ optimality (fun s ↦ unnormEntropyFDeriv (α s)) u (omdExpWeights hd α g) g t := by
  have hw_succ_pos := omdExpWeights_pos hd α g (t + 1) (by omega)
  have hw_succ := omdExpWeights_mem_stdSimplex hd α g (t + 1) (by omega)
  have h_diff := hasFDerivAt_unnormEntropy (α (t + 1)) (omdExpWeights hd α g (t + 1)) hw_succ_pos
  have h_conv := convexOn_unnormEntropy_stdSimplex (d := d) (α (t + 1)) hα'_pos.le
  have h_min := omdExpWeights_isMinOn hd α g t ht hα'_pos
  exact optimality_nonneg_of_isMinOn (ψ := fun s ↦ unnormEntropy (α s))
    (gψ := fun s ↦ unnormEntropyFDeriv (α s))
    t h_diff h_conv hw_succ hu h_min

/-- Cumulative first-order optimality deficit is non-negative for the concrete `omdExpWeights`
trajectory at any comparator $u \in \Delta^{d-1}$. -/
theorem omdExpWeights_sum_optimality_nonneg (hd : 0 < d) (α : ℕ → ℝ)
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (T : ℕ)
    (hα_pos : ∀ t ∈ Ico 1 (T + 1), 0 < α (t + 1))
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ stdSimplex) :
    0 ≤ ∑ t ∈ Ico 1 (T + 1),
      optimality (fun s ↦ unnormEntropyFDeriv (α s)) u (omdExpWeights hd α g) g t :=
  sum_nonneg fun t ht ↦
    omdExpWeights_optimality_nonneg hd α g t (mem_Ico.mp ht).1 (hα_pos t ht) hu

end Online.OCO.LEA.COMD2
