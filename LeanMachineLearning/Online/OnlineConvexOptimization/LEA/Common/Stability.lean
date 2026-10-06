/-
Copyright (c) 2026 Isidoor Pinillo Esquivel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isidoor Pinillo Esquivel
-/
module

public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.Common.RegretTerms
public import LeanMachineLearning.Online.OnlineConvexOptimization.LEA.Common.Regularizer

/-!
# Stability Bound for Learning with Expert Advice (LEA)

This file proves the local-norm stability bound for Learning with Expert Advice (LEA)
following Orabona (Lemma 7.15 / Lemma 6.32) using the coordinate-wise Fenchel-Young inequality,
the Mean Value Theorem for Bregman divergence, and the unconstrained Exponential Gradient candidate
maximizer to bound the stability term directly using the iterate $w_t$:
$$\sum_{t=1}^T \mathrm{stability}_t \le
  \sum_{t=1}^T \frac{1}{2\alpha_t} \sum_{i=1}^d w_{t, i} (g_t)_i^2.$$

## Main definitions
* `stability`: One-round stability tradeoff between loss reduction and divergence.
* `expGradCandidate`: Unconstrained exponential gradient candidate maximizer.

## Main results
* `dual_local_norm_eta_le`: Coordinate-weighted duality bound with step size $\eta$.
* `stability_le_dual_norm`: One-round stability term bound via MVT at
  intermediate point $z$.
* `stability_le_dual_norm_wt`: One-round stability bound with iterate $w_t$
  (Orabona Lemma 7.15 / Lemma 6.32).
* `sum_stability_le_dual_norm_wt`: Cumulative stability bound with $w_t$.
-/

open scoped BigOperators Bregman Topology
open Finset

@[expose] public section

namespace Online.OCO.LEA

variable {d : ℕ}

/-! ### Scalar and Coordinate Duality (Fenchel-Young / Local Norms Replacement)

Mathlib currently does not provide general local norms $\|v\|_{\nabla^2\psi(z)}$ or their duals
$\|g\|_{\nabla^2\psi(z)^{-1}}^*$. For the unnormalized negative entropy regularizer, the Hessian
is diagonal with entries $(\nabla^2\psi(z))_{ii} = 1 / z_i$.

The lemma `dual_local_norm_eta_le` is the concrete, coordinate-wise replacement: it directly proves
the Fenchel-Young duality bound:
$$\langle \eta g, v \rangle - \frac{1}{2} \|v\|_z^2 \le \frac{\eta^2}{2} \|g\|_{z, *}^2,$$
where $\|v\|_z^2 = \sum_i v_i^2 / z_i$ and $\|g\|_{z, *}^2 = \sum_i z_i g_i^2$. -/

/-- Scaled coordinate-wise duality inequality with learning rate $\eta$:
$$\eta \sum_{i=1}^d v_i g_i - \frac{1}{2} \sum_{i=1}^d \frac{v_i^2}{z_i}
  \le \frac{\eta^2}{2} \sum_{i=1}^d z_i g_i^2.$$

This serves as the concrete coordinate replacement for the local-norm Fenchel-Young inequality
$\langle \eta g, v \rangle - \frac{1}{2} \|v\|_z^2 \le \frac{\eta^2}{2} (\|g\|_z^*)^2$. -/
lemma dual_local_norm_eta_le (η : ℝ) (v : EuclideanSpace ℝ (Fin d)) (g : Fin d → ℝ)
    (z : EuclideanSpace ℝ (Fin d)) (hz : ∀ i, 0 < z i) :
    η * (∑ i, v i * g i) - (1 / 2 : ℝ) * (∑ i, (v i) ^ 2 / z i) ≤
      (η ^ 2 / 2) * ∑ i, z i * (g i) ^ 2 := by
  calc η * (∑ i, v i * g i) - (1 / 2 : ℝ) * (∑ i, (v i) ^ 2 / z i)
    _ = ∑ i, (v i * (η * g i) - (1 / 2 : ℝ) * ((v i) ^ 2 / z i)) := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]; congr 1 with i; ring
    _ ≤ ∑ i, (1 / 2 : ℝ) * (z i * (η * g i) ^ 2) := sum_le_sum fun i _ ↦ by
      have h_sq := div_nonneg (sq_nonneg (v i - z i * (η * g i))) (hz i).le
      have : (v i - z i * (η * g i))^2 / z i =
          (v i)^2 / z i - 2 * (v i * (η * g i)) + z i * (η * g i)^2 := by
        field_simp [(hz i).ne']; ring
      linarith
    _ = (η ^ 2 / 2) * ∑ i, z i * (g i) ^ 2 := by
      rw [mul_sum]; congr 1 with i; ring

/-- One-round stability bound for Learning with Expert Advice via the Mean Value Theorem (MVT):
when $w_{t+1} \in \text{stdSimplex}$, and iterates $w_{t+1}, w_t$ have strictly positive
coordinates, the round-$t$ stability term with regularizer scale $\alpha_t > 0$
`stability (fun s ↦ unnormEntropyShifted (α s)) (fun s ↦ unnormEntropyFDeriv (α s)) w g t`
is upper bounded by $\frac{1}{2 \alpha_t} \sum_{i=1}^d z_i (g_t)_i^2$
for some intermediate point $z \in [w_{t+1}, w_t]$. -/
theorem stability_le_dual_norm (w : ℕ → EuclideanSpace ℝ (Fin d))
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (α : ℕ → ℝ) (t : ℕ) (hα_pos : 0 < α t)
    (hw_next_pos : ∀ i, 0 < w (t + 1) i)
    (hw_t_pos : ∀ i, 0 < w t i) :
    ∃ z ∈ segment ℝ (w (t + 1)) (w t),
      stability (fun s ↦ unnormEntropyShifted (α s)) (fun s ↦ unnormEntropyFDeriv (α s)) w g t ≤
        (1 / (2 * α t)) * ∑ i, z i * (g t (EuclideanSpace.basisFun (Fin d) ℝ i)) ^ 2 := by
  have h_pos : ∀ z ∈ segment ℝ (w (t + 1)) (w t), ∀ i, 0 < (z : EuclideanSpace ℝ (Fin d)) i := by
    rintro z ⟨a, b, ha, hb, hab, rfl⟩ i
    dsimp
    obtain rfl | ha_pos := eq_or_lt_of_le ha
    · have : b = 1 := by linarith
      simp [this, hw_t_pos i]
    · linarith [mul_pos ha_pos (hw_next_pos i), mul_nonneg hb (hw_t_pos i).le]
  obtain ⟨z, hz_seg, hz_breg⟩ := bregDiv_unnormEntropy_mvt (α t) (w (t + 1)) (w t) h_pos
  refine ⟨z, hz_seg, ?_⟩
  dsimp [stability]
  rw [bregDiv_unnormEntropyShifted, hz_breg]
  have h_decomp : g t (w t - w (t + 1)) =
      ∑ i, (w t i - w (t + 1) i) * g t (EuclideanSpace.basisFun (Fin d) ℝ i) := by
    have : w t - w (t + 1) =
        ∑ i, (w t i - w (t + 1) i) • EuclideanSpace.basisFun (Fin d) ℝ i := by
      ext i; simp [EuclideanSpace.basisFun_apply, Pi.single_apply]
    rw [this, map_sum]
    refine sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]
  simp_rw [show ∀ i, (w (t + 1) i - w t i)^2 = (w t i - w (t + 1) i)^2 from
    fun i ↦ by rw [← neg_sub (w t i) (w (t + 1) i), neg_sq]]
  have h_dual := dual_local_norm_eta_le (1 / α t) (w t - w (t + 1))
    (fun i ↦ g t (EuclideanSpace.basisFun (Fin d) ℝ i)) z (h_pos z hz_seg)
  have h_pi (i : Fin d) : (w t - w (t + 1)) i = w t i - w (t + 1) i := rfl
  simp_rw [h_pi] at h_dual
  have h_mult := mul_le_mul_of_nonneg_left h_dual hα_pos.le
  have h_rw : α t * ((1 / α t) * ∑ i, (w t i - w (t + 1) i) *
        g t (EuclideanSpace.basisFun (Fin d) ℝ i) - (1 / 2 : ℝ) *
        ∑ i, (w t i - w (t + 1) i) ^ 2 / z i) =
      (∑ i, (w t i - w (t + 1) i) * g t (EuclideanSpace.basisFun (Fin d) ℝ i)) -
        (α t / 2) * ∑ i, (w t i - w (t + 1) i) ^ 2 / z i := by
    rw [mul_sub, ← mul_assoc, mul_one_div_cancel hα_pos.ne', one_mul]; ring
  have h_rw_rhs : α t * (((1 / α t) ^ 2 / 2) * ∑ i, z i *
        (g t (EuclideanSpace.basisFun (Fin d) ℝ i)) ^ 2) =
      (1 / (2 * α t)) * ∑ i, z i * (g t (EuclideanSpace.basisFun (Fin d) ℝ i)) ^ 2 := by
    calc α t * (((1 / α t) ^ 2 / 2) * ∑ i, z i *
          (g t (EuclideanSpace.basisFun (Fin d) ℝ i)) ^ 2)
      _ = (α t * (1 / (α t ^ 2 * 2))) * ∑ i, z i *
            (g t (EuclideanSpace.basisFun (Fin d) ℝ i)) ^ 2 := by ring
      _ = (1 / (2 * α t)) * ∑ i, z i * (g t (EuclideanSpace.basisFun (Fin d) ℝ i)) ^ 2 := by
        congr 1; field_simp [hα_pos.ne']
  linarith [h_decomp, h_mult, h_rw, h_rw_rhs]

/-! ### Stability Bound via Candidate Maximizer (Orabona Lemma 7.15 / Lemma 6.32) -/

/-- Stability bound for $w_{t+1} \in s$ derived via a candidate maximizer
$\tilde{w}_{t+1} \in s$: bounds the stability term by the local norm at an
intermediate point $\tilde{z} \in [\tilde{w}_{t+1}, w_t]$ via `stability_le_dual_norm`. -/
theorem stability_le_dual_norm_of_isMaxOn (w : ℕ → EuclideanSpace ℝ (Fin d))
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (α : ℕ → ℝ) (t : ℕ) (hα_pos : 0 < α t)
    (s : Set (EuclideanSpace ℝ (Fin d)))
    (hw_next : w (t + 1) ∈ s)
    (w_tilde_next : EuclideanSpace ℝ (Fin d))
    (hw_tilde_pos : ∀ i, 0 < w_tilde_next i)
    (hw_t_pos : ∀ i, 0 < w t i)
    (h_max : IsMaxOn (fun x ↦ (g t) (w t - x) -
      D_[unnormEntropyShifted (α t)](x, w t, unnormEntropyFDeriv (α t) (w t))) s
      w_tilde_next) :
    ∃ z ∈ segment ℝ w_tilde_next (w t),
      stability (fun s ↦ unnormEntropyShifted (α s)) (fun s ↦ unnormEntropyFDeriv (α s)) w g t ≤
        (1 / (2 * α t)) * ∑ i, z i * (g t (EuclideanSpace.basisFun (Fin d) ℝ i)) ^ 2 := by
  let w_cand : ℕ → EuclideanSpace ℝ (Fin d) := fun k ↦
    if k = t + 1 then w_tilde_next else w k
  have h_cand_next : w_cand (t + 1) = w_tilde_next := ite_eq_left rfl
  have h_cand_t : w_cand t = w t := ite_eq_right (show t ≠ t + 1 by omega)
  obtain ⟨z, hz_seg, hz_le⟩ := stability_le_dual_norm w_cand g α t hα_pos
    (by rw [h_cand_next]; exact hw_tilde_pos) (by rw [h_cand_t]; exact hw_t_pos)
  rw [h_cand_next, h_cand_t] at hz_seg
  dsimp [stability] at hz_le
  rw [h_cand_next, h_cand_t] at hz_le
  refine ⟨z, hz_seg, ?_⟩
  have h_le_max : stability (fun s ↦ unnormEntropyShifted (α s))
      (fun s ↦ unnormEntropyFDeriv (α s)) w g t ≤
      (g t) (w t - w_tilde_next) -
        D_[unnormEntropyShifted (α t)](w_tilde_next, w t, unnormEntropyFDeriv (α t) (w t)) := by
    dsimp [stability]
    exact h_max hw_next
  linarith

/-! ### Unconstrained Exponential Gradient Candidate Maximizer -/

/-- The unconstrained candidate minimizer $\tilde{w}_{t+1}$ in coordinate form:
$$\tilde{w}_{t+1, i} = w_{t, i} \exp\left(-\frac{\langle g_t, e_i \rangle}{\alpha}\right)$$ -/
noncomputable def expGradCandidate (α : ℝ) (wt : EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i ↦ wt i * Real.exp (- (g (EuclideanSpace.basisFun (Fin d) ℝ i)) / α))

@[simp]
lemma expGradCandidate_apply (α : ℝ) (wt : EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (i : Fin d) :
    expGradCandidate α wt g i = wt i * Real.exp (- (g (EuclideanSpace.basisFun (Fin d) ℝ i)) / α) :=
  rfl

lemma expGradCandidate_pos (α : ℝ) (wt : EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hwt_pos : ∀ i, 0 < wt i) (i : Fin d) :
    0 < expGradCandidate α wt g i :=
  mul_pos (hwt_pos i) (Real.exp_pos _)

/-- When $g_i \ge 0$ and $\alpha > 0$, candidate coordinates are bounded above by $w_{t, i}$. -/
lemma expGradCandidate_le_wt (α : ℝ) (hα_pos : 0 < α)
    (wt : EuclideanSpace ℝ (Fin d)) (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hg_nonneg : ∀ i, 0 ≤ g (EuclideanSpace.basisFun (Fin d) ℝ i))
    (hwt_nonneg : ∀ i, 0 ≤ wt i) (i : Fin d) :
    expGradCandidate α wt g i ≤ wt i := by
  dsimp [expGradCandidate]
  have h_div_nonpos : - (g (EuclideanSpace.basisFun (Fin d) ℝ i)) / α ≤ 0 := by
    rw [neg_div, neg_nonpos]
    exact div_nonneg (hg_nonneg i) hα_pos.le
  have h_exp_le_one : Real.exp (- (g (EuclideanSpace.basisFun (Fin d) ℝ i)) / α) ≤ 1 := by
    simpa using Real.exp_le_exp_of_le h_div_nonpos
  calc wt i * Real.exp (- (g (EuclideanSpace.basisFun (Fin d) ℝ i)) / α)
    _ ≤ wt i * 1 := mul_le_mul_of_nonneg_left h_exp_le_one (hwt_nonneg i)
    _ = wt i := mul_one (wt i)

/-- Any point on the segment $[\tilde{w}, w]$ is coordinate-wise bounded above by $w$
when $\tilde{w} \le w$. -/
lemma segment_le_of_le (w_tilde w_t : EuclideanSpace ℝ (Fin d))
    (h_le : ∀ i, w_tilde i ≤ w_t i)
    (z : EuclideanSpace ℝ (Fin d)) (hz : z ∈ segment ℝ w_tilde w_t) (i : Fin d) :
    z i ≤ w_t i := by
  rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
  dsimp
  calc a * w_tilde i + b * w_t i
    _ ≤ a * w_t i + b * w_t i := by
      linarith [mul_le_mul_of_nonneg_left (h_le i) ha]
    _ = (a + b) * w_t i := by ring
    _ = w_t i := by rw [hab, one_mul]

/-- `expGradCandidate` is the global maximizer on the positive orthant
$\mathcal{X} = \{x \in \mathbb{R}^d \mid \forall i, 0 < x_i\}$ of the unconstrained OMD objective
$x \mapsto \langle g_t, w_t - x \rangle - D_{\psi_{\alpha_t}}(x, w_t)$. -/
theorem isMaxOn_expGradCandidate (α : ℝ) (hα_pos : 0 < α)
    (wt : EuclideanSpace ℝ (Fin d)) (hwt_pos : ∀ i, 0 < wt i)
    (g : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    IsMaxOn (fun x ↦ g (wt - x) -
      D_[unnormEntropyShifted α](x, wt, unnormEntropyFDeriv α wt))
      {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 < x i} (expGradCandidate α wt g) := by
  set w_cand := expGradCandidate α wt g
  have hw_cand_pos : ∀ i, 0 < w_cand i := expGradCandidate_pos α wt g hwt_pos
  intro x hx
  dsimp
  rw [bregDiv_unnormEntropyShifted, bregDiv_unnormEntropyShifted]
  have h_diff_grad : (unnormEntropyFDeriv α wt - unnormEntropyFDeriv α w_cand) = g := by
    ext v
    simp only [unnormEntropyFDeriv_apply, sub_apply]
    have h_log_ratio (i : Fin d) : Real.log (wt i) - Real.log (w_cand i) =
        (g (EuclideanSpace.basisFun (Fin d) ℝ i)) / α := by
      have h_cand_i : w_cand i =
          wt i * Real.exp (- (g (EuclideanSpace.basisFun (Fin d) ℝ i)) / α) := rfl
      rw [h_cand_i, Real.log_mul (hwt_pos i).ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
    have h_g_sum : g v = ∑ i, v i * g (EuclideanSpace.basisFun (Fin d) ℝ i) := by
      have : v = ∑ i, v i • EuclideanSpace.basisFun (Fin d) ℝ i := by
        ext i; simp [EuclideanSpace.basisFun_apply, Pi.single_apply]
      conv_lhs => rw [this]
      rw [map_sum]
      refine sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]
    have h_rw_sum : α * ∑ i, v i * (Real.log (wt i) - Real.log (w_cand i)) =
        ∑ i, v i * g (EuclideanSpace.basisFun (Fin d) ℝ i) := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ ↦ by
        rw [h_log_ratio i]
        have hα_ne : α ≠ 0 := hα_pos.ne'
        rw [mul_left_comm, mul_div_cancel₀ _ hα_ne]
    rw [← mul_sub, ← sum_sub_distrib]
    have h_dist : (∑ i, (v i * Real.log (wt i) - v i * Real.log (w_cand i))) =
        ∑ i, v i * (Real.log (wt i) - Real.log (w_cand i)) :=
      sum_congr rfl fun i _ ↦ by ring
    rw [h_dist, h_rw_sum, ← h_g_sum]
  have h_three := bregDiv_three_point (f := unnormEntropy α) (z := x) (x := w_cand) (y := wt)
    (J_x := unnormEntropyFDeriv α w_cand) (J_y := unnormEntropyFDeriv α wt)
  have h_grad_eval : (unnormEntropyFDeriv α wt - unnormEntropyFDeriv α w_cand) (x - w_cand) =
      g (x - w_cand) := by rw [h_diff_grad]
  rw [h_grad_eval] at h_three
  have h_lin : g (wt - w_cand) - g (wt - x) = g (x - w_cand) := by
    have : wt - w_cand - (wt - x) = x - w_cand := by ext; simp
    rw [← map_sub, this]
  have h_nonneg := bregDiv_unnormEntropy_nonneg α hα_pos.le x w_cand hx hw_cand_pos
  linarith [h_three, h_lin, h_nonneg]

/-- Stability bound for strictly positive iterates $w_t, w_{t+1} > 0$ when losses
are non-negative $g_t \ge 0$: bounds the stability term directly with $w_t$ instead of
the intermediate point $z$. -/
theorem stability_le_dual_norm_wt (w : ℕ → EuclideanSpace ℝ (Fin d))
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (α : ℕ → ℝ) (t : ℕ) (hα_pos : 0 < α t)
    (hw_next_pos : ∀ i, 0 < w (t + 1) i)
    (hw_t_pos : ∀ i, 0 < w t i)
    (hg_nonneg : ∀ i, 0 ≤ g t (EuclideanSpace.basisFun (Fin d) ℝ i)) :
    stability (fun s ↦ unnormEntropyShifted (α s)) (fun s ↦ unnormEntropyFDeriv (α s)) w g t ≤
      (1 / (2 * α t)) * ∑ i, w t i * (g t (EuclideanSpace.basisFun (Fin d) ℝ i)) ^ 2 := by
  have h_max := isMaxOn_expGradCandidate (α t) hα_pos (w t) hw_t_pos (g t)
  have hw_next_mem : w (t + 1) ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 < x i} := hw_next_pos
  obtain ⟨z, hz_seg, hz_le⟩ := stability_le_dual_norm_of_isMaxOn w g α t hα_pos
    {x | ∀ i, 0 < x i} hw_next_mem (expGradCandidate (α t) (w t) (g t))
    (expGradCandidate_pos (α t) (w t) (g t) hw_t_pos) hw_t_pos h_max
  have hz_le_wt (i : Fin d) : z i ≤ w t i := by
    refine segment_le_of_le (expGradCandidate (α t) (w t) (g t)) (w t) ?_ z hz_seg i
    intro j
    exact expGradCandidate_le_wt (α t) hα_pos (w t) (g t) hg_nonneg (fun k ↦ (hw_t_pos k).le) j
  have h_sum_le : ∑ i, z i * (g t (EuclideanSpace.basisFun (Fin d) ℝ i)) ^ 2 ≤
      ∑ i, w t i * (g t (EuclideanSpace.basisFun (Fin d) ℝ i)) ^ 2 := by
    refine sum_le_sum fun i _ ↦ ?_
    exact mul_le_mul_of_nonneg_right (hz_le_wt i) (sq_nonneg _)
  have h_factor_pos : 0 ≤ 1 / (2 * α t) := by
    refine div_nonneg zero_le_one (mul_nonneg (by norm_num) hα_pos.le)
  calc stability (fun s ↦ unnormEntropyShifted (α s)) (fun s ↦ unnormEntropyFDeriv (α s)) w g t
    _ ≤ (1 / (2 * α t)) * ∑ i, z i * (g t (EuclideanSpace.basisFun (Fin d) ℝ i)) ^ 2 := hz_le
    _ ≤ (1 / (2 * α t)) * ∑ i, w t i *
          (g t (EuclideanSpace.basisFun (Fin d) ℝ i)) ^ 2 :=
        mul_le_mul_of_nonneg_left h_sum_le h_factor_pos

/-- Multi-round cumulative stability bound for strictly positive iterates $w_t, w_{t+1} > 0$
when losses are non-negative $g_t \ge 0$:
$$\sum_{t=1}^T \mathrm{stability}_t \le
  \sum_{t=1}^T \frac{1}{2\alpha_t} \sum_{i=1}^d w_{t, i} (g_t)_i^2.$$ -/
theorem sum_stability_le_dual_norm_wt (w : ℕ → EuclideanSpace ℝ (Fin d))
    (g : ℕ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (α : ℕ → ℝ) (T : ℕ)
    (hα_pos : ∀ t ∈ Ico 1 (T + 1), 0 < α t)
    (hw_pos : ∀ t ∈ Ico 1 (T + 2), ∀ i, 0 < w t i)
    (hg_nonneg : ∀ t ∈ Ico 1 (T + 1),
      ∀ i, 0 ≤ g t (EuclideanSpace.basisFun (Fin d) ℝ i)) :
    ∑ t ∈ Ico 1 (T + 1),
      stability (fun s ↦ unnormEntropyShifted (α s)) (fun s ↦ unnormEntropyFDeriv (α s)) w g t ≤
      ∑ t ∈ Ico 1 (T + 1), (1 / (2 * α t)) *
        ∑ i, w t i * (g t (EuclideanSpace.basisFun (Fin d) ℝ i)) ^ 2 := by
  refine sum_le_sum fun t ht ↦ ?_
  have hw_next_pos : ∀ i, 0 < w (t + 1) i := by
    rw [mem_Ico] at ht
    exact hw_pos (t + 1) (by rw [mem_Ico]; omega)
  have hw_t_pos : ∀ i, 0 < w t i := by
    rw [mem_Ico] at ht
    exact hw_pos t (by rw [mem_Ico]; omega)
  exact stability_le_dual_norm_wt w g α t (hα_pos t ht)
    hw_next_pos hw_t_pos (hg_nonneg t ht)

end Online.OCO.LEA
