/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Integrability of inner products
-/

@[expose] public section

open scoped ENNReal RealInnerProductSpace

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E} {P : Measure Ω}

lemma MemLp.eLpNorm_rpow_norm_lt_top [SeminormedAddCommGroup E]
    {f : Ω → E} {p : ℝ≥0∞}
    (hf : MemLp f p P) (hp_zero : p ≠ 0) (hp_top : p ≠ ∞) :
    eLpNorm (fun x ↦ ‖f x‖ ^ p.toReal) 1 P < ∞ := by
  simp only [eLpNorm_one_eq_lintegral_enorm, norm_nonneg, ENNReal.toReal_nonneg,
    Real.enorm_rpow_of_nonneg, enorm_norm]
  exact (hf.integrable_enorm_rpow hp_zero hp_top).hasFiniteIntegral

lemma MemLp.integrable_inner [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : Ω → E}
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω ↦ ⟪f ω, g ω⟫) P := by
  rw [← memLp_one_iff_integrable]
  constructor
  · exact hf.aestronglyMeasurable.inner hg.aestronglyMeasurable
  have h x : ‖⟪f x, g x⟫‖ ≤ ‖‖f x‖ ^ (2 : ℝ) + ‖g x‖ ^ (2 : ℝ)‖ := by
    norm_cast
    calc ‖⟪f x, g x⟫‖ ≤ ‖f x‖ * ‖g x‖ := norm_inner_le_norm _ _
      _ ≤ 2 * ‖f x‖ * ‖g x‖ := by
        gcongr
        exact le_mul_of_one_le_left (norm_nonneg _) one_le_two
      _ ≤ ‖‖f x‖ ^ 2 + ‖g x‖ ^ 2‖ := (two_mul_le_add_sq _ _).trans (le_abs_self _)
  refine (eLpNorm_mono h).trans_lt ((eLpNorm_add_le ?_ ?_ le_rfl).trans_lt ?_)
  · exact (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
  · exact (hg.norm.aemeasurable.pow_const _).aestronglyMeasurable
  rw [ENNReal.add_lt_top]
  exact ⟨hf.eLpNorm_rpow_norm_lt_top (by simp) (by simp),
    hg.eLpNorm_rpow_norm_lt_top (by simp) (by simp)⟩

end MeasureTheory
