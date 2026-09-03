/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.SumRewards
import LMLExtra.SumRewardsBounds

/-!
# Bounds on the empirical mean

This file demonstrates how `LeanMachineLearning` uses `LMLExtra`: the import of
`LMLExtra.SumRewardsBounds` is private (plain `import`, not `public import`), so nothing from
`LMLExtra` is re-exported, and its theorems are only used inside proofs. The statements below
mention only `LeanMachineLearning` definitions.
-/

@[expose] public section

namespace Learning

variable {𝓐 Ω : Type*} [DecidableEq 𝓐] {A : ℕ → Ω → 𝓐} {a : 𝓐} {t : ℕ} {ω : Ω}

lemma empMean_le_of_le {R : ℕ → Ω → ℝ} {c : ℝ} (h_pull : pullCount A a t ω ≠ 0)
    (hR : ∀ s < t, A s ω = a → R s ω ≤ c) :
    empMean A R a t ω ≤ c := by
  have h_pos : (0 : ℝ) < pullCount A a t ω := by exact_mod_cast Nat.pos_of_ne_zero h_pull
  rw [empMean, div_le_iff₀ h_pos, mul_comm]
  exact sumRewards_le_pullCount_mul hR

lemma le_empMean_of_le {R : ℕ → Ω → ℝ} {c : ℝ} (h_pull : pullCount A a t ω ≠ 0)
    (hR : ∀ s < t, A s ω = a → c ≤ R s ω) :
    c ≤ empMean A R a t ω := by
  have h_pos : (0 : ℝ) < pullCount A a t ω := by exact_mod_cast Nat.pos_of_ne_zero h_pull
  rw [empMean, le_div_iff₀ h_pos, mul_comm]
  exact pullCount_mul_le_sumRewards hR

end Learning
