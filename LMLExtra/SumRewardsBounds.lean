/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.SumRewards

/-!
# Bounds on sums of rewards

Demo file for the `LMLExtra` library.

`LMLExtra` may use everything in `LeanMachineLearning`. In the other direction,
`LeanMachineLearning` may use the *theorems* proved here (only inside proofs), but none of the
*data* defined here: the definition `pullTimes` and the `Prop`-valued predicate `WasPulled` below
must not appear in any statement or definition of `LeanMachineLearning`.
This is enforced by the `extraData` environment linter.

## Main results

* `sumRewards_le_pullCount_mul`, `pullCount_mul_le_sumRewards`: bounds on the sum of rewards of
  an action in terms of its number of pulls. Their statements only involve `LeanMachineLearning`
  definitions, so `LeanMachineLearning` can use them.
-/

@[expose] public section

open Finset

namespace Learning

variable {𝓐 𝓨 Ω : Type*} [DecidableEq 𝓐] [AddCommGroup 𝓨]
  {A : ℕ → Ω → 𝓐} {R : ℕ → Ω → 𝓨} {a : 𝓐} {s t : ℕ} {ω : Ω}

/-- Times before `t` at which action `a` was chosen. -/
def pullTimes (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : Finset ℕ :=
  (range t).filter (fun s ↦ A s ω = a)

@[simp]
lemma mem_pullTimes : s ∈ pullTimes A a t ω ↔ s < t ∧ A s ω = a := by simp [pullTimes]

lemma card_pullTimes : #(pullTimes A a t ω) = pullCount A a t ω := rfl

lemma sumRewards_eq_sum_pullTimes : sumRewards A R a t ω = ∑ s ∈ pullTimes A a t ω, R s ω := by
  simp [sumRewards, pullTimes, sum_filter]

/-- Action `a` was chosen at least once before time `t`. -/
def WasPulled (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : Prop := (pullTimes A a t ω).Nonempty

lemma wasPulled_iff : WasPulled A a t ω ↔ ∃ s < t, A s ω = a := by
  simp [WasPulled, Finset.Nonempty]

lemma sumRewards_le_pullCount_mul {R : ℕ → Ω → ℝ} {c : ℝ}
    (hR : ∀ s < t, A s ω = a → R s ω ≤ c) :
    sumRewards A R a t ω ≤ pullCount A a t ω * c := by
  rw [sumRewards_eq_sum_pullTimes, ← card_pullTimes, ← nsmul_eq_mul]
  exact sum_le_card_nsmul _ _ _ fun s hs ↦ hR s (mem_pullTimes.1 hs).1 (mem_pullTimes.1 hs).2

lemma pullCount_mul_le_sumRewards {R : ℕ → Ω → ℝ} {c : ℝ}
    (hR : ∀ s < t, A s ω = a → c ≤ R s ω) :
    pullCount A a t ω * c ≤ sumRewards A R a t ω := by
  rw [sumRewards_eq_sum_pullTimes, ← card_pullTimes, ← nsmul_eq_mul]
  exact card_nsmul_le_sum _ _ _ fun s hs ↦ hR s (mem_pullTimes.1 hs).1 (mem_pullTimes.1 hs).2

end Learning
