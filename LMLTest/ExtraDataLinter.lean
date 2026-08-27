/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Batteries.Tactic.Lint
import LeanMachineLearning.Tactic.Linter.ExtraData
import LMLExtra.SumRewardsBounds

/-! # Tests for the `extraData` linter

The declarations below live outside `LMLExtra`, so the linter applies to them.
-/

open Finset Learning

variable {𝓐 Ω : Type*} [DecidableEq 𝓐] {A : ℕ → Ω → 𝓐} {a : 𝓐} {t : ℕ} {ω : Ω}

section allowed

/-- A proof may use an `LMLExtra` theorem. -/
theorem ok_thm_uses_extra_theorem {R : ℕ → Ω → ℝ} {c : ℝ}
    (hR : ∀ s < t, A s ω = a → R s ω ≤ c) :
    sumRewards A R a t ω ≤ pullCount A a t ω * c :=
  sumRewards_le_pullCount_mul hR

/-- A proof may use an `LMLExtra` theorem whose statement mentions `LMLExtra` data. -/
theorem ok_thm_uses_extra_theorem_about_extra_data (h : ∃ s < t, A s ω = a) :
    0 < pullCount A a t ω := by
  rw [← card_pullTimes]
  exact card_pos.2 (wasPulled_iff.2 h)

/-- The proof subterm of a definition may use an `LMLExtra` theorem about `LMLExtra` data. -/
noncomputable def ok_def_with_proof_subterm (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) :
    {n : ℕ // n = pullCount A a t ω} :=
  ⟨pullCount A a t ω, by rw [← card_pullTimes]⟩

end allowed

section forbidden

/-- The statement mentions an `LMLExtra` definition. -/
theorem bad_thm_statement : #(pullTimes A a t ω) = pullCount A a t ω := card_pullTimes

/-- The statement mentions an `LMLExtra` `Prop`-valued definition. -/
theorem bad_thm_statement_prop_def (h : WasPulled A a t ω) : 0 < pullCount A a t ω := by
  rw [← card_pullTimes]
  exact card_pos.2 h

/-- The value uses an `LMLExtra` definition. -/
def bad_def_value (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : Finset ℕ := pullTimes A a t ω

end forbidden

/--
error: -- Found 3 errors in 6 declarations (plus 1 automatically generated ones) in the current file with 1 linters

/- The `extraData` linter reports:
DECLARATIONS DEPEND ON `LMLExtra` DATA. Only theorems of `LMLExtra` may be used, and only inside proofs:
This linter can be disabled with `@[nolint extraData]`. -/
#check @bad_thm_statement /- depends on `LMLExtra` data: [pullTimes] -/
#check @bad_thm_statement_prop_def /- depends on `LMLExtra` data: [WasPulled] -/
#check @bad_def_value /- depends on `LMLExtra` data: [pullTimes] -/
-/
#guard_msgs in
#lint only extraData
