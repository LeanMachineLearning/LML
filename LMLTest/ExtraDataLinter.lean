/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Batteries.Tactic.Lint
import LeanMachineLearning.Tactic.Linter.ExtraData
import LMLExtra.SumRewardsBounds

/-! # Tests for the `extraData` linter

The declarations below live outside `LMLExtra`, so the linter applies to them. The first two
sections show the intended behavior. The following ones are attempts to make a declaration depend
on `LMLExtra` data without being reported: the `#lint` at the end shows that every attempt is
caught on the constant that actually mentions the data (which is not always the declaration
written by the user).

Attempts that are rejected elsewhere and therefore do not appear here:
* `attribute [nolint extraData] Learning.pullCount` from another file: attributes cannot be added
  to declarations of imported modules.
* `public import`/`meta import`/`import all` of `LMLExtra`, or importing it from a non-`module`
  file: rejected by `scripts/check_extra_imports.sh`.
* `@[nolint extraData]` added by a metaprogram: ignored by `scripts/check_extra_data.lean`.
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

/-! Launder through an "internal"-looking name. Reported on `Learning._laundered`. -/

def Learning._laundered (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : Finset ℕ := pullTimes A a t ω

def a1_uses_laundered (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : Finset ℕ :=
  Learning._laundered A a t ω

/-! Launder through a private definition. Reported on `laundered`. -/

private def laundered (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : Finset ℕ := pullTimes A a t ω

def a2_uses_private (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : Finset ℕ := laundered A a t ω

/-! Structure field default value. Reported on `WithDefault.times._default`, and on the use since
the default is inlined. -/

structure WithDefault (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) where
  times : Finset ℕ := pullTimes A a t ω

def a3_uses_default (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : WithDefault A a t ω := {}

/-! `partial def`: the body lives in `a4_partial._unsafe_rec`, where it is reported. -/

partial def a4_partial (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) (n : ℕ) : Finset ℕ :=
  if n = 0 then pullTimes A a t ω else a4_partial A a t ω (n - 1)

/-! `if` on an `LMLExtra` proposition with classical decidability. -/

open Classical in
noncomputable def a5_ite (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : ℕ :=
  if WasPulled A a t ω then 1 else 0

/-! `Classical.choose` with a clean predicate and an `LMLExtra` witness: allowed. The chosen
element only depends on the predicate, not on the witness of the proof. -/

noncomputable def a6_choose (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : Finset ℕ :=
  Classical.choose (p := fun s ↦ #s = pullCount A a t ω)
    ⟨_, card_pullTimes (A := A) (a := a) (t := t) (ω := ω)⟩

/-! Launder through an instance. Reported on `instEvil`. -/

instance instEvil : Inhabited (Finset ℕ) := ⟨pullTimes (fun _ _ ↦ 0) 0 0 ()⟩

noncomputable def a7_default : Finset ℕ := @default _ instEvil

/-! `match`: the `LMLExtra` data ends up in the main definition. -/

def a8_match (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) (n : ℕ) : Finset ℕ :=
  match n with
  | 0 => pullTimes A a t ω
  | _ + 1 => ∅

/-! `where` auxiliary. Reported on `a9_where.aux`. -/

def a9_where (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : Finset ℕ := aux
where aux : Finset ℕ := pullTimes A a t ω

/-! `@[nolint extraData]` disables the linter on the declaration, visibly. -/

@[nolint extraData]
def a10_nolint (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : Finset ℕ := pullTimes A a t ω

def a10_uses (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : Finset ℕ := a10_nolint A a t ω

/-! Data smuggled through a proposition: the statement of the theorem is reported. -/

theorem a11_nonempty (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) :
    Nonempty {s : Finset ℕ // s = pullTimes A a t ω} := ⟨⟨_, rfl⟩⟩

noncomputable def a11_choice (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : Finset ℕ :=
  (Classical.choice (a11_nonempty A a t ω)).1

/-! `LMLExtra` data as an implicit argument of a `LeanMachineLearning`/Mathlib constant. -/

noncomputable def a12_implicit (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : ℕ :=
  @Finset.card ℕ (pullTimes A a t ω)

/-! `opaque` with a body: the body is not unfoldable but it is what the compiled code runs. -/

opaque a13_opaque (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) : Finset ℕ := pullTimes A a t ω

/-! `@[implemented_by]` an `LMLExtra` definition: the logical content is clean, the compiled code
is `LMLExtra`'s. -/

@[implemented_by pullTimes]
def a14_impl {𝓐 Ω : Type*} [DecidableEq 𝓐] (A : ℕ → Ω → 𝓐) (a : 𝓐) (t : ℕ) (ω : Ω) :
    Finset ℕ := ∅

/--
error: -- Found 17 errors in 29 declarations (plus 18 automatically generated ones) in the current file with 1 linters

/- The `extraData` linter reports:
DECLARATIONS DEPEND ON `LMLExtra` DATA. Only theorems of `LMLExtra` may be used, and only inside proofs:
This linter can be disabled with `@[nolint extraData]`. -/
#check @a4_partial._unsafe_rec /- depends on `LMLExtra` data: [pullTimes] -/
#check @WithDefault.times._default /- depends on `LMLExtra` data: [pullTimes] -/
#check @bad_thm_statement /- depends on `LMLExtra` data: [pullTimes] -/
#check @bad_thm_statement_prop_def /- depends on `LMLExtra` data: [WasPulled] -/
#check @bad_def_value /- depends on `LMLExtra` data: [pullTimes] -/
#check @_laundered /- depends on `LMLExtra` data: [pullTimes] -/
#check @laundered /- depends on `LMLExtra` data: [pullTimes] -/
#check @a3_uses_default /- depends on `LMLExtra` data: [pullTimes] -/
#check @a5_ite /- depends on `LMLExtra` data: [WasPulled] -/
#check instEvil /- depends on `LMLExtra` data: [pullTimes] -/
#check @a8_match /- depends on `LMLExtra` data: [pullTimes] -/
#check @a9_where.aux /- depends on `LMLExtra` data: [pullTimes] -/
#check @a11_nonempty /- depends on `LMLExtra` data: [pullTimes] -/
#check @a11_choice /- depends on `LMLExtra` data: [pullTimes] -/
#check @a12_implicit /- depends on `LMLExtra` data: [pullTimes] -/
#check @a13_opaque /- depends on `LMLExtra` data: [pullTimes] -/
#check @a14_impl /- depends on `LMLExtra` data: [pullTimes] -/
-/
#guard_msgs in
#lint only extraData
