/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Lemmas about the product σ-algebra on a function space

## Main statements

* `MeasurableSpace.comap_pi`: the comap of the product σ-algebra by a map `g` is the supremum of
  the comaps of the σ-algebras of the coordinates by the coordinates of `g`.
* `MeasurableSpace.iSup_comap_restrictFin`: the σ-algebras of the projections of `ℕ → E` on the
  first `n` coordinates generate the product σ-algebra.
-/

@[expose] public section

open Function

namespace MeasurableSpace

variable {δ : Type*} {X : δ → Type*} [m : ∀ a, MeasurableSpace (X a)] {α : Type*}

/-- The comap of the product σ-algebra by `g` is the supremum of the comaps of the σ-algebras of
the coordinates by the coordinates of `g`. -/
lemma comap_pi {g : α → ∀ a, X a} : pi.comap g = ⨆ a, (m a).comap (fun x ↦ g x a) := by
  simp_rw [pi, comap_iSup, comap_comp, comp_def]

/-- The σ-algebras of the projections of `ℕ → E` on the first `n` coordinates generate the
product σ-algebra. -/
lemma iSup_comap_restrictFin {E : Type*} [mE : MeasurableSpace E] :
    ⨆ n : ℕ, MeasurableSpace.comap (fun f : ℕ → E ↦ fun i : Fin n ↦ f i)
      MeasurableSpace.pi = MeasurableSpace.pi := by
  refine le_antisymm
    (iSup_le fun n ↦ (Measurable.of_eval fun _ ↦ measurable_pi_apply _).comap_le)
    (iSup_le fun i ↦ le_iSup_of_le (i + 1) ?_)
  have : (fun f : ℕ → E ↦ f i) =
      (fun h : Fin (i + 1) → E ↦ h ⟨i, i.lt_succ_self⟩) ∘
        fun f : ℕ → E ↦ fun j : Fin (i + 1) ↦ f j := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

end MeasurableSpace
