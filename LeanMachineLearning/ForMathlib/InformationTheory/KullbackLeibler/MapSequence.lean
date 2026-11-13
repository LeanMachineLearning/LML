/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

import Statlib.Divergence.FDiv.TrimApprox
import Statlib.Divergence.KullbackLeibler.Basic

/-!
# The Kullback–Leibler divergence along a generating sequence of maps

Let `μ, ν` be finite measures on `α` and `g n : α → β n` be measurable maps whose σ-algebras
`comap (g n)` increase to the σ-algebra of `α` (for instance the projections of a sequence space
on its first `n` coordinates). Then the divergence of `μ` and `ν` is the supremum of the
divergences of their images by the `g n`:
`klDiv μ ν = ⨆ n, klDiv (μ.map (g n)) (ν.map (g n))`.

## Main statements

* `klDiv_eq_iSup_map`: the divergence along a generating sequence of maps.

## Implementation notes

The inequality `≥` is the data-processing inequality. For `≤`, the divergences of the images
converge to `klDiv μ ν`: this is Statlib's `tendsto_fDiv_map_of_iSup_comap_eq` for the
f-divergence `fDiv klDivFun`, which is `klDiv` (`klDiv_eq_fDiv`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace InformationTheory

variable {α : Type*} {m0 : MeasurableSpace α} {μ ν : Measure α} [IsFiniteMeasure μ]
  [IsFiniteMeasure ν]

/-- **The divergence along a generating sequence of maps.** If the σ-algebras `comap (g n)` of
measurable maps `g n : α → β n` increase to the σ-algebra of `α`, then the divergence of two
finite measures is the supremum of the divergences of their images by the `g n`. -/
lemma klDiv_eq_iSup_map {β : ℕ → Type*} [mβ : ∀ n, MeasurableSpace (β n)] {g : ∀ n, α → β n}
    (hg : ∀ n, Measurable (g n))
    (hmono : Monotone fun n ↦ (mβ n).comap (g n))
    (hsup : ⨆ n, (mβ n).comap (g n) = m0) :
    klDiv μ ν = ⨆ n, klDiv (μ.map (g n)) (ν.map (g n)) := by
  refine le_antisymm ?_ (iSup_le fun n ↦ klDiv_map_le μ ν (hg n))
  have h := tendsto_fDiv_map_of_iSup_comap_eq (f := klDivFun) (μ := μ) (ν := ν) hg hmono hsup
  simp_rw [← klDiv_eq_fDiv] at h
  exact le_of_tendsto' h fun n ↦ le_iSup (fun n ↦ klDiv (μ.map (g n)) (ν.map (g n))) n

end InformationTheory
