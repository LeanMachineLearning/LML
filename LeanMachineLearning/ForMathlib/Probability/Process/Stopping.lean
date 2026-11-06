/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Process.Stopping

/-!
# Measurability of stopping times valued in `ℕ∞`

`IsStoppingTime.measurable'` gives the measurability of a stopping time `τ : Ω → WithTop ℕ` for the
Borel σ-algebra of `WithTop ℕ`. The same type seen as `ℕ∞` carries the discrete σ-algebra, a
different instance: `IsStoppingTime.measurable_enat` gives measurability for that one.
-/

@[expose] public section

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {f : Filtration ℕ mΩ} {τ : Ω → ℕ∞}

/-- A stopping time `τ : Ω → ℕ∞` of a filtration indexed by `ℕ` is measurable for the discrete
σ-algebra of `ℕ∞` (`IsStoppingTime.measurable'` is about the Borel σ-algebra of `WithTop ℕ`). -/
lemma measurable_enat (hτ : IsStoppingTime f τ) : Measurable τ :=
  -- the preimage of each (Borel-measurable) singleton is measurable
  measurable_to_countable' fun x ↦ hτ.measurable' (measurableSet_singleton (α := WithTop ℕ) x)

end MeasureTheory.IsStoppingTime
