/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Measurable equivalences

This file extends the theory of measurable equivalences, providing utilities for
working with products and unit types.

## Main declarations

* `MeasurableEquiv.punit`: measurable equivalence between `PUnit`s.
-/

@[expose] public section

namespace MeasurableEquiv

universe x y

/-- The measurable equivalence between two `PUnit`s. -/
abbrev punit : PUnit.{x + 1} ≃ᵐ PUnit.{y + 1} := ofUniqueOfUnique _ _

end MeasurableEquiv
