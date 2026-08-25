/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Process.Filtration

/-!
# Shifted filtrations
-/

@[expose] public section

namespace MeasureTheory

variable {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}

-- todo: generalize to other index sets, not just `ℕ`
def Filtration.shiftUp (F : Filtration ℕ mΩ) (n : ℕ) : Filtration ℕ mΩ where
  seq i := F.seq (i + n)
  mono' i j hij := F.mono (by grind)
  le' i := F.le (i + n)

def Filtration.shiftDown (F : Filtration ℕ mΩ) (n : ℕ) : Filtration ℕ mΩ where
  seq i := F.seq (i - n)
  mono' i j hij := F.mono (by grind)
  le' i := F.le (i - n)

end MeasureTheory
