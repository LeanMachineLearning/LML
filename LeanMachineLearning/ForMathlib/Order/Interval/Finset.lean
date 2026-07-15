/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Order.Interval.Finset.Nat

/-!
# Lemmas about finite intervals.
-/

@[expose] public section

namespace Finset

instance {n : ℕ} : Nonempty (Iic n) := ⟨0, insert_eq_self.mp rfl⟩

end Finset
