/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Order.Interval.Finset.Basic

/-!
# Lemmas about finite intervals

We record that the interval `Finset.Iic a`, seen as a type, is nonempty.
-/

@[expose] public section

namespace Finset

instance {α : Type*} [Preorder α] [LocallyFiniteOrderBot α] {a : α} : Nonempty (Iic a) :=
  nonempty_Iic.to_subtype

end Finset
