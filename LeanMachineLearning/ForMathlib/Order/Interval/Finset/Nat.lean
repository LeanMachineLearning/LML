/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Order.Interval.Finset.Nat

/-!
# Lemmas about finite intervals of natural numbers

## Main statements

* `coe_default_Iic_zero`: the default element of `Finset.Iic 0` is `0`.
-/

@[expose] public section

lemma coe_default_Iic_zero : ((default : Finset.Iic 0) : ℕ) = 0 := rfl
