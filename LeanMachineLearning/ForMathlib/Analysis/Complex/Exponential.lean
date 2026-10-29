/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Complex.Exponential

/-!
# Bounds on the real exponential

## Main statements

* `Real.exp_le_one_add_add_of_abs_le_one`: for `|x| ≤ 1`, `exp x ≤ 1 + x + 3 / 4 * x ^ 2`.
-/

@[expose] public section

namespace Real

/-- Second-order bound on the exponential on `[-1, 1]`, from `Real.exp_bound`. -/
lemma exp_le_one_add_add_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    exp x ≤ 1 + x + 3 / 4 * x ^ 2 := by
  have h := Real.exp_bound hx (n := 2) two_pos
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith [(abs_le.1 h).2]

end Real
