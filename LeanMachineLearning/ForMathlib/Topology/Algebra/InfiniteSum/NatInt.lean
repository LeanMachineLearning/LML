/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Series over the natural numbers below an extended natural number

## Main statements

* `tsum_indicator_natCast_lt_eq_sum_range`: for a finite `n : ℕ∞`, the series of `f` restricted to
  `{t : ℕ | t < n}` is the finite sum `∑ t ∈ range n.toNat, f t`.
-/

@[expose] public section

open Finset

/-- For a finite `n : ℕ∞`, the series of `f` restricted to the natural numbers `t < n` is the
finite sum of `f` over `range n.toNat`. -/
lemma tsum_indicator_natCast_lt_eq_sum_range {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    {n : ℕ∞} (hn : n ≠ ⊤) (f : ℕ → E) :
    ∑' t : ℕ, {t : ℕ | (t : ℕ∞) < n}.indicator f t = ∑ t ∈ range n.toNat, f t := by
  lift n to ℕ using hn
  have hs : {t : ℕ | (t : ℕ∞) < n} = range n := by
    ext; simp [ENat.natCast_lt_natCast]
  rw [hs, ENat.toNat_natCast, sum_eq_tsum_indicator]
