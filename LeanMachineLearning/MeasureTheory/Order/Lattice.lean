/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Order.Lattice

/-! # Measurable inf of a finite set

-/

@[expose] public section

open Finset

variable {δ α : Type*} [MeasurableSpace δ] [SemilatticeInf α] [MeasurableSpace α] [MeasurableInf₂ α]

@[measurability]
theorem Finset.measurable_inf' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → δ → α}
    (hf : ∀ n ∈ s, Measurable (f n)) : Measurable (s.inf' hs f) :=
  Finset.inf'_induction hs _ (fun _f hf _g hg => hf.inf hg) fun n hn => hf n hn
