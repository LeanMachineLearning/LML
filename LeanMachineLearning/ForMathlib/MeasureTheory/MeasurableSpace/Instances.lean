/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Data.ENat.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Measurability of functions with values in `ℕ∞`

## Main statements

* `Measurable.coe_nat_enat`: the coercion to `ℕ∞` of a measurable function is measurable.
* `Measurable.enat_toNat`: `ENat.toNat` of a measurable function is measurable.
-/

@[expose] public section

variable {α : Type*} {mα : MeasurableSpace α}

/-- The coercion `ℕ → ℕ∞` of a measurable function is measurable. -/
@[fun_prop]
lemma Measurable.coe_nat_enat {f : α → ℕ} (hf : Measurable f) :
    Measurable (fun a ↦ (f a : ℕ∞)) := Measurable.comp (by fun_prop) hf

/-- `ENat.toNat` of a measurable function is measurable. -/
@[fun_prop]
lemma Measurable.enat_toNat {f : α → ℕ∞} (hf : Measurable f) : Measurable (fun a ↦ (f a).toNat) :=
  Measurable.comp (by fun_prop) hf
