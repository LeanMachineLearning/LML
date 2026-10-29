/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import Mathlib.Basic.Unique
public import Mathlib.Data.Prod.Basic

/-!
# `Unique` instance for products

A product of two types with a unique element has a unique element.
-/

@[expose] public section

instance Prod.instUnique {α β : Type*} [Unique α] [Unique β] : Unique (α × β) where
  default := (default, default)
  uniq p := by simp [Prod.ext_iff, Unique.eq_default]
