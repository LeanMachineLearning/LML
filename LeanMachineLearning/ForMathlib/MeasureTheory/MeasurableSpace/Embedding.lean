/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Order.Restriction
public import Mathlib.Probability.Kernel.IonescuTulcea.Maps

/-!
# Measurable equivalences

Measurable equivalences between product and pi types, used to manipulate histories of sequential
learning algorithms (elements of `Fin n → 𝓐 × 𝓨` or `Iic n → 𝓐 × 𝓨`).

* `MeasurableEquiv.uniqueProd`, `MeasurableEquiv.prodUnique`: drop a component that lives in a type
  with a unique element.
* `MeasurableEquiv.IicSuccProd`: `(Π i : Iic (n + 1), X i) ≃ᵐ (Π i : Iic n, X i) × X (n + 1)`.
* `MeasurableEquiv.finSuccPiIic`: `(Π i : Fin (n + 1), X i) ≃ᵐ (Π i : Iic n, X i)`.
* `MeasurableEquiv.finSuccProd`: `(Fin (n + 1) → X) ≃ᵐ (Fin n → X) × X`.
-/

@[expose] public section

open Finset Preorder

lemma coe_default_Iic_zero : ((default : Iic 0) : ℕ) = 0 := rfl

namespace MeasurableEquiv

section Unique

/-- The measurable equivalence `α × β ≃ᵐ β` when `α` has a unique element. -/
def uniqueProd (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] [Unique α] :
    α × β ≃ᵐ β where
  toFun := Prod.snd
  invFun b := (default, b)
  left_inv _ := Prod.ext (Unique.eq_default _).symm rfl
  right_inv _ := rfl
  measurable_toFun := measurable_snd
  measurable_invFun := measurable_const.prodMk measurable_id

@[simp]
lemma uniqueProd_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Unique α]
    (p : α × β) :
    uniqueProd α β p = p.2 := rfl

@[simp]
lemma uniqueProd_symm_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Unique α]
    (b : β) :
    (uniqueProd α β).symm b = (default, b) := rfl

/-- The measurable equivalence `α × β ≃ᵐ α` when `β` has a unique element. -/
def prodUnique (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] [Unique β] :
    α × β ≃ᵐ α where
  toFun := Prod.fst
  invFun a := (a, default)
  left_inv _ := Prod.ext rfl (Unique.eq_default _).symm
  right_inv _ := rfl
  measurable_toFun := measurable_fst
  measurable_invFun := measurable_id.prodMk measurable_const

@[simp]
lemma prodUnique_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Unique β]
    (p : α × β) :
    prodUnique α β p = p.1 := rfl

@[simp]
lemma prodUnique_symm_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Unique β]
    (a : α) :
    (prodUnique α β).symm a = (a, default) := rfl

end Unique

section Iic

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

/-- Measurable equivalence between a product up to `n + 1` and the pair of the product up to `n` and
the space at `n + 1`. -/
def IicSuccProd (X : ℕ → Type*) [∀ n, MeasurableSpace (X n)] (n : ℕ) :
    MeasurableEquiv (Π i : Iic (n + 1), X i) ((Π i : Iic n, X i) × X (n + 1)) :=
  (IicProdIoc (Nat.le_succ n)).symm.trans
    (prodCongr (refl _) (piSingleton n).symm)

lemma symm_IicSuccProd (n : ℕ) :
    (IicSuccProd X n).symm =
      (prodCongr (refl _) (piSingleton n)).trans
        (IicProdIoc (Nat.le_succ n)) := rfl

@[simp]
lemma IicSuccProd_apply (n : ℕ) (h : Π i : Iic (n + 1), X i) :
    IicSuccProd X n h = (fun i : Iic n ↦ h ⟨i.1, by grind⟩, h ⟨n + 1, by simp⟩) :=
  rfl

lemma coe_prodCongr {α β γ δ : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
    (e₁ : MeasurableEquiv α β) (e₂ : MeasurableEquiv γ δ) :
    (prodCongr e₁ e₂ : (α × γ) → (β × δ)) = Prod.map e₁ e₂ := rfl

lemma coe_refl {α : Type*} {mα : MeasurableSpace α} :
    (refl α : α → α) = id := rfl

end Iic

section Fin

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

/-- Measurable equivalence between `Π i : Fin (n + 1), X i` and `Π i : Iic n, X i`. -/
def finSuccPiIic (X : ℕ → Type*) [∀ n, MeasurableSpace (X n)] (n : ℕ) :
    (Π i : Fin (n + 1), X i) ≃ᵐ (Π i : Iic n, X i) where
  toFun h i := h ⟨i.1, Nat.lt_succ_of_le (mem_Iic.mp i.2)⟩
  invFun h i := h ⟨i.1, mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

@[simp]
lemma finSuccPiIic_apply (n : ℕ) (h : Π i : Fin (n + 1), X i) (i : Iic n) :
    finSuccPiIic X n h i = h ⟨i.1, Nat.lt_succ_of_le (mem_Iic.mp i.2)⟩ := rfl

@[simp]
lemma finSuccPiIic_symm_apply (n : ℕ) (h : Π i : Iic n, X i) (i : Fin (n + 1)) :
    (finSuccPiIic X n).symm h i = h ⟨i.1, mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩ :=
  rfl

lemma finSuccPiIic_symm_comp_frestrictLe (n : ℕ) :
    (finSuccPiIic X n).symm ∘ frestrictLe n = fun x (i : Fin (n + 1)) ↦ x i := rfl

/-- Measurable equivalence between `Fin (n + 1) → X` and `(Fin n → X) × X`. -/
def finSuccProd (X : Type*) [MeasurableSpace X] (n : ℕ) :
    (Fin (n + 1) → X) ≃ᵐ (Fin n → X) × X :=
  (piFinSuccAbove (fun _ ↦ X) (Fin.last n)).trans prodComm

@[simp]
lemma finSuccProd_apply {X : Type*} [MeasurableSpace X] (n : ℕ)
    (h : Fin (n + 1) → X) :
    finSuccProd X n h = (fun i ↦ h i.castSucc, h (Fin.last n)) := by
  simp [finSuccProd]
  rfl

@[simp]
lemma finSuccProd_symm_apply {X : Type*} [MeasurableSpace X] (n : ℕ)
    (p : (Fin n → X) × X) :
    (finSuccProd X n).symm p = Fin.snoc p.1 p.2 := by
  simp [finSuccProd]
  rfl

end Fin

end MeasurableEquiv
