/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Measurability from factorization

-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

lemma measurable_of_factorsThrough {f : α → β} {g : α → γ} {h : β → γ}
    (h_meas : Measurable h) (hg_eq : g = h ∘ f) :
    Measurable[mβ.comap f] g := by
  rw [hg_eq]
  exact h_meas.comp (.of_comap_le le_rfl)

lemma measurable_of_todo [Nonempty β] {f : β → α} {g : α → γ} (hf_meas : MeasurableEmbedding f)
    (hg_meas : Measurable g) (hg : Function.FactorsThrough g hf_meas.invFun) :
    Measurable[mβ.comap hf_meas.invFun] g := by
  refine measurable_of_factorsThrough (h := g ∘ f) (by fun_prop) ?_
  ext x
  refine hg ?_
  exact (hf_meas.leftInverse_invFun (hf_meas.invFun x)).symm

lemma measurable_of_todo' {f : β → α} {f' : α → β} {g : α → γ}
    (hff' : Function.LeftInverse f' f) (hg : Function.FactorsThrough g f')
    (hf : Measurable f) (hg_meas : Measurable g) :
    Measurable[mβ.comap f'] g := by
  refine measurable_of_factorsThrough (h := g ∘ f) (by fun_prop) ?_
  ext x
  refine hg ?_
  exact (hff' (f' x)).symm

variable {ι X Z : Type*} {mι : MeasurableSpace ι}
  [mX : MeasurableSpace X] {mZ : MeasurableSpace Z}
  {g : (ι → X) → Z}

lemma measurable_comap_of_dependsOn {s : Set ι}
    (hs : s.Nonempty) (hg : DependsOn g s) (hg_meas : Measurable g) :
    Measurable[MeasurableSpace.comap s.domRestrict inferInstance] g := by
  obtain ⟨i₀, hi₀⟩ := hs
  classical
  let f : ((i : s) → X) → (ι → X) := fun x i ↦ x (if his : i ∈ s then ⟨i, his⟩ else ⟨i₀, hi₀⟩)
  have hg_eq : g = (g ∘ f) ∘ s.domRestrict := by
    ext x
    refine hg fun i his ↦ ?_
    simp [f, his]
  have hf : Measurable f := by
    classical
    rw [measurable_pi_iff]
    intro i
    by_cases his : i ∈ s <;> simp only [his, ↓reduceDIte, f] <;> fun_prop
  rw [hg_eq]
  exact (hg_meas.comp hf).comp (.of_comap_le le_rfl)

end MeasureTheory
