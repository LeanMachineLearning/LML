/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.Tactic.EqLift.Kernel.Lift
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Probability.Kernel.Category.SFinKer

/-!
# Kernel morphisms

This file defines the transformation between categorical morphisms in `SFinKer` and kernel objects.

## Main declarations

* `fromHom`: transforms a categorical morphism in `SFinKer` to a `Kernel`.
* `hom`: transforms a `Kernel` to a categorical morphism in `SFinKer`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MeasurableEquiv CategoryTheory
open scoped SFinKer CategoryTheory CategoryTheory.MonoidalCategory

namespace ProbabilityTheory.Kernel

variable {X Y T Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace T]
  [MeasurableSpace Z]

section

variable {SX SY ST SZ : SFinKer} {ex : SX ≃ᵐ X} {ey : SY ≃ᵐ Y}

/-- Transform a morphism in `SFinKer` into a kernel. -/
noncomputable def fromHom (κ : SX ⟶ SY) : Kernel X Y := (κ.1.comap ex.symm (by fun_prop)).map ey

instance {κ : SX ⟶ SY} : IsSFiniteKernel (fromHom (ex := ex) (ey := ey) κ) := by
  simp only [fromHom]
  have := κ.2
  infer_instance

/-- Transform a kernel into a morphism in `SFinKer`. -/
noncomputable def hom (κ : Kernel X Y) [IsSFiniteKernel κ] : SX ⟶ SY := by
  refine ⟨(κ.map ey.symm).comap ex (by fun_prop), ?_⟩
  have := κ.2
  infer_instance

lemma hom_apply (κ : Kernel X Y) [IsSFiniteKernel κ] (a : SX) :
    (κ.hom (ex := ex) (ey := ey)).1 a = (κ.map ey.symm) (ex a) := rfl

lemma hom_apply' (κ : Kernel X Y) [IsSFiniteKernel κ] (a : SX) {s : Set SY}
    (hs : MeasurableSet s) :
    (κ.hom (ex := ex) (ey := ey)).1 a s = κ (ex a) (ey '' s) := by
  simp only [hom, coe_comap, Function.comp_apply]
  rw [map_apply' _ ey.symm.measurable _ hs, preimage_symm]

instance {κ : Kernel X Y} [IsDeterministic κ] [IsMarkovKernel κ] :
    Deterministic (hom (ex := ex) (ey := ey) κ) := by
  set κ_hom := hom (ex := ex) (ey := ey) κ
  have : IsDeterministic κ_hom.hom := by
    refine ⟨?_⟩
    ext a s hs
    simp only [hom, κ_hom]
    have := κ.parallelComp_self_comp_copy
    have := DFunLike.congr_fun (x := ex a) this
    have := DFunLike.congr_fun (x := ey.prodCongr ey '' s) this
    rw [comap_parallelComp_comap, map_parallelComp_map, comp_apply', comp_apply',
      copy, deterministic_apply, lintegral_dirac', comap_apply', map_apply', parallelComp_apply',
      lintegral_comap, lintegral_map]
    · rw [comp_apply', comp_apply', copy, deterministic_apply, lintegral_dirac',
        parallelComp_apply'] at this
      · convert this
        all_goals try rfl
        · ext y
          simp [MeasurableEquiv.prodCongr]
          aesop
        · simp only [copy, deterministic_apply]
          rw [Measure.dirac_apply', Measure.dirac_apply']
          · refine Set.indicator_eq_indicator ?_ rfl
            simp [MeasurableEquiv.prodCongr]
            aesop
          · exact (measurableSet_image (ey.prodCongr ey)).mpr hs
          · exact hs
      all_goals try measurability
      · exact Kernel.measurable_coe _ (by measurability)
    all_goals try measurability
    · exact Kernel.measurable_coe _ hs
    · exact Kernel.measurable_coe _ hs
  have : IsMarkovKernel κ_hom.hom :=
    have : IsMarkovKernel (κ.map ey.symm) :=
      IsMarkovKernel.map _ (by fun_prop)
    IsMarkovKernel.comap _ (by fun_prop)
  exact SX.deterministic_deterministic SY κ_hom.hom

end

lemma hom_congr (SX SY : SFinKer) (ex : SX ≃ᵐ X) (ey : SY ≃ᵐ Y)
    (κ η : Kernel X Y) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    κ = η ↔ κ.hom (ex := ex) (ey := ey) = η.hom (ex := ex) (ey := ey) := by
  constructor
  · grind
  · intro h
    ext a s hs
    replace h := DFunLike.congr (x := ex.symm a) (congrArg SFinKer.Hom.hom h) rfl
    replace h := DFunLike.congr (x := ey.symm '' s) h rfl
    rw [hom_apply', hom_apply'] at h
    · simp only [apply_symm_apply] at h
      rwa [image_symm, image_preimage] at h
    · measurability
    · measurability

section

variable (SX SY SZ ST : SFinKer) (ex : SX ≃ᵐ X) (ey : SY ≃ᵐ Y) (ez : SZ ≃ᵐ Z) (et : ST ≃ᵐ T)

lemma comp_hom (η : Kernel X Y) (κ : Kernel Z X) [IsSFiniteKernel η] [IsSFiniteKernel κ] :
    κ.hom (ex := ez) (ey := ex) ≫ η.hom (ex := ex) (ey := ey) =
      (η ∘ₖ κ).hom (ex := ez) (ey := ey) := by
  ext a s hs
  dsimp
  rw [hom_apply', comp_apply', comp_apply', hom_apply, lintegral_map]
  · congr with y
    simp [hom_apply' _ _ hs]
  all_goals try fun_prop
  all_goals try measurability
  · exact Kernel.measurable_coe η.hom.hom hs

lemma parallelComp_hom (κ : Kernel X Y) (η : Kernel Z T) [IsSFiniteKernel η] [IsSFiniteKernel κ] :
    κ.hom (ex := ex) (ey := ey) ⊗ₘ η.hom (ex := ez) (ey := et) =
      hom (ex := ex.prodCongr ez) (ey := ey.prodCongr et) (κ ∥ₖ η) := by
  ext : 1; dsimp
  simp only [hom]
  rw [id_parallelComp_comp_parallelComp_id, comap_parallelComp_comap, map_parallelComp_map]
  · rfl
  all_goals fun_prop

lemma id_hom : 𝟙 SX = Kernel.id.hom (ex := ex) (ey := ex) := by
  ext; dsimp
  rw [hom_apply', id_apply, id_apply, Measure.dirac_apply', Measure.dirac_apply']
  · exact Set.indicator_eq_indicator (by simp) rfl
  all_goals measurability

lemma whiskerLeft (κ : Kernel X Y) [IsSFiniteKernel κ] : SZ ◁ κ.hom (ex := ex) (ey := ey) =
      (Kernel.id (α := Z) ∥ₖ κ).hom (ex := ez.prodCongr ex) (ey := ez.prodCongr ey) := by
  ext _ _ hs; dsimp
  simp only [hom]
  rw [parallelComp_apply, comap_apply, map_apply, id_apply,
    comap_apply, map_apply, parallelComp_apply, id_apply]
  · simp only [Measure.dirac_prod, MeasurableEquiv.prodCongr]
    rw [Measure.map_map, Measure.map_map, Measure.map_apply, Measure.map_apply]
    · congr 3
      simp
    all_goals try fun_prop
    all_goals exact hs
  all_goals fun_prop

lemma whiskerRight (κ : Kernel X Y) [IsSFiniteKernel κ] :
    κ.hom (ex := ex) (ey := ey) ▷ SZ =
      (κ ∥ₖ Kernel.id (α := Z)).hom (ex := ex.prodCongr ez) (ey := ey.prodCongr ez) := by
  ext _ _ hs; dsimp
  simp only [hom]
  rw [parallelComp_apply, comap_apply, map_apply, id_apply, comap_apply, map_apply,
    parallelComp_apply, id_apply]
  · simp only [Measure.prod_dirac, MeasurableEquiv.prodCongr]
    rw [Measure.map_map, Measure.map_map, Measure.map_apply, Measure.map_apply]
    · congr with y
      · simp
      · simp
    all_goals try fun_prop
    all_goals exact hs
  all_goals fun_prop

open scoped ComonObj

lemma counit : ε[SX] = (Kernel.discard X).hom (ex := ex) (ey := punit) := by
  ext : 1; dsimp
  simp only [hom, discard]
  rw [deterministic_map (by fun_prop) (by fun_prop)]
  rfl

lemma comul : Δ[SX] = (Kernel.copy X).hom (ex := ex) (ey := ex.prodCongr ex) := by
  ext : 1; dsimp
  simp only [hom, copy]
  rw [deterministic_map (by fun_prop) (by fun_prop)]
  congr with x
  all_goals simp [MeasurableEquiv.prodCongr]

lemma braiding_hom : (β_ SX SY).hom =
    (Kernel.swap X Y).hom (ex := ex.prodCongr ey) (ey := ey.prodCongr ex) := by
  ext : 1; dsimp
  simp only [hom, swap]
  rw [deterministic_map (by fun_prop) (by fun_prop)]
  congr with x
  all_goals simp [MeasurableEquiv.prodCongr]

variable {X₀ Y₀ Z₀ : Type*} [MeasurableSpace X₀] [MeasurableSpace Y₀] [MeasurableSpace Z₀]
    (ex₀ : X ≃ᵐ X₀) (ey₀ : Y ≃ᵐ Y₀) (ez₀ : Z ≃ᵐ Z₀)

lemma leftUnitor_hom : (λ_ SX).hom = hom (ex := punit.prodCongr ex) (ey := ex)
    (lift (Kernel.id.map (Prod.snd : PUnit × X₀ → X₀))
      (ex := punit.prodCongr ex₀) (ey := ex₀)) := by
  ext; dsimp
  rw [hom_apply', lift_apply', id_map (by fun_prop), id_map (by fun_prop), deterministic_apply',
    deterministic_apply', Set.image]
  · refine Set.indicator_eq_indicator ?_ rfl
    simp [MeasurableEquiv.prodCongr]
  all_goals measurability

lemma leftUnitor_inv : (λ_ SX).inv = hom (ex := ex) (ey := punit.prodCongr ex)
    (lift (Kernel.id.map (fun x ↦ (PUnit.unit, x))) (ex := ex₀) (ey := punit.prodCongr ex₀)) := by
  ext; dsimp
  rw [hom_apply', lift_apply', id_map (by fun_prop), id_map (by fun_prop), deterministic_apply',
    deterministic_apply']
  · refine Set.indicator_eq_indicator ?_ rfl
    simp [Set.image, MeasurableEquiv.prodCongr]
    constructor
    all_goals simp_all
  all_goals measurability

lemma rightUnitor_hom : (ρ_ SX).hom = hom (ex := ex.prodCongr punit) (ey := ex)
    (lift (Kernel.id.map (Prod.fst : X₀ × PUnit → X₀))
      (ex := ex₀.prodCongr punit) (ey := ex₀)) := by
  ext; dsimp
  rw [hom_apply', lift_apply', id_map (by fun_prop), id_map (by fun_prop), deterministic_apply',
    deterministic_apply']
  · refine Set.indicator_eq_indicator ?_ rfl
    simp [MeasurableEquiv.prodCongr]
  all_goals measurability

lemma rightUnitor_inv : (ρ_ SX).inv = hom (ex := ex) (ey := ex.prodCongr punit)
    (lift (Kernel.id.map (fun x ↦ (x, PUnit.unit))) (ex := ex₀) (ey := ex₀.prodCongr punit)) := by
  ext; dsimp
  rw [hom_apply', lift_apply', id_map (by fun_prop), id_map (by fun_prop), deterministic_apply',
    deterministic_apply']
  · refine Set.indicator_eq_indicator ?_ rfl
    simp [Set.image, MeasurableEquiv.prodCongr]
    constructor
    all_goals simp_all
  all_goals measurability

lemma associator_hom : (α_ SX SY SZ).hom =
    hom (ex := (ex.prodCongr ey).prodCongr ez) (ey := ex.prodCongr (ey.prodCongr ez))
      (lift (Kernel.deterministic prodAssoc (by fun_prop))
        (ex := (ex₀.prodCongr ey₀).prodCongr ez₀) (ey := ex₀.prodCongr (ey₀.prodCongr ez₀))) := by
  ext; dsimp
  simp only [hom]
  rw [comap_apply', map_apply', lift_apply', deterministic_apply', deterministic_apply']
  · refine Set.indicator_eq_indicator ?_ rfl
    simp [MeasurableEquiv.prodCongr, prodAssoc]
  all_goals measurability

lemma associator_inv : (α_ SX SY SZ).inv =
    hom (ex := ex.prodCongr (ey.prodCongr ez)) (ey := (ex.prodCongr ey).prodCongr ez)
      (lift (Kernel.deterministic prodAssoc.symm (by fun_prop))
        (ex := ex₀.prodCongr (ey₀.prodCongr ez₀)) (ey := (ex₀.prodCongr ey₀).prodCongr ez₀)) := by
  ext; dsimp
  simp only [hom]
  rw [comap_apply', map_apply', lift_apply', deterministic_apply', deterministic_apply']
  · refine Set.indicator_eq_indicator ?_ rfl
    simp [MeasurableEquiv.prodCongr, prodAssoc]
  all_goals measurability

end

end ProbabilityTheory.Kernel
