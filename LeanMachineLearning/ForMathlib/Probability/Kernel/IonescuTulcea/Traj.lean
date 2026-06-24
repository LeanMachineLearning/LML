/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
module

public import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! # Lemmas about `traj` and `trajMeasure`
-/

@[expose] public section

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]
  {μ₀ : Measure (X 0)} [IsProbabilityMeasure μ₀]

section MeasurableEquiv

lemma coe_default_Iic_zero : ((default : Iic 0) : ℕ) = 0 := rfl

end MeasurableEquiv

namespace ProbabilityTheory.Kernel

lemma traj_zero_map_eval_zero :
    (Kernel.traj κ 0).map (fun h ↦ h (default : Iic 0))
      = Kernel.deterministic (MeasurableEquiv.piUnique (fun i : Iic 0 ↦ X i))
        (MeasurableEquiv.piUnique _).measurable := by
  suffices (Kernel.traj κ 0).map (fun h ↦ h (default : Iic 0))
      = (Kernel.partialTraj κ 0 0).map (MeasurableEquiv.piUnique (fun i : Iic 0 ↦ X i)) by
    rwa [Kernel.partialTraj_zero, Kernel.deterministic_map] at this
    fun_prop
  rw [← Kernel.traj_map_frestrictLe, ← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
  rfl

/-- Measurable equivalence between a product up to `n + 1` and the pair of the product up to `n` and
the space at `n + 1`. -/
def _root_.MeasurableEquiv.IicSuccProd (X : ℕ → Type*) [∀ n, MeasurableSpace (X n)] (n : ℕ) :
    MeasurableEquiv (Π i : Iic (n + 1), X i) ((Π i : Iic n, X i) × X (n + 1)) :=
  (MeasurableEquiv.IicProdIoc (Nat.le_succ n)).symm.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.piSingleton n).symm)

lemma symm_IicSuccProd (n : ℕ) :
    (MeasurableEquiv.IicSuccProd X n).symm =
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.piSingleton n)).trans
        (MeasurableEquiv.IicProdIoc (Nat.le_succ n)) := rfl

@[simp]
lemma MeasurableEquiv.IicSuccProd_apply (n : ℕ) (h : Π i : Iic (n + 1), X i) :
    MeasurableEquiv.IicSuccProd X n h = (fun i : Iic n ↦ h ⟨i.1, by grind⟩, h ⟨n + 1, by simp⟩) :=
  rfl

lemma MeasurableEquiv.coe_prodCongr {α β γ δ : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
    (e₁ : MeasurableEquiv α β) (e₂ : MeasurableEquiv γ δ) :
    (MeasurableEquiv.prodCongr e₁ e₂ : (α × γ) → (β × δ)) = Prod.map e₁ e₂ := rfl

lemma MeasurableEquiv.coe_refl {α : Type*} {mα : MeasurableSpace α} :
    (MeasurableEquiv.refl α : α → α) = id := rfl

set_option backward.isDefEq.respectTransparency false in
lemma hasLaw_Iic_of_forall_hasCondDistrib'
    {Y : (n : ℕ) → Ω → X n} (h0 : HasLaw (Y 0) μ₀ P) {N n : ℕ}
    (h_condDistrib : ∀ n < N, HasCondDistrib (Y (n + 1)) (fun ω ↦ fun i : Iic n ↦ Y i ω) (κ n) P)
    (hn : n ≤ N) :
    HasLaw (fun ω (i : Iic n) ↦ Y i ω)
      ((partialTraj κ 0 n) ∘ₘ (μ₀.map (MeasurableEquiv.piUnique _).symm)) P := by
  revert hn
  induction n with
  | zero =>
    intro _
    simp only [piUnique_symm_apply, partialTraj_self, Measure.id_comp]
    rw [← h0.map_eq, AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    constructor
    · have h_meas := h0.aemeasurable
      have : (fun ω (i : Iic 0) ↦ Y i ω) = (MeasurableEquiv.piUnique _).symm ∘ (Y 0) := by
        ext ω i
        simp only [piUnique_symm_apply, Function.comp_apply]
        rw [Unique.eq_default i]
        simp [coe_default_Iic_zero]
      rw [this]
      exact AEMeasurable.comp_aemeasurable (by fun_prop) h_meas
    · congr
      ext ω i
      simp only [Function.comp_apply]
      rw [Unique.eq_default i]
      simp [coe_default_Iic_zero]
  | succ n hn =>
    intro hn_le
    specialize h_condDistrib n (by grind)
    specialize hn (by grind)
    have h_law := hn.prod_of_hasCondDistrib h_condDistrib
    have : (fun ω (i : Iic (n + 1)) ↦ Y i ω) =
        (MeasurableEquiv.IicSuccProd X n).symm ∘
          (fun ω ↦ (fun i : Iic n ↦ Y i ω, Y (n + 1) ω)) := by
      suffices (MeasurableEquiv.IicSuccProd X n) ∘ (fun ω (i : Iic (n + 1)) ↦ Y i ω) =
          (fun ω ↦ (fun i : Iic n ↦ Y i ω, Y (n + 1) ω)) by
        rw [← this, ← Function.comp_assoc, MeasurableEquiv.symm_comp_self]
        simp
      ext ω : 1
      simp
    rw [this]
    refine HasLaw.comp ⟨by fun_prop, ?_⟩ h_law
    rw [Measure.compProd_eq_comp_prod, partialTraj_succ_eq_comp (by simp), Measure.comp_assoc,
      ← Measure.deterministic_comp_eq_map (by fun_prop), Measure.comp_assoc]
    congr 1
    rw [← Kernel.comp_assoc]
    congr
    rw [Kernel.deterministic_comp_eq_map, partialTraj_succ_self, symm_IicSuccProd]
    rw [MeasurableEquiv.coe_trans, MeasurableEquiv.coe_prodCongr]
    rw [Kernel.map_comp_right _ (by fun_prop) (by fun_prop),
      ← Kernel.map_prod_map _ _ (by fun_prop) (by fun_prop)]
    congr
    simp [MeasurableEquiv.coe_refl]

lemma hasLaw_Iic_of_forall_hasCondDistrib {Y : (n : ℕ) → Ω → X n} (h0 : HasLaw (Y 0) μ₀ P)
    (h_condDistrib : ∀ n, HasCondDistrib (Y (n + 1)) (fun ω ↦ fun i : Iic n ↦ Y i ω) (κ n) P)
    (n : ℕ) :
    HasLaw (fun ω (i : Iic n) ↦ Y i ω)
      ((partialTraj κ 0 n) ∘ₘ (μ₀.map (MeasurableEquiv.piUnique _).symm)) P := by
  exact hasLaw_Iic_of_forall_hasCondDistrib' (N := n) h0 (fun n _ ↦ h_condDistrib n) le_rfl

omit [IsProbabilityMeasure μ₀] in
lemma trajMeasure_map_frestrictLe (n : ℕ) :
    (trajMeasure μ₀ κ).map (frestrictLe n) =
      (partialTraj κ 0 n) ∘ₘ (μ₀.map (MeasurableEquiv.piUnique _).symm) := by
  rw [trajMeasure, ← Measure.deterministic_comp_eq_map (by fun_prop), Measure.comp_assoc,
    Kernel.deterministic_comp_eq_map, traj_map_frestrictLe]

lemma eq_trajMeasure_map_frestrictLe {Y : (n : ℕ) → Ω → X n} (h0 : HasLaw (Y 0) μ₀ P) {N : ℕ}
    (h_condDistrib : ∀ n < N, HasCondDistrib (Y (n + 1)) (fun ω ↦ fun i : Iic n ↦ Y i ω) (κ n) P) :
    P.map (fun ω (n : Iic N) ↦ Y n ω) = (trajMeasure μ₀ κ).map (frestrictLe N) := by
  rw [(hasLaw_Iic_of_forall_hasCondDistrib' h0 h_condDistrib le_rfl).map_eq,
    trajMeasure_map_frestrictLe]

/-- Uniqueness of `trajMeasure`. -/
lemma hasLaw_trajMeasure {Y : (n : ℕ) → Ω → X n} (hY_meas : ∀ n, Measurable (Y n))
    (h0 : HasLaw (Y 0) μ₀ P)
    (h_condDistrib : ∀ n, HasCondDistrib (Y (n + 1)) (fun ω ↦ fun i : Iic n ↦ Y i ω) (κ n) P) :
    HasLaw (fun ω n ↦ Y n ω) (trajMeasure μ₀ κ) P where
  aemeasurable := by fun_prop
  map_eq := by
    refine IsProjectiveLimit.unique (P := fun (J : Finset ℕ) ↦ P.map (fun ω (i : J) ↦ Y i ω)) ?_ ?_
    · exact isProjectiveLimit_map (by fun_prop)
    rw [isProjectiveLimit_nat_iff]
    swap; · exact isProjectiveMeasureFamily_map_restrict (by fun_prop)
    intro n
    rw [(hasLaw_Iic_of_forall_hasCondDistrib h0 h_condDistrib n).map_eq,
      trajMeasure_map_frestrictLe]

end ProbabilityTheory.Kernel
