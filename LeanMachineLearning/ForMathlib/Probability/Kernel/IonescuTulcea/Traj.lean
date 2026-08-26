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

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
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
lemma hasLaw_trajMeasure [IsFiniteMeasure P]
    {Y : (n : ℕ) → Ω → X n} (hY_meas : ∀ n, Measurable (Y n))
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

section Fin

/-- Measurable equivalence between `Π i : Fin (n + 1), X i` and `Π i : Iic n, X i`. -/
def _root_.MeasurableEquiv.finSuccPiIic (X : ℕ → Type*) [∀ n, MeasurableSpace (X n)] (n : ℕ) :
    (Π i : Fin (n + 1), X i) ≃ᵐ (Π i : Iic n, X i) where
  toFun h i := h ⟨i.1, Nat.lt_succ_of_le (mem_Iic.mp i.2)⟩
  invFun h i := h ⟨i.1, mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

@[simp]
lemma _root_.MeasurableEquiv.finSuccPiIic_apply (n : ℕ) (h : Π i : Fin (n + 1), X i) (i : Iic n) :
    MeasurableEquiv.finSuccPiIic X n h i = h ⟨i.1, Nat.lt_succ_of_le (mem_Iic.mp i.2)⟩ := rfl

@[simp]
lemma _root_.MeasurableEquiv.finSuccPiIic_symm_apply (n : ℕ) (h : Π i : Iic n, X i)
    (i : Fin (n + 1)) :
    (MeasurableEquiv.finSuccPiIic X n).symm h i = h ⟨i.1, mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩ :=
  rfl

lemma _root_.MeasurableEquiv.finSuccPiIic_symm_comp_frestrictLe (n : ℕ) :
    (MeasurableEquiv.finSuccPiIic X n).symm ∘ frestrictLe n = fun x (i : Fin (n + 1)) ↦ x i := rfl

/-- Measurable equivalence between `Fin (n + 1) → X` and `(Fin n → X) × X`. -/
def _root_.MeasurableEquiv.finSuccProd (X : Type*) [MeasurableSpace X] (n : ℕ) :
    (Fin (n + 1) → X) ≃ᵐ (Fin n → X) × X :=
  (MeasurableEquiv.piFinSuccAbove (fun _ ↦ X) (Fin.last n)).trans MeasurableEquiv.prodComm

@[simp]
lemma _root_.MeasurableEquiv.finSuccProd_apply {X : Type*} [MeasurableSpace X] (n : ℕ)
    (h : Fin (n + 1) → X) :
    MeasurableEquiv.finSuccProd X n h = (fun i ↦ h i.castSucc, h (Fin.last n)) := by
  simp [MeasurableEquiv.finSuccProd]
  rfl

@[simp]
lemma _root_.MeasurableEquiv.finSuccProd_symm_apply {X : Type*} [MeasurableSpace X] (n : ℕ)
    (p : (Fin n → X) × X) :
    (MeasurableEquiv.finSuccProd X n).symm p = Fin.snoc p.1 p.2 := by
  simp [MeasurableEquiv.finSuccProd]
  rfl

end Fin

section FinTraj

variable {κ' : (n : ℕ) → Kernel (Π i : Fin n, X i) (X n)} [∀ n, IsMarkovKernel (κ' n)]

lemma comap_comap_symm {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} (κ : Kernel α γ) (e : β ≃ᵐ α) :
    (κ.comap e e.measurable).comap e.symm e.symm.measurable = κ := by
  ext a : 1
  simp [Kernel.comap_apply]

/-- Kernels indexed by `Iic n` (as needed for `Kernel.traj`), obtained from kernels indexed by
`Fin n`: the kernel `κ' (n + 1)` on `Π i : Fin (n + 1), X i` is seen as a kernel on
`Π i : Iic n, X i`. -/
noncomputable
def iicOfFin (κ' : (n : ℕ) → Kernel (Π i : Fin n, X i) (X n)) (n : ℕ) :
    Kernel (Π i : Iic n, X i) (X (n + 1)) :=
  (κ' (n + 1)).comap (MeasurableEquiv.finSuccPiIic X n).symm (by fun_prop)

instance (n : ℕ) : IsMarkovKernel (iicOfFin κ' n) := by unfold iicOfFin; infer_instance

omit [∀ n, IsMarkovKernel (κ' n)] in
lemma comap_iicOfFin (n : ℕ) :
    (iicOfFin κ' n).comap (MeasurableEquiv.finSuccPiIic X n) (by fun_prop) = κ' (n + 1) :=
  comap_comap_symm _ (MeasurableEquiv.finSuccPiIic X n).symm

/-- Measure on trajectories `Π n, X n` built from kernels `κ' n : Kernel (Π i : Fin n, X i) (X n)`
describing the law of the coordinate `n` given the `n` previous coordinates.
The initial measure is `κ' 0 default`. -/
noncomputable
def trajMeasureFin (κ' : (n : ℕ) → Kernel (Π i : Fin n, X i) (X n)) [∀ n, IsMarkovKernel (κ' n)] :
    Measure (Π n, X n) :=
  trajMeasure (κ' 0 default) (iicOfFin κ')
deriving IsProbabilityMeasure

lemma trajMeasureFin_def :
    trajMeasureFin κ' = trajMeasure (κ' 0 default) (iicOfFin κ') := rfl

omit [IsProbabilityMeasure μ₀] in
lemma hasLaw_eval_zero_trajMeasure : HasLaw (fun x ↦ x 0) μ₀ (trajMeasure μ₀ κ) where
  aemeasurable := (measurable_pi_apply 0).aemeasurable
  map_eq := by
    have h := trajMeasure_map_frestrictLe (κ := κ) (μ₀ := μ₀) 0
    rw [partialTraj_self, Measure.id_comp] at h
    have h2 := congrArg (Measure.map (MeasurableEquiv.piUnique (fun i : Iic 0 ↦ X i))) h
    rw [Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop)] at h2
    exact h2.trans (MeasurableEquiv.map_map_symm _)

lemma hasLaw_eval_zero_trajMeasureFin :
    HasLaw (fun x ↦ x 0) (κ' 0 default) (trajMeasureFin κ') :=
  hasLaw_eval_zero_trajMeasure

lemma hasCondDistrib_trajMeasureFin (n : ℕ) :
    HasCondDistrib (fun x ↦ x n) (fun x (i : Fin n) ↦ x i) (κ' n) (trajMeasureFin κ') := by
  cases n with
  | zero =>
    rw [show (fun (x : Π n, X n) (i : Fin 0) ↦ x i) = fun _ ↦ default from
      funext fun _ ↦ Unique.eq_default _]
    exact hasLaw_eval_zero_trajMeasureFin.hasCondDistrib_const
  | succ n =>
    have h : HasCondDistrib (fun x ↦ x (n + 1)) (frestrictLe n) (iicOfFin κ' n)
        (trajMeasureFin κ') :=
      ⟨by fun_prop, map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm⟩
    have h' := h.measurableEquiv_comp_right (MeasurableEquiv.finSuccPiIic X n).symm
    rwa [MeasurableEquiv.symm_symm, comap_iicOfFin,
      MeasurableEquiv.finSuccPiIic_symm_comp_frestrictLe] at h'

/-- Uniqueness of `trajMeasureFin`. -/
lemma hasLaw_trajMeasureFin [IsProbabilityMeasure P]
    {Y : (n : ℕ) → Ω → X n} (hY_meas : ∀ n, Measurable (Y n))
    (h_condDistrib : ∀ n, HasCondDistrib (Y n) (fun ω (i : Fin n) ↦ Y i ω) (κ' n) P) :
    HasLaw (fun ω n ↦ Y n ω) (trajMeasureFin κ') P := by
  unfold trajMeasureFin
  refine hasLaw_trajMeasure hY_meas ?_ fun n ↦ ?_
  · have h := h_condDistrib 0
    rw [show (fun ω (i : Fin 0) ↦ Y i ω) = fun _ ↦ default from
      funext fun _ ↦ Unique.eq_default _] at h
    exact h.hasLaw_of_const'
  · exact (h_condDistrib (n + 1)).measurableEquiv_comp_right (MeasurableEquiv.finSuccPiIic X n)

lemma eq_trajMeasureFin_map [IsProbabilityMeasure P]
    {Y : (n : ℕ) → Ω → X n} (hY_meas : ∀ n, Measurable (Y n)) {N : ℕ}
    (h_condDistrib : ∀ n < N, HasCondDistrib (Y n) (fun ω (i : Fin n) ↦ Y i ω) (κ' n) P) :
    P.map (fun ω (i : Fin N) ↦ Y i ω) = (trajMeasureFin κ').map (fun x (i : Fin N) ↦ x i) := by
  cases N with
  | zero =>
    rw [show (fun ω (i : Fin 0) ↦ Y i ω) = fun _ ↦ default from
      funext fun _ ↦ Unique.eq_default _,
      show (fun (x : Π n, X n) (i : Fin 0) ↦ x i) = fun _ ↦ default from
      funext fun _ ↦ Unique.eq_default _,
      Measure.map_const, Measure.map_const, measure_univ, measure_univ]
  | succ N =>
    have h0 : HasLaw (Y 0) (κ' 0 default) P := by
      have h := h_condDistrib 0 (by omega)
      rw [show (fun ω (i : Fin 0) ↦ Y i ω) = fun _ ↦ default from
        funext fun _ ↦ Unique.eq_default _] at h
      exact h.hasLaw_of_const'
    have h := eq_trajMeasure_map_frestrictLe (κ := iicOfFin κ') h0 (N := N) fun n hn ↦
      (h_condDistrib (n + 1) (by omega)).measurableEquiv_comp_right
        (MeasurableEquiv.finSuccPiIic X n)
    have h1 : (fun ω (i : Fin (N + 1)) ↦ Y i ω) =
        (MeasurableEquiv.finSuccPiIic X N).symm ∘ (fun ω (n : Iic N) ↦ Y n ω) := rfl
    rw [h1, ← Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop), h, trajMeasureFin_def,
      Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop),
      MeasurableEquiv.finSuccPiIic_symm_comp_frestrictLe]

end FinTraj

end ProbabilityTheory.Kernel
