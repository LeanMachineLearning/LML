/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.IdentDistrib

/-! # Lemmas about `HasLaw`
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {P : Measure Ω}

lemma _root_.AEMeasurable.hasLaw_map {X : Ω → 𝓧} (hX : AEMeasurable X P) :
    HasLaw X (P.map X) P := ⟨hX, rfl⟩

lemma _root_.Measurable.hasLaw_map {X : Ω → 𝓧} (hX : Measurable X) (P : Measure Ω) :
    HasLaw X (P.map X) P := ⟨hX.aemeasurable, rfl⟩

section Cond

variable {ι : Type*} [Countable ι] {mι : MeasurableSpace ι} [MeasurableSingletonClass ι]

/-- Two random variables which are identically distributed conditionally on each atom of a
countable measurable partition are identically distributed. -/
lemma identDistrib_of_forall_identDistrib_cond [IsFiniteMeasure P] {g : Ω → ι}
    (hg : Measurable g) {X Y : Ω → 𝓧} (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ i, IdentDistrib X Y P[|g ⁻¹' {i}] P[|g ⁻¹' {i}]) :
    IdentDistrib X Y P P where
  aemeasurable_fst := hX.aemeasurable
  aemeasurable_snd := hY.aemeasurable
  map_eq := by
    ext s hs
    rw [Measure.map_apply hX hs, Measure.map_apply hY hs]
    have h_union (t : Set Ω) : t = ⋃ i, t ∩ g ⁻¹' {i} := by ext; simp
    have h_disj (t : Set Ω) : Pairwise (Function.onFun Disjoint fun i ↦ t ∩ g ⁻¹' {i}) := by
      intro i j hij
      rw [Function.onFun, Set.disjoint_left]
      rintro x ⟨-, hi⟩ ⟨-, hj⟩
      exact hij ((show g x = i from hi).symm.trans hj)
    rw [h_union (X ⁻¹' s), h_union (Y ⁻¹' s),
      measure_iUnion (h_disj _) fun i ↦ (hs.preimage hX).inter (hg (measurableSet_singleton i)),
      measure_iUnion (h_disj _) fun i ↦ (hs.preimage hY).inter (hg (measurableSet_singleton i))]
    refine tsum_congr fun i ↦ ?_
    rw [Set.inter_comm, ← cond_mul_eq_inter (hg (measurableSet_singleton i)),
      Set.inter_comm _ (g ⁻¹' {i}), ← cond_mul_eq_inter (hg (measurableSet_singleton i)),
      ← Measure.map_apply hX hs, ← Measure.map_apply hY hs, (h i).map_eq]

/-- If a random variable has law `μ` conditionally on each atom of positive probability of a
countable measurable partition, then it has law `μ`. -/
lemma hasLaw_of_forall_hasLaw_cond [IsProbabilityMeasure P] {g : Ω → ι} (hg : Measurable g)
    {X : Ω → 𝓧} (hX : Measurable X) {μ : Measure 𝓧}
    (h : ∀ i, P (g ⁻¹' {i}) ≠ 0 → HasLaw X μ P[|g ⁻¹' {i}]) :
    HasLaw X μ P where
  aemeasurable := hX.aemeasurable
  map_eq := by
    ext s hs
    rw [Measure.map_apply hX hs]
    have h_union : X ⁻¹' s = ⋃ i, X ⁻¹' s ∩ g ⁻¹' {i} := by ext; simp
    have h_disj : Pairwise (Function.onFun Disjoint fun i ↦ X ⁻¹' s ∩ g ⁻¹' {i}) := by
      intro i j hij
      rw [Function.onFun, Set.disjoint_left]
      rintro x ⟨-, hi⟩ ⟨-, hj⟩
      exact hij ((show g x = i from hi).symm.trans hj)
    have h_univ : Set.univ = ⋃ i, g ⁻¹' {i} := by ext; simp
    have h_disj_univ : Pairwise (Function.onFun Disjoint fun i ↦ g ⁻¹' {i}) := by
      intro i j hij
      rw [Function.onFun, Set.disjoint_left]
      exact fun x hi hj ↦ hij ((show g x = i from hi).symm.trans hj)
    calc P (X ⁻¹' s)
    _ = ∑' i, P (X ⁻¹' s ∩ g ⁻¹' {i}) := by
      conv_lhs => rw [h_union]
      exact measure_iUnion h_disj fun i ↦ (hs.preimage hX).inter (hg (measurableSet_singleton i))
    _ = ∑' i, μ s * P (g ⁻¹' {i}) := by
      refine tsum_congr fun i ↦ ?_
      rw [Set.inter_comm, ← cond_mul_eq_inter (hg (measurableSet_singleton i))]
      by_cases hi : P (g ⁻¹' {i}) = 0
      · simp [hi]
      · rw [← Measure.map_apply hX hs, (h i hi).map_eq]
    _ = μ s := by
      rw [ENNReal.tsum_mul_left, ← measure_iUnion h_disj_univ
        fun i ↦ hg (measurableSet_singleton i), ← h_univ, measure_univ, mul_one]

end Cond

section Pi

variable {ι : Type*} {𝓧 : ι → Type*} [∀ i, MeasurableSpace (𝓧 i)]

/-- Let `Y n : Ω → Π i, 𝓧 i` be random variables with law `μ`, indexed by a countably generated
filter `L`. If for every `ω` and `i`, `Y n ω i` is eventually equal to `Y' ω i` along `L`, then `Y'`
also has law `μ`. -/
lemma hasLaw_of_forall_eventually_eq [IsFiniteMeasure P] {κ : Type*} {L : Filter κ} [L.NeBot]
    [L.IsCountablyGenerated] {μ : Measure (Π i, 𝓧 i)} {Y : κ → Ω → Π i, 𝓧 i} {Y' : Ω → Π i, 𝓧 i}
    (hY : ∀ n, Measurable (Y n)) (hY' : AEMeasurable Y' P)
    (h_law : ∀ n, HasLaw (Y n) μ P) (h_lim : ∀ ω i, ∀ᶠ n in L, Y n ω i = Y' ω i) :
    HasLaw Y' μ P where
  aemeasurable := hY'
  map_eq := by
    refine ext_of_generate_finite (measurableCylinders _) generateFrom_measurableCylinders.symm
      isPiSystem_measurableCylinders (fun s hs ↦ ?_) ?_
    · obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).1 hs
      rw [Measure.map_apply_of_aemeasurable hY' (hS.cylinder _)]
      have h_tendsto : Tendsto (fun n ↦ P (Y n ⁻¹' cylinder I S)) L
          (𝓝 (P (Y' ⁻¹' cylinder I S))) := by
        refine tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure L P
          (fun n ↦ (hS.cylinder _).preimage (hY n)) fun ω ↦ ?_
        have h_ev : ∀ᶠ n in L, ∀ i ∈ I, Y n ω i = Y' ω i :=
          (eventually_all_finset I).2 fun i _ ↦ h_lim ω i
        filter_upwards [h_ev] with n hn
        simp only [Set.mem_preimage, mem_cylinder]
        have : I.restrict (Y n ω) = I.restrict (Y' ω) := funext fun i ↦ hn i i.2
        rw [this]
      have h_const : Tendsto (fun n ↦ P (Y n ⁻¹' cylinder I S)) L (𝓝 (μ (cylinder I S))) := by
        have : (fun n ↦ P (Y n ⁻¹' cylinder I S)) = fun _ ↦ μ (cylinder I S) := by
          funext n
          rw [← Measure.map_apply (hY n) (hS.cylinder _), (h_law n).map_eq]
        rw [this]
        exact tendsto_const_nhds
      exact tendsto_nhds_unique h_tendsto h_const
    · obtain ⟨n⟩ := L.nonempty_of_neBot
      rw [Measure.map_apply_of_aemeasurable hY' MeasurableSet.univ, Set.preimage_univ,
        ← (h_law n).map_eq,
        Measure.map_apply (hY n) MeasurableSet.univ, Set.preimage_univ]

end Pi

end ProbabilityTheory
