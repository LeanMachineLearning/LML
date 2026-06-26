/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Deterministic
public import LeanMachineLearning.SequentialLearning.FiniteActions
public import LeanMachineLearning.SequentialLearning.StationaryEnv

/-! # Round-Robin algorithm

That algorithm chooses each of finitely many actions in a round-robin fashion.
That is, if there are `K` actions numbered from 0 to `K - 1`, then at time `n` it chooses
he action `n % K`.

## Main definitions

* `roundRobinAlgorithm`: the Round-Robin algorithm.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning
open scoped ENNReal NNReal

section Aux

lemma sum_mod_range {K : ℕ} (hK : 0 < K) (a : Fin K) :
    (∑ s ∈ range K, if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) = 1 := by
  have h_iff (s : ℕ) (hs : s < K) : ⟨s % K, Nat.mod_lt _ hK⟩ = a ↔ s = a := by
    simp only [Nat.mod_eq_of_lt hs, Fin.ext_iff]
  calc (∑ s ∈ range K, if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0)
  _ = ∑ s ∈ range K, if s = a then 1 else 0 := sum_congr rfl fun s hs ↦ by grind
  _ = _ := by
    rw [sum_ite_eq']
    simp

lemma sum_mod_range_mul {K : ℕ} (hK : 0 < K) (m : ℕ) (a : Fin K) :
    (∑ s ∈ range (K * m), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) = m := by
  induction m with
  | zero => simp
  | succ n hn =>
    calc (∑ s ∈ range (K * (n + 1)), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0)
    _ = (∑ s ∈ range (K * n + K), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) := by ring_nf
    _ = (∑ s ∈ range (K * n), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0)
        + (∑ s ∈ Ico (K * n) (K * n + K), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) := by
      rw [sum_range_add_sum_Ico]
      grind
    _ = n + (∑ s ∈ Ico (K * n) (K * n + K), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) := by
      rw [hn]
    _ = n + (∑ s ∈ range K, if ⟨(s + K * n) % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) := by
      congr 1
      let e : ℕ ↪ ℕ := ⟨fun i : ℕ ↦ i + K * n, fun i j hij ↦ by grind⟩
      have : Finset.map e (range K) = Ico (K * n) (K * n + K) := by
        ext x
        simp only [mem_map, mem_range, Function.Embedding.coeFn_mk, mem_Ico, e]
        refine ⟨fun h ↦ by grind, fun h ↦ ?_⟩
        use x - K * n
        grind
      rw [← this, Finset.sum_map]
      congr
    _ = n + (∑ s ∈ range K, if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) := by simp
    _ = n + 1 := by rw [sum_mod_range hK]

end Aux

namespace Learning

variable {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} {K : ℕ}

section AlgorithmDefinition

/-- Action chosen by the Round-Robin algorithm at time `n + 1`. This is action `(n + 1) % K`. -/
noncomputable
def RoundRobin.nextAction (hK : 0 < K) (n : ℕ) : Fin K := ⟨(n + 1) % K, Nat.mod_lt _ hK⟩

/-- The Round-Robin algorithm: deterministic algorithm that chooses action `n % K` at time `n`. -/
noncomputable
def roundRobinAlgorithm (hK : 0 < K) : Algorithm (Fin K) 𝓨 :=
  detAlgorithm (fun n _ ↦ RoundRobin.nextAction hK n) (by fun_prop) ⟨0, hK⟩

end AlgorithmDefinition

namespace RoundRobin

variable {hK : 0 < K} {ν : Kernel (Fin K) 𝓨} [IsMarkovKernel ν]
  {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → Fin K} {Y : ℕ → Ω → 𝓨}

lemma action_zero
    (h : IsAlgEnvSeqUntil A Y (roundRobinAlgorithm hK) (stationaryEnv ν) P 0) :
    A 0 =ᵐ[P] fun _ ↦ ⟨0, hK⟩ := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact h.action_zero_detAlgorithm

lemma action_ae_eq_roundRobinNextAction (n : ℕ)
    (h : IsAlgEnvSeqUntil A Y (roundRobinAlgorithm hK) (stationaryEnv ν) P (n + 1)) :
    A (n + 1) =ᵐ[P] fun _ ↦ nextAction hK n :=
  h.action_detAlgorithm_ae_eq (by grind)

/-- The action chosen at time `n` is the action `n % K`. -/
lemma action_ae_eq (n : ℕ)
    (h : IsAlgEnvSeqUntil A Y (roundRobinAlgorithm hK) (stationaryEnv ν) P n) :
    A n =ᵐ[P] fun _ ↦ ⟨n % K, Nat.mod_lt _ hK⟩ := by
  cases n with
  | zero => exact action_zero h
  | succ n =>
    filter_upwards [action_ae_eq_roundRobinNextAction n h] with h hn_eq
    rw [hn_eq, nextAction]

/-- At time `K * m`, the number of times each action is chosen is equal to `m`. -/
lemma pullCount_mul (m : ℕ)
    (h : IsAlgEnvSeqUntil A Y (roundRobinAlgorithm hK) (stationaryEnv ν) P (K * m - 1))
    (a : Fin K) :
    pullCount A a (K * m) =ᵐ[P] fun _ ↦ m := by
  rw [Filter.EventuallyEq]
  simp_rw [pullCount_eq_sum]
  have h_arm (n : range (K * m)) : A n =ᵐ[P] fun _ ↦ ⟨n % K, Nat.mod_lt _ hK⟩ :=
    action_ae_eq n (h.mono (by have := n.2; simp only [mem_range] at this; grind))
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at h_arm
  filter_upwards [h_arm] with ω h_arm
  have h_arm' {i : ℕ} (hi : i ∈ range (K * m)) : A i ω = ⟨i % K, Nat.mod_lt _ hK⟩ := h_arm ⟨i, hi⟩
  calc (∑ s ∈ range (K * m), if A s ω = a then 1 else 0)
  _ = (∑ s ∈ range (K * m), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) :=
    sum_congr rfl fun s hs ↦ by rw [h_arm' hs]
  _ = m := sum_mod_range_mul hK m a

lemma pullCount_eq_one
    (h : IsAlgEnvSeqUntil A Y (roundRobinAlgorithm hK) (stationaryEnv ν) P (K - 1)) (a : Fin K) :
    pullCount A a K =ᵐ[P] fun _ ↦ 1 := by
  suffices pullCount A a (K * 1) =ᵐ[P] fun _ ↦ 1 by simpa using this
  refine pullCount_mul 1 (P := P) (ν := ν) (Y := Y) (hK := hK) ?_ a
  simpa

lemma time_gt_of_pullCount_gt_one
    (h : IsAlgEnvSeqUntil A Y (roundRobinAlgorithm hK) (stationaryEnv ν) P (K - 1)) (a : Fin K) :
    ∀ᵐ ω ∂P, ∀ n, 1 < pullCount A a n ω → K < n := by
  filter_upwards [pullCount_eq_one h a] with h h_eq n hn
  rw [← h_eq] at hn
  by_contra! h_lt
  exact hn.not_ge (pullCount_mono _ h_lt _)

lemma pullCount_pos_of_time_ge
    (h : IsAlgEnvSeqUntil A Y (roundRobinAlgorithm hK) (stationaryEnv ν) P (K - 1)) :
    ∀ᵐ ω ∂P, ∀ n, K ≤ n → ∀ b : Fin K, 0 < pullCount A b n ω := by
  have h_ae a := pullCount_eq_one h a
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at h_ae
  filter_upwards [h_ae] with ω hω n hn a
  refine Nat.one_pos.trans_le ?_
  rw [← hω a]
  exact pullCount_mono _ hn _

lemma pullCount_pos_of_pullCount_gt_one
    (h : IsAlgEnvSeqUntil A Y (roundRobinAlgorithm hK) (stationaryEnv ν) P (K - 1)) (a : Fin K) :
    ∀ᵐ ω ∂P, ∀ n, 1 < pullCount A a n ω → ∀ b : Fin K, 0 < pullCount A b n ω := by
  filter_upwards [time_gt_of_pullCount_gt_one h a, pullCount_pos_of_time_ge h] with ω h1 h2 n h_gt a
  exact h2 n (h1 n h_gt).le a

end RoundRobin

end Learning
