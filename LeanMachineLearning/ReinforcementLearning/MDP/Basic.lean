/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
public import LeanMachineLearning.SequentialLearning.Deterministic

/-!
# Markov decision processes

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning

/-- Markov decision process with state space `𝓢`, action space `𝓐`, and reward space `𝓡`, described
by a transition kernel `P : Kernel (𝓢 × 𝓐) 𝓢` and a reward kernel `R : Kernel (𝓢 × 𝓐) 𝓡`.
See `MDP.env` for the environment associated with the MDP. -/
structure MDP (𝓢 𝓐 𝓡 : Type*) [MeasurableSpace 𝓢] [MeasurableSpace 𝓐] [MeasurableSpace 𝓡] where
  P : Kernel (𝓢 × 𝓐) 𝓢
  [hP : IsMarkovKernel P]
  R : Kernel (𝓢 × 𝓐) 𝓡
  [hR : IsMarkovKernel R]

namespace Learning.MDP

variable {𝓢 𝓐 𝓡 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} {m𝓡 : MeasurableSpace 𝓡}

instance (M : MDP 𝓢 𝓐 𝓡) : IsMarkovKernel M.P := M.hP
instance (M : MDP 𝓢 𝓐 𝓡) : IsMarkovKernel M.R := M.hR

/-! ### The environment -/

open Classical in
protected noncomputable def env [h𝓢 : Nonempty 𝓢] (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) :
    Environment 𝓢 𝓐 𝓡 where
      obs
      | 0 => Kernel.const _ (if IsProbabilityMeasure μ₀ then μ₀ else Measure.dirac h𝓢.some)
      | n + 1 => M.P.comap (fun h ↦ ((h (Fin.last n)).obs, (h (Fin.last n)).action)) (by fun_prop)
      feedback := fun _ ↦ M.R.comap (fun p ↦ (p.1.2, p.2)) (by fun_prop)
      isMarkovKernel_obs n := by
        cases n
        · split_ifs <;> infer_instance
        · infer_instance

lemma measurable_env [Nonempty 𝓢] (M : MDP 𝓢 𝓐 𝓡) : Measurable M.env := by
  rw [measurable_environment_iff]
  refine fun n ↦ ⟨?_, by fun_prop⟩
  cases n with
  | zero =>
    refine Kernel.measurable_const.comp ?_
    exact Measurable.ite ProbabilityMeasure.measurableSet_isProbabilityMeasure
      (by fun_prop) (by fun_prop)
  | succ n => fun_prop

/-! ### Stationary policies and their trajectory laws -/

-- todo: this is a generic definition of a stationary policy, not specific to MDPs.
/-- The stationary deterministic policy `π` as an algorithm: it plays `π s` in the current
state `s`. -/
noncomputable def policyAlg (π : 𝓢 → 𝓐) (hπ : Measurable π) : Algorithm 𝓢 𝓐 𝓡 :=
  detAlgorithm (fun _ p ↦ π p.2) fun _ ↦ hπ.comp measurable_snd

variable [Nonempty 𝓢]

/-- The law of the trajectory of the policy `π` started at the state `s`: `E^π_s`. -/
noncomputable def policyMeasure (M : MDP 𝓢 𝓐 𝓡) (π : 𝓢 → 𝓐) (hπ : Measurable π) (s : 𝓢) :
    Measure (ℕ → Round 𝓢 𝓐 𝓡) :=
  trajMeasure (policyAlg π hπ) (M.env (Measure.dirac s))
deriving IsProbabilityMeasure

/-- The law of the state-action trajectory of the policy `π` from the state `s` (no rewards). -/
noncomputable def stateLaw (M : MDP 𝓢 𝓐 𝓡) (π : 𝓢 → 𝓐) (hπ : Measurable π) (s : 𝓢) :
    Measure (ℕ → 𝓢 × 𝓐) :=
  (policyMeasure M π hπ s).map (fun h n ↦ ((h n).obs, (h n).action))

instance (M : MDP 𝓢 𝓐 𝓡) (π : 𝓢 → 𝓐) (hπ : Measurable π) (s : 𝓢) :
    IsProbabilityMeasure (stateLaw M π hπ s) := Measure.isProbabilityMeasure_map (by fun_prop)

/-! ### Mean rewards -/


variable [NormedAddCommGroup 𝓡] [NormedSpace ℝ 𝓡]

/-- The mean reward `r(s, a) = 𝔼[R (s, a)]` of a state-action pair. -/
noncomputable def meanReward (R : Kernel (𝓢 × 𝓐) 𝓡) [IsMarkovKernel R] (p : 𝓢 × 𝓐) : 𝓡 := (R p)[id]

end Learning.MDP
