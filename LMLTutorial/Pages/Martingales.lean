/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module
public import VersoManual
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Martingale.OptionalSampling

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

@[expose] public section

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

#doc (Manual) "Stochastic Processes and Martingales" =>
%%%
htmlSplit := .never
%%%

```lean -show
open Filter
open scoped ENNReal NNReal Topology

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
```

# Stochastic processes, filtrations, and martingales

We define a measurable space {lean}`Ω`, with a probability measure {lean}`(P : Measure Ω)`.

```lean
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
```

Let then `X` be a stochastic process indexed by `ℕ`: a function `ℕ → Ω → E`.
Here `E` is a Banach space, a complete normed space (that's what the martingale property needs).
We will often need a measurability condition on `X` in lemmas, but we don't add it yet.

```lean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mE : MeasurableSpace E} {X : ℕ → Ω → E}
```

A filtration is a monotone family of sub-σ-algebras indexed by `ℕ`.
```lean
variable {𝓕 : Filtration ℕ mΩ} {n : ℕ}

example : ∀ n, 𝓕 n ≤ mΩ := Filtration.le 𝓕

example {i j : ℕ} (hij : i ≤ j) : 𝓕 i ≤ 𝓕 j := Filtration.mono 𝓕 hij
```

If `X` is a martingale, then it is adapted to the filtration, which means that for all `n`,
`X n` is (strongly) measurable with respect to {lean}`𝓕 n`.
```lean
example (hX : Martingale X 𝓕 P) : StronglyAdapted 𝓕 X := hX.stronglyAdapted

example (hX : Martingale X 𝓕 P) (n : ℕ) : StronglyMeasurable[𝓕 n] (X n) := hX.stronglyAdapted n

example [BorelSpace E] (hX : Martingale X 𝓕 P) (n : ℕ) : Measurable[𝓕 n] (X n) :=
  (hX.stronglyAdapted n).measurable

/-- A martingale satisfies the following equality: for all `i ≤ j`, the conditional expectation of
`X j` with respect to `𝓕 i` is equal to `X i`. -/
example (hX : Martingale X 𝓕 P) {i j : ℕ} (hij : i ≤ j) : P[X j | 𝓕 i] =ᵐ[P] X i :=
  hX.condExp_ae_eq hij

/-- For a submartingale, the conditional expectation of `Y j` with respect to `𝓕 i` is greater than
or equal to `Y i`. -/
example {Y : ℕ → Ω → ℝ} (hX : Submartingale Y 𝓕 P) {i j : ℕ} (hij : i ≤ j) :
    Y i ≤ᵐ[P] P[Y j | 𝓕 i] :=
  hX.ae_le_condExp hij
```

*Almost everywhere martingale convergence theorem*: An L¹-bounded submartingale converges
almost everywhere to a `⨆ n, 𝓕 n`-measurable function, its limit process `𝓕.limitProcess Y P`.
This is the Mathlib lemma `Submartingale.ae_tendsto_limitProcess`.

```lean
example {Y : ℕ → Ω → ℝ} (hY : Submartingale Y 𝓕 P)
    {R : ℝ≥0} (hbdd : ∀ n, eLpNorm (Y n) 1 P ≤ R) :
    ∀ᵐ ω ∂P, Tendsto (Y · ω) atTop (𝓝 (𝓕.limitProcess Y P ω)) :=
  hY.ae_tendsto_limitProcess hbdd
```

# Stopping times

A stopping time with respect to a filtration indexed by `ℕ` is a random time `τ : Ω → ℕ∞` such that
for all `n`, the set `{ω | τ ω ≤ n}` is measurable with respect to {lean}`𝓕 n`.

```lean
variable {τ : Ω → ℕ∞} (hτ : IsStoppingTime 𝓕 τ)

example (i : ℕ) : MeasurableSet[𝓕 i] {ω | τ ω ≤ i} := hτ.measurableSet_le i
```

*The optional stopping theorem* (fair game theorem): an adapted integrable process `Y`
is a submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `Y` at `τ` has expectation smaller than or equal to that of its stopped value at
`π`.
```lean
example {Y : ℕ → Ω → ℝ} (hadp : StronglyAdapted 𝓕 Y)
    (hint : ∀ i, Integrable (Y i) P) :
    Submartingale Y 𝓕 P ↔ ∀ τ π : Ω → ℕ∞, IsStoppingTime 𝓕 τ → IsStoppingTime 𝓕 π →
      τ ≤ π → (∃ N : ℕ, ∀ x, π x ≤ N) → P[stoppedValue Y τ] ≤ P[stoppedValue Y π] :=
  ⟨fun hf _ _ hτ hπ hle ⟨_, hN⟩ => hf.expected_stoppedValue_mono hτ hπ hle hN,
    submartingale_of_expected_stoppedValue_mono hadp hint⟩
```
