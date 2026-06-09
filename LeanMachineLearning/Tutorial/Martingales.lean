/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Martingale.OptionalSampling

/-! # Tutorial source file for martingales -/

@[expose] public section

open Filter
open scoped ENNReal NNReal Topology
/-

# Martingales
-/

/- We open namespaces. The effect is that after that command, we can call lemmas in those namespaces
without their namespace prefix: for example, we can write `inter_comm` instead of `Set.inter_comm`.
Hover over `open` if you want to learn more. -/
open MeasureTheory ProbabilityTheory Set

/- We define a measure space `Ω`: a type with a `MeasurableSpace Ω` variable (a σ-algebra) on which
we also define a mesure `P : Measure Ω`.
We then state that `P` is a probability measure. That is, `P univ = 1`, where `univ : Set Ω` is the
universal set in `Ω` (the set that contains all `x : Ω`). -/

-- ANCHOR: Variables
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
-- ANCHOR_END: Variables

/- One can take the measure of a set `A`. -/
-- ANCHOR: ExProba
example {A : Set Ω} : ℝ≥0∞ := P A
-- ANCHOR_END: ExProba

/- `ℝ≥0∞`, or `ENNReal`, is the type of extended non-negative real numbers, which contain `∞`.
Measures can in general take infinite values, but since our `ℙ` is a probability measure,
it actually takes only values up to 1.
`simp` knows that a probability measure is finite and will use the lemmas `measure_ne_top`
or `measure_lt_top` to prove that `ℙ A ≠ ∞` or `ℙ A < ∞`.
The `finiteness` tactic is specialized in proving that `ℝ≥0∞` expressions are finite.

Hint: use `#check measure_ne_top` to see what that lemma does.

The operations on `ℝ≥0∞` are not as nicely behaved as on `ℝ`: `ℝ≥0∞` is not a ring and
subtraction truncates to zero for example. If you find that lemma `lemma_name` used to transform
an equation does not apply to `ℝ≥0∞`, try to find a lemma named something like
`ENNReal.lemma_name_of_something` and use that instead. -/

/- A stochastic process indexed by `ℕ`: a function `ℕ → Ω → E`. Here `E` is a Banach space,
a complete normed space (that's what the martingale property needs).
We will often need a measurability condition on `X` in lemmas, but we don't add it yet. -/

-- ANCHOR: Variables2
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mE : MeasurableSpace E} {X : ℕ → Ω → E}
-- ANCHOR_END: Variables2

/- A filtration: a monotone family of sub-σ-algebras indexed by `ℕ`.
Remember that you can learn about a definition by hovering over it, or by using ctrl-click to go to
its declaration. -/
-- ANCHOR: Filtration
variable {𝓕 : Filtration ℕ mΩ}

example : ∀ n, 𝓕 n ≤ mΩ := Filtration.le 𝓕

example {i j : ℕ} (hij : i ≤ j) : 𝓕 i ≤ 𝓕 j := Filtration.mono 𝓕 hij
-- ANCHOR_END: Filtration

/-- If `X` is a martingale, then it is adapted to the filtration, which means that for all `n`,
`X n` is (strongly) measurable with respect to `𝓕 n`. -/
-- ANCHOR: Martingale
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
-- ANCHOR_END: Martingale

/-- **Almost everywhere martingale convergence theorem**: An L¹-bounded submartingale converges
almost everywhere to a `⨆ n, ℱ n`-measurable function. -/
-- ANCHOR: AeTendstoLimitProcess
theorem ae_tendsto_limitProcess {Y : ℕ → Ω → ℝ} (hY : Submartingale Y 𝓕 P)
    {R : ℝ≥0} (hbdd : ∀ n, eLpNorm (Y n) 1 P ≤ R) :
    ∀ᵐ ω ∂P, Tendsto (Y · ω) atTop (𝓝 (𝓕.limitProcess Y P ω)) := by
  classical
  suffices ∃ g, StronglyMeasurable[⨆ n, 𝓕 n] g ∧ ∀ᵐ ω ∂P, Tendsto (Y · ω) atTop (𝓝 (g ω)) by
    rw [Filtration.limitProcess, dif_pos this]
    exact (Classical.choose_spec this).2
  set g' : Ω → ℝ := fun ω ↦ if h : ∃ c, Tendsto (Y · ω) atTop (𝓝 c) then h.choose else 0
  have hle : ⨆ n, 𝓕 n ≤ mΩ := sSup_le fun m ⟨n, hn⟩ ↦ hn ▸ 𝓕.le _
  have hg' : ∀ᵐ ω ∂P.trim hle, Tendsto (Y · ω) atTop (𝓝 (g' ω)) := by
    filter_upwards [hY.exists_ae_trim_tendsto_of_bdd hbdd] with ω hω
    simp_rw [g', dif_pos hω]
    exact hω.choose_spec
  have hg'm : AEStronglyMeasurable[⨆ n, 𝓕 n] g' (P.trim hle) :=
    (@aemeasurable_of_tendsto_metrizable_ae' _ _ (⨆ n, 𝓕 n) _ _ _ _ _ _ _
      (fun n ↦ ((hY.stronglyMeasurable n).measurable.mono (le_sSup ⟨n, rfl⟩ : 𝓕 n ≤ ⨆ n, 𝓕 n)
        le_rfl).aemeasurable) hg').aestronglyMeasurable
  obtain ⟨g, hgm, hae⟩ := hg'm
  have hg : ∀ᵐ ω ∂P.trim hle, Tendsto (Y · ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hae, hg'] with ω hω hg'ω using hω ▸ hg'ω
  exact ⟨g, hgm, measure_eq_zero_of_trim_eq_zero hle hg⟩
-- ANCHOR_END: AeTendstoLimitProcess

/-! ## Stopping times -/

/- A stopping time with respect to a filtration is a random time `τ : Ω → ℕ` such that
for all `n`, the set `{ω | τ ω ≤ n}` is measurable with respect to `𝓕 n`. -/

-- ANCHOR: Variables3
variable {τ : Ω → ℕ∞} (hτ : IsStoppingTime 𝓕 τ)

example (i : ℕ) : MeasurableSet[𝓕 i] {ω | τ ω ≤ i} := hτ.measurableSet_le i
-- ANCHOR_END: Variables3

/-- **The optional stopping theorem** (fair game theorem): an adapted integrable process `Y`
is a submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `Y` at `τ` has expectation smaller than its stopped value at `π`. -/
-- ANCHOR: submartingale_iff_expected_stoppedValue_mono
theorem submartingale_iff_expected_stoppedValue_mono' {Y : ℕ → Ω → ℝ} (hadp : StronglyAdapted 𝓕 Y)
    (hint : ∀ i, Integrable (Y i) P) :
    Submartingale Y 𝓕 P ↔ ∀ τ π : Ω → ℕ∞, IsStoppingTime 𝓕 τ → IsStoppingTime 𝓕 π →
      τ ≤ π → (∃ N : ℕ, ∀ x, π x ≤ N) → P[stoppedValue Y τ] ≤ P[stoppedValue Y π] :=
  ⟨fun hf _ _ hτ hπ hle ⟨_, hN⟩ => hf.expected_stoppedValue_mono hτ hπ hle hN,
    submartingale_of_expected_stoppedValue_mono hadp hint⟩
-- ANCHOR_END: submartingale_iff_expected_stoppedValue_mono
