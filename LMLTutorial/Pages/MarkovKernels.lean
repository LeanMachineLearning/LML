/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LMLTutorial.References
import VersoManual
import Mathlib.Probability.Kernel.Composition.Lemmas

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

#doc (Manual) "Markov Kernels" =>
%%%
htmlSplit := .never
%%%

This tutorial presents a central object in our treatment of stochastic algorithms: Markov kernels, which are measurable maps between a measurable space and the probability measures on another measurable space.

For a more in-depth exposition, see {citep Docs.degenne2025markov}[].

# Definition

In probability theory, we need functions to be measurable to be able to work with them.
A transition kernel from a measurable space `𝓧` to a measurable space `𝓨` is a function `𝓧 → Measure 𝓨` that is measurable.
What it means in practice is that each time one wants to work with a function that takes measures as values, the right thing to do is to manipulate it as a kernel.

```lean -show

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
variable {P : Measure 𝓧} [IsProbabilityMeasure P]
  {κ : Kernel 𝓧 𝓨} [IsMarkovKernel κ]
```

```lean
example (κ : Kernel 𝓧 𝓨) (x : 𝓧) : Measure 𝓨 := κ x

example (κ : Kernel 𝓧 𝓨) : Measurable κ := κ.measurable

example (f : 𝓧 → Measure 𝓨) (hf : Measurable f) : Kernel 𝓧 𝓨 := ⟨f, hf⟩
```

Of course there is a big gap in that explanation: what does it mean for a measure-valued function to be measurable?

Such a function is measurable if for every measurable set `B` of `𝓨`, the function `𝓧 → ℝ≥0∞` defined by `fun x ↦ κ x B` is measurable.
```lean
example (f : 𝓧 → Measure 𝓨) :
    Measurable f ↔ ∀ B : Set 𝓨, MeasurableSet B → Measurable (fun x : 𝓧 ↦ f x B) :=
  ⟨fun hf _ hB ↦ (Measure.measurable_coe hB).comp hf,
    Measure.measurable_of_measurable_coe f⟩
```

Kernels arise naturally when describing the outcomes of sequential experiments.
For a toy example, suppose that if the weather is good one day, we know that it will be good the next day with probability 0.8, and if it is bad weather instead, it will be good the next day with probability 0.4.
We can describe that situation with a Markov kernel `κ` from a type with two elements `{good, bad}` to itself such that `κ good` is the probability measure giving probability 0.8 to good weather and 0.2 to bad weather, and `κ bad` is the probability measure giving probability 0.4 to good weather and 0.6 to bad weather.
On such a simple example there is no need for the measurability condition of kernels: every function from a finite set with discrete sigma-algebra to a measurable space is measurable.
However, the measurability is important in non-discrete spaces.


Kernels are fully specified by their action on measurable functions.
That is, if two kernels `κ η : Kernel 𝓧 𝓨` are such that for every measurable function `f : 𝓨 → ℝ≥0∞` and every `x : 𝓧`, `∫ y, f y ∂(κ x) = ∫ y, f y ∂(η x)`, then `κ = η`.
```lean
example (κ η : Kernel 𝓧 𝓨) :
    κ = η ↔ ∀ x f, Measurable f → ∫⁻ y, f y ∂(κ x) = ∫⁻ y, f y ∂(η x) :=
  Kernel.ext_fun_iff
```
Another way to show that two kernels are equal is to show that their values `κ x` and `η x` are equal for all `x`, which since they are measures can be checked by checking that they give the same value to all measurable sets.

# Classes of kernels

A kernel `κ : 𝓧 ⟶ 𝓨` is a Markov kernel if `κ x` is a probability measure for every `x : 𝓧`.
If the supremum of `κ x univ` over `x : 𝓧` is finite, then `κ` is said to be a finite kernel.
Finally, Mathlib also contains the class of s-finite kernels, which are kernels that can be expressed as a countable sum of finite kernels.
Those three properties are denoted by typeclasses {InlineLean.module}`[IsMarkovKernel κ]`, `[IsFiniteKernel κ]` and `[IsSFiniteKernel κ]` respectively.

```lean
example (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] (x : 𝓧) :
    κ x Set.univ = 1 := by simp

example (κ : Kernel 𝓧 𝓨) [IsFiniteKernel κ] :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ a, κ a Set.univ ≤ C :=
  IsFiniteKernel.exists_univ_le

example (κ : Kernel 𝓧 𝓨) [IsFiniteKernel κ] (x : 𝓧) :
    IsFiniteMeasure (κ x) := inferInstance
```

A measurable random variable `X : 𝓧 → 𝓨` can be seen as a `Kernel 𝓧 𝓨` that maps `ω : 𝓧` to the Dirac measure at `X ω`.
Such a kernel is called a deterministic kernel and is a Markov kernel.
It is denoted by `Kernel.deterministic X hX`, where `hX` is the measurability condition on `X`.
Among the deterministic kernels, a few play a special role.
The identity kernel `Kernel.id : Kernel 𝓧 𝓧` is the deterministic kernel associated with the identity function: it maps `x` to the Dirac measure at `x`.
The copy kernel `Kernel.copy : Kernel 𝓧 (𝓧 × 𝓧)` maps `x` to the Dirac measure at `(x, x)`.
The discard kernel `Kernel.discard : Kernel 𝓧 Unit` maps `x` to the unique probability measure on the one-point space `Unit`.
Another useful (not deterministic) kernel is the constant kernel `Kernel.const μ : Kernel Ω 𝓧` which maps every point of `Ω` to the same probability measure `μ` on `𝓧`.


# Composition

TODO: describe the various ways to compose or take products of kernels.
