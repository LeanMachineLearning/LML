/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import VersoManual
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

#doc (Manual) "Probability Spaces and Measures" =>
%%%
htmlSplit := .never
%%%

```lean -show
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
```

First, in order to work on probability we need a measurable space.
We can define a probability measure on such a space as follows.
```lean
variable {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
```
The class `MeasurableSpace Ω` defines a sigma-algebra on `Ω`. We then introduced a measure `P` on that sigma-algebra and specified that it should be a probability measure.
If we want to work on `ℝ` or another well known type the typeclass inference system will find `[MeasurableSpace ℝ]` on its own. We can write simply
```lean
variable {P : Measure ℝ} [IsProbabilityMeasure P]
```

With the code above, we can introduce several probability measures on the same space. When using lemmas and definitions about those measures, we will need to specify which measure we are talking about.
For example, the variance of a random variable `X` with respect to the measure `P` will be `variance X P`.

But perhaps we just want a space with a canonical probability measure, which would be the one used without us having to tell Lean explicitly.
That can be done with the `MeasureSpace` class. A `MeasureSpace` is a `MeasurableSpace` with a canonical measure called `volume`.
The probability library of Mathlib defines a notation `ℙ` for that measure. We still need to tell that we want it to be a probability measure though.
```lean
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
```
Remark 1: in the code above we can't write only `[IsProbabilityMeasure ℙ]` because Lean would then not know to which space the default measure `ℙ` refers to.
That will not be necessary when we use `ℙ` in proofs because the context will be enough to infer `Ω`.

Remark 2: a lemma written for `P : Measure Ω` in a `MeasurableSpace Ω` will apply for the special measure `ℙ` in a `MeasureSpace Ω`, but the converse is not true.
Mathlib focuses on generality, hence uses the `MeasurableSpace` spelling for its lemmas. In another context, the convenience of `MeasureSpace` may be preferable.


Remark 3: `IsProbabilityMeasure` vs `ProbabilityMeasure`.
The examples above used `{P : Measure Ω} [IsProbabilityMeasure P]` to define a probability measure. That's the standard way to do it.
Mathlib also contains a type `ProbabilityMeasure Ω`: the subtype of measures that are probability measures.
The goal of that type is to work on the set of probability measures on `Ω`.
In particular, it comes with a topology, the topology of convergence in distribution (weak convergence of measures).
If we don't need to work with that topology, `{P : Measure Ω} [IsProbabilityMeasure P]` should be preferred.


# Probability of events

An event is a measurable set: there is no special event definition in Mathlib.
The probability of that event is the measure of the set.
A `Measure` can be applied to a set like a function and returns a value in `ENNReal` (denoted by `ℝ≥0∞`, available after `open scoped ENNReal`).
```lean
example (P : Measure ℝ) (s : Set ℝ) : ℝ≥0∞ := P s
```
The probability of the event `s` is thus `P s`.
The type `ℝ≥0∞` represents the nonnegative reals and infinity: the measure of a set is a nonnegative real number which in general may be infinite.
If `P` is a probability measure, it actually takes only values up to 1.
The tactic `simp` knows that a probability measure is finite and will use the lemmas `measure_ne_top` or `measure_lt_top` to prove that `P s ≠ ∞` or `P s < ∞`.

The operations on `ℝ≥0∞` are not as nicely behaved as on `ℝ`: `ℝ≥0∞` is not a ring. For example, subtraction truncates to zero.
If one finds that lemma `lemma_name` used to transform an equation does not apply to `ℝ≥0∞`, a good thing to try is to find a lemma named like `ENNReal.lemma_name_of_something` and use that instead (it will typically require that one variable is not infinite).

For many lemmas to apply, the set `s` will need to be a measurable set. The way to express that is `MeasurableSet s`.


# Random variables

A random variable is a measurable function from a measurable space to another.
```lean
variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} (hX : Measurable X)
```
In that code we defined a random variable `X` from the measurable space `Ω` to `ℝ` (for which the typeclass inference system finds a measurable space instance). The assumption `hX` states that `X` is measurable, which is necessary for most manipulations.

If we define a measure `P` on `Ω`, we can talk about the law or distribution of a random variable `X : Ω → E`.
The law of `X` is a measure on `E`, with value `P (X ⁻¹' s)` on any measurable set `s` of `E`.
This is how we define the map of the measure `P` by `X`, `Measure.map X P` or more succinctly `P.map X`.
There is no specific notation for that law.
To say that `X` is Gaussian with mean 0 and variance 1, write `P.map X = gaussianReal 0 1`.

The expectation of `X` is the integral of that function against the measure `P`, written `∫ ω, X ω ∂P`.
The notation `P[X]` is shorthand for that expectation. In a `MeasureSpace`, we can further use the notation `𝔼[X]`.

Remark: there are two types of integrals in Mathlib, Bochner integrals and Lebesgue integrals.
The expectation notations stand for the Bochner integral, which is defined for `X : Ω → E` with `E` a normed space over `ℝ` (`[NormedAddCommGroup E] [NormedSpace ℝ E]`).
They don't work for `Y : Ω → ℝ≥0∞` since `ℝ≥0∞` is not a normed space, but those functions can be integrated with the Lebesgue integral: `∫⁻ ω, Y ω ∂P`.
There is no expectation notation for the Lebesgue integral.

# Discrete probability

In discrete probability, measurability is not an issue: every set and every function are measurable.
The typeclass `[DiscreteMeasurableSpace Ω]` signals that every set of `Ω` is measurable and the lemma `MeasurableSet.of_discrete` provides a proof of measurability.
To obtain measurability of a function from `Ω`, use `Measurable.of_discrete`.

Any countable type with measurable singletons is a `DiscreteMeasurableSpace`, for example `ℕ` or `Fin n`.

A way to define a probability measure on a discrete space `Ω` is to use the type `PMF Ω`, which stands for probability mass function.
`PMF Ω` is the subtype of functions `Ω → ℝ≥0∞` that sum to 1.
One can get a `Measure Ω` from `p : PMF Ω` with `p.toMeasure`.
When writing a theorem about probability on finite spaces, it preferable to write it for a `Measure` in a `DiscreteMeasurableSpace` than for a `PMF` for better integration with the library.


# Additional typeclasses on measurable spaces

Some results in probability theory require the sigma-algebra to be the Borel sigma-algebra, generated by the open sets. For example, with the Borel sigma-algebra the open sets are measurable and continuous functions are measurable.
For that we first need `Ω` to be a topological space and we then need to add a `[BorelSpace Ω]` variable.
```lean
variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω]
```

For properties related to conditional distributions, it is often convenient or necessary to work in a standard Borel space (a measurable space arising as the Borel sets of some Polish topology). See the `StandardBorelSpace` typeclass.
Note that a countable discrete measurable space is a standard Borel space, so there is no need to worry about that typeclass when doing discrete probability.
