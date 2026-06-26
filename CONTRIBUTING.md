# Contributing to Lean Machine Learning

We welcome contributions from the community and appreciate your efforts to improve the project. Please follow the guidelines below to ensure a smooth contribution process.

## How to contribute

Fork the repository and create a new branch for your contribution. Make your changes and submit a pull request to the main branch. Please provide a clear description of your changes and the motivation behind them.

## What to contribute

See the [Roadmap](https://leanmachinelearning.org/roadmap/).

#### Finding tasks

Head over to our github issues if you are looking for a short contribution.

## Coordination

Most contributions are welcome as straightforward PRs.
However, for major developments, it is recommended to discuss it on zulip first.

## Style and documentation

We generally follow the [Mathlib style for coding and documentation](https://leanprover-community.github.io/contribute/style.html), so please read that.

#### Folders and namespaces

We place new material about machine learning in the `Learning` namespace, in an appropriate folder (e.g. `Online/Bandit` for bandits).

For results about definitions from Mathlib, we place them in the same namespace as the original definition (typically `MeasureTheory` or `ProbabilityTheory`), and in a subfolder of the `ForMathlib` folder that corresponds to where they would be if added to Mathlib (e.g. `ForMathlib/Probability/Independence` for results about independence).

The `Tutorial` folder is reserved for material used in the tutorial, and should not be used for general contributions.

## Code quality and LLM policy

The strength of the library lies in carefully designed and reviewed definitions.
The standard is reusable code, not merely code that compiles.
We want to build the basis on which others can base their research efforts.

LLM use is not discouraged, but their output should be carefully reviewed for code quality before submitting pull requests.
We reserve the right to close any PR for which we deem that the reviewing effort is not worth the contribution.
