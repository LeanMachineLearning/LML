# Naming of algorithms and environments

The file `Algorithm.lean` defines the `Algorithm` and `Environment` structures.
An algorithm has a sequence of Markov kernels (the policy) which reads a history and an observation and returns an action.
```lean
structure Algorithm (𝓞 𝓐 𝓨 : Type*) [MeasurableSpace 𝓞] [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]
    where
  /-- Law of the action of round `n` given the past rounds and the current observation. -/
  policy : (n : ℕ) → Kernel (Hist 𝓞 𝓐 𝓨 n × 𝓞) 𝓐
  /-- The policy is a Markov kernel. -/
  [isMarkovKernel_policy : ∀ n, IsMarkovKernel (policy n)]
```
An environment has two sequences of kernels: one for observations, which reads the history, and one for feedback, which reads the history, the current observation and the current action.
```lean
structure Environment (𝓞 𝓐 𝓨 : Type*) [MeasurableSpace 𝓞] [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]
    where
  /-- Law of the observation of round `n` given the past rounds. -/
  obs : (n : ℕ) → Kernel (Hist 𝓞 𝓐 𝓨 n) 𝓞
  /-- Law of the feedback of round `n` given the past rounds, the observation and the action. -/
  feedback : (n : ℕ) → Kernel ((Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐) 𝓨
  /-- The observation kernel is a Markov kernel. -/
  [isMarkovKernel_obs : ∀ n, IsMarkovKernel (obs n)]
  /-- The feedback kernel is a Markov kernel. -/
  [isMarkovKernel_feedback : ∀ n, IsMarkovKernel (feedback n)]
```

In many applications, some of those kernels are deterministic, or do not depend on some of their inputs.
We detail here the naming conventions for the various constructors, predicates and accessors that are used in the library.

NOTE: some names described below are marked as MISSING because they are not yet implemented in the library.
They may never be implemented if we don't need them.
If you need one of them, treat the name here as a recommendation that you may want to use.

Generic constructions live in the `Algorithm` and `Environment` namespaces.
Predicates live in the `Algorithm` and `Environment` namespaces: they are classes when they carry an accessor, and `Prop` definitions otherwise.
Accessors are namespaced so that dot notation works.

All time zero accessors are `…Zero` definitions. Example: `Algorithm.policyZero`.

## Algorithms

The policy at round `n` can depend on `n`, on the history at `n` and the current observation. It can be deterministic or stochastic.

Not stochastic: `Algorithm.IsDeterministic`, `Algorithm.deterministic`

No observation: `Algorithm.IgnoresObs` (MISSING), `Algorithm.comapObs fun _ ↦ ()`

No history: `Algorithm.IsMarkov`, `Algorithm.markov`

No history, no observation: `Algorithm.IsOpenLoop` (MISSING), `Algorithm.openLoop` (MISSING), `Algorithm.ofSeq` (MISSING) (det version)

Not time-dependent, no history: `Algorithm.IsStationary` (MISSING), `Algorithm.stationary` (MISSING)

No time, no history, no observation: `Algorithm.const`

## Environments

The observation at round `n` can depend on `n` and on the history at `n`, and can be deterministic or stochastic.

The feedback at round `n` can depend on `n`, on the history at `n`, on the current observation and on the current action.
It can be deterministic or stochastic.

In general, the dependence on history is the same for both kernels.

All for obs, no action for feedback: `Environment.FeedbackIgnoresAction` (MISSING), `Environment.adversary` (MISSING).

No history for obs and feedback: `Environment.IsOblivious`, `Environment.oblivious`.

No time, no history for obs and feedback: `Environment.IsStationary`, `Environment.stationary`.

No time, last round of history for obs, not history for feedback: `Environment.IsMarkov` (MISSING), `Environment.markov` (MISSING).

Determinism: `Environment.HasDeterministicObs` (MISSING), `Environment.HasDeterministicFeedback`, `Environment.detFeedback` (any observation kernels, deterministic feedback).

### Obs = Unit

Only the feedback matters, so the constructors are named by the feedback's shape.
It can depend on time, history and action and be stochastic or deterministic.

general: use `Environment` with Obs = Unit.

No history: `Environment.banditSeq` and `Environment.bandit` (no time).

No history, deterministic: `Environment.evalSeq` and `Environment.eval` (no time).

No history, no action (only time): `Environment.indep` (MISSING) and `Environment.ofSeq` (MISSING) (deterministic).

Nothing: `Environment.const` (MISSING) (stochastic). The deterministic version is probably not useful.

## Examples

Oblivious adversarial bandit environment: Obs = Unit, feedback depends on time and action, deterministic. Use `Environment.evalSeq`.

Stochastic optimization: Obs = Unit, feedback depends on time and action, stochastic. Use `Environment.banditSeq`.
