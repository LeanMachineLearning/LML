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

Generic constructions live in the `Algorithm` and `Environment` namespaces.
A `det` prefix marks the deterministic version of a constructor.
Predicates are root-level `Is…Alg` / `Is…Env` classes when they carry an accessor, and namespaced `Prop` definitions otherwise.
Accessors are namespaced so that dot notation works.
Every row may read the time `n` unless it says "stationary" or "nothing".
Every `det…` constructor is the stochastic one applied to `Kernel.deterministic`, gets both the determinism instance and the dependence instance, and takes its measurability proofs as `by fun_prop` autoparams.

All time zero accessors are root-level `…0` definitions. Example: `Algorithm.policy0`.

## Algorithms

The policy at round `n` can depend on `n`, on the history at `n` and the current observation. It can be deterministic or stochastic.

Not stochastic: `Algorithm.IsDeterministic`, `Algorithm.deterministic`

No observation: `Algorithm.IgnoresObs`, `Algorithm.comapObs fun _ ↦ ()`

No history: `Algorithm.IsMarkov`, `Algorithm.markov`

No history, no observation: `Algorithm.IsOpenLoop`, `Algorithm.openLoop`, `Algorithm.ofSeq` (det version)

Not time-dependent, no history: `Algorithm.IsStationary`, `Algorithm.stationary`

No time, no history, no observation: `Algorithm.const`

## Environments

The observation at round `n` can depend on `n` and on the history at `n`, and can be deterministic or stochastic.

The feedback at round `n` can depend on `n`, on the history at `n`, on the current observation and on the current action.
It can be deterministic or stochastic.

In general, the dependence on history is the same for both kernels.

All for obs, no action for feedback: `Environment.FeedbackIgnoresAction`, `Environment.adversary`.

No history for obs and feedback: `Environment.IsOblivious`, `Environment.oblivious`.

No time, no history for obs and feedback: `Environment.IsStationary`, `Environment.stationary`.

No time, last round of history for obs, not history for feedback: `Environment.IsMarkov`, `Environment.markov`.

Determinism: `Environment.HasDeterministicObs`, `Environment.HasDeterministicFeedback`.

### Obs = Unit

Only the feedback matters, so the constructors are named by the feedback's shape.
It can depend on time, history and action and be stochastic or deterministic.

general: use `Environment` with Obs = Unit.

No history: use oblivious or stationary environment with Obs = Unit.

No history, deterministic: `Environment.evalSeq` and `Environment.eval` (no time).

No history, no action (only time): `Environment.indep` and `Environment.ofSeq` (deterministic).

Nothing: `Environment.const` (stochastic). The deterministic version is probably not useful.

## Examples

Oblivious adversarial bandit environment: Obs = Unit, feedback depends on time and action, deterministic. Which constructor? `Environment.evalSeq`.

Stochastic optimization: Obs = Unit, feedback depends on time and action, stochastic. Which constructor? `Environment.banditSeq`.

| Policy reads | Stochastic constructor | Deterministic constructor | Predicate | Accessor |
|---|---|---|---|---|
| history, obs | `Algorithm` | `Algorithm.deterministic f`, was `detAlgorithm` | `IsDeterministicAlg`, exists | `alg.nextAction n`, was `nextAction alg n` |
| history only | `alg.comapObs fun _ ↦ ()`, exists | same | `Algorithm.IgnoresObs`, new def | none |
| obs | `Algorithm.markov π`, `π : ℕ → Kernel 𝓞 𝓐`, new | `Algorithm.detMarkov f`, `f : ℕ → 𝓞 → 𝓐`, new | `IsMarkovAlg`, new | `alg.policyCondObs n : Kernel 𝓞 𝓐` |
| obs, stationary | `Algorithm.stationary π`, `π : Kernel 𝓞 𝓐`, new | `Algorithm.detStationary f`, `f : 𝓞 → 𝓐`, new | `IsStationaryAlg`, new | same, constant in `n` |
| time only | `Algorithm.openLoop μ`, `μ : ℕ → Measure 𝓐`, new | `Algorithm.ofSeq x`, was `fixedDesignAlg` | `IsOpenLoopAlg`, new | `alg.actionLaw n : Measure 𝓐` |
| nothing | `Algorithm.const μ`, was `randomSampling` | `Algorithm.detConst a`, new | none, use `IsOpenLoopAlg` | none |

Named instances of rows: `Algorithm.uniform`, was `uniformAlgorithm`, is `const` of the uniform
measure; `Algorithm.roundRobin hK`, was `roundRobinAlgorithm`, is `ofSeq`. The bandit-specific
`ucbAlgorithm`, `etcAlgorithm` and `tsAlgorithm` keep their names in the `Bandits` namespace.

Implications provided as instances: stationary implies Markov, open loop implies Markov, and the
deterministic constructors of each row give both instances. The three dependence predicates are
the named cases of `Algorithm.FactorsThrough`.

## Environments

### General observation type

| Obs reads | Feedback reads | Stochastic constructor | Deterministic constructor | Predicate | Accessors |
|---|---|---|---|---|---|
| history | history, obs, action | the structure | `Environment.deterministic g f`, new | `IsDeterministicEnv`, redefined to cover both kernels | `env.obsFun n`, `env.feedbackFun n` |
| history | history, obs | `Environment.adversary ρ κ`, new | `Environment.detAdversary g f`, new | `Environment.FeedbackIgnoresAction`, from LMLPapers | none |
| last round | obs, action | `Environment.markov ρ P ν`, new | `Environment.detMarkov s₀ P f`, new | `IsMarkovEnv`, new | `env.transition n : Kernel (Round 𝓞 𝓐 𝓨) 𝓞`, `env.feedbackCondObsAction n : Kernel (𝓞 × 𝓐) 𝓨` |
| last obs and action, stationary | obs, action | `Environment.mdp ρ P r`, new | `Environment.detMdp s₀ P r`, new | none, use `IsMarkovEnv` | same |
| time only | obs, action | `Environment.oblivious ρ ν`, `ρ : ℕ → Measure 𝓞`, `ν : ℕ → Kernel (𝓞 × 𝓐) 𝓨`, new signature | `Environment.detOblivious o f`, new | `IsObliviousEnv`, redefined | `env.obsLaw n : Measure 𝓞`, `env.feedbackCondObsAction n` |
| nothing | obs, action, stationary | `Environment.stationary ρ ν`, `ρ : Measure 𝓞`, `ν : Kernel (𝓞 × 𝓐) 𝓨`, new signature | `Environment.detStationary o₀ f`, new | `IsStationaryEnv`, new | same, constant in `n` |

Today's `detEnvironment obs f`, with random observations and deterministic feedback, becomes
`Environment.detFeedback obs f` with the definition `Environment.HasDeterministicFeedback`, or is
dropped since nothing uses it.

### No observation

With `𝓞 = Unit` only the feedback matters, so these constructors are named by the feedback's shape
rather than by a dependence word. They are the existing bandit constructors, unchanged in type.

| Feedback reads | Stochastic constructor | Deterministic constructor |
|---|---|---|
| time, action | `Environment.banditSeq ν`, `ν : ℕ → Kernel 𝓐 𝓨`, was `obliviousEnv` | `Environment.evalSeq g`, was `onlineEvalEnv` |
| action | `Environment.bandit ν`, `ν : Kernel 𝓐 𝓨`, was `stationaryEnv` | `Environment.eval f`, was `evalEnv` |
| time only | `Environment.indep P`, `P : ℕ → Measure 𝓨`, new | `Environment.ofSeq y`, was `seqEnv` in LMLPapers |
| nothing | `Environment.iid P`, was `iidEnv` in LMLPapers | `Environment.const y`, new |

The general predicates apply to this table as they are. The one extra accessor is
`env.feedbackCondAction n : Kernel 𝓐 𝓨`, defined only for `𝓞 = Unit` from
`feedbackCondObsAction`; it is today's `feedbackCondAction env n`. The identities tying the two
tables together are simp lemmas: `bandit ν` is `stationary` of the Dirac measure and
`ν.prodMkLeft Unit`, `eval f` is `detStationary`, `ofSeq y` is `evalSeq` of constant functions,
`iid P` is `bandit` of the constant kernel, and `indep P` is `banditSeq` of constant kernels.

### Hidden parameter

`Environment.bayes Q env : Environment (𝓔 × 𝓞) 𝓐 𝓨` for a family `env : 𝓔 → Environment 𝓞 𝓐 𝓨`,
new; `Environment.bayesBandit Q κ : Environment 𝓔 𝓐 𝓨`, was `bayesStationaryEnv`.

Implications provided as instances: stationary implies oblivious implies Markov, and `mdp` is a
`markov` instance.

Time zero: `Environment.obs0` unchanged; `Environment.feedback0`, was `ν0`;
`Environment.feedbackFun0`, was `feedbackFunZero`.
