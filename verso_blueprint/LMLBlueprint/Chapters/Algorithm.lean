import Verso
import VersoManual
import VersoBlueprint
import LeanMachineLearning.SequentialLearning.Deterministic
import LeanMachineLearning.SequentialLearning.FiniteActions
import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
import LeanMachineLearning.SequentialLearning.StationaryEnv
import LMLBlueprint.References
import LMLBlueprint.TeXPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Iterative stochastic algorithms" =>

:::group "algorithm_environment"
Stochastic algorithms and environments
:::

Warning: all times start at zero.

TODO: notations

All measurable spaces are assumed to be standard Borel.

:::definition "algorithm" (parent := "algorithm_environment") (lean := "Learning.Algorithm")
A sequential, stochastic algorithm with actions in a measurable space $`\mathcal{A}` and observations in a measurable space $`\mathcal{R}` is described by the following data:
- for all $`t \in \mathbb{N}`, a policy $`\pi_t : (\mathcal{A} \times \mathcal{R})^{t+1} \rightsquigarrow \mathcal{A}`, a Markov kernel which gives the distribution of the action of the algorithm at time $`t+1` given the history of previous actions and observations,
- $`P_0 \in \mathcal{P}(\mathcal{A})`, a probability measure that gives the distribution of the first action.
:::

After the algorithm takes an action, the environment generates an observation according to a Markov kernel $`\nu_t : (\mathcal{A} \times \mathcal{R})^{t+1} \times \mathcal{A} \rightsquigarrow \mathcal{R}`.

:::definition "environment" (parent := "algorithm_environment") (lean := "Learning.Environment")
An environment with which an algorithm interacts is described by the following data:
- for all $`t \in \mathbb{N}`, a feedback $`\nu_t : (\mathcal{A} \times \mathcal{R})^{t+1} \times \mathcal{A} \rightsquigarrow \mathcal{R}`, a Markov kernel which gives the distribution of the observation at time $`t+1` given the history of previous pulls and observations, and the action of the algorithm at time $`t+1`,
- $`\nu'_0 \in \mathcal{A} \rightsquigarrow \mathcal{R}`, a Markov kernel that gives the distribution of the first observation given the first action.
:::


:::definition "detAlgorithm" (parent := "algorithm_environment") (lean := "Learning.detAlgorithm")
An algorithm ({uses "algorithm"}[]) is deterministic if its initial probability measure $`P_0` is a Dirac measure and if all its policies $`\pi_t` are deterministic kernels.
:::


:::definition "stationaryEnv" (parent := "algorithm_environment") (lean := "Learning.stationaryEnv")
An environment ({uses "environment"}[]) is stationary if there exists a Markov kernel $`\nu : \mathcal{A} \rightsquigarrow \mathcal{R}` such that $`\nu'_0 = \nu` and for all $`t \in \mathbb{N}`, for all $`h_t \in (\mathcal{A} \times \mathcal{R})^{t+1}`, for all $`a \in \mathcal{A}`, $`\nu_t(h_t, a) = \nu(a)`.
:::

TODO: possibly change the _stationary_ name.


Let's detail four examples of interactions between an algorithm and an environment.
- *First order optimization*. The objective of the algorithm is to find the minimum of a function $`f : \mathbb{R}^d \to \mathbb{R}`.
  The action space is $`\mathcal{A} = \mathbb{R}^d` (a point on which the function will be queried) and the observation space is $`\mathcal{R} = \mathbb{R} \times \mathbb{R}^d`.
  The environment is described by a function $`g : \mathbb{R}^d \to \mathbb{R} \times \mathbb{R}^d` such that for all $`x \in \mathbb{R}^d`, $`g(x) = (f(x), \nabla f(x))`. That is, the kernel $`\nu_t` is deterministic and depends only on the action: it is given by $`\nu_t(h_t, x) = \delta_{g(x)}` (the Dirac measure at $`g(x)`).
  An example of algorithm is gradient descent with fixed step size $`\eta > 0`: this is a deterministic algorithm defined by $`P_0 = \delta_{x_0}` for some initial point $`x_0 \in \mathbb{R}^d` and for all $`t \in \mathbb{N}`, $`\pi_t(h_t) = \delta_{x_{t+1}}` where $`x_{t+1} = x_t - \eta \nabla g_2(x_t)`.
- *Stochastic bandits*. The action space is $`\mathcal{A} = [K]` for some $`K \in \mathbb{N}` (the set of arms) and the observation space is $`\mathcal{R} = \mathbb{R}` (the reward obtained after pulling an arm).
  The kernel $`\nu_t` is stationary and depends only on the action: there are probability distributions $`(P_a)_{a \in [K]}` such that for all $`t \in \mathbb{N}`, for all $`h_t \in (\mathcal{A} \times \mathcal{R})^{t+1}`, for all $`a \in \mathcal{A}`, $`\nu_t(h_t, a) = P_a`.
- *Adversarial bandits*. The action space is $`\mathcal{A} = [K]` for some $`K \in \mathbb{N}` (the set of arms) and the observation space is $`\mathcal{R} = \mathbb{R}` (the reward obtained after pulling an arm).
  The reward kernels are usually taken to be deterministic and in an _oblivious_ adversarial bandit they depend only on the time step: there is a sequence of vectors $`(r_t)_{t \in \mathbb{N}}` in $`[0,1]^K` such that for all $`t \in \mathbb{N}`, for all $`h_t \in (\mathcal{A} \times \mathcal{R})^{t+1}`, for all $`a \in \mathcal{A}`, $`\nu_t(h_t, a) = \delta_{r_{t,a}}` (the Dirac measure at $`r_{t,a}`).
- *Reinforcement learning in Markov decision processes*.
  TODO: main feature is that $`\mathcal{R} = \mathcal{S} \times \mathbb{R}` where $`\mathcal{S}` is the state space, and the kernel $`\nu_t` depends on the last state only.


We will want to make global probabilistic statements about the whole sequence of actions and observations.
For example, we may want to prove that an optimization algorithm converges to the minimum of a function almost surely.
For such a statement to make sense, we need a probability space on which the whole sequence of actions and observations is defined as a random variable.

We denote by $`P(X \mid Y)` the conditional distribution of a random variable $`X` given another random variable $`Y` under a probability measure $`P`.
When we write that $`P(X \mid Y) = \kappa`, or that $`X` has conditional distribution $`\kappa` given $`Y`, the equality should be understood as holding $`Y_* P`-almost surely.

*Lean remark*: `HasCondDistrib`

In the Lean implementation, we define a predicate to state those almost sure equalities of conditional distributions: `HasCondDistrib X Y k P` states that under the probability measure $`P`, the random variable $`X` has conditional distribution $`k` given the random variable $`Y` (almost surely with respect to the law of $`X`).
For convenience, the predicate also records that both random variables are almost everywhere measurable.


:::definition "history" (parent := "algorithm_environment") (lean := "Learning.IsAlgEnvSeq.hist, Learning.IsAlgEnvSeq.step")
For two sequences of random variables $`A : \mathbb{N} \to \Omega \to \mathcal{A}` and $`R : \mathbb{N} \to \Omega \to \mathcal{R}` (actions and observations), we call step of the interaction at time $`t` the random variable $`X_t : \Omega \to \mathcal{A} \times \mathcal{R}` defined by $`X_t(\omega) = (A_t(\omega), R_t(\omega))`.
We call history up to time $`t` the random variable $`H_t : \Omega \to (\mathcal{A} \times \mathcal{R})^{t+1}` defined by $`H_t(\omega) = (X_0(\omega), \ldots, X_t(\omega))`.
:::


:::definition "IsAlgEnvSeq" (parent := "algorithm_environment") (lean := "Learning.IsAlgEnvSeq")
Let $`\mathfrak{A}` be an algorithm ({uses "algorithm"}[]) and $`\mathfrak{E}` be an environment ({uses "environment"}[]).
A probability space $`(\Omega, P)` and two sequences of random variables $`A : \mathbb{N} \to \Omega \to \mathcal{A}` and $`R : \mathbb{N} \to \Omega \to \mathcal{R}` form an algorithm-environment interaction for $`\mathfrak{A}` and $`\mathfrak{E}` if the following conditions hold:
1. The law of $`A_0` is $`P_0`.
2. $`P \left( R_0 \mid A_0 \right) = \nu'_0`.
3. For all $`t \in \mathbb{N}`, $`P\left(A_{t+1} \mid A_0, R_0, \ldots, A_t, R_t \right) = \pi_t`.
4. For all $`t \in \mathbb{N}`, $`P\left(R_{t+1} \mid A_0, R_0, \ldots, A_t, R_t, A_{t+1}\right) = \nu_t`.

Uses: {uses "history"}[]
:::


:::lemma_ "law_step" (parent := "algorithm_environment") (lean := "Learning.IsAlgEnvSeq.hasLaw_step_zero, Learning.IsAlgEnvSeq.hasCondDistrib_step")
In an algorithm-environment interaction $`(A, R, P)` as in {uses "IsAlgEnvSeq"}[],
- the law of the initial step $`X_0` is $`P_0 \otimes \nu'_0`,
- for all $`t \in \mathbb{N}`, $`P \left( X_{t+1} \mid H_t \right) = \pi_t \otimes \nu_t`.
:::

:::proof "law_step"
Immediate from the properties of an algorithm-environment interaction.
:::


:::definition "IsAlgEnvSeq.filtration" (parent := "algorithm_environment") (lean := "Learning.IsAlgEnvSeq.filtration, Learning.IsAlgEnvSeq.filtrationAction")
For an algorithm-environment interaction $`(A, R, P)` as in {uses "IsAlgEnvSeq"}[], we denote by $`\mathcal{F}_t` the sigma-algebra generated by the history up to time $`t`: $`\mathcal{F}_t = \sigma(H_t)`.
We denote by $`\mathcal{F}^A_t` the sigma-algebra generated by the history up to time $`t-1` and the action at time $`t`: $`\mathcal{F}^A_t = \sigma(H_{t-1}, A_t)`.
:::


:::lemma_ "IsAlgEnvSeq.adapted" (parent := "algorithm_environment") (lean := "Learning.IsAlgEnvSeq.adapted_step, Learning.IsAlgEnvSeq.adapted_hist, Learning.IsAlgEnvSeq.adapted_action, Learning.IsAlgEnvSeq.adapted_reward")
The history, step, action and observation processes ({uses "history"}[]) are adapted to the filtration $`(\mathcal{F}_t)_{t \in \mathbb{N}}` ({uses "IsAlgEnvSeq.filtration"}[]).
:::

:::proof "IsAlgEnvSeq.adapted"
By definition of the filtration.
:::


:::theorem "isAlgEnvSeq_unique" (parent := "algorithm_environment") (lean := "Learning.isAlgEnvSeq_unique")
If $`(A, R, P)` and $`(A', R', P')` are two {uses "IsAlgEnvSeq"}[algorithm-environment interactions] for the same {uses "algorithm"}[algorithm] $`\mathfrak{A}` and {uses "environment"}[environment] $`\mathfrak{E}`, then the joint distributions of the sequences of actions and observations are equal: the law of $`(A_i, R_i)_{i \in \mathbb{N}}` under $`P` is equal to the law of $`(A'_i, R'_i)_{i \in \mathbb{N}}` under $`P'`.

This is Proposition 4.8 in {Informal.citep lattimore2020bandit}[].
:::

:::proof "isAlgEnvSeq_unique"
Uses: {uses "ionescu-tulcea"}[], {uses "law_step"}[], {uses "trajMeasure"}[]
:::




# Stationary environment

:::group "stationary_environment"
Stationary environments
:::

Recall that in a stationary environment, there exists a Markov kernel $`\nu : \mathcal{A} \rightsquigarrow \mathcal{R}` such that $`\nu'_0 = \nu` and for all $`t \in \mathbb{N}`, for all $`h_t \in (\mathcal{A} \times \mathcal{R})^{t+1}`, for all $`a \in \mathcal{A}`, $`\nu_t(h_t, a) = \nu(a)`.

Let $`(A, R, P)` be an algorithm-environment interaction in a stationary environment with kernel $`\nu`.

:::lemma_ "condDistrib_reward_stationaryEnv" (parent := "stationary_environment") (lean := "Learning.IsAlgEnvSeq.condDistrib_reward_stationaryEnv")
In a {uses "stationaryEnv"}[stationary environment], an {uses "IsAlgEnvSeq"}[algorithm-environment interaction] satisfies for any $`t \in \mathbb{N}`, $`P\left(R_t \mid A_t\right) = \nu`.
:::

:::proof "condDistrib_reward_stationaryEnv"
Uses: {uses "law_step"}[]
:::


::: lemma_ "condIndepFun_reward_hist_action" (parent := "stationary_environment") (lean := "Learning.IsAlgEnvSeq.condIndepFun_reward_hist_action")
For an {uses "IsAlgEnvSeq"}[algorithm-environment interaction] in a {uses "stationaryEnv"}[stationary environment], for any $`t \in \mathbb{N}`, the reward $`R_{t+1}` is conditionally independent of the history $`H_t` given the action $`A_{t+1}` (more succinctly, $`R_{t+1} \ind H_t \mid A_{t+1}`).
:::

:::proof "condIndepFun_reward_hist_action"
:::



# Probability space: Ionescu-Tulcea theorem

We saw that the distribution of the sequence of actions and observations in a suitable probability space is uniquely determined by the algorithm and the environment.
We now show that such a probability space actually exists: for any algorithm and environment, we build an algorithm-environment interaction.

:::group "ionescu_tulcea"
Ionescu-Tulcea theorem
:::

## Ionescu-Tulcea theorem

If we group together the policy of the algorithm and the kernel of the environment at each time step, we get a sequence of Markov kernels $`(\kappa_t)_{t \in \mathbb{N}}`, with $`\kappa_t : (\mathcal{A} \times \mathcal{R})^{t+1}  \rightsquigarrow (\mathcal{A} \times \mathcal{R})`.


We now abstract that situation and consider a sequence of measurable spaces $`(\Omega_t)_{t \in \mathbb{N}}`, a probability measure $`\mu` on $`\Omega_0` and a sequence of Markov kernels $`\kappa_t : \prod_{s=0}^t \Omega_s \rightsquigarrow \Omega_{t+1}`.
The Ionescu-Tulcea theorem builds a probability space from the sequence of kernels and the initial measure.


:::theorem "ionescu-tulcea" (parent := "ionescu_tulcea") (lean := "ProbabilityTheory.Kernel.traj")
Let $`(\Omega_t)_{t \in \mathbb{N}}` be a family of measurable spaces. Let $`(\kappa_t)_{t \in \mathbb{N}}` be a family of Markov kernels such that for any $`t`, $`\kappa_t` is a kernel from $`\prod_{i=0}^t \Omega_{i}` to $`\Omega_{t+1}`.
Then there exists a unique Markov kernel $`\xi : \Omega_0 \rightsquigarrow \prod_{i = 1}^{\infty} \Omega_{i}` such that for any $n \ge 1$,
$`\pi_{[1,n]*} \xi = \kappa_0 \otimes \ldots \otimes \kappa_{n-1}`.
Here $`\pi_{[1,n]} : \prod_{i=1}^{\infty} \Omega_i \to \prod_{i=1}^n \Omega_i` is the projection on the first $`n` coordinates.
:::

The Ionescu-Tulcea theorem in Mathlib {Informal.citep marion2025formalization}[] actually generates kernels $`\xi_t : \prod_{s=0}^t \Omega_s \rightsquigarrow \prod_{s=0}^{\infty} \Omega_s` for any $`t`, with the property that the kernels are the identity on the first $`t+1` coordinates.

:::definition "trajMeasure" (parent := "ionescu_tulcea") (lean := "ProbabilityTheory.Kernel.trajMeasure")
For $`\mu \in \mathcal{P}(\Omega_0)`, we call trajectory measure the probability measure $`\xi_0 \circ \mu` on $`\Omega_{\mathcal{T}} := \prod_{i=0}^{\infty} \Omega_i`.
We denote it by $`P_{\mathcal{T}}`.
The $`\mathcal{T}` subscript stands for _trajectory_.
:::


:::definition "IT.history" (parent := "ionescu_tulcea") (lean := "Learning.IT.hist, Learning.IT.step")
For $`t \in \mathbb{N}`, we denote by $`X_t \in \Omega_t` the random variable describing the time step $`t`, and by $`H_t \in \prod_{s=0}^t \Omega_s` the history up to time $`t`.
Formally, these are measurable functions on $`\Omega_{\mathcal{T}}`, defined by $`X_t(\omega) = \omega_t` and $`H_t(\omega) = (\omega_1, \ldots, \omega_t)`.
:::

Note: $`(X_t)_{t \in \mathbb{N}}` is the canonical process on $`\Omega_{\mathcal{T}}`. $`H_t` is equal to $`\pi_{[0,t]}`.


:::definition "IT.filtration" (parent := "ionescu_tulcea") (lean := "Learning.IT.filtration")
For $`t \in \mathbb{N}`, we denote by $`\mathcal{F}_t` the sigma-algebra generated by the {uses "IT.history"}[history] up to time $`t`: $`\mathcal{F}_t = \sigma(H_t)`.
The family $`(\mathcal{F}_t)_{t \in \mathbb{N}}` is a filtration on $`\Omega_{\mathcal{T}}`.
:::

$`(\mathcal{F}_t)_{t \in \mathbb{N}}` is the canonical filtration on $`\Omega_{\mathcal{T}}`, and is the natural filtration for the canonical process $`(X_t)_{t \in \mathbb{N}}`.

:::lemma_ "IT.adapted_history" (parent := "ionescu_tulcea") (lean := "Learning.IT.adapted_step, Learning.IT.adapted_hist")
The random variables $`X_t` and $`H_t` ({uses "IT.history"}[]) are $`\mathcal{F}_t`-measurable.
Said differently, the processes $`(X_t)_{t \in \mathbb{N}}` and $`(H_t)_{t \in \mathbb{N}}` are adapted to the {uses "IT.filtration"}[filtration] $`(\mathcal{F}_t)_{t \in \mathbb{N}}`.
:::


:::lemma_ "IT.condDistrib_X_add_one" (parent := "ionescu_tulcea") (lean := "ProbabilityTheory.Kernel.condDistrib_trajMeasure")
For any $`t \in \mathbb{N}`, $`P_{\mathcal{T}}\left(X_{t+1} \mid H_t\right) = \kappa_t`.

Uses: {uses "IT.history"}[], {uses "ionescu-tulcea"}[], {uses "trajMeasure"}[]
:::

:::proof "IT.condDistrib_X_add_one"
This is proved through the defining property of the conditional distribution: it is the almost surely unique Markov kernel $`\eta` such that $`((H_t)_* P_{\mathcal{T}}) \otimes \eta = (H_t, X_{t+1})_*P_{\mathcal{T}}`.

TODO: complete proof.
:::


:::lemma_ "IT.law_X_zero" (parent := "ionescu_tulcea") (lean := "Learning.IsAlgEnvSeq.hasLaw_step_zero")
The law of $`X_0` under $`P_{\mathcal{T}}` is $`\mu`.

Uses: {uses "IT.history"}[], {uses "trajMeasure"}[].
:::



## Case of an algorithm-environment interaction

We now go back to the setting of an algorithm interacting with an environment and suppose that $`\Omega_t = \mathcal{A} \times \mathcal{R}` for some measurable spaces $`\mathcal{A}` and $`\mathcal{R}`, and that for all $`t \in \mathbb{N}`, $`\kappa_t = \pi_t \otimes \nu_t` for policy kernels $`\pi_t : (\mathcal{A} \times \mathcal{R})^{t+1} \rightsquigarrow \mathcal{A}` and feedback kernels $`\nu_t : (\mathcal{A} \times \mathcal{R})^{t+1} \times \mathcal{A} \rightsquigarrow \mathcal{R}`.
Likewise, $`\mu = P_0 \otimes \nu'_0` for a probability measure $`P_0` on $`\mathcal{A}` and a Markov kernel $`\nu'_0 : \mathcal{A} \rightsquigarrow \mathcal{R}`.
The step random variable $`X_t` takes values in $`\mathcal{A} \times \mathcal{R}`.

:::definition "IT.actionReward" (parent := "ionescu_tulcea") (lean := "Learning.IT.action, Learning.IT.reward")
We write $`A_t` and $`R_t` for the projections of $`X_t` ({uses "IT.history"}[]) on $`\mathcal{A}` and $`\mathcal{R}` respectively.
$`A_t` is the action taken at time $`t` and $`R_t` is the reward received at time $`t`.
Formally, $`A_t(\omega) = \omega_{t,1}` and $`R_t(\omega) = \omega_{t,2}` for $`\omega = \prod_{t=0}^{+\infty}(\omega_{t,1}, \omega_{t,2}) \in \Omega_{\mathcal{T}} = \prod_{t=0}^{+\infty} \mathcal{A} \times \mathcal{R}`.
:::


:::lemma_ "IT.adapted_action_reward" (parent := "ionescu_tulcea") (lean := "Learning.IT.adapted_action, Learning.IT.adapted_reward")
The random variables $`A_t` and $`R_t` ({uses "IT.actionReward"}[]) are $`\mathcal{F}_t`-measurable.
Said differently, the processes $`(A_t)_{t \in \mathbb{N}}` and $`(R_t)_{t \in \mathbb{N}}` are adapted to the {uses "IT.filtration"}[filtration] $`(\mathcal{F}_t)_{t \in \mathbb{N}}`.
:::

:::proof "IT.adapted_action_reward"
Uses: {uses "IT.adapted_history"}[].
:::


We need to check that the random variables $`A_t` and $`R_t` have the expected conditional distributions.

:::lemma_ "IT.condDistrib_A_add_one" (parent := "ionescu_tulcea") (lean := "Learning.IT.condDistrib_action")
For any $`t \in \mathbb{N}`, $`P_{\mathcal{T}}\left(A_{t+1} \mid H_t\right) = \pi_t`.

Uses: {uses "environment"}[], {uses "algorithm"}[], {uses "ionescu-tulcea"}[], {uses "IT.actionReward"}[], {uses "trajMeasure"}[], {uses "IT.history"}[].
:::

:::proof "IT.condDistrib_A_add_one"
By {uses "IT.condDistrib_X_add_one"}[], $`P_{\mathcal{T}}\left(X_{t+1} \mid H_t\right) = \kappa_t = \pi_t \otimes \nu_t`.
Since $`A_{t+1}` is the projection of $`X_{t+1}` on $`\mathcal{A}`, $`P_{\mathcal{T}}\left(A_{t+1} \mid H_t\right)` is $`((H_t)_* P_{\mathcal{T}})`-almost surely equal to the projection of $`\kappa_t` on $`\mathcal{A}`, which is $`\pi_t`.
:::


:::lemma_ "IT.condDistrib_R_add_one" (parent := "ionescu_tulcea") (lean := "Learning.IT.condDistrib_reward")
For any $`t \in \mathbb{N}`, $`P_{\mathcal{T}}\left(R_{t+1} \mid H_t, A_{t+1}\right) = \nu_t`.

Uses: {uses "environment"}[], {uses "algorithm"}[], {uses "ionescu-tulcea"}[], {uses "IT.actionReward"}[], {uses "trajMeasure"}[], {uses "IT.history"}[].
:::

:::proof "IT.condDistrib_R_add_one"
It suffices to show that $`((H_t, A_{t+1})_* P_{\mathcal{T}}) \otimes \nu_t = (H_t, A_{t+1}, R_{t+1})_* P_{\mathcal{T}} = (H_t, X_{t+1})_* P_{\mathcal{T}}`.
By {uses "IT.condDistrib_X_add_one"}[], $`P_{\mathcal{T}}\left(X_{t+1} \mid H_t\right) = \pi_t \otimes \nu_t`.
Thus $`((H_t)_* P_{\mathcal{T}}) \otimes (\pi_t \otimes \nu_t) = (H_t, X_{t+1})_* P_{\mathcal{T}}`.

We thus have to prove that $`((H_t)_* P_{\mathcal{T}}) \otimes (\pi_t \otimes \nu_t) = ((H_t, A_{t+1})_* P_{\mathcal{T}}) \otimes \nu_t`.

By {uses "IT.condDistrib_A_add_one"}[], $`(H_t, A_{t+1})_* P_{\mathcal{T}} = (H_t)_* P_{\mathcal{T}} \otimes \pi_t`, and replacing this in the right-hand side gives the left-hand side (using associativity of the composition-product).
:::


:::lemma_ "IT.law_A_zero" (parent := "ionescu_tulcea") (lean := "Learning.IT.hasLaw_action_zero")
The law of $`A_0` under $`P_{\mathcal{T}}` is $`P_0`.

Uses: {uses "environment"}[], {uses "algorithm"}[], {uses "IT.actionReward"}[], {uses "trajMeasure"}[].
:::

:::proof "IT.law_A_zero"
$`X_0` has law $`\mu = P_0 \otimes \nu'_0`. $`A_0` is the projection of $`X_0` on the first space $`\mathcal{A}` and $`\nu_0'` is Markov, so $`A_0` has law $`P_0`.

Uses: {uses "ionescu-tulcea"}[], {uses "IT.history"}[], {uses "IT.law_X_zero"}[].
:::


:::lemma_ "IT.condDistrib_R_zero" (parent := "ionescu_tulcea") (lean := "Learning.IT.condDistrib_reward_zero")
$`P_{\mathcal{T}}\left(R_0 \mid A_0\right) = \nu'_0`.

Uses: {uses "environment"}[], {uses "algorithm"}[], {uses "IT.actionReward"}[], {uses "trajMeasure"}[], {uses "ionescu-tulcea"}[].
:::

:::proof "IT.condDistrib_R_zero"
To prove almost sure equality, it is enough to prove that $`(A_{0*} P_{\mathcal{T}}) \otimes P_{\mathcal{T}}\left(R_0 \mid A_0\right) = (A_{0*} P_{\mathcal{T}}) \otimes \nu'_0`.
By definition of the conditional distribution, we have $`(A_{0*} P_{\mathcal{T}}) \otimes P_{\mathcal{T}}\left(R_0 \mid A_0\right) = (A_0, R_0)_* P_{\mathcal{T}} = X_{0*} P_{\mathcal{T}}`.
By {uses "IT.law_X_zero"}[], $`X_{0*} P_{\mathcal{T}} = \mu = P_0 \otimes \nu'_0`.
By {uses "IT.law_A_zero"}[], $`A_{0*} P_{\mathcal{T}} = P_0`.
Thus the two sides are equal.
:::


:::theorem "isAlgEnvSeq_trajMeasure" (parent := "ionescu_tulcea") (lean := "Learning.IT.isAlgEnvSeq_trajMeasure")
In the {uses "trajMeasure"}[probability space $`(\Omega_{\mathcal{T}}, P_{\mathcal{T}})`] constructed from an algorithm $`\mathfrak{A}` and an environment $`\mathfrak{E}` as above, the sequences of random variables $`A : \mathbb{N} \to \Omega_{\mathcal{T}} \to \mathcal{A}` and $`R : \mathbb{N} \to \Omega_{\mathcal{T}} \to \mathcal{R}` form an {uses "IsAlgEnvSeq"}[algorithm-environment interaction] for $`\mathfrak{A}` and $`\mathfrak{E}`.

Uses: {uses "ionescu-tulcea"}[], {uses "IT.actionReward"}[].
:::

:::proof "isAlgEnvSeq_trajMeasure"
The four conditions of {uses "IsAlgEnvSeq"}[] are exactly the statements of {uses "IT.law_A_zero"}[], {uses "IT.condDistrib_R_zero"}[], {uses "IT.condDistrib_A_add_one"}[] and {uses "IT.condDistrib_R_add_one"}[].
:::



# Finitely many actions

:::group "finite_actions"
Finite action space
:::

When the number of actions is finite, it makes sense to count how many times each action was chosen up to a certain time.
We can also define the time step at which an action was chosen a certain number of times, and the value of the reward obtained when pulling an action for the $m$-th time.

:::definition "pullCount" (parent := "finite_actions") (lean := "Learning.pullCount")
For an action $`a \in \mathcal{A}` and a time $`t \in \mathbb{N}`, we denote by $`N_{t,a}` the number of times that action $`a` has been chosen before time $`t`, that is $`N_{t,a} = \sum_{s=0}^{t-1} \mathbb{I}\{A_s = a\}`.
:::

Note that the sum goes up to $`t-1`, so that $`N_{t,a}` counts the number of times action $`a` was chosen _before_ time $`t`.


*Remark: Building vs analyzing algorithms*

When we describe an algorithm, we give the data of the policies $`\pi_t`, which are functions of the partial history up to time $`t`, in $`(\mathcal{A} \times \mathcal{R})^{t+1}`.
That means that any tool used to define a policy must be a function defined on $`(\mathcal{A} \times \mathcal{R})^{t+1}`.
For example a definition of the empirical mean of an action must be a function $`t : \mathbb{N} \to (\mathcal{A} \times \mathcal{R})^{t+1} \to \mathbb{R}`.

When we analyze an algorithm, we work on the other hand on a probability space $`(\Omega, P)`, in which $`\Omega` could be for example $`(\mathcal{A} \times \mathcal{R})^{\mathbb{N}}`, the full history, which describes the whole sequence of actions and rewards.
As a stochastic process, the empirical mean of an action is a function $`\mathbb{N} \to (\mathcal{A} \times \mathcal{R})^{\mathbb{N}} \to \mathbb{R}`.

Thus there are two similar but still distinct types of objects: those defined on the partial history, which are used to build algorithms, and those defined on a generic probability space (the full history in the Ionescu-Tulcea construction), which are used to analyze algorithms.


:::lemma_ "pullCount_basic" (parent := "finite_actions") (lean := "Learning.pullCount_zero, Learning.pullCount_mono, Learning.pullCount_add_one, Learning.pullCount_le, Learning.pullCount_congr")
We note the following basic properties of {uses "pullCount"}[$`N_{t,a}`]:
- $`N_{0,a} = 0`.
- $`N_{t,a}` is non-decreasing in $`t`.
- $`N_{t + 1, A_t} = N_{t, A_t} + 1` and for $`a \ne A_t`, $`N_{t + 1, a} = N_{t, a}`.
- $`N_{t, a} \le t`.
- If for all $`s \le t`, $`A_s(\omega) = A_s(\omega')`, then $`N_{t+1, a}(\omega) = N_{t+1, a}(\omega')`.
:::


:::lemma_ "predictable_pullCount" (parent := "finite_actions") (lean := "Learning.isPredictable_pullCount")
Let $`a \in \mathcal{A}`. The process {uses "pullCount"}[$`(N_{t,a})_{t \in \mathbb{N}}`] is predictable with respect to the {uses "IsAlgEnvSeq.filtration"}[filtration $`\mathcal{F}`] of the algorithm-environment interaction.
:::

:::proof "predictable_pullCount"
Uses: {uses "history"}[], {uses "pullCount_basic"}[]
:::


:::definition "stepsUntil" (parent := "finite_actions") (lean := "Learning.stepsUntil")
For an action $`a \in \mathcal{A}` and a time $`n \in \mathbb{N}`, we denote by $`T_{n,a} \in \mathbb{N} \cup \{+\infty\}` the time at which action $`a` was chosen for the $`n`-th time, that is $`T_{n,a} = \min\{s \in \mathbb{N} \mid N_{s+1,a} = n\}`.
Note that $`T_{n, a}` can be infinite if the action is not chosen $`n` times.

Uses: {uses "pullCount"}[]
:::

By definition, $`T_{n, a}` is the hitting time of the set $`\{n\}` by the process $`t \mapsto N_{t+1,a}`, which is adapted since $`N_{t,a}` is predictable.
Equivalently, $`T_{n, a}` is the hitting time of the set $`[n, +\infty]` by that process.


:::lemma_ "stepsUntil_basic" (parent := "finite_actions") (lean := "Learning.stepsUntil_zero_of_ne, Learning.stepsUntil_zero_of_eq, Learning.stepsUntil_pullCount_le, Learning.stepsUntil_pullCount_eq, Learning.action_stepsUntil, Learning.pullCount_stepsUntil_add_one, Learning.pullCount_stepsUntil")
We note the following basic properties of {uses "stepsUntil"}[$`T_{n,a}`]:
- $`T_{0,a} = 0` for $`a \ne A_0`. $`T_{0,A_0} = \infty`.
- $`T_{N_{t+1, a}, a} \le t`.
- $`T_{N_{t + 1, A_t}, A_t} = t`.
- If $`T_{n, a} \ne \infty` and $`n > 0`, then $`A_{T_{n, a}} = a`.
- If $`T_{n, a} \ne \infty`, then $`N_{T_{n, a} + 1, a} = n`.
- If $`T_{n, a} \ne \infty` and $`n > 0`, then $`N_{T_{n, a}, a} = n - 1`.
- If for all $`s \le t`, $`A_s(\omega) = A_s(\omega')`, then $`T_{n, a}(\omega) = t \iff T_{n, a}(\omega') = t`.
:::

:::proof "stepsUntil_basic"
Uses: {uses "pullCount_basic"}[]
:::


:::lemma_ "isStoppingTime_stepsUntil" (parent := "finite_actions") (lean := "Learning.isStoppingTime_stepsUntil")
Let $`a \in \mathcal{A}`. For any $`n > 0`, the random variable {uses "stepsUntil"}[$`T_{n,a}`] is a stopping time with respect to the {uses "IsAlgEnvSeq.filtration"}[filtration $`\mathcal{F}`].
:::

:::proof "isStoppingTime_stepsUntil"
A hitting time of a set by an adapted process is a stopping time.

Uses: {uses "pullCount_basic"}[]
:::


Let $`\Omega' = \mathcal{R}^{\mathbb{N} \times \mathcal{A}}` and let $`\Omega = \Omega_{\mathcal{T}} \times \Omega'` (which will be an extension of the trajectory probability space once we choose a measure on $`\Omega'`).
Let $`Z_{n, a} : \Omega \to \mathcal{R}` be the projection on the coordinate indexed by $`(n,a)` in $`\Omega'`.
Extending the probability space in that way allows us to define without ambiguity the reward received when choosing an action for the $`n`-th time, even if that action is never actually chosen $`n` times.


:::definition "rewardByCount" (parent := "finite_actions") (lean := "Learning.rewardByCount")
We define $`Y_{n, a} = R_{T_{n,a}} \mathbb{I}\{T_{n, a} < \infty\} + Z_{n,a} \mathbb{I}\{T_{n, a} = \infty\}`, the reward received when choosing action $`a` for the $`n`-th time if {uses "stepsUntil"}[that time] is finite, and equal to $`Z_{n,a}` otherwise.
In that expression, we see $`R_{T_{n,a}}` and $`T_{n, a}` as random variables on $`\Omega` instead of $`\Omega_{\mathcal{T}}`.
:::


:::lemma_ "rewardByCount_pullCount" (parent := "finite_actions") (lean := "Learning.rewardByCount_pullCount_add_one_eq_reward")
$`Y_{N_{t, A_t} + 1, A_t} = R_t`.

Uses: {uses "rewardByCount"}[], {uses "pullCount"}[]
:::

:::proof "rewardByCount_pullCount"
This is perhaps hard to parse at first sight, but it follows directly from the definitions.
At time $t$, the action chosen is $`A_t` and we see a reward $`R_t`.
That action had already been chosen $`N_{t, A_t}` times before time $t$, so the reward $`R_t` is the reward received when choosing action $`A_t` for the $`(N_{t, A_t} + 1)`-th time, which is $`Y_{N_{t, A_t} + 1, A_t}` by definition.

Uses: {uses "stepsUntil_basic"}[].
:::



# Scalar rewards

TODO: change the name _reward_ to _observation_ throughout the chapter?

We now focus on the case where the reward space is $`\mathcal{R} = \mathbb{R}`.

:::group "scalar_rewards"
Scalar rewards
:::

:::definition "sumRewards" (parent := "scalar_rewards") (lean := "Learning.sumRewards")
Let $`S_{t, a} = \sum_{s=0}^{t-1} R_s \mathbb{I}\{A_s = a\}` be the sum of the rewards obtained by chosing action $`a` before time $`t`.
:::


:::definition "empMean" (parent := "scalar_rewards") (lean := "Learning.empMean")
Let $`\hat{\mu}_{t, a} = \frac{S_{t, a}}{N_{t, a}} = \frac{1}{N_{t,a}} \sum_{s=0}^{t-1} R_s \mathbb{I}\{A_s = a\}` if $`N_{t, a} > 0`, and $`\hat{\mu}_{t, a} = 0` otherwise.
This is the empirical mean of the rewards obtained by choosing action $`a` before time $`t`.

Uses: {uses "sumRewards"}[], {uses "pullCount"}[]
:::

Note: in bandit papers it is common to (implicitly) define the empirical mean as $`+\infty` when the action was never chosen, but in Lean it has to be a real number, and the Lean default value for division by zero is $`0`.


:::lemma_ "isPredictable_sumRewards" (parent := "scalar_rewards") (lean := "Learning.IsAlgEnvSeq.isPredictable_sumRewards, Learning.IsAlgEnvSeq.isPredictable_empMean")
The processes {uses "sumRewards"}[$`(S_{t,a})_{t \in \mathbb{N}}`] and {uses "empMean"}[$`(\hat{\mu}_{t,a})_{t \in \mathbb{N}}`] are predictable with respect to the {uses "IsAlgEnvSeq.filtration"}[filtration $`\mathcal{F}`] of the algorithm-environment interaction.
:::

:::proof "isPredictable_sumRewards"
Uses: {uses "predictable_pullCount"}[], {uses "sumRewards"}[], {uses "empMean"}[]
:::


The following lemma is very useful to relate the two ways of indexing the rewards: by time step and by pull count.

:::lemma_ "sum_rewardByCount" (parent := "scalar_rewards") (lean := "Learning.sum_rewardByCount_eq_sumRewards")
The sum of the first {uses "pullCount"}[$`N_{t, a}`] rewards received when choosing action $`a` is equal to the sum of the rewards obtained by choosing action $`a` before time $`t`:
$$`\sum_{n=1}^{N_{t, a}} Y_{n, a} = S_{t,a} \: .`

Uses: {uses "rewardByCount"}[], {uses "sumRewards"}[].
:::

:::proof "sum_rewardByCount"
Uses:  {uses "rewardByCount_pullCount"}[].
:::
