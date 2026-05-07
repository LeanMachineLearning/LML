import Verso
import VersoManual
import VersoBlueprint
import LeanMachineLearning.SequentialLearning.Algorithms.RoundRobin
import LeanMachineLearning.SequentialLearning.Deterministic
import LeanMachineLearning.SequentialLearning.FiniteActions
import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
import LeanMachineLearning.SequentialLearning.StationaryEnv
import LeanMachineLearning.Online.Bandit.Algorithms.ETC
import LeanMachineLearning.Online.Bandit.Algorithms.UCB
import LeanMachineLearning.Online.Bandit.ArrayProbSpace
import LeanMachineLearning.Online.Bandit.Regret
import LeanMachineLearning.Online.Bandit.RewardByCountMeasure
import LeanMachineLearning.Online.Bandit.SumRewards
import LeanMachineLearning.Probability.Moments.SubGaussian
import LMLBlueprint.References
import LMLBlueprint.TeXPrelude
import Mathlib.Probability.Moments.SubGaussian

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Bandit algorithms" =>

:::group "banditAlgorithms"
Bandit algorithms
:::


# Round-Robin

This is not an interesting bandit algorithm per se, but it is used as a subroutine in other algorithms and can be a simple baseline.
This algorithm simply cycles through the arms in order.

:::definition "roundRobinAlgorithm" (parent := "banditAlgorithms") (lean := "Learning.RoundRobin.nextAction, Learning.roundRobinAlgorithm")
The Round-Robin algorithm is the {uses "detAlgorithm"}[deterministic algorithm] defined as follows: at time $`t \in \mathbb{N}`, $`A_t = t \mod K`.
:::


:::lemma_ "pullCount_roundRobinAlgorithm" (parent := "banditAlgorithms") (lean := "Learning.RoundRobin.pullCount_mul")
For the Round-Robin algorithm, for any arm $`a \in [K]`, at time $`Km` we have
$$`
  N_{Km,a} = m \: .
`

Uses: {uses "stationaryEnv"}[], {uses "IsAlgEnvSeq"}[] , {uses "pullCount"}[], {uses "roundRobinAlgorithm"}[].
:::

:::proof "pullCount_roundRobinAlgorithm"
  Uses {uses "environment"}[], {uses "history"}[], {uses "pullCount_basic"}[], {uses "roundRobinAlgorithm"}[]
:::


TODO: regret.




# Explore-Then-Commit

Note: times start at 0 to be consistent with Lean.

Note: we will describe the algorithm by writing $`A_t = ...`, but our formal bandit model needs a policy $`\pi_t` that gives the distribution of the arm to pull. What me mean is that $`\pi_t` is a Dirac distribution at that arm.

:::definition "etcAlgorithm" (parent := "banditAlgorithms") (lean := "Bandits.ETC.nextArm, Bandits.etcAlgorithm")
The Explore-Then-Commit (ETC) algorithm with parameter $`m \in \mathbb{N}` is the {uses "detAlgorithm"}[deterministic algorithm] defined as follows:
1. for $`t < Km`, $`A_t = t \mod K` (pull each arm $`m` times),
2. compute $`\hat{A}_m^* = \arg\max_{a \in [K]} \hat{\mu}_a`, where $`\hat{\mu}_a = \frac{1}{m} \sum_{t=0}^{Km-1} \mathbb{I}(A_t = a) X_t` is the empirical mean of the rewards for arm $`a`,
3. for $`t \ge Km`, $`A_t = \hat{A}_m^*` (pull the empirical best arm).
:::

:::lemma_ "ETC.isAlgEnvSeqUntil_roundRobinAlgorithm" (parent := "banditAlgorithms") (lean := "Bandits.ETC.isAlgEnvSeqUntil_roundRobinAlgorithm")

An {uses "IsAlgEnvSeq"}[algorithm-environment sequence] for the {uses "etcAlgorithm"}[Explore-Then-Commit algorithm] with parameter $`m` is an algorithm-environment sequence for the {uses "roundRobinAlgorithm"}[Round-Robin algorithm] until time $`Km - 1`.
That is, ETC plays the same as Round-Robin until time $`Km - 1`.

Uses {uses "stationaryEnv"}[].
:::


:::lemma_ "pullCount_etcAlgorithm" (parent := "banditAlgorithms") (lean := "Bandits.ETC.pullCount_of_ge")
For the {uses "etcAlgorithm"}[Explore-Then-Commit algorithm] with parameter $`m`, for any arm $`a \in [K]` and any time $`t \ge Km`, we have
$$`
  N_{t,a}
  = m + (t - Km) \mathbb{I}\{\hat{A}_m^* = a\}
  \: .
`

Uses: {uses "stationaryEnv"}[], {uses "IsAlgEnvSeq"}[], {uses "pullCount"}[].
:::

:::proof "pullCount_etcAlgorithm"
  Uses: {uses "pullCount_roundRobinAlgorithm"}[], {uses "ETC.isAlgEnvSeqUntil_roundRobinAlgorithm"}[]
:::

:::lemma_ "sumRewards_bestArm_le_of_arm_mul_eq" (parent := "banditAlgorithms") (lean := "Bandits.ETC.sumRewards_bestArm_le_of_arm_mul_eq")
If $`\hat{A}_m^* = a`, then we have $`S_{Km, a^*} \le S_{Km, a}`.

Uses: {uses "stationaryEnv"}[], {uses "IsAlgEnvSeq"}[], {uses "sumRewards"}[], {uses "etcAlgorithm"}[]
:::

:::proof "sumRewards_bestArm_le_of_arm_mul_eq"
  Uses: {uses "environment"}[], {uses "history"}[], {uses "pullCount"}[], {uses "empMean"}[], {uses "etcAlgorithm"}[]
:::


:::lemma_ "prob_etc_error_le_exp" (parent := "banditAlgorithms") (lean := "Bandits.ETC.prob_arm_mul_eq_le")
Suppose that $`\nu(a)` is $`\sigma^2`-{uses "subGaussian"}[sub-Gaussian] for all arms $`a \in [K]`.
Then for the {uses "etcAlgorithm"}[Explore-Then-Commit algorithm] with parameter $`m`, for any arm $`a \in [K]` with $`\Delta_a > 0`, we have $`P(\hat{A}_m^* = a) \le \exp\left(- \frac{m \Delta_a^2}{4 \sigma^2}\right)`.

Uses: {uses "stationaryEnv"}[], {uses "IsAlgEnvSeq"}[], {uses "gap"}[]
:::

:::proof "prob_etc_error_le_exp"
By {uses "sumRewards_bestArm_le_of_arm_mul_eq"}[],
$$`
  P(\hat{A}_m^* = a)
  \le P(S_{Km, a} \ge S_{Km, a^*})
  \: .
`
By {uses "prob_sumRewards_le_sumRewards_le"}[], and then the concentration inequality of {uses "probReal_sum_le_sum_streamMeasure"}[] we have
$$`
  P\left(S_{Km, a^*} \le S_{Km, a}\right)
  &\le (\otimes_a \nu(a))^{\otimes \mathbb{N}} \left( \sum_{s=0}^{m-1} \omega_{s, a^*} \le \sum_{s=0}^{m-1} \omega_{s, a} \right)
  \\
  &\le \exp\left( -m \frac{\Delta_a^2}{4 \sigma^2} \right)
  \: .
`

Uses: {uses "environment"}[], {uses "pullCount"}[], {uses "etcAlgorithm"}[]
:::


:::theorem "regret_etc_le" (parent := "banditAlgorithms") (lean := "Bandits.ETC.regret_le")
Suppose that $`\nu(a)` is $`\sigma^2`-{uses "subGaussian"}[sub-Gaussian] for all arms $`a \in [K]`.
Then for {uses "etcAlgorithm"}[Explore-Then-Commit algorithm] with parameter $`m`, the expected regret after $`T` pulls with $`T \ge Km` is bounded by
$$`
  P[R_T]
  \le m \sum_{a=1}^K \Delta_a + (T - Km) \sum_{a=1}^K \Delta_a \exp\left(- \frac{m \Delta_a^2}{4 \sigma^2}\right)
  \: .
`

Uses: {uses "stationaryEnv"}[], {uses "regret"}[], {uses "IsAlgEnvSeq"}[], {uses "gap"}[]
:::

:::proof "regret_etc_le"
By {uses "regret_eq_sum_pullCount_mul_gap"}[], we have $`P[R_T] = \sum_{a=1}^K P\left[N_{T,a}\right] \Delta_a`~.
It thus suffices to bound $`P[N_{T,a}]` for each arm $`a` with $`\Delta_a > 0`.
It suffices to prove that
$$`
  P[N_{T,a}]
  \le m + (T - Km) \exp\left(- \frac{m \Delta_a^2}{4 \sigma^2}\right)
  \: .
`

By {uses "pullCount_etcAlgorithm"}[],
$$`
  N_{T,a}
  = m + (T - Km) \mathbb{I}\{\hat{A}_m^* = a\}
  \: .
`

It thus suffices to prove the inequality $`P(\hat{A}_m^* = a) \le \exp\left(- \frac{m \Delta_a^2}{4 \sigma^2}\right)` for $`\Delta_a > 0`.
This is done in {uses "prob_etc_error_le_exp"}[].


Uses: {uses "integral_regret_eq_sum_mul"}[], {uses "pullCount_basic"}[],
:::


# UCB

:::definition "ucbAlgorithm" (parent := "banditAlgorithms") (lean := "Bandits.UCB.nextArm, Bandits.ucbAlgorithm")
The UCB algorithm with parameter $`c \in \mathbb{R}_+` is the {uses "detAlgorithm"}[deterministic algorithm] defined as follows:
1. for $`t < K`, $`A_t = t \mod K` (pull each arm once),
2. for $`t \ge K`, $`A_t = \arg\max_{a \in [K]} \left( \hat{\mu}_{t,a} + \sqrt{\frac{2 c \log(t + 1)}{N_{t,a}}} \right)`, where $`\hat{\mu}_{t,a} = \frac{1}{N_{t,a}} \sum_{s=0}^{t-1} \mathbb{I}(A_s = a) X_s` is the empirical mean of the rewards for arm `a`.
:::


Note: the argmax in the second step is chosen in a measurable way.


:::lemma_ "UCB.isAlgEnvSeqUntil_roundRobinAlgorithm" (parent := "banditAlgorithms") (lean := "Bandits.UCB.isAlgEnvSeqUntil_roundRobinAlgorithm")
An {uses "IsAlgEnvSeq"}[algorithm-environment sequence] for the {uses "ucbAlgorithm"}[UCB algorithm] is an algorithm-environment sequence for the {uses "roundRobinAlgorithm"}[Round-Robin algorithm] until time $`K - 1`.
That is, UCB plays the same as Round-Robin until time $`K - 1`.

Uses: {uses "stationaryEnv"}[].
:::


:::lemma_ "ucbIndex_le_ucbIndex_arm" (parent := "banditAlgorithms") (lean := "Bandits.UCB.ucbIndex_le_ucbIndex_arm")
For the {uses "ucbAlgorithm"}[UCB algorithm], for all time $`t \ge K` and arm $`a \in [K]`, we have
$$`
  \hat{\mu}_{t,a} + \sqrt{\frac{2 c \log(t + 1)}{N_{t,a}}}
  \le \hat{\mu}_{t,A_t} + \sqrt{\frac{2 c \log(t + 1)}{N_{t,A_t}}}
  \: .
`

Uses: {uses "stationaryEnv"}[], {uses "IsAlgEnvSeq"}[], {uses "pullCount"}[], {uses "empMean"}[]
:::

:::proof "ucbIndex_le_ucbIndex_arm"
By definition of the algorithm.
:::


:::lemma_ "gap_arm_le_two_mul_ucbWidth" (parent := "banditAlgorithms") (lean := "Bandits.UCB.gap_arm_le_two_mul_ucbWidth, Bandits.UCB.pullCount_arm_le")
Suppose that we have the 3 following conditions:
1. $`\mu^* \le \hat{\mu}_{t, a^*} + \sqrt{\frac{2 c \log(t + 1)}{N_{t,a^*}}}`,
2. $`\hat{\mu}_{t,A_t} - \sqrt{\frac{2 c \log(t + 1)}{N_{t,A_t}}} \le \mu_{A_t}`,
3. $`\hat{\mu}_{t, a^*} + \sqrt{\frac{2 c \log(t + 1)}{N_{t,a^*}}} \le \hat{\mu}_{t,A_t} + \sqrt{\frac{2 c \log(t + 1)}{N_{t,A_t}}}`.

Then if $`N_{t,A_t} > 0` we have
$$`
  \Delta_{A_t}
  \le 2 \sqrt{\frac{2 c \log(t + 1)}{N_{t,A_t}}}
  \: .
`

And in turn, if $`\Delta_{A_t} > 0` we get
$$`
  N_{t,A_t}
  \le \frac{8 c \log(t + 1)}{\Delta_{A_t}^2}
  \: .
`

Note that the third condition is always satisfied for UCB by {uses "ucbIndex_le_ucbIndex_arm"}[], but this lemma, as stated, is independent of the UCB algorithm.

Uses: {uses "pullCount"}[], {uses "gap"}[], {uses "empMean"}[].
:::


:::lemma_ "prob_ucbIndex_le" (parent := "banditAlgorithms") (lean := "Bandits.UCB.prob_ucbIndex_le")
Suppose that $`\nu(a)` is $`\sigma^2`-{uses "subGaussian"}[sub-Gaussian] for all arms $`a \in [K]`.
Let $`c \ge 0` be a real number.
Then for any time $`n \in \mathbb{N}` and any arm $`a \in [K]`, we have
$$`
  P\left(0 < N_{n, a} \ \wedge \ \hat{\mu}_{n, a} + \sqrt{\frac{2 c \sigma^2 \log(n + 1)}{N_{n,a}}} \le \mu_a\right)
  \le \frac{1}{(n + 1)^{c - 1}}
  \: .
`

And also,
$$`
  P\left(0 < N_{n, a} \ \wedge \ \hat{\mu}_{n, a} - \sqrt{\frac{2 c \sigma^2 \log(n + 1)}{N_{n,a}}} \ge \mu_a\right)
  \le \frac{1}{(n + 1)^{c - 1}}
  \: .
`

Uses: {uses "stationaryEnv"}[], {uses "IsAlgEnvSeq"}[], {uses "pullCount"}[], {uses "empMean"}[]
:::

:::proof "prob_ucbIndex_le"
  Uses: {uses "prob_sum_le_sqrt_log"}[], {uses "ionescu-tulcea"}[], {uses "prob_pullCount_prod_sumRewards_mem_le"}[].
:::


:::lemma_ "pullCount_le_add_three" (parent := "banditAlgorithms")
For $`C` a natural number, for any time $`n \in \mathbb{N}` and any arm $`a \in [K]`, we have
$$`
  N_{n,a}
  &\le C + 1
  \\&\quad +
      \sum_{s=1}^{n-1} \mathbb{I}\{A_s = a \ \wedge \ C < N_{s,a} \ \wedge \
        \mu^* \le \hat{\mu}_{s, a^*} + \sqrt{\frac{2 c \sigma^2 \log(s + 1)}{N_{s,a^*}}} \ \wedge \
        \hat{\mu}_{s, A_s} - \sqrt{\frac{2 c \sigma^2 \log(s + 1)}{N_{s,A_s}}} \le \mu_{A_s}\}
  \\&\quad +
      \sum_{s=1}^{n-1}
        \mathbb{I}\{0 < N_{s, a^*} \ \wedge \ \hat{\mu}_{s, a^*} + \sqrt{\frac{2 c \sigma^2 \log(s + 1)}{N_{s,a^*}}} <
          \mu^*\}
  \\&\quad +
      \sum_{s=1}^{n-1}
        \mathbb{I}\{0 < N_{s, a} \ \wedge \ \mu_a <
          \hat{\mu}_{s, a} - \sqrt{\frac{2 c \sigma^2 \log(s + 1)}{N_{s,a}}}\}
`

Uses: {uses "pullCount"}[], {uses "empMean"}[], {uses "stationaryEnv"}[], {uses "IsAlgEnvSeq"}[], {uses "ucbAlgorithm"}[].
:::

:::proof "pullCount_le_add_three"
  Uses: {uses "environment"}[], {uses "ucbAlgorithm"}[], {uses "pullCount_basic"}[]
:::


:::lemma_ "some_sum_eq_zero" (parent := "banditAlgorithms")
For the {uses "ucbAlgorithm"}[UCB algorithm] with parameter $`c \sigma^2 \ge 0`, for any time $`n \in \mathbb{N}` and any arm $`a \in [K]` with positive gap, the first sum in {uses "pullCount_le_add_three"}[] is equal to zero for positive $`C` such that $`C \ge \frac{8 c \sigma^2 \log(n + 1)}{\Delta_a^2}`.

Uses: {uses "stationaryEnv"}[], {uses "IsAlgEnvSeq"}[], {uses "ucbAlgorithm"}[], {uses "pullCount"}[], {uses "gap"}[], {uses "empMean"}[].

The Lean declaration is "Bandits.UCB.some\_sum\_eq\_zero" but adding it causes a strange error, so I removed it.
:::

:::proof "some_sum_eq_zero"
  Uses: {uses "environment"}[], {uses "ucbAlgorithm"}[], {uses "ucbIndex_le_ucbIndex_arm"}[], {uses "pullCount_basic"}[], {uses "gap_arm_le_two_mul_ucbWidth"}[]
:::


:::lemma_ "expectation_pullCount_le" (parent := "banditAlgorithms") (lean := "Bandits.UCB.expectation_pullCount_le")
Suppose that $`\nu(a)` is $`\sigma^2`-{uses "subGaussian"}[sub-Gaussian] for all arms $`a \in [K]`.
For the {uses "ucbAlgorithm"}[UCB algorithm] with parameter $`c \sigma^2 > 0`, for any time $`n \in \mathbb{N}` and any arm $`a \in [K]` with positive {uses "gap"}[gap], we have
$$`
  P[N_{n,a}]
  \le \frac{8 c \sigma^2 \log(n + 1)}{\Delta_a^2} + 2 + 2 \sum_{s=0}^{n-1} \frac{1}{(s + 1)^{c - 1}}
  \: .
`

Uses: {uses "stationaryEnv"}[], {uses "IsAlgEnvSeq"}[], {uses "pullCount"}[].
:::

:::proof "expectation_pullCount_le"
  Uses: {uses "some_sum_eq_zero"}[], {uses "prob_ucbIndex_le"}[], {uses "pullCount_basic"}[], {uses "pullCount_le_add_three"}[]
:::


:::lemma_ "ucb_regret_le" (parent := "banditAlgorithms") (lean := "Bandits.UCB.regret_le")
Suppose that $`\nu(a)` is $`\sigma^2`-{uses "subGaussian"}[sub-Gaussian] for all arms $`a \in [K]`.
For the {uses "ucbAlgorithm"}[UCB algorithm] with parameter $`c \sigma^2 > 0`, for any time $`n \in \mathbb{N}`, we have
$$`
  P[R_n]
  \le \sum_{a : \Delta_a > 0} \left(\frac{8 c \sigma^2 \log(n + 1)}{\Delta_a} + 2 \Delta_a\left(1 + \sum_{s=0}^{n-1} \frac{1}{(s + 1)^{c - 1}}\right)\right)
  \: .
`

Uses: {uses "stationaryEnv"}[], {uses "regret"}[], {uses "IsAlgEnvSeq"}[], {uses "gap"}[].
:::

:::proof "ucb_regret_le"
  Uses: {uses "integral_regret_eq_sum_mul"}[], {uses "pullCount_basic"}[], {uses "expectation_pullCount_le"}[]
:::

TODO: for $`c > 2`, the sum converges to a constant, so we get a logarithmic regret bound.
