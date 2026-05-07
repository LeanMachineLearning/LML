import Verso
import VersoManual
import VersoBlueprint
import LeanMachineLearning.SequentialLearning.Deterministic
import LeanMachineLearning.SequentialLearning.FiniteActions
import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
import LeanMachineLearning.SequentialLearning.StationaryEnv
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

#doc (Manual) "Concentration inequalities" =>

# Sub-Gaussian random variables

:::group "subGaussian"
Sub-Gaussian random variables
:::

:::definition "subGaussian" (parent := "subGaussian") (lean := "ProbabilityTheory.HasSubgaussianMGF")
A real valued random variable $`X` is $`\sigma^2`-sub-Gaussian if for any $`\lambda \in \mathbb{R}`,
$$`
  P\left[e^{\lambda X}\right]
  \le e^{\frac{\lambda^2 \sigma^2}{2}}
  \: .
`
:::


:::lemma_ "subGaussian_add_of_indepFun" (parent := "subGaussian") (lean := "ProbabilityTheory.HasSubgaussianMGF.add_of_indepFun")
If $`X` is $`\sigma_1^2`-{uses "subGaussian"}[sub-Gaussian] and $`Y` is $`\sigma_2^2`-sub-Gaussian, and $`X` and $`Y` are independent, then $`X + Y` is $`(\sigma_1^2 + \sigma_2^2)`-sub-Gaussian.
:::


:::lemma_ "hoeffding_one" (parent := "subGaussian") (lean := "ProbabilityTheory.HasSubgaussianMGF.measure_ge_le")
For $`X` a $`\sigma^2`-{uses "subGaussian"}[sub-Gaussian] random variable, for any $`t \ge 0`,
$$`
  P(X \ge t)
  \le \exp\left(- \frac{t^2}{2 \sigma^2}\right)
  \: .
`
:::


:::theorem "hoeffding" (parent := "subGaussian") (lean := "ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun")
Let $`X_1, \ldots, X_n` be independent random variables such that $`X_i` is $`\sigma_i^2`-{uses "subGaussian"}[sub-Gaussian] for $`i \in [n]`.
Then for any $`t \ge 0`,
$$`
  P\left(\sum_{i=1}^n X_i \ge t\right)
  \le \exp\left(- \frac{t^2}{2 \sum_{i=1}^n \sigma_i^2}\right)
  \: .
`
:::

:::proof "hoeffding"
Uses: {uses "subGaussian_add_of_indepFun"}[], {uses "hoeffding_one"}[].
:::


:::lemma_ "measure_sum_le_sum_le'" (parent := "subGaussian")
Let $`X_1, \ldots, X_n` be random variables such that $`X_i - P[X_i]` is $`\sigma_{X,i}^2`-{uses "subGaussian"}[sub-Gaussian] for $`i \in [n]`.
Let $`Y_1, \ldots, Y_m` be random variables such that $`Y_i - P[Y_i]` is $`\sigma_{Y,i}^2`-{uses "subGaussian"}[sub-Gaussian] for $`i \in [m]`.
Suppose further that the vectors $`X` and $`Y` are independent and that $`\sum_{i = 1}^m P[Y_i] \le \sum_{i = 1}^n P[X_i]`.
Then
$$`
  P\left(\sum_{i=1}^m Y_i \ge \sum_{i=1}^n X_i\right)
  \le \exp\left(- \frac{\left(\sum_{i = 1}^n P[X_i] - \sum_{i=1}^m P[Y_i]\right)^2}{2 \sum_{i=1}^n (\sigma_{X,i}^2 + \sigma_{Y,i}^2)}\right)
  \: .
`

This is "ProbabilityTheory.HasSubgaussianMGF.measure\_sum\_le\_sum\_le'" in Lean, but I get a strange error if I add that information.
:::

:::proof "measure_sum_le_sum_le'"
Uses: {uses "subGaussian_add_of_indepFun"}[], {uses "hoeffding_one"}[].
:::



# Concentration of the sums of rewards in bandit models

:::group "concentrationBandits"
Concentration of the sums of rewards in bandit models
:::

:::lemma_ "identDistrib_pullCount_prod_sumRewards" (parent := "concentrationBandits") (lean := "Bandits.ArrayModel.identDistrib_pullCount_prod_sumRewards")
In the array model, for $`t \in \mathbb{N}`, the random variable $`(N_{t,a}, S_{t, a})_{a \in \mathcal{A}}` has the same distribution as $`(N_{t,a}, \sum_{s=0}^{N_{t,a}-1} \omega_{2, s, a})_{a \in \mathcal{A}}`.

Uses: {uses "arrayMeasure"}[] ,{uses "AM.history"}[], {uses "algorithm"}[], {uses "sumRewards"}[], {uses "pullCount"}[].
:::

:::proof "identDistrib_pullCount_prod_sumRewards"
Uses: {uses "AM.history"}[], {uses "stepsUntil_basic"}[], {uses "ionescu-tulcea"}[], {uses "algFunction"}[], {uses "AM.measurable_hist"}[], {uses "rewardByCount"}[], {uses "pullCount_basic"}[], {uses "stepsUntil"}[], {uses "sum_rewardByCount"}[].
:::


:::lemma_ "AM.identDistrib_sum_range_snd" (parent := "concentrationBandits") (lean := "Bandits.ArrayModel.identDistrib_sum_range_snd")
In the {uses "arrayMeasure"}[array model], for $`k \in \mathbb{N}`, the random variable $`\sum_{s=0}^{k-1} \omega_{2, s, a}` has the same distribution as a sum of $`k` i.i.d. random variables with law $`\nu(a)`.
:::

:::proof "AM.identDistrib_sum_range_snd"
By definition of {uses "arrayMeasure"}[$`P_{\mathcal{A}}`].
:::


:::lemma_ "prob_pullCount_prod_sumRewards_mem_le" (parent := "concentrationBandits") (lean := "Bandits.ArrayModel.prob_pullCount_prod_sumRewards_mem_le, Bandits.prob_pullCount_prod_sumRewards_mem_le")
In the {uses "arrayMeasure"}[array model], for $`t \in \mathbb{N}`, $`a \in \mathcal{A}`, and a measurable set $`B \subseteq \mathbb{N} \times \mathbb{R}`,
$$`
  P_{\mathcal{A}}\left((N_{t,a}, S_{t, a}) \in B\right)
  \le \sum_{k < t, \exists r, (k, r) \in B} \nu(a)^{\otimes \mathbb{N}} \left(\sum_{s=0}^{k-1} \omega_{s} \in \{x \mid \exists n, (n, x) \in B\}\right)
  \: .
`
As a consequence, this also holds for any algorithm-environment sequence.

Uses: {uses "AM.history"}[], {uses "sumRewards"}[], {uses "pullCount"}[], {uses "stationaryEnv"}[], {uses "IsAlgEnvSeq"}[].
:::

:::proof "prob_pullCount_prod_sumRewards_mem_le"
  Uses: {uses "AM.identDistrib_sum_range_snd"}[], {uses "identDistrib_pullCount_prod_sumRewards"}[], {uses "AM.measurable_hist"}[], {uses "pullCount_basic"}[], {uses "isAlgEnvSeq_arrayMeasure"}[], {uses "AM.measurable_hist"}[], {uses "isAlgEnvSeq_unique"}[]
:::


:::lemma_ "prob_sumRewards_le_sumRewards_le" (parent := "concentrationBandits") (lean := "Bandits.ArrayModel.prob_sumRewards_le_sumRewards_le, Bandits.probReal_sumRewards_le_sumRewards_le")
In the array model,
$$`
  P_{\mathcal{A}}\left( N_{t, a^*} = m_1 \wedge N_{t, a} = m_2 \wedge S_{t, a^*} \le S_{t, a}\right)
  \le (\otimes_a \nu(a))^{\otimes \mathbb{N}} \left( \sum_{s=0}^{m_1-1} \omega_{s, a^*} \le \sum_{s=0}^{m_2-1} \omega_{s, a} \right)
  \: .
`
As a consequence, this also holds for any algorithm-environment sequence.

Uses: {uses "AM.history"}[], {uses "sumRewards"}[], {uses "pullCount"}[], {uses "stationaryEnv"}[], {uses "IsAlgEnvSeq"}[]
:::

:::proof "prob_sumRewards_le_sumRewards_le"
  Uses: {uses "identDistrib_pullCount_prod_sumRewards"}[], {uses "AM.measurable_hist"}[], {uses "pullCount_basic"}[], {uses "isAlgEnvSeq_arrayMeasure"}[], {uses "AM.measurable_hist"}[], {uses "isAlgEnvSeq_unique"}[]
:::



## Sub-Gaussian rewards

:::lemma_ "probReal_sum_le_sum_streamMeasure" (parent := "concentrationBandits") (lean := "Bandits.probReal_sum_le_sum_streamMeasure")
Let $`\nu(a)` be a $`\sigma^2`-{uses "subGaussian"}[sub-Gaussian] distribution on $`\mathbb{R}` for each arm $`a \in \mathcal{A}`.
$$`
  (\otimes_a \nu(a))^{\otimes \mathbb{N}} \left( \sum_{s=0}^{m-1} \omega_{s, a^*} \le \sum_{s=0}^{m-1} \omega_{s, a} \right)
  \le \exp\left( -m \frac{\Delta_a^2}{4 \sigma^2} \right)
`

Uses: {uses "ionescu-tulcea"}[], {uses "gap"}[]
:::

:::proof "probReal_sum_le_sum_streamMeasure"
  Uses: {uses "measure_sum_le_sum_le'"}[]
:::


:::lemma_ "prob_sum_le_sqrt_log" (parent := "concentrationBandits") (lean := "Bandits.prob_sum_le_sqrt_log, Bandits.prob_sum_ge_sqrt_log")
Let $`\nu(a)` be a $`\sigma^2`-{uses "subGaussian"}[sub-Gaussian] distribution on $`\mathbb{R}` for each arm $`a \in \mathcal{A}`.
Let $`c \ge 0` be a real number and $`k` a positive natural number.
Then
$$`
  \nu(a)^{\otimes \mathbb{N}} \left( \sum_{s=0}^{k-1} (\omega_{s} - \mu_a) \le - \sqrt{2 c k \sigma^2 \log(n + 1)} \right)
  \le \frac{1}{(n + 1)^{c}}
  \: .
`

The same upper bound holds for the upper tail:
$$`
  \nu(a)^{\otimes \mathbb{N}} \left( \sum_{s=0}^{k-1} (\omega_{s} - \mu_a) \ge \sqrt{2 c k \sigma^2 \log(n + 1)} \right)
  \le \frac{1}{(n + 1)^{c}}
  \: .
`

Uses: {uses "ionescu-tulcea"}[]
:::

:::proof "prob_sum_le_sqrt_log"
  Uses: {uses "hoeffding"}[].
:::
