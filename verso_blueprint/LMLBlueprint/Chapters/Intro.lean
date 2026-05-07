import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Introduction" =>
%%%
htmlSplit := .never
%%%

A bandit algorithm sequentially chooses actions and then observes rewards, whose distribution depends on the action chosen.
The algorithm does not know the distribution of the rewards and sees only a reward from the chosen action at any given time.
A key part of the interaction is that the algorithm can choose the next action based on all the previous actions and rewards.
The goal of the algorithm is typically to maximize the cumulative reward over time.
The researcher studying bandit algorithms is interested in the performance of the algorithm, which is measured by the _regret_ $`R_T` after choosing $`T` actions, that is the difference between the cumulative reward of always playing the best action and the cumulative reward of the algorithm.
A theoretical guarantee will be of the form $`\mathbb{E}[R_T] \le f(T)` for some function $`f`.
Here the expectation is taken over the randomness of the algorithm and the rewards.
In parallel to the theoretical study, the researcher may also be interested in the practical performance of the algorithm, which is usually measured by the average regret over several runs of the algorithm with rewards sampled from standard probability distributions.

From that description, we highlight three key components of research work on bandit algorithms:
- A bandit algorithm is both a subject of theoretical study and a practical tool, that we should be able to implement and run,
- the bandit model defines a probability space, on which we want to take expectations, and the theoretical study deals with random variables on that space using tools like concentration inequalities,
- for the experimental part, we need to be able to sample rewards from a range of probability distributions.

# Notations

$`P(E)` is the probability of event $`E` under the probability distribution $`P`.

$`P[X]` is the expectation of random variable $`X`.

$`P[X \mid Y]` is the conditional expectation of random variable $`X` given random variable $`Y`.

$`P(X \mid Y)` is the conditional distribution of random variable $`X` given random variable $`Y`.
