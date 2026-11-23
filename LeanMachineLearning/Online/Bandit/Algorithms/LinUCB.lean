/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Fawad Haider
-/
module


/-!
# LinUCB for finite-action linear bandits

This module is the public entry point for the finite-action LinUCB development.

The implementation is split across submodules under
`LeanMachineLearning.Online.Bandit.Algorithms.LinUCB.*`; importing this file re-exports the full
LinUCB API, including the algorithm definition, confidence events, concentration interfaces,
deterministic regret decomposition, elliptical-potential/log-det bounds, and final regret theorems.
-/
