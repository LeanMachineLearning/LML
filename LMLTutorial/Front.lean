/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LMLTutorial.Pages.BasicProbability
import LMLTutorial.Pages.DefiningAlgorithm
import LMLTutorial.Pages.Installation
import LMLTutorial.Pages.MarkovKernels
import LMLTutorial.Pages.Martingales
import VersoManual

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

#doc (Manual) "Lean Machine Learning" =>
%%%
authors := []
shortTitle := "Lean Machine Learning"
%%%

These tutorial pages will guide you through using the [Lean Machine Learning](https://leanmachinelearning.org) library.

{include 0 LMLTutorial.Pages.Installation}

{include 0 LMLTutorial.Pages.BasicProbability}

{include 0 LMLTutorial.Pages.MarkovKernels}

{include 0 LMLTutorial.Pages.DefiningAlgorithm}

{include 0 LMLTutorial.Pages.Martingales}
