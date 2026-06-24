/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import VersoManual
import LMLTutorial.Front

set_option linter.style.header false
set_option linter.style.setOption false

open Verso.Genre.Manual Verso.Output.Html

def extraHead : Array Verso.Output.Html := #[
  {{<link rel="icon" type="image/x-icon" href="static/favicon.svg"/>}},
  {{<link rel="stylesheet" href="static/style.css"/>}},
  {{<script src="static/scripts.js"></script>}},
]

def config : RenderConfig := {
  extraHead := extraHead,
  sourceLink := some "https://github.com/LeanMachineLearning/LML",
  issueLink := some "https://github.com/LeanMachineLearning/LML/issues",
}

def main := manualMain (%doc LMLTutorial.Front) (config := config)
