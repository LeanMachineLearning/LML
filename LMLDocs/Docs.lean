import VersoManual

import LMLDocs.Front

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

def main := manualMain (%doc LMLDocs.Front) (config := config)
