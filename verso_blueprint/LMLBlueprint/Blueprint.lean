import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LMLBlueprint.Chapters.Algorithm
import LMLBlueprint.Chapters.Bandit
import LMLBlueprint.Chapters.BanditAlgs
import LMLBlueprint.Chapters.Concentration
import LMLBlueprint.Chapters.Intro

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldProofs true
set_option verso.blueprint.summary.debugDiagnostics false

#doc (Manual) "Lean Machine Learning" =>

Blueprint for the bandit parts of the [Lean Machine Learning](https://leanmachinelearning.org) library.

{include 0 LMLBlueprint.Chapters.Intro}
{include 0 LMLBlueprint.Chapters.Algorithm}
{include 0 LMLBlueprint.Chapters.Bandit}
{include 0 LMLBlueprint.Chapters.Concentration}
{include 0 LMLBlueprint.Chapters.BanditAlgs}

{blueprint_graph}
{blueprint_summary}
{blueprint_bibliography}
