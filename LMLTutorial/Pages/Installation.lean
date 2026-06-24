/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import VersoManual

open Verso.Genre Manual

#doc (Manual) "Installation and Setup" =>
%%%
htmlSplit := .never
%%%

This tutorial guides you through installing Lean and setting up the Lean Machine Learning library.

# Installing Lean

Before using the Lean Machine Learning library, you need to install Lean.

Follow the official installation instructions at [https://lean-lang.org/install/](https://lean-lang.org/install/).

The recommended installation process will set up VS Code with the Lean extension.

# Installing the Lean Machine Learning library

There are two ways to get the library depending on your needs:
1. *Clone the repository*: if you want to explore the source code and experiment with modifications of the library, clone the GitHub repository
2. *Use as a dependency*: if you want to use the library in your own Lean project, you can add it as a dependency in your `lakefile.toml` (instructions below)

## Cloning the Repository

Move to a directory where you want to store the library, then run:

```
git clone https://github.com/LeanMachineLearning/LML.git
cd LML
```
This will create a local copy of the repository on your machine and move to the project directory.
We then need to build the project.
```
lake exe cache get
lake build
```
The `lake exe cache get` will get the precompiled Mathlib cache, which significantly speeds up the build process. The `lake build` command will then compile the library and all its dependencies.

Note that if you want to contribute to the library, you should fork the repository and clone your fork instead of the main repository.

## Using as a Dependency

To use the library in your own Lean project (see the Lean installation instructions for how to create a project), add it as a dependency in your `lakefile.toml`:

```
[[require]]
name = "LeanMachineLearning"
git = "https://github.com/LeanMachineLearning/LML"
```

# Testing the installation

Create a new Lean file in your project and add the following code:
```
import LeanMachineLearning

#check Learning.Algorithm
```

If you don't see any errors, then the library is correctly installed and you can start using it in your own projects!
