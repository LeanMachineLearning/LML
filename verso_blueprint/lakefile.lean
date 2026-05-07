import Lake
open Lake DSL

require verso from git "https://github.com/leanprover/verso"@"v4.29.0"
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"
require LeanMachineLearning from "../"

package LMLBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib LMLBlueprint where

lean_exe «blueprint-gen» where
  root := `Main
