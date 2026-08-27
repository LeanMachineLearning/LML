#!/usr/bin/env bash
# `LeanMachineLearning` may only import `LMLExtra` privately, i.e. with a plain
# `import LMLExtra.Foo`. A `public import` would re-export `LMLExtra` to every importer of the
# file, and an `import all` would give access to the non-public declarations of the `LMLExtra`
# file. Both would circumvent the checks that the module system performs on private imports.
# See `LeanMachineLearning/Tactic/Linter/ExtraData.lean`.
set -euo pipefail
cd "$(dirname "$0")/.."

pattern='^[[:space:]]*(public[[:space:]]+(meta[[:space:]]+)?import([[:space:]]+all)?|(meta[[:space:]]+)?import[[:space:]]+all)[[:space:]]+LMLExtra([.[:space:]]|$)'
if grep -rnE --include='*.lean' "$pattern" LeanMachineLearning LeanMachineLearning.lean; then
  echo "error: LeanMachineLearning must import LMLExtra privately (plain 'import LMLExtra.Foo')." >&2
  exit 1
fi
echo "OK: LeanMachineLearning imports LMLExtra only privately."
