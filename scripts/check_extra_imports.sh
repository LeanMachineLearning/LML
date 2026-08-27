#!/usr/bin/env bash
# `LeanMachineLearning` may only import `LMLExtra` privately, i.e. with a plain
# `import LMLExtra.Foo`, and only from files using the module system.
#
# * `public import` would re-export `LMLExtra` to every importer of the file.
# * `import all` would give access to the non-public declarations of the `LMLExtra` file.
# * `meta import` would run `LMLExtra` metaprograms (macros, elaborators, initializers) while
#   elaborating `LeanMachineLearning`.
# * In a file that is not a `module`, every import is public and meta.
#
# All of these would circumvent the checks that the module system performs on private imports.
# See `LeanMachineLearning/Tactic/Linter/ExtraData.lean`.
set -euo pipefail
cd "$(dirname "$0")/.."

# Any import of `LMLExtra`, with any modifiers.
any='^[[:space:]]*((public|meta)[[:space:]]+)*import([[:space:]]+all)?[[:space:]]+LMLExtra([.[:space:]]|$)'
# The only allowed form: `import LMLExtra.Foo`, at the start of the line, no modifiers.
allowed='^[0-9]+:import[[:space:]]+LMLExtra(\.[A-Za-z0-9_.]+)?[[:space:]]*(--.*)?$'

status=0
for f in $(grep -rlE --include='*.lean' "$any" LeanMachineLearning LeanMachineLearning.lean || true); do
  if grep -nE "$any" "$f" | grep -vE "$allowed"; then
    echo "error: $f: LMLExtra must be imported with a plain 'import LMLExtra.Foo'." >&2
    status=1
  fi
  if ! grep -qE '^module([[:space:]]|$)' "$f"; then
    echo "error: $f imports LMLExtra but is not a 'module': its imports are public and meta." >&2
    status=1
  fi
done
if [ "$status" -eq 0 ]; then
  echo "OK: LeanMachineLearning imports LMLExtra only privately, from module files."
fi
exit "$status"
