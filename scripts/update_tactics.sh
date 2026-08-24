#!/usr/bin/env bash

# Vendors the standalone tactic projects (EqLift, KernelHom) into
# LeanMachineLearning/Tactic:
#   1. clones each upstream repository into a temporary directory,
#   2. extracts its main folder (e.g. EqLift/EqLift) and its root module file
#      (e.g. EqLift/EqLift.lean),
#   3. rewrites every `import EqLift.` / `import KernelHom.` (including the
#      `public import` and `meta import` forms) into
#      `import LeanMachineLearning.Tactic.EqLift.` /
#      `import LeanMachineLearning.Tactic.KernelHom.`,
#   4. prepends the LML copyright header to the root module files, which the
#      upstream ones do not carry.
#
# Warning: the destination folders are wiped and replaced, so any local edit
# made to the vendored files is lost. Check `git diff` after running.
#
# Usage: scripts/update_tactics.sh [project ...]     (default: all projects)
#   DEST=<dir>  override the destination directory (defaults to
#               LeanMachineLearning/Tactic), useful for dry runs.

set -euo pipefail

GITHUB_USER="gaetanserre"
PREFIX="LeanMachineLearning.Tactic"
ALL_PROJECTS=(EqLift KernelHom)

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEST="${DEST:-$REPO_ROOT/LeanMachineLearning/Tactic}"

if [ "$#" -gt 0 ]; then
  PROJECTS=("$@")
else
  PROJECTS=("${ALL_PROJECTS[@]}")
fi

HEADER='/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

'

TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

# Build the sed program rewriting the imports of *every* known project, so that
# cross-project imports (KernelHom depends on EqLift) are rewritten too.
SED_ARGS=()
for project in "${ALL_PROJECTS[@]}"; do
  SED_ARGS+=(-e "s/(^|[[:space:]])import ${project}\.(\\w)/\1import ${PREFIX}.${project}.\2/g")
done

mkdir -p "$DEST"

for project in "${PROJECTS[@]}"; do
  echo "==> $project"

  git clone --quiet --depth 1 \
    "https://github.com/${GITHUB_USER}/${project}.git" "$TMP_DIR/$project"

  src_dir="$TMP_DIR/$project/$project"
  src_root="$TMP_DIR/$project/$project.lean"
  for path in "$src_dir" "$src_root"; do
    if [ ! -e "$path" ]; then
      echo "    error: $path not found in the cloned repository" >&2
      exit 1
    fi
  done

  # Extract the main folder and its root module file.
  rm -rf "${DEST:?}/$project" "${DEST:?}/$project.lean"
  cp -r "$src_dir" "$DEST/$project"
  { printf '%s' "$HEADER"; cat "$src_root"; } > "$DEST/$project.lean"

  # Rewrite the imports.
  mapfile -t files < <(find "$DEST/$project" -type f -name '*.lean')
  files+=("$DEST/$project.lean")
  sed -E -i "${SED_ARGS[@]}" "${files[@]}"

  echo "    ${#files[@]} file(s) written to ${DEST#"$REPO_ROOT/"}/$project{,.lean}"

  # Sanity check: no unqualified import of a vendored project may remain.
  for other in "${ALL_PROJECTS[@]}"; do
    if grep -rEn "(^|[[:space:]])import ${other}\." "$DEST/$project" "$DEST/$project.lean"; then
      echo "    error: leftover unqualified '${other}.' imports (see above)" >&2
      exit 1
    fi
  done
done

echo
echo "Done. Check \`git diff\` for local edits that were overwritten, and"
echo "regenerate LeanMachineLearning.lean if the module list changed."
