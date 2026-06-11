#!/usr/bin/env bash
# Lists all definitions (def, abbrev, structure, class, irreducible_def) in LeanMachineLearning Lean files.
# Usage: ./scripts/list_definitions.sh [directory]
# Default directory: LeanMachineLearning/

set -euo pipefail

DIR="${1:-LeanMachineLearning}"

grep -rn \
  --include="*.lean" \
  -E '(^|[[:space:]])(noncomputable[[:space:]]+|private[[:space:]]+|protected[[:space:]]*)*(irreducible_def|def|abbrev|structure|class)[[:space:]]+[a-zA-Z_]' \
  "$DIR" \
| sed -E 's|^([^:]+):([0-9]+):(.*)$|\1:\2:\3|' \
| while IFS=: read -r file line content; do
    # Skip comment lines
    [[ "$content" =~ ^[[:space:]]*-- ]] && continue
    kind=$(echo "$content" | grep -oE '(irreducible_def|def|abbrev|structure|class)[[:space:]]+[a-zA-Z_][^[:space:](:{]*' | head -1 | sed -E 's/[[:space:]]+/ /g')
    [[ -n "$kind" ]] && echo "$file:$line: $kind"
  done
