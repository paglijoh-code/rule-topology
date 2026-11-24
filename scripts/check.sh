#!/usr/bin/env bash
# Forbidden constructs, then the Lean build of the main library with walls A and B (kernel-checks every theorem).
set -euo pipefail
cd "$(dirname "$0")/.."
if grep -rnE '(^|[^`])(\bsorry\b|native_decide)|^\s*axiom\b|implemented_by|@\[extern' --include='*.lean' --exclude-dir=.lake lean; then
  echo "forbidden construct in Lean sources" >&2; exit 1
fi
( cd lean && lake build )
echo "check passed"
