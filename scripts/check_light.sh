#!/usr/bin/env bash
# Everything except the Lean build: forbidden constructs, generator tests, initial-run sources of the 32 walls. Minutes.
set -euo pipefail
cd "$(dirname "$0")/.."
PY=${PYTHON:-python3}
# No escape hatches in any Lean source.
if grep -rnE '(^|[^`])(\bsorry\b|native_decide)|^\s*axiom\b|implemented_by|@\[extern' --include='*.lean' --exclude-dir=.lake lean; then
  echo "forbidden construct in Lean sources" >&2; exit 1
fi
"$PY" -m certgen.test_certgen
# The generator reproduces the initial-run sources that were kept (into a temporary directory).
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
"$PY" -m certgen.emit_all --lean-dir "$tmp" --no-limits > /dev/null
"$PY" -m certgen.verify_sources "$tmp" --initial
echo "light check passed (Lean was not built)"
