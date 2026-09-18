#!/usr/bin/env bash
set -euxo pipefail

export TMPDIR="$PWD/.lake/tmp"
test -n "${WATCHDOG_TOOLCHAIN:-}"
test -x "$WATCHDOG_TOOLCHAIN/bin/lean"
export LAKE_OVERRIDE_LEAN=true
export LEAN="$WATCHDOG_TOOLCHAIN/bin/lean"

# `--iofail` promotes Lean warnings to target failures.  Keep that first pass as
# a warning detector, but verify a nonzero result with an ordinary build: only a
# genuine compiler failure stops the sandbox.  Warning-only builds finish the
# remaining trusted audits and emit a marker that the outer workflow turns into
# a non-required, human-review-only status.
set +e
lake build --iofail
strict_build_status=$?
set -e
warning_only=0
if [ "$strict_build_status" -ne 0 ]; then
  lake build
  warning_only=1
fi
lake env lean --run scripts/Axioms.lean

if [[ -x scripts/euler-project-gates.sh ]]; then
  bash scripts/euler-project-gates.sh
fi

git diff --check

if [ "$warning_only" = 1 ]; then
  echo "KIP126_WARNING_ONLY_BUILD=1"
fi
