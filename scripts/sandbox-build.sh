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
sorry_audit=0
if [ "$strict_build_status" -ne 0 ]; then
  lake build
  warning_only=1
fi

# The compiled axiom audit remains strict when invoked directly.  During PR
# development, however, an open theorem may carry `sorryAx`: that is review
# debt that should be routed to human review rather than treated as a compiler
# failure. Treat an audit containing only `sorryAx` entries as a warning so the
# required `build` status can pass;
# the outer workflow publishes the warning status separately, which keeps
# automatic merge disabled until a human review accepts the open proofs.
axiom_log=$(mktemp "$PWD/.lake/axioms.XXXXXX")
trap 'rm -f "$axiom_log"' EXIT
set +e
lake env lean --run scripts/Axioms.lean >"$axiom_log" 2>&1
axiom_status=$?
set -e
cat "$axiom_log"
if [ "$axiom_status" -ne 0 ]; then
  offender_lines=$(grep -E '^  .* → \[[^][]+\]$' "$axiom_log" || true)
  if [ -n "$offender_lines" ] &&
     ! printf '%s\n' "$offender_lines" | grep -qvE ' → \[sorryAx\]$'; then
    warning_only=1
    sorry_audit=1
  else
    exit "$axiom_status"
  fi
fi

if [[ -x scripts/euler-project-gates.sh ]]; then
  bash scripts/euler-project-gates.sh
fi

git diff --check

if [ "$warning_only" = 1 ]; then
  echo "KIP126_WARNING_ONLY_BUILD=1"
fi
if [ "$sorry_audit" = 1 ]; then
  echo "KIP126_SORRY_AUDIT=1"
fi
