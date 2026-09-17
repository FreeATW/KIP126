#!/usr/bin/env bash
set -euo pipefail

lake build KIP126 --iofail
lake env lean --run scripts/Axioms.lean

# Historical compatibility is checked separately and never expands the trusted
# library's allowlist. Report actual dependencies and verify the immutable source.
lake build KIPBase
lake build kipbaseAudit
legacy_report=$(mktemp)
trap 'rm -f "$legacy_report"' EXIT
lake exe kipbaseAudit > "$legacy_report"
python3 scripts/kipbase-migration.py --audit-report "$legacy_report"
python3 -m unittest scripts.test_kipbase_migration scripts.test_workflow_routing

if [[ -x scripts/euler-project-gates.sh ]]; then
  bash scripts/euler-project-gates.sh
fi

PYTHONPATH=. python3 scripts/perf/test_perf.py -v
PYTHONPATH=scripts python3 -m unittest scripts.pr_status.test_pr_status -v
python3 -m py_compile scripts/perf/*.py scripts/profile/*.py scripts/pr_status/*.py
git diff --check
