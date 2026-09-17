#!/usr/bin/env bash
set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_ROOT"

# Pin the blueprint toolchain to the customized fork under KIP/tools (6-state
# lifecycle / extended node states). Override with KIP_TOOLS_DIR if needed.
KIP_TOOLS_DIR="${KIP_TOOLS_DIR:-/inspire/hdd/project/qproject-fundationmodel/czxs25250150/KIP/tools}"

if [[ ! -d "$KIP_TOOLS_DIR/leanblueprint" || ! -d "$KIP_TOOLS_DIR/plastexdepgraph" ]]; then
  echo "ERROR: KIP_TOOLS_DIR=$KIP_TOOLS_DIR is missing leanblueprint/ or plastexdepgraph/" >&2
  exit 1
fi

# Resolve the python interpreter that backs the `leanblueprint` CLI — we must
# install/verify packages against *that* interpreter, not whatever python3 is on
# PATH (which on this host is a separate uv-managed environment).
LB_BIN="$(command -v leanblueprint || true)"
if [[ -n "$LB_BIN" ]]; then
  LB_PY="$(awk 'NR==1 && /^#!/ {sub(/^#!/, ""); split($0, a, " "); print a[1]; exit}' "$LB_BIN")"
fi
LB_PY="${LB_PY:-/usr/bin/python}"
if [[ ! -x "$LB_PY" ]]; then
  echo "ERROR: cannot locate python interpreter for leanblueprint (tried '$LB_PY')" >&2
  exit 1
fi

# Re-install editable from KIP/tools only if the active resolution differs.
need_install=0
for pkg in plastexdepgraph leanblueprint; do
  loc="$("$LB_PY" -c "import ${pkg}, os; print(os.path.dirname(os.path.dirname(${pkg}.__file__)))" 2>/dev/null || true)"
  if [[ "$loc" != "$KIP_TOOLS_DIR/${pkg}" ]]; then
    need_install=1
  fi
done

if [[ "$need_install" == "1" ]]; then
  echo "==> $LB_PY -m pip install -e $KIP_TOOLS_DIR/{plastexdepgraph,leanblueprint}"
  "$LB_PY" -m pip install --quiet -e "$KIP_TOOLS_DIR/plastexdepgraph" -e "$KIP_TOOLS_DIR/leanblueprint"
fi

# 1. Build the Lean project so checkdecls has compiled olean files.
echo "==> lake build"
lake build

# 2. Blueprint: PDF + web + checkdecls.
echo "==> leanblueprint pdf"
leanblueprint pdf

echo "==> leanblueprint web"
leanblueprint web

echo "==> leanblueprint checkdecls"
leanblueprint checkdecls

echo "==> Done"
