#!/usr/bin/env bash
set -euo pipefail

repo=${1:-.}
revision=${2:-HEAD}

git -C "$repo" rev-parse --verify "${revision}^{commit}" >/dev/null

for required in KIP126.lean lakefile.lean lake-manifest.json lean-toolchain; do
  git -C "$repo" cat-file -e "${revision}:${required}"
done

# Hash committed build inputs, not the commit id. A documentation-only main commit
# therefore reuses its parent's trusted outputs, while any Lean source, Lake pin,
# build definition, or toolchain change gets a distinct immutable cache key.
entries=$(
  git -C "$repo" ls-tree -r --full-tree "$revision" -- \
    KIP126.lean KIP126 KIPBase.lean KIPBase lakefile.lean lake-manifest.json lean-toolchain |
    awk -F '\t' '
      $2 == "KIP126.lean" ||
      $2 == "KIPBase.lean" ||
      $2 == "lakefile.lean" ||
      $2 == "lake-manifest.json" ||
      $2 == "lean-toolchain" ||
      $2 ~ /^KIP126\/.*\.lean$/ ||
      $2 ~ /^KIPBase\/.*\.lean$/
    '
)

if [[ -z "$entries" ]]; then
  echo "no committed KIP126 build inputs found at $revision" >&2
  exit 1
fi

printf '%s\n' "$entries" | sha256sum | awk '{print $1}'
