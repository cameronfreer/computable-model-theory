#!/usr/bin/env bash
# Run every audit module (the axiom-policy acceptance gates) exactly as CI does.
#
# Audit modules live outside the root import spine, so `lake build` alone never
# elaborates them; each must be checked explicitly with `lake env lean`. The set is
# discovered from git (sorted for determinism) rather than hard-coded or shell-globbed,
# so a newly added *Audit.lean file can never be silently skipped.
#
# Usage: scripts/run-audit-modules.sh   (from anywhere inside the repo)
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

status=0
count=0
while IFS= read -r file; do
  count=$((count + 1))
  echo "== ${file}"
  if ! lake env lean "${file}"; then
    status=1
    echo "-- FAILED: ${file}" >&2
  fi
done < <(git ls-files '*Audit.lean' | sort)

if [ "${count}" -eq 0 ]; then
  echo "No audit modules found via git ls-files '*Audit.lean'" >&2
  exit 1
fi

echo "Checked ${count} audit module(s)."
exit "${status}"
