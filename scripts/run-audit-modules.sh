#!/usr/bin/env bash
# Run every audit module (the axiom-policy acceptance gates) exactly as CI does.
#
# Audit modules live outside the root import spine, so `lake build` alone never
# elaborates them; each must be checked explicitly with `lake env lean`. The tracked set
# is discovered from git (sorted for determinism) rather than hard-coded or shell-globbed,
# so a newly added *Audit.lean file can never be silently skipped.
#
# Untracked *Audit.lean files in the working tree ARE run, and the script then fails with
# an explicit "stage the new audit module" message. CI only ever sees committed files, so
# a local sweep that quietly reported a smaller module count than the working tree
# contains would be a false green: the new module looks checked when it was never visited.
# Staging is not committing, so `git add` is always a safe way to clear this.
#
# Usage: scripts/run-audit-modules.sh   (from anywhere inside the repo)
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

tracked_list="$(git ls-files '*Audit.lean' | sort)"
untracked_list="$(git ls-files --others --exclude-standard '*Audit.lean' | sort)"

n_tracked="$(printf '%s' "${tracked_list}" | grep -c . || true)"
n_untracked="$(printf '%s' "${untracked_list}" | grep -c . || true)"

# An audit module must not import another audit module. Audit .oleans are never built (they
# are outside the root import spine and no lean_lib globs them), so such an import resolves
# only against a stale local artifact and fails on a clean checkout — a CI-only breakage that
# a local sweep reports as green. Shared fixtures belong in a spine module instead.
bad_imports=0
while IFS= read -r file; do
  [ -n "${file}" ] || continue
  if grep -qE '^import .*Audit$' "${file}"; then
    echo "ERROR: ${file} imports another audit module:" >&2
    grep -nE '^import .*Audit$' "${file}" | sed 's/^/    /' >&2
    bad_imports=1
  fi
done < <(printf '%s\n%s\n' "${tracked_list}" "${untracked_list}")
if [ "${bad_imports}" -ne 0 ]; then
  echo >&2
  echo "Audit .oleans are never built, so this only works against a stale local artifact." >&2
  echo "Move the shared declarations into a module in the import spine." >&2
  exit 1
fi

status=0
count=0
while IFS= read -r file; do
  [ -n "${file}" ] || continue
  count=$((count + 1))
  echo "== ${file}"
  if ! lake env lean "${file}"; then
    status=1
    echo "-- FAILED: ${file}" >&2
  fi
done < <(printf '%s\n%s\n' "${tracked_list}" "${untracked_list}")

if [ "${count}" -eq 0 ]; then
  echo "No audit modules found via git ls-files '*Audit.lean'" >&2
  exit 1
fi

echo "Checked ${count} audit module(s) (${n_tracked} tracked, ${n_untracked} untracked)."

if [ "${n_untracked}" -gt 0 ]; then
  echo >&2
  echo "ERROR: stage the new audit module(s). They were checked above, but CI discovers" >&2
  echo "audit modules from git, so an unstaged file is invisible to CI:" >&2
  while IFS= read -r file; do
    [ -n "${file}" ] && echo "  git add ${file}" >&2
  done < <(printf '%s\n' "${untracked_list}")
  status=1
fi

exit "${status}"
