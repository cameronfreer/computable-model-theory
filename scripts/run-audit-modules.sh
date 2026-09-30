#!/usr/bin/env bash
# Run every audit module (the axiom-policy acceptance gates) exactly as CI does.
#
# Audit modules live outside the root import spine, so `lake build` alone never
# elaborates them; each must be checked explicitly with `lake lean`. The tracked set
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

# Modules are elaborated with `lake lean`, not `lake env lean`, so that the package's Lean options
# (`leanOptions` in lakefile.toml) apply exactly as they do under `lake build` and in the editor.
#
# They run in parallel. Environment:
# * AUDIT_JOBS: a positive integer (default: the number of CPUs, at most 8). `xargs -P 0` would mean
#   unbounded concurrency, so zero and non-numbers are rejected.
# * AUDIT_TMPDIR: base directory for the per-run scratch directory (default: $TMPDIR, else /tmp).
#   The logs live there, and so do the temporary files of the Lean processes, which run with TMPDIR
#   pointing inside it; the whole directory is removed on exit.
# * AUDIT_LEAN_CMD: the elaboration command (default: `lake lean`); overridden only by the runner's
#   self-test.
# Each job is identified by its position in the sorted list, not by a name derived from its path, so
# distinct paths can never share a log or an exit status. Output is printed in sorted order, so the
# log reads as a sequential run.
all_list="$(printf '%s\n%s\n' "${tracked_list}" "${untracked_list}" | grep . || true)"
count="$(printf '%s' "${all_list}" | grep -c . || true)"

if printf '%s\n' "${all_list}" | grep -q '[[:space:]]'; then
  echo "ERROR: audit module paths must not contain whitespace:" >&2
  printf '%s\n' "${all_list}" | grep '[[:space:]]' | sed 's/^/    /' >&2
  exit 1
fi

if [ -n "${AUDIT_JOBS:-}" ]; then
  case "${AUDIT_JOBS}" in
    ''|*[!0-9]*|0*) echo "ERROR: AUDIT_JOBS must be a positive integer, got '${AUDIT_JOBS}'" >&2
      exit 2 ;;
  esac
  jobs="${AUDIT_JOBS}"
else
  jobs="$(nproc 2>/dev/null || echo 2)"
  [ "${jobs}" -gt 8 ] && jobs=8
fi

tmpbase="${AUDIT_TMPDIR:-${TMPDIR:-/tmp}}"
rundir="$(mktemp -d "${tmpbase%/}/audit-run.XXXXXX")"
trap 'rm -rf "${rundir}"' EXIT
mkdir -p "${rundir}/tmp"
export AUDIT_LEAN_CMD="${AUDIT_LEAN_CMD:-lake lean}"

if [ "${count}" -gt 0 ]; then
  printf '%s\n' "${all_list}" | awk '{ print NR, $0 }' |
    TMPDIR="${rundir}/tmp" xargs -P "${jobs}" -L 1 sh -c \
      'if ${AUDIT_LEAN_CMD} "$2" > "$0/$1.log" 2>&1; then echo 0; else echo 1; fi > "$0/$1.rc"' \
      "${rundir}" || true
fi

status=0
n=0
while IFS= read -r file; do
  [ -n "${file}" ] || continue
  n=$((n + 1))
  echo "== ${file}"
  cat "${rundir}/${n}.log" 2>/dev/null || true
  if [ "$(cat "${rundir}/${n}.rc" 2>/dev/null || echo 1)" != 0 ]; then
    status=1
    echo "-- FAILED: ${file}" >&2
  fi
done <<< "${all_list}"

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
