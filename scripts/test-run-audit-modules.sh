#!/usr/bin/env bash
# Self-test for scripts/run-audit-modules.sh, run in a scratch git repository with a stub elaborator
# (AUDIT_LEAN_CMD='grep -q pass': a module "passes" iff it contains the word `pass`).
#
# * Two audit paths that flatten to the same name when `/` is replaced by `_`
#   (A_B/FooAudit.lean and A/B_FooAudit.lean), one failing and one passing: the run must fail and
#   name the failing one. A runner keyed by flattened names would let the pass overwrite the failure.
# * The same pair, both passing: the run must succeed.
# * AUDIT_JOBS=0 and a non-number are rejected (`xargs -P 0` would be unbounded).
#
# Usage: scripts/test-run-audit-modules.sh   (honours AUDIT_TMPDIR / TMPDIR for its scratch space)
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
tmpbase="${AUDIT_TMPDIR:-${TMPDIR:-/tmp}}"
work="$(mktemp -d "${tmpbase%/}/audit-selftest.XXXXXX")"
trap 'rm -rf "${work}"' EXIT

git -C "${work}" init -q
mkdir -p "${work}/scripts" "${work}/M/A_B" "${work}/M/A"
cp "${here}/run-audit-modules.sh" "${work}/scripts/"
echo fail > "${work}/M/A_B/FooAudit.lean"
echo pass > "${work}/M/A/B_FooAudit.lean"
git -C "${work}" add M scripts

run() { (cd "${work}" && AUDIT_TMPDIR="${work}" AUDIT_LEAN_CMD='grep -q pass' "$@" \
  bash scripts/run-audit-modules.sh) > "${work}/out.log" 2>&1; }

fail=0
if run env; then
  echo "FAIL: colliding paths with one failure reported success" >&2; fail=1
elif ! grep -q -- '-- FAILED: M/A_B/FooAudit.lean' "${work}/out.log" ||
    grep -q -- '-- FAILED: M/A/B_FooAudit.lean' "${work}/out.log"; then
  echo "FAIL: colliding paths misattributed the failure" >&2; cat "${work}/out.log" >&2; fail=1
fi

echo pass > "${work}/M/A_B/FooAudit.lean"
if ! run env; then
  echo "FAIL: two passing audits reported failure" >&2; cat "${work}/out.log" >&2; fail=1
fi

for j in 0 abc; do
  set +e; run env AUDIT_JOBS="${j}"; rc=$?; set -e
  if [ "${rc}" -ne 2 ]; then echo "FAIL: AUDIT_JOBS=${j} was not rejected (exit ${rc})" >&2; fail=1; fi
done

[ "${fail}" -eq 0 ] && echo "run-audit-modules.sh self-test: passed."
exit "${fail}"
