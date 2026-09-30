#!/usr/bin/env bash
# Strict gate for the classical Fraïssé layer (ExtensionRichFamily, RepresentativeAge,
# ExtensionRichDirectLimit): build the modules, then elaborate each module and its audit with
# warnings as errors and the Mathlib standard linter set. Fails fast.
#
# Usage: scripts/check-classical-fraisse.sh   (from anywhere inside the repo)
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

modules=(
  ComputableModelTheory.ModelTheory.ExtensionRichFamily
  ComputableModelTheory.ModelTheory.RepresentativeAge
  ComputableModelTheory.ModelTheory.ExtensionRichDirectLimit
)

lake build "${modules[@]}"
for m in "${modules[@]}"; do
  file="$(printf '%s' "${m}" | tr . /).lean"
  audit="${file%.lean}Audit.lean"
  echo "== ${file}"
  lake env lean -DautoImplicit=false -DwarningAsError=true -Dlinter.mathlibStandardSet=true \
    "${file}"
  echo "== ${audit}"
  lake env lean -DautoImplicit=false -DwarningAsError=true "${audit}"
done
echo "Classical Fraïssé layer: strict build, standard axioms, import isolation — all passed."
