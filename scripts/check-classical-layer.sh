#!/usr/bin/env bash
# Strict gate for the classical, Mathlib-only layer (the Fraïssé interfaces ExtensionRichFamily,
# RepresentativeAge, ExtensionRichDirectLimit; orbit isolation and countable primeness; rooted
# extension): build the modules, then elaborate each module and its audit with warnings as errors
# and the Mathlib standard linter set. Fails fast.
#
# Deliberately `lake env lean`, not `lake lean`: the ordinary audit sweep elaborates with the
# package's Lean options, including any project-wide compatibility settings the effective layer
# needs, but this gate checks the classical layer *without* them, so the extraction cannot silently
# acquire the effective layer's elaboration debt. Options it does need are passed explicitly below.
#
# Usage: scripts/check-classical-layer.sh   (from anywhere inside the repo)
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

modules=(
  ComputableModelTheory.ModelTheory.ExtensionRichFamily
  ComputableModelTheory.ModelTheory.RepresentativeAge
  ComputableModelTheory.ModelTheory.ExtensionRichDirectLimit
  ComputableModelTheory.ModelTheory.FraisseExistence
  ComputableModelTheory.ModelTheory.OrbitIsolation
  ComputableModelTheory.ModelTheory.CountablePrime
  ComputableModelTheory.ModelTheory.NamedParameters
  ComputableModelTheory.ModelTheory.RootedExtension
)

lake build "${modules[@]}"
for m in "${modules[@]}"; do
  file="$(printf '%s' "${m}" | tr . /).lean"
  audit="${file%.lean}Audit.lean"
  echo "== ${file}"
  lake env lean -DautoImplicit=false -DwarningAsError=true -Dlinter.mathlibStandardSet=true \
    "${file}"
  echo "== ${audit}"
  # `lake env lean` builds nothing, and an audit may import modules outside the library's import
  # closure (e.g. extra Mathlib files for a fixture): build the audit's own imports first.
  mapfile -t audit_imports < <(sed -n 's/^import \([^ ]*\).*/\1/p' "${audit}")
  lake build "${audit_imports[@]}"
  lake env lean -DautoImplicit=false -DwarningAsError=true "${audit}"
done
echo "Classical layer: strict build, standard axioms, import isolation — all passed."
