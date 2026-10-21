/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Classical
import ComputableModelTheory.Util.AssertAxioms
import ComputableModelTheory.Util.ImportGuard

/-!
# Audit: the classical entry point

Outside the root import spine; CI checks it through `scripts/run-audit-modules.sh`, and with
warnings as errors through `scripts/check-classical-layer.sh`.

* **Import-only**: `ComputableModelTheory.Classical` defines no declarations of its own.
* **Import guard**: `ComputableModelTheory.Classical` imports exactly the eight classical modules,
  and its transitive import closure contains no other module of this library, no module of
  `InfinitaryLogic` and no module of `TauCeti` (`ImportGuard.forbiddenPrefixes`) — downstream gets
  Mathlib plus the classical layer, nothing effective. The predicate itself is checked to reject a
  `TauCeti` module; `ImportGuardControlAudit` checks that the same walk reports TauCeti from a
  module that does reach it.
* **Standard axioms**, by defining module, for every declaration of each of the eight modules (the
  declarations live in `FirstOrder.Language`, so a scan filtered by this library's namespace would
  miss them).
* **The name clash** with Mathlib's order-theoretic `IsAtomic`: the qualified forms elaborate
  outside the namespace (`test_isAtomic_qualified`); a bare `IsAtomic` after
  `open FirstOrder.Language` resolves by overloading (`test_isAtomic_bare`).
-/

/-! ### Import guard -/

open Lean in
run_cmd do
  let env ← getEnv
  let target := `ComputableModelTheory.Classical
  let classical : List Name := [`ComputableModelTheory.ModelTheory.CountablePrime,
    `ComputableModelTheory.ModelTheory.ExtensionRichDirectLimit,
    `ComputableModelTheory.ModelTheory.ExtensionRichFamily,
    `ComputableModelTheory.ModelTheory.FraisseExistence,
    `ComputableModelTheory.ModelTheory.NamedParameters,
    `ComputableModelTheory.ModelTheory.OrbitIsolation,
    `ComputableModelTheory.ModelTheory.RepresentativeAge,
    `ComputableModelTheory.ModelTheory.RootedExtension]
  let some idx := env.getModuleIdx? target | throwError "{target} is not imported"
  let direct := (env.header.moduleData[idx.toNat]!).imports.map (·.module)
  unless direct.filter (· != `Init) == classical.toArray do
    throwError "unexpected direct imports of {target}: {direct}"
  let bad := ComputableModelTheory.ImportGuard.forbiddenInClosure env classical direct
  unless bad.isEmpty do
    throwError "{target} transitively imports {bad}"

/-! ### The guard's predicate, as a negative control

The closure above reaches no forbidden module, so the walk alone would pass vacuously were a prefix
missing from `forbiddenPrefixes`. The predicate is checked directly: it rejects a module of each
forbidden prefix, including `TauCeti`, accepts the allowed classical modules and Mathlib. -/

open Lean ComputableModelTheory.ImportGuard in
run_cmd do
  let rejected : List Name := [`TauCeti.ModelTheory.Infinitary.Syntax,
    `InfinitaryLogic.Scott.BackAndForth,
    `ComputableModelTheory.ModelTheory.Computable.InfinitaryBridge]
  for m in rejected do
    unless isForbidden [] m do throwError "the import guard does not reject {m}"
  unless !isForbidden [`ComputableModelTheory.ModelTheory.RootedExtension]
      `ComputableModelTheory.ModelTheory.RootedExtension do
    throwError "the import guard rejects an allowed classical module"
  unless !isForbidden [] `Mathlib.ModelTheory.Fraisse do
    throwError "the import guard rejects a Mathlib module"

/-! ### The entry module is import-only -/

-- `ComputableModelTheory.Classical` itself defines no declarations, so the module scans below cover
-- everything it exports.
open Lean in
run_cmd do
  let env ← getEnv
  let target := `ComputableModelTheory.Classical
  let some idx := env.getModuleIdx? target | throwError "{target} is not imported"
  let own := env.constants.toList.filter fun (n, _) ↦ env.getModuleIdxFor? n == some idx
  unless own.isEmpty do
    throwError "{target} defines declarations: {own.map (·.1)}"

/-! ### The name clash, outside the namespace -/

universe u v w

open FirstOrder in
/-- The qualified name elaborates outside `FirstOrder.Language`. -/
theorem test_isAtomic_qualified {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]
    (h : Language.IsAtomic (L.completeTheory M) M) :
    FirstOrder.Language.IsAtomic (L.completeTheory M) M :=
  h

/-- A bare `IsAtomic` after `open FirstOrder.Language` still elaborates, by overloading against the
order-theoretic class; the qualified form above is the robust one. -/
theorem test_isAtomic_bare {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]
    (h : FirstOrder.Language.IsAtomic (L.completeTheory M) M) :
    open FirstOrder.Language in IsAtomic (L.completeTheory M) M :=
  h

/-! ### Standard axioms, by defining module -/

#assert_standard_axioms test_isAtomic_qualified
#assert_standard_axioms test_isAtomic_bare

#assert_module_standard_axioms ComputableModelTheory.ModelTheory.CountablePrime
#assert_module_standard_axioms ComputableModelTheory.ModelTheory.ExtensionRichDirectLimit
#assert_module_standard_axioms ComputableModelTheory.ModelTheory.ExtensionRichFamily
#assert_module_standard_axioms ComputableModelTheory.ModelTheory.FraisseExistence
#assert_module_standard_axioms ComputableModelTheory.ModelTheory.NamedParameters
#assert_module_standard_axioms ComputableModelTheory.ModelTheory.OrbitIsolation
#assert_module_standard_axioms ComputableModelTheory.ModelTheory.RepresentativeAge
#assert_module_standard_axioms ComputableModelTheory.ModelTheory.RootedExtension
