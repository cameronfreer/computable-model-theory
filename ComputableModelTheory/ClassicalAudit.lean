/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Classical
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the classical entry point

Outside the root import spine; CI checks it through `scripts/run-audit-modules.sh`, and with
warnings as errors through `scripts/check-classical-layer.sh`.

* **Import-only**: `ComputableModelTheory.Classical` defines no declarations of its own.
* **Import guard**: `ComputableModelTheory.Classical` imports exactly the eight classical modules,
  and its transitive import closure contains no other module of this library and no module of
  `InfinitaryLogic` — downstream gets Mathlib plus the classical layer, nothing effective.
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
  let mut seen : NameSet := {}
  let mut todo : Array Name := direct
  while h : todo.size > 0 do
    let m := todo.back
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    if !classical.contains m &&
        ((`ComputableModelTheory).isPrefixOf m || (`InfinitaryLogic).isPrefixOf m) then
      throwError "{target} transitively imports {m}"
    if let some j := env.getModuleIdx? m then
      todo := todo ++ (env.header.moduleData[j.toNat]!).imports.map (·.module)

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
