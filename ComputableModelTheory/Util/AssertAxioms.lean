/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Tactic.Basic

/-!
# Axiom-policy assertion command

`#assert_standard_axioms decl` fails elaboration — and therefore any batch build or CI
run containing it — if `decl` depends on any axiom other than `propext`,
`Classical.choice`, or `Quot.sound`. The audit modules use it to make the repository's
axiom policy executable rather than merely inspectable.
-/

open Lean Elab Command in
/-- `#assert_standard_axioms decl` fails elaboration (exiting nonzero in batch mode) if
`decl` depends on any axiom other than `propext`, `Classical.choice`, or `Quot.sound`. -/
elab "#assert_standard_axioms " id:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverload id
  let axioms ← liftCoreM <| collectAxioms c
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := axioms.filter fun a ↦ !allowed.contains a
  unless bad.isEmpty do
    throwError "'{c}' depends on non-standard axioms: {bad.toList}"
  logInfo m!"'{c}' depends only on standard axioms: {axioms.toList}"
