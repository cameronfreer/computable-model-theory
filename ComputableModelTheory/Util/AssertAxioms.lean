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

`#assert_module_standard_axioms Mod` applies the same check to **every** declaration whose defining
module is `Mod`, whatever its namespace — so a module's audit cannot silently miss a constant that a
hand-written list or a namespace-prefix scan would omit.
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

open Lean Elab Command in
/-- `#assert_module_standard_axioms Mod` fails elaboration if any declaration defined in the
imported module `Mod` depends on an axiom other than `propext`, `Classical.choice`, or
`Quot.sound`, or if `Mod` defines no declarations at all. -/
elab "#assert_module_standard_axioms " mod:ident : command => do
  let env ← getEnv
  let m := mod.getId
  let some idx := env.getModuleIdx? m | throwError "module '{m}' is not imported"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then
      count := count + 1
      let axioms ← liftCoreM <| collectAxioms n
      let bad := axioms.filter fun a ↦ !allowed.contains a
      unless bad.isEmpty do
        throwError "'{n}' (defined in {m}) depends on non-standard axioms: {bad.toList}"
  if count == 0 then
    throwError "module '{m}' defines no declarations"
  logInfo m!"all {count} declarations of {m} depend only on standard axioms"
