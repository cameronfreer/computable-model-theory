/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Lean

/-!
# Import-closure guard

The classical entry point promises **Mathlib plus the classical layer, nothing else**. This module
states that boundary once, as data, so the audit that enforces it and the control that exercises
it share one definition.

* `forbiddenPrefixes`: this library itself (outside the explicitly allowed modules),
  `InfinitaryLogic`, and `TauCeti`, which infinitary-logic's dependency graph brings in.
* `isForbidden allowed m`: `m` lies under a forbidden prefix and is not in `allowed`.
* `forbiddenInClosure env allowed roots`: every forbidden module in the transitive import closure
  of `roots`, read from the environment's module headers. It returns them all, rather than failing
  on the first, so a control can ask *which* prefixes were reached.
-/

open Lean

namespace ComputableModelTheory.ImportGuard

/-- The module-name prefixes the classical layer's import closure must avoid. -/
def forbiddenPrefixes : List Name :=
  [`ComputableModelTheory, `InfinitaryLogic, `TauCeti]

/-- A module is forbidden when it lies under a forbidden prefix and is not explicitly allowed. -/
def isForbidden (allowed : List Name) (m : Name) : Bool :=
  !allowed.contains m && forbiddenPrefixes.any (·.isPrefixOf m)

/-- Every forbidden module in the transitive import closure of `roots`, roots included. -/
def forbiddenInClosure (env : Environment) (allowed : List Name) (roots : Array Name) :
    Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := roots
  let mut bad : Array Name := #[]
  while h : todo.size > 0 do
    let m := todo.back
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    if isForbidden allowed m then bad := bad.push m
    if let some j := env.getModuleIdx? m then
      todo := todo ++ (env.header.moduleData[j.toNat]!).imports.map (·.module)
  return bad

end ComputableModelTheory.ImportGuard
