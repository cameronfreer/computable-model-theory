/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.InfinitaryBridge
import ComputableModelTheory.Util.ImportGuard

/-!
# Audit: the classical import guard detects what it forbids

`ClassicalAudit` walks the classical entry point's import closure and finds no forbidden module.
That is only meaningful if the same walk *does* report forbidden modules where they are present.
This control runs it from the infinitary bridge, which imports infinitary-logic and, through it,
TauCeti: the walk must report modules under **both** `InfinitaryLogic` and `TauCeti`.

Kept separate from `ClassicalAudit` so that audit's own imports stay the classical entry point and
the test tooling.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let root := `ComputableModelTheory.ModelTheory.Computable.InfinitaryBridge
  let bad := ComputableModelTheory.ImportGuard.forbiddenInClosure env [] #[root]
  unless bad.any (`TauCeti).isPrefixOf do
    throwError "the import guard reports no TauCeti module from {root}"
  unless bad.any (`InfinitaryLogic).isPrefixOf do
    throwError "the import guard reports no InfinitaryLogic module from {root}"
