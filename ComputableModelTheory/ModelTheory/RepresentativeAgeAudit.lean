/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.RepresentativeAge
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: Fraïssé classes from concrete representatives

Outside the root import spine; CI checks it explicitly.

* **Independent universes**: language, index and carrier universes are separate
  (`test_countable_quotient`); the class lives in the carrier universe.
* **Countability is of isomorphism classes**, not of the bundled class
  (`test_countable_quotient`).
* **An empty index gives the empty class** (`test_empty_index`); **an empty carrier can be a
  representative** (`test_empty_carrier`) — inhabited index and inhabited carriers are distinct.
* **Standard axioms** for every declaration of the production module (the `run_cmd` below scans the
  module's own constants, whatever their namespace) and for the regression rows.
* **Import isolation**: the production module's only import besides `Init` is
  `Mathlib.ModelTheory.Fraisse`, and its transitive closure contains no module of this library or of
  `InfinitaryLogic`.
-/

universe u v w z

open CategoryTheory FirstOrder FirstOrder.Language

namespace FirstOrder.Language

/-- Essential countability, in independent language, index and carrier universes: countably many
isomorphism classes, not a countable set of bundled structures. -/
theorem test_countable_quotient {L : Language.{u, v}} {I : Type z} [Countable I]
    (F : I → Bundled.{w} L.Structure) :
    (Quotient.mk' '' representativeClass F).Countable :=
  representativeClass_countable_quotient F

/-- An empty carrier can be a representative. -/
theorem test_empty_carrier {L : Language} {M : Type*} [L.Structure M] [IsEmpty M] :
    (⟨M, inferInstance⟩ : Bundled L.Structure) ∈
      representativeClass (fun _ : Unit => (⟨M, inferInstance⟩ : Bundled L.Structure)) :=
  mem_representativeClass _ ()

/-- An empty index gives the empty class. -/
theorem test_empty_index {L : Language} (F : Empty → Bundled L.Structure) :
    representativeClass F = ∅ := by
  ext M
  constructor
  · rintro ⟨i, _⟩
    exact i.elim
  · intro h
    exact False.elim h

end FirstOrder.Language

-- Every declaration of the production module uses only the standard axioms, and the module's
-- imports stay below the computable layers.
open Lean in
run_cmd do
  let env ← getEnv
  let target := `ComputableModelTheory.ModelTheory.RepresentativeAge
  let some idx := env.getModuleIdx? target | throwError "{target} is not imported"
  let mut count := 0
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then
      count := count + 1
      for ax in ← collectAxioms n do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "{n} uses nonstandard axiom {ax}"
  if count == 0 then throwError "no declarations found in {target}"
  let direct := (env.header.moduleData[idx.toNat]!).imports.map (·.module)
  unless direct.filter (· != `Init) == #[`Mathlib.ModelTheory.Fraisse] do
    throwError "unexpected direct imports of {target}: {direct}"
  let mut seen : NameSet := {}
  let mut todo : Array Name := direct
  while h : todo.size > 0 do
    let m := todo.back
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    if (`ComputableModelTheory).isPrefixOf m || (`InfinitaryLogic).isPrefixOf m then
      throwError "{target} transitively imports {m}"
    if let some j := env.getModuleIdx? m then
      todo := todo ++ (env.header.moduleData[j.toNat]!).imports.map (·.module)

#assert_standard_axioms FirstOrder.Language.test_countable_quotient
#assert_standard_axioms FirstOrder.Language.test_empty_carrier
#assert_standard_axioms FirstOrder.Language.test_empty_index
