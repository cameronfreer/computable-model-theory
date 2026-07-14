/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.Jump
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for the minimal oracle jump calculus

Named acceptance tests for the `ComputesJumpOf` interface, its bridges, and the displayed
`0′` implementation, checked by `#assert_standard_axioms`. Outside the root import spine;
CI checks it via `scripts/run-audit-modules.sh`.

Coverage: the oracle-lifting and domain-decision clauses at coded types; the positive and
pivotal (r.e.-complement) bridges; monotonicity and the iterated-jump composition; the
concrete `haltingChar` instance at the empty oracle set; and non-vacuity — the classical
halting problem is decidable in the displayed `0′`.
-/

open Encodable

section

variable {α : Type*} [Primcodable α]
variable {J J₁ J₂ O : Set (ℕ →. ℕ)} {p : α → Prop}

/-- Oracle lifting for computable predicates. -/
theorem test_computesJumpOf_lift (hJ : ComputesJumpOf J O) (hp : ComputablePredIn O p) :
    ComputablePredIn J p :=
  hJ.computablePredIn_lift hp

/-- An `O`-r.e. predicate is decidable in any jump-computing oracle set. -/
theorem test_rePredIn_computablePredIn (hJ : ComputesJumpOf J O) (hp : REPredIn O p) :
    ComputablePredIn J p :=
  hJ.rePredIn_computablePredIn hp

/-- The pivotal bridge: an `O`-r.e.-complement predicate is decidable in any
jump-computing oracle set. -/
theorem test_compl_rePredIn_computablePredIn (hJ : ComputesJumpOf J O)
    (hp : REPredIn O fun a ↦ ¬p a) : ComputablePredIn J p :=
  hJ.compl_rePredIn_computablePredIn hp

/-- Monotonicity in the deciding oracle set. -/
theorem test_computesJumpOf_mono (hJJ : J₁ ⊆ J) (hJ : ComputesJumpOf J₁ O) :
    ComputesJumpOf J O :=
  hJ.mono_left hJJ

/-- Iterated jumps compose at the interface level. -/
theorem test_computesJumpOf_trans (h₂ : ComputesJumpOf J₂ J₁)
    (h₁ : ComputesJumpOf J₁ O) : ComputesJumpOf J₂ O :=
  h₂.trans h₁

/-- The displayed `0′`: the halting characteristic computes the jump of the empty
oracle set. -/
theorem test_computesJumpOf_haltingChar_empty :
    ComputesJumpOf {haltingChar} (∅ : Set (ℕ →. ℕ)) :=
  computesJumpOf_haltingChar_empty

/-- Non-vacuity: the classical halting problem is decidable in the displayed `0′`. -/
theorem test_haltingKernel_computablePredIn :
    ComputablePredIn {haltingChar} haltingKernel :=
  haltingKernel_computablePredIn

/-- The pivotal bridge instantiated at the displayed `0′`: any co-c.e. predicate on a
coded type is decidable in the halting characteristic. -/
theorem test_compl_rePred_computablePredIn_haltingChar
    (hp : REPredIn (∅ : Set (ℕ →. ℕ)) fun a ↦ ¬p a) :
    ComputablePredIn {haltingChar} p :=
  computesJumpOf_haltingChar_empty.compl_rePredIn_computablePredIn hp

end

#assert_standard_axioms test_computesJumpOf_lift
#assert_standard_axioms test_rePredIn_computablePredIn
#assert_standard_axioms test_compl_rePredIn_computablePredIn
#assert_standard_axioms test_computesJumpOf_mono
#assert_standard_axioms test_computesJumpOf_trans
#assert_standard_axioms test_computesJumpOf_haltingChar_empty
#assert_standard_axioms test_haltingKernel_computablePredIn
#assert_standard_axioms test_compl_rePred_computablePredIn_haltingChar
