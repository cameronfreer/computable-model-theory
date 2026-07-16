/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ComputableAge
import InfinitaryLogic.Scott.AtomicDiagram
import InfinitaryLogic.Scott.BackAndForth
import InfinitaryLogic.Methods.Henkin.Completeness

/-!
# Thin representation boundary to `infinitary-logic`

The B1a bridge: `infinitary-logic` is pinned at `6614ec7` (Lean and mathlib `v4.32.0`,
matching this repository), and this module is the *entire* deliberate import surface —
exactly the Scott/back-and-forth modules D2 needs and the Henkin module E1 needs, no
umbrella import. Transitive helper dependencies: `LeanArchitect` (the `@[blueprint]`
attribute) and `checkdecls`.

Both projects build on mathlib's `FirstOrder.Language` and `L.Structure`, in the same
`FirstOrder.Language` namespace, so the boundary is instance-discipline alignment, not
data conversion: upstream declarations take structures as instance-implicits, while a
computable age carries its structures as *values* (`K.structureAt i`). The wrappers here
(`sameAtomicTypeAt`, `bfEquivAt`) fix those instances by explicit `@`-application — the
same discipline as the rest of the age layer — and `bfEquivAt_zero` re-exports the
upstream level-zero characterization through the boundary.

Import-surface status at `6614ec7` (all proved, standard axioms — audited in
`InfinitaryBridgeAudit`):

* `SameAtomicType` (`Scott/AtomicDiagram.lean`) — **relational caveat**, documented
  upstream at its definition: for languages with function symbols it omits arbitrary term
  equalities, so it is weaker than full atomic equivalence; CMT's `AtomicEquivalent`
  includes them. D2's agreement theorem therefore carries `[L.IsRelational]`;
  relationalization for general languages would be a separate bridge, not part of D2.
* `BFEquiv`, `BFEquiv.zero` (`Scott/BackAndForth.lean`) — the definitions do not consume
  `[L.IsRelational]`; the hypothesis matters for the semantic adequacy above, not for
  well-formedness.
* `TermModel`, `termModelStructure`, `truthLemma`, `ConsistencyPropertyEq`,
  `model_existence`, `karp_completeness` (`Methods/Henkin/*`) — classical existence
  through maximal-consistency machinery from a *supplied* consistency property; E1 will
  reuse the syntax and semantic lemmas without pretending the construction is effective.
-/

open FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace ComputableAgeIn

variable (K : ComputableAgeIn O L)

/-- Same atomic type between tuples of the presentations at two indices, with the stored
structures passed explicitly. The boundary wrapper for `SameAtomicType`; on relational
languages this is upstream's full atomic-type agreement (see the module docstring for the
function-symbol caveat). -/
def sameAtomicTypeAt (i j : ℕ) {n : ℕ} (a b : Fin n → ℕ) : Prop :=
  @SameAtomicType L ℕ (K.structureAt i) n ℕ (K.structureAt j) a b

/-- Back-and-forth equivalence at an ordinal between tuples of the presentations at two
indices, with the stored structures passed explicitly. The boundary wrapper for
`BFEquiv`. -/
def bfEquivAt (i j : ℕ) (α : Ordinal) {n : ℕ} (a b : Fin n → ℕ) : Prop :=
  @BFEquiv L ℕ (K.structureAt i) ℕ (K.structureAt j) α n a b

/-- Level zero of back-and-forth equivalence is same atomic type, through the boundary:
the upstream characterization `BFEquiv.zero` re-exported at indexed presentations. -/
theorem bfEquivAt_zero (i j : ℕ) {n : ℕ} (a b : Fin n → ℕ) :
    K.bfEquivAt i j 0 a b ↔ K.sameAtomicTypeAt i j a b :=
  @BFEquiv.zero L ℕ (K.structureAt i) ℕ (K.structureAt j) n a b

end ComputableAgeIn

end FirstOrder.Language
