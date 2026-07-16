/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.AtomicEquiv
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

section RelationalAgreement

/-! ### D2: the relational agreement theorem

On relational languages the two atomic notions coincide: CMT's `AtomicEquivalent`
(agreement on all term equalities and relation atoms) and upstream's `SameAtomicType`
(agreement on all variable-level atomic indices). The relational hypothesis is essential
in the equivalence's interesting direction: with function symbols, `AtomicIdx` omits
equalities between non-variable terms, so `SameAtomicType` would be strictly weaker.
Relationalization of general languages is a separate bridge, deliberately not part of
this theorem. -/

variable {L' : Language} {M N : Type*} [L'.Structure M] [L'.Structure N] {k : ℕ}

/-- In a relational language every term is a variable. -/
private theorem exists_eq_var [L'.IsRelational] {α : Type*} (t : L'.Term α) :
    ∃ i, t = Term.var i := by
  cases t with
  | var i => exact ⟨i, rfl⟩
  | func f _ => exact isEmptyElim f

/-- D2 agreement, general form: on a relational language, atomic equivalence is exactly
same atomic type. Variables index all atoms: term-equality atoms reduce to
variable-equality indices and relation atoms to relation indices, in both directions. -/
theorem atomicEquivalent_iff_sameAtomicType [L'.IsRelational] (a : Fin k → M)
    (b : Fin k → N) :
    AtomicEquivalent L' a b ↔ @SameAtomicType L' M _ k N _ a b := by
  constructor
  · rintro ⟨hterm, hrel⟩ idx
    cases idx with
    | eq i j => exact hterm (Term.var i) (Term.var j)
    | rel R f => exact hrel R fun m ↦ Term.var (f m)
  · intro h
    refine ⟨fun t₁ t₂ ↦ ?_, fun R ts ↦ ?_⟩
    · obtain ⟨i, rfl⟩ := exists_eq_var t₁
      obtain ⟨j, rfl⟩ := exists_eq_var t₂
      exact h (.eq i j)
    · choose g hg using fun m ↦ exists_eq_var (ts m)
      have ha : (fun m ↦ (ts m).realize a) = a ∘ g := funext fun m ↦ by rw [hg m]; rfl
      have hb : (fun m ↦ (ts m).realize b) = b ∘ g := funext fun m ↦ by rw [hg m]; rfl
      rw [ha, hb]
      exact h (.rel R g)

end RelationalAgreement

namespace ComputableAgeIn

variable (K : ComputableAgeIn O L)

/-- D2 at indexed presentations: on a relational language, same atomic type through the
boundary is CMT's atomic equivalence with the stored structures passed explicitly. -/
theorem sameAtomicTypeAt_iff_atomicEquivalent [L.IsRelational] (i j : ℕ) {n : ℕ}
    (a b : Fin n → ℕ) :
    K.sameAtomicTypeAt i j a b ↔
      @AtomicEquivalent L ℕ ℕ (K.structureAt i) (K.structureAt j) n a b :=
  (@atomicEquivalent_iff_sameAtomicType L ℕ ℕ (K.structureAt i) (K.structureAt j) n
    _ a b).symm

/-- D2 in back-and-forth form: on a relational language, level zero of back-and-forth
equivalence at indexed presentations is CMT's atomic equivalence. -/
theorem bfEquivAt_zero_iff_atomicEquivalent [L.IsRelational] (i j : ℕ) {n : ℕ}
    (a b : Fin n → ℕ) :
    K.bfEquivAt i j 0 a b ↔
      @AtomicEquivalent L ℕ ℕ (K.structureAt i) (K.structureAt j) n a b :=
  (K.bfEquivAt_zero i j a b).trans (K.sameAtomicTypeAt_iff_atomicEquivalent i j a b)

end ComputableAgeIn

end FirstOrder.Language
