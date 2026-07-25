/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialTheorem28
import ComputableModelTheory.ModelTheory.Computable.GraphExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for CHMM Theorem 2.8, empty-capable setting

An **end-to-end** acceptance run of the headline theorem on the case the empty-capable
layer exists for: a family in the graph language — no constants, no function symbols —
every member of which has a genuinely **empty** carrier. Outside the root import spine; CI
checks it via `scripts/run-audit-modules.sh`.

The gates invoke the public theorem and its public components; none of them reconstructs a
proof out of internal lemmas.

* `test_stepsForTuple_empty_query` — the step search on the empty tuple halts and returns
  the empty step list (the boundary Cameron flagged: it must be `stepsForTuple []` that is
  exercised, not merely the standalone empty generated presentation).
* `test_hasHP` — the family satisfies the *semantic* hereditary property. Every member is
  empty, so every finitely generated substructure of a member is empty, and any two empty
  graph structures are isomorphic.
* `test_theorem28` — the named assembly returns a family with the same isomorphism classes
  admitting a computable hereditary-property selector, and its witness is `reindexed`.
* `test_chp_empty_query` — the selector, invoked through `PartialCHP`, halts on the empty
  query tuple and the member it selects records generators exactly `[]`.
* `test_chp_empty_embedding` — the identity-on-values embedding specializes to an
  empty-into-empty embedding, with no `Nonempty` hypothesis anywhere.
* `test_reindexed_domain_empty` — the re-indexed member's carrier really is empty, so the
  run above is not vacuously about some nonempty stand-in.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)}

/-! ### Emptiness facts for the graph language -/

instance : IsEmpty (Language.graph.Term (Fin 0)) :=
  ⟨fun T ↦ by
    induction T with
    | var a => exact a.elim0
    | func f _ _ => exact isEmptyElim f⟩

/-- Any two empty graph structures are isomorphic. This needs the language: it is **false**
for a general language, since a `0`-ary relation could hold in one empty structure and fail
in the other. The graph language has relations only at arity `2`, and a `Fin 2`-tuple in an
empty type cannot exist. -/
def graphEmptyEquiv {M N : Type} [Language.graph.Structure M] [Language.graph.Structure N]
    [IsEmpty M] [IsEmpty N] : M ≃[Language.graph] N where
  toFun x := isEmptyElim x
  invFun y := isEmptyElim y
  left_inv x := isEmptyElim x
  right_inv y := isEmptyElim y
  map_fun' f _ := isEmptyElim f
  map_rel' {n} r x := by
    match n, r with
    | 0, r => exact isEmptyElim r
    | 1, r => exact isEmptyElim r
    | 2, .adj => exact isEmptyElim (x 0)
    | (_ + 3), r => exact isEmptyElim r

/-! ### The fixture: a graph family every member of which is empty -/

/-- A uniformly computable family in the constant-free relational graph language whose
every member has an **empty** carrier: nothing is ever enumerated, and the recorded
generator tuple is `[]`. The ambient structure data is the path graph on `ℕ`, so the
members are honest empty substructures of a genuine graph — not a degenerate language. -/
def emptyGraphFamily : PartialAgeIn O Language.graph where
  structureAt _ := pathGraphStructure
  enum? _ _ := Option.none
  enum?_computableIn := ComputableIn.const Option.none
  gens _ := []
  gens_computableIn := ComputableIn.const []
  funEval _ _ := Part.some 0
  funEval_recursiveIn := ComputableIn.const 0
  funEval_correct := fun _ d _ ↦ isEmptyElim d
  relEval _ _ := Part.some true
  relEval_recursiveIn := ComputableIn.const true
  relEval_correct := fun _ d hd ↦ by
    obtain ⟨n, r, v⟩ := d
    match n, r with
    | 0, r => exact isEmptyElim r
    | 1, r => exact isEmptyElim r
    | 2, .adj =>
      obtain ⟨m, hm⟩ := hd 0
      exact absurd hm (by simp)
    | (_ + 3), r => exact isEmptyElim r
  generates := fun _ x ↦ by
    constructor
    · rintro ⟨m, hm⟩
      exact absurd hm (by simp)
    · rintro ⟨T, -⟩
      exact isEmptyElim (show Language.graph.Term (Fin 0) from T)

@[simp]
theorem emptyGraphFamily_domainAt (i : ℕ) :
    (emptyGraphFamily (O := O)).domainAt i = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ hx ↦ by
    obtain ⟨m, hm⟩ := hx
    exact absurd hm (by simp [emptyGraphFamily])

instance (i : ℕ) : IsEmpty ((emptyGraphFamily (O := O)).memberAt i).domain :=
  ⟨fun s ↦ absurd (show (s : ℕ) ∈ (emptyGraphFamily (O := O)).domainAt i from s.2)
    (by simp)⟩

/-! ### The gates -/

/-- Gate: the step search on the **empty** query tuple halts, returning the empty step
list. -/
theorem test_stepsForTuple_empty_query (i : ℕ) :
    ([] : List ℕ) ∈ (emptyGraphFamily (O := O)).stepsForTuple i [] :=
  Part.mem_some _

/-- Gate: the family satisfies the semantic hereditary property. Every member is empty, so
every finitely generated substructure of a member is empty, and any two empty graph
structures are isomorphic. -/
theorem test_hasHP : (emptyGraphFamily (O := O)).HasHP := by
  intro i n t
  haveI : IsEmpty (Substructure.closure Language.graph (Set.range t)) :=
    ⟨fun s ↦ isEmptyElim s.1⟩
  exact ⟨0, ⟨graphEmptyEquiv⟩⟩

/-- Gate: the named Theorem 2.8 assembly applies, and its witness is the tuple
re-indexing. -/
theorem test_theorem28 :
    (∃ B : PartialAgeIn O Language.graph,
        (emptyGraphFamily (O := O)).SameClass B ∧ B.PartialCHP) ∧
      (emptyGraphFamily (O := O)).SameClass (emptyGraphFamily (O := O)).reindexed ∧
      (emptyGraphFamily (O := O)).reindexed.PartialCHP :=
  ⟨PartialAgeIn.exists_sameClass_partialCHP _ test_hasHP,
    ((emptyGraphFamily (O := O)).reindexed_sameClass test_hasHP).symm,
    (emptyGraphFamily (O := O)).reindexed_partialCHP⟩

/-- Gate: invoked through the public `PartialCHP` predicate, the selector halts on the
empty query tuple and the member it selects records generators exactly `[]` — and that
member sits inside the queried one. -/
theorem test_chp_empty_query (e : ℕ) :
    ∃ (sel : ℕ → List ℕ →. ℕ) (c : ℕ), c ∈ sel e [] ∧
      (emptyGraphFamily (O := O)).reindexed.gens c = [] ∧
      (emptyGraphFamily (O := O)).reindexed.structureAt c =
        (emptyGraphFamily (O := O)).reindexed.structureAt e ∧
      (emptyGraphFamily (O := O)).reindexed.domainAt c ⊆
        (emptyGraphFamily (O := O)).reindexed.domainAt e := by
  obtain ⟨sel, -, hspec⟩ := (emptyGraphFamily (O := O)).reindexed_partialCHP
  obtain ⟨c, hc, hgens, hstr, hsub⟩ := hspec e [] (by simp)
  exact ⟨sel, c, hc, hgens, hstr, hsub⟩

/-- Gate: the identity-on-values embedding of the selected member into the queried one
exists for the empty query — empty into empty, with no `Nonempty` hypothesis. -/
theorem test_chp_empty_embedding (e : ℕ) :
    ∃ c : ℕ, Nonempty
      (((emptyGraphFamily (O := O)).reindexed.memberAt c).domain ↪[Language.graph]
        ((emptyGraphFamily (O := O)).reindexed.memberAt e).domain) := by
  obtain ⟨sel, -, hspec⟩ := (emptyGraphFamily (O := O)).reindexed_partialCHP
  obtain ⟨c, -, -, hstr, hsub⟩ := hspec e [] (by simp)
  exact ⟨c, ⟨PartialAgeIn.memberEmbedding hstr hsub⟩⟩

/-- Gate: the re-indexed members really are empty — the run above is not vacuously about a
nonempty stand-in. -/
theorem test_reindexed_domain_empty (e : ℕ) :
    (emptyGraphFamily (O := O)).reindexed.domainAt e = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ by
    have h := (emptyGraphFamily (O := O)).reindexed_domainAt_subset e hx
    rw [emptyGraphFamily_domainAt] at h
    exact h

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_stepsForTuple_empty_query
#assert_standard_axioms FirstOrder.Language.test_hasHP
#assert_standard_axioms FirstOrder.Language.test_theorem28
#assert_standard_axioms FirstOrder.Language.test_chp_empty_query
#assert_standard_axioms FirstOrder.Language.test_chp_empty_embedding
#assert_standard_axioms FirstOrder.Language.test_reindexed_domain_empty
