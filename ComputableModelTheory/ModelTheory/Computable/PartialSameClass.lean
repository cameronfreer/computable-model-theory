/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialAgeSemantics
import ComputableModelTheory.ModelTheory.Computable.PartialTupleReindex

/-!
# The re-indexed family represents the same isomorphism classes

CHMM Theorem 2.8's same-class conclusion for the empty-capable setting: under the
**semantic** hereditary property `HasHP`, the tuple re-indexing `A.reindexed` and the
original family `A` represent the same isomorphism classes.

Both directions run entirely through the semantic bridges of `PartialAgeSemantics` — no
enumeration and no evaluator appears:

* **Re-indexed → original.** Member `e`'s carrier is exactly the closure of
  `tupleAtSteps` (the range equality), so `closureDomainEquiv` identifies it with that
  tuple's closure computed *inside* the ambient member's carrier. `HasHP` then supplies a
  member isomorphic to that closure, and the two isomorphisms compose.
* **Original → re-indexed.** `stepsForTuple` halts on the recorded generators — they are
  on-domain — and returns steps recovering them, so the re-indexed member at those steps
  has generator tuple exactly `gens j`. Its carrier is the closure of `gens j`, which the
  original generation law says is all of member `j`. The two members then have equal
  carriers and the identity closes it.

The second direction is deliberately **semantic and existential**. `stepsForTuple` is
partial recursive, but that is not used here and would not justify more: nothing claims
the two representations are computably isomorphic, and Theorem 2.8 does not need it.

The identity equivalence (`eqDomainEquiv`) needs no nonemptiness, so a member with empty
generators and an empty carrier — the case the empty-capable layer exists for — closes
through carrier equality alone.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace PartialAgeIn

variable (A : PartialAgeIn O L)

/-! ### The re-indexed generator tuple, inside the ambient member -/

/-- The recorded generator tuple of re-indexed member `e`, lifted into the ambient member's
carrier subtype. The lift is possible precisely because `tupleAtSteps` is on-domain by
construction — this is what ranging over enumeration steps rather than raw tuples buys. -/
noncomputable def reindexGens (e : ℕ) :
    Fin (A.reindexed.gens e).length → (A.memberAt (memberIndex e).1).domain :=
  fun k ↦ ⟨(A.reindexed.gens e).get k,
    A.mem_domainAt_of_mem_tupleAtSteps ((A.reindexed.gens e).get_mem k)⟩

@[simp]
theorem reindexGens_val (e : ℕ) (k : Fin (A.reindexed.gens e).length) :
    ((A.reindexGens e k : (A.memberAt (memberIndex e).1).domain) : ℕ) =
      Tuple.view (A.reindexed.gens e) k :=
  rfl

/-- The carrier of a re-indexed member, by term values over its lifted generator tuple:
the form `closureDomainEquiv` consumes. -/
theorem mem_reindexed_domain_iff_term (e : ℕ) (x : ℕ) :
    x ∈ (A.reindexed.memberAt e).domain ↔
      ∃ T : L.Term (Fin (A.reindexed.gens e).length),
        ((T.realize (A.reindexGens e) : (A.memberAt (memberIndex e).1).domain) : ℕ) = x := by
  letI : L.Structure ℕ := A.structureAt (memberIndex e).1
  rw [PartialAgeIn.memberAt_domain, A.reindexed_domainAt e]
  show x ∈ Substructure.closure L (Set.range (Tuple.view (A.reindexed.gens e))) ↔ _
  rw [mem_closure_range_iff_exists_term]
  exact exists_congr fun T ↦ by
    rw [(A.memberAt (memberIndex e).1).realize_domain_val (A.reindexGens e) T]
    rfl

/-! ### Re-indexed → original, through the semantic hereditary property -/

/-- Every re-indexed member is isomorphic to some original member: its carrier *is* the
closure of a finite tuple inside an original member, and `HasHP` is exactly the statement
that such closures reappear. -/
theorem exists_isoTo_of_hasHP (h : A.HasHP) (e : ℕ) :
    ∃ j, (A.reindexed.memberAt e).IsoTo (A.memberAt j) := by
  obtain ⟨j, hj⟩ := h (memberIndex e).1 (A.reindexed.gens e).length (A.reindexGens e)
  refine ⟨j, hj.elim fun eq ↦ ⟨eq.comp ?_⟩⟩
  exact PartialCePresentationIn.closureDomainEquiv (P := A.memberAt (memberIndex e).1)
    (Q := A.reindexed.memberAt e) (A.reindexGens e) rfl (A.mem_reindexed_domain_iff_term e)

/-! ### Original → re-indexed, through the recorded generators -/

/-- The recorded generators of a member are on-domain — so `stepsForTuple` halts on
them. -/
theorem gens_forall_mem_domainAt (j : ℕ) : ∀ x ∈ A.gens j, x ∈ A.domainAt j := by
  intro x hx
  obtain ⟨k, hk⟩ := List.mem_iff_get.1 hx
  exact hk ▸ A.gens_mem_domainAt k

/-- Every original member reappears among the re-indexed ones, by the identity: pick
enumeration steps recovering its recorded generators, and the re-indexed member there has
the same carrier. No nonemptiness hypothesis — an empty member closes through the carrier
equality alone. -/
theorem exists_isoTo_reindexed (j : ℕ) :
    ∃ e, (A.memberAt j).IsoTo (A.reindexed.memberAt e) := by
  obtain ⟨steps, -, hsteps⟩ := A.exists_mem_stepsForTuple (A.gens_forall_mem_domainAt j)
  obtain ⟨e, he⟩ := memberIndex_surjective j steps
  have hstr : (A.memberAt j).str = (A.reindexed.memberAt e).str := by
    show A.structureAt j = A.structureAt (memberIndex e).1
    rw [he]
  have hdom : (A.memberAt j).domain = (A.reindexed.memberAt e).domain := by
    rw [PartialAgeIn.memberAt_domain, PartialAgeIn.memberAt_domain, A.reindexed_domainAt e]
    ext x
    rw [A.mem_domainAt_iff_term]
    show (∃ T : L.Term (Fin (A.gens j).length),
        x = @Term.realize L ℕ (A.structureAt j) _ (Tuple.view (A.gens j)) T) ↔
      x ∈ @Substructure.closure L ℕ (A.structureAt (memberIndex e).1)
        (Set.range (Tuple.view (A.tupleAtSteps (memberIndex e).1 (memberIndex e).2)))
    rw [he]
    letI : L.Structure ℕ := A.structureAt j
    show _ ↔ x ∈ Substructure.closure L (Set.range (Tuple.view (A.tupleAtSteps j steps)))
    rw [hsteps, mem_closure_range_iff_exists_term]
    exact ⟨fun ⟨T, hT⟩ ↦ ⟨T, hT.symm⟩, fun ⟨T, hT⟩ ↦ ⟨T, hT.symm⟩⟩
  exact ⟨e, ⟨PartialCePresentationIn.eqDomainEquiv hstr hdom⟩⟩

/-! ### The same-class conclusion -/

/-- **CHMM Theorem 2.8, same-class conclusion (empty-capable setting).** Under the
semantic hereditary property, the tuple re-indexing represents exactly the isomorphism
classes of the original family. No claim of computable isomorphism is made or needed. -/
theorem reindexed_sameClass (h : A.HasHP) : A.reindexed.SameClass A :=
  ⟨A.exists_isoTo_of_hasHP h, A.exists_isoTo_reindexed⟩

end PartialAgeIn

end FirstOrder.Language
