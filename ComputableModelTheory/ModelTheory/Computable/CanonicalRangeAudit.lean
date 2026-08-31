/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CanonicalRange
import ComputableModelTheory.ModelTheory.Computable.ConstantExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the generated range of a realized embedding

**`test_range_equality` is the load-bearing row.** Everything else in `CanonicalRange` is packaging
over it: the corestriction is the same carrier map with a membership proof, and the equivalence adds
only surjectivity, which is the range equality read backwards. Gating it separately means a later
refactor cannot weaken the semantic content while leaving the two wrappers looking intact.

**Nothing here is effective**, and `test_no_effectivity_needed` says so by shape: the equivalence is
produced from an embedding and a realization witness alone — no oracle, no inclusion hypothesis, no
`Part`. That is what lets the same lemma serve both half-steps and the base case of Proposition 3.2,
which sit at different oracles.

**The empty-source case is exercised on a language with a constant.** With no constants `D_[]` is
empty and surjectivity onto it is trivial; the interesting case is a nonempty member with *no*
recorded generators, which is exactly what a constant produces.
`test_empty_source_nonempty_target` puts the equivalence onto `D_[] = {7}` in the one-constant
language, so the surjectivity clause has something to hit. Without this row, the base case of the
back-and-forth would be gated only where it is vacuous.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn.PartialRealizesBetween

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {A : PartialAgeIn O L} {S : ComputableStructureIn O L}
variable {F : PotentialEmbeddingData}
variable {f : (A.memberAt F.domIdx).domain ↪[L] (S.canonicalAge.memberAt F.codIdx).domain}

/-! ### The load-bearing fact -/

/-- **The range of a realized embedding is exactly the canonical member at its range tuple's
code.** A member is the term-closure of its recorded generators, and the embedding carries terms to
terms over `F.rangeTuple`; on the canonical side that tuple *is* the member's own recorded tuple.

The two wrappers below are packaging; this is the content. -/
theorem test_range_equality (h : PartialRealizesBetween A S.canonicalAge F f) :
    Set.range (fun x : (A.memberAt F.domIdx).domain ↦
        ((f x : (S.canonicalAge.memberAt F.codIdx).domain) : ℕ))
      = S.canonicalAge.domainAt (encode F.rangeTuple) :=
  range_eq_canonicalAge_domainAt h

/-- **The target must be a canonical age.** This row records the dependency by shape: the statement
names `S.canonicalAge` on the right, and the proof rests on `gens (encode t) = t`, which no general
`PartialAgeIn` supplies. The *source* `A` is arbitrary. -/
theorem test_source_is_arbitrary (h : PartialRealizesBetween A S.canonicalAge F f) :
    S.canonicalAge.gens (encode F.rangeTuple) = F.rangeTuple ∧
      Set.range (fun x : (A.memberAt F.domIdx).domain ↦
          ((f x : (S.canonicalAge.memberAt F.codIdx).domain) : ℕ))
        = S.canonicalAge.domainAt (encode F.rangeTuple) :=
  ⟨allTupleFor_encode F.rangeTuple, range_eq_canonicalAge_domainAt h⟩

/-! ### The packaging -/

/-- The corestriction moves nothing: its underlying natural is `f`'s. -/
theorem test_corestriction_is_f (h : PartialRealizesBetween A S.canonicalAge F f)
    (x : (A.memberAt F.domIdx).domain) :
    ((toCanonicalRangeEmbedding h x :
        (S.canonicalAge.memberAt (encode F.rangeTuple)).domain) : ℕ)
      = ((f x : (S.canonicalAge.memberAt F.codIdx).domain) : ℕ) :=
  rfl

/-- Surjectivity — the range equality read backwards, and the only thing the equivalence adds. -/
theorem test_surjective (h : PartialRealizesBetween A S.canonicalAge F f) :
    Function.Surjective (toCanonicalRangeEmbedding h) :=
  toCanonicalRangeEmbedding_surjective h

/-- **The keystone**, and its application equation: the equivalence is the same carrier map. -/
theorem test_equiv (h : PartialRealizesBetween A S.canonicalAge F f) :
    Nonempty ((A.memberAt F.domIdx).domain ≃[L]
        (S.canonicalAge.memberAt (encode F.rangeTuple)).domain) ∧
      ∀ x, ((toCanonicalRangeEquiv h x :
          (S.canonicalAge.memberAt (encode F.rangeTuple)).domain) : ℕ)
        = ((f x : (S.canonicalAge.memberAt F.codIdx).domain) : ℕ) :=
  ⟨⟨toCanonicalRangeEquiv h⟩, fun _ ↦ rfl⟩

/-- **The corestriction is itself realized**, at the data with the codomain moved to
`encode F.rangeTuple` — so the three consumers of the keystone never reopen the range equality. -/
theorem test_corestriction_realizes (h : PartialRealizesBetween A S.canonicalAge F f) :
    PartialRealizesBetween A S.canonicalAge
      (PotentialEmbeddingData.ofTriple (F.domIdx, encode F.rangeTuple, F.rangeTuple))
      (toCanonicalRangeEquiv h).toEmbedding :=
  toCanonicalRangeEquiv_realizes h

/-- **The inverse realizes the reverse tight data**, whose range tuple is the *source's own* recorded
generators. That is what makes it more than a restatement of `test_corestriction_realizes`: the
forward direction's range tuple is handed to it by `F`, the reverse direction's has to be read off
`A`. Both half-steps of the back-and-forth invert an equivalence of this shape. -/
theorem test_corestriction_symm_realizes (h : PartialRealizesBetween A S.canonicalAge F f) :
    PartialRealizesBetween S.canonicalAge A
      (PotentialEmbeddingData.ofTriple (encode F.rangeTuple, F.domIdx, A.gens F.domIdx))
      (toCanonicalRangeEquiv h).symm.toEmbedding :=
  toCanonicalRangeEquiv_symm_realizes h

/-- The two directions meet where they should: the forward corestriction's codomain index is the
inverse's domain index. -/
theorem test_corestriction_symm_endpoints (_h : PartialRealizesBetween A S.canonicalAge F f) :
    (PotentialEmbeddingData.ofTriple
        (F.domIdx, encode F.rangeTuple, F.rangeTuple)).codIdx
      = (PotentialEmbeddingData.ofTriple
        (encode F.rangeTuple, F.domIdx, A.gens F.domIdx)).domIdx :=
  rfl

/-- **No effectivity is consumed.** The equivalence is produced from an embedding and a realization
witness alone — no oracle appears in the hypotheses beyond the one carrying the families, no `O ⊆ E`,
no `Part`. This is what lets one lemma serve both half-steps and the base case of Proposition 3.2. -/
theorem test_no_effectivity_needed
    (f : (A.memberAt F.domIdx).domain ↪[L] (S.canonicalAge.memberAt F.codIdx).domain)
    (h : PartialRealizesBetween A S.canonicalAge F f) :
    Nonempty ((A.memberAt F.domIdx).domain ≃[L]
      (S.canonicalAge.memberAt (encode F.rangeTuple)).domain) :=
  ⟨toCanonicalRangeEquiv h⟩

end PartialAgeIn.PartialRealizesBetween

/-! ### The empty-source case, on a language with a constant

With no constants `D_[]` is empty and surjectivity onto it says nothing. The one-constant language
gives a member with **no recorded generators and a nonempty carrier**, which is the case the base
step of the back-and-forth actually meets. -/

section EmptySource

variable {O : Set (ℕ →. ℕ)}

/-- The one-constant structure, as a computable structure. -/
def constS (O : Set (ℕ →. ℕ)) : ComputableStructureIn O constLang :=
  { inst := constStructure, isComputable := constIsComputable }

/-- The empty query's data: no generators on either side. -/
def emptyF : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple
    (encode ([] : Tuple ℕ), encode ([] : Tuple ℕ), ([] : Tuple ℕ))

/-- **The empty-generated member is nonempty**: the constant is in it. This is what makes the
surjectivity clause non-trivial below. -/
theorem test_empty_member_is_nonempty :
    (7 : ℕ) ∈ (constS O).canonicalAge.domainAt (encode ([] : Tuple ℕ)) := by
  refine (constS O).mem_canonicalAge_domainAt_of_gens (allTupleFor_encode []) ?_
  refine ⟨Term.func ConstFunctions.c (fun k ↦ k.elim0), ?_⟩
  rfl

/-- The identity realizes the empty data. -/
theorem emptyF_realizes :
    (constS O).canonicalAge.PartialRealizesBetween ((constS O).canonicalAge) emptyF
      (PartialAgeIn.memberEmbedding rfl (Set.Subset.refl _)) := by
  refine ⟨?_, ?_⟩
  · show ((constS O).canonicalAge.gens (encode ([] : Tuple ℕ))).length = ([] : Tuple ℕ).length
    rw [(constS O).canonicalAge_gens, allTupleFor_encode]
  · intro k
    have hgens : (constS O).canonicalAge.gens emptyF.domIdx = [] := allTupleFor_encode []
    have hzero : ((constS O).canonicalAge.gens emptyF.domIdx).length = 0 := by rw [hgens]; rfl
    exact (Fin.cast hzero k).elim0

/-- **Surjectivity onto a nonempty constant closure.** The source member has no recorded generators
at all, yet the equivalence must hit `7` — so the empty case is exercised where it has content, not
only where it is vacuous. -/
theorem test_empty_source_nonempty_target :
    ∃ x, ((PartialAgeIn.PartialRealizesBetween.toCanonicalRangeEquiv
        (emptyF_realizes (O := O)) x :
      ((constS O).canonicalAge.memberAt (encode emptyF.rangeTuple)).domain) : ℕ) = 7 := by
  obtain ⟨x, hx⟩ := PartialAgeIn.PartialRealizesBetween.toCanonicalRangeEmbedding_surjective
    (emptyF_realizes (O := O)) ⟨7, test_empty_member_is_nonempty⟩
  exact ⟨x, congrArg Subtype.val hx⟩

end EmptySource

end FirstOrder.Language

#assert_standard_axioms
  FirstOrder.Language.PartialAgeIn.PartialRealizesBetween.test_range_equality
#assert_standard_axioms
  FirstOrder.Language.PartialAgeIn.PartialRealizesBetween.test_source_is_arbitrary
#assert_standard_axioms
  FirstOrder.Language.PartialAgeIn.PartialRealizesBetween.test_corestriction_is_f
#assert_standard_axioms
  FirstOrder.Language.PartialAgeIn.PartialRealizesBetween.test_surjective
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.PartialRealizesBetween.test_equiv
#assert_standard_axioms
  FirstOrder.Language.PartialAgeIn.PartialRealizesBetween.test_corestriction_realizes
#assert_standard_axioms
  FirstOrder.Language.PartialAgeIn.PartialRealizesBetween.test_corestriction_symm_realizes
#assert_standard_axioms
  FirstOrder.Language.PartialAgeIn.PartialRealizesBetween.test_corestriction_symm_endpoints
#assert_standard_axioms
  FirstOrder.Language.PartialAgeIn.PartialRealizesBetween.test_no_effectivity_needed
#assert_standard_axioms FirstOrder.Language.test_empty_member_is_nonempty
#assert_standard_axioms FirstOrder.Language.emptyF_realizes
#assert_standard_axioms FirstOrder.Language.test_empty_source_nonempty_target
