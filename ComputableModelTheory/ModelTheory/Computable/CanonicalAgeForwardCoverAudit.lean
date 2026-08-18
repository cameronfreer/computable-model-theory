/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CanonicalAgeForwardCover
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the forward cover `𝕂_𝒟 → K`

**The hypothesis split is the point of this file.** `test_answer_totality_needs_no_rep` takes the
`InfinitudeCertificate` and the selector spec and *nothing else*: the pulled tuple's validity at its
stage is carrier bookkeeping, and says nothing about how carrier codes are named.
`test_self_matching_needs_rep` is where `RepresentedByRawRep` appears, because that is where
`forall₂_omegaStageEmbedding` — the statement that the pullback's ω-image is the query — is used.
The two rows sit next to each other so that a later refactor cannot quietly move the stronger
hypothesis earlier.

`test_one_answer` records that the stage, the pulled tuple and the selected index come out of a
*single* `Part`. Totalizing them separately would let them drift — the tuple is valid only at its own
stage, and the selected member is related only to that tuple — and no later theorem would catch it.

`test_empty_query` exercises `[] ↦ (0, [])` all the way through the hereditary property. Without it,
a later nonemptiness assumption could enter the producer unnoticed: `PartialAgeIn` is empty-capable
precisely so the canonical age's empty-tuple member is a real member, and the forward cover must
answer its query like any other.

`test_forwardCover_generatorCompatible` is the payoff, and its proof is the generic theorem
verbatim — the whole point of routing both covers through the generated-image constructor.
`test_both_directions` shows the two covers side by side, at one oracle, each compatible.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {K : PartialAgeIn O L}

/-! ### The selector-facing form -/

/-- **CHP hands over potential embedding data with a realizer** — the form the producer consumes,
so no coordinate bookkeeping crosses the boundary. -/
theorem test_chpSpec_extraction {E : Set (ℕ →. ℕ)} (h : MappedPartialCHPIn E K) :
    ∃ sel : ℕ → List ℕ →. ℕ,
      RecursiveIn E (fun p : ℕ × List ℕ ↦ sel p.1 p.2) ∧ K.MappedCHPSpec sel :=
  MappedPartialCHPIn.exists_chpSpec h

section Cover

variable {sel : ℕ → ℕ → PartialJointEmbeddingData} {baseIdx : ℕ}
variable {hne : ∀ n, (K.domainAt (cjepSchedule sel baseIdx n)).Nonempty}
variable {hspec : K.JointSpec sel} {hsel : ComputableIn O fun p : ℕ × ℕ ↦ sel p.1 p.2}
variable (Z : (selfChain K sel baseIdx hne hspec hsel).LimitIn)
variable (chpSel : ℕ → List ℕ →. ℕ)

/-! ### The answer, and what its totality costs -/

/-- **The pulled tuple is a valid query at its stage** — carrier bookkeeping only, with no claim
about how carrier codes are named. -/
theorem test_query_validity {e : ℕ} {p : ℕ × List ℕ}
    (hp : p ∈ Z.rankTupleAtStagePart (allTupleFor e)) :
    ∀ x ∈ p.2, x ∈ K.domainAt (cjepSchedule sel baseIdx p.1) :=
  mem_domainAt_of_mem_rankTuple Z hp

/-- **Totality of the answer needs the certificate and the selector spec — and not
`RepresentedByRawRep`.** This row typechecks precisely because `forwardAnswerPart_dom` takes no
such hypothesis; if a refactor moved it earlier, this row would stop elaborating. -/
theorem test_answer_totality_needs_no_rep (cert : Z.presentation.InfinitudeCertificate)
    (hchpSpec : K.MappedCHPSpec chpSel) (e : ℕ) : (forwardAnswerPart Z chpSel e).Dom :=
  forwardAnswerPart_dom Z chpSel cert hchpSpec e

variable (cert : Z.presentation.InfinitudeCertificate) (hchpSpec : K.MappedCHPSpec chpSel)

include cert hchpSpec in
/-- **One answer, one `.get`.** The stage, the pulled tuple and the selected index are projections of
a single member of a single `Part`, so they cannot drift apart. -/
theorem test_one_answer (e : ℕ) :
    (forwardStage Z chpSel cert hchpSpec e, forwardTuple Z chpSel cert hchpSpec e)
        ∈ Z.rankTupleAtStagePart (allTupleFor e) ∧
      forwardIndex Z chpSel cert hchpSpec e
        ∈ chpSel (cjepSchedule sel baseIdx (forwardStage Z chpSel cert hchpSpec e))
          (forwardTuple Z chpSel cert hchpSpec e) :=
  ⟨mem_rankTupleAtStagePart Z chpSel cert hchpSpec e, mem_chpSel Z chpSel cert hchpSpec e⟩

include cert hchpSpec in
/-- **The selection is actual**, from `MappedCHPSpec` with no coordinate argument. -/
theorem test_selection_is_actual (e : ℕ) :
    K.PartialIsEmbedding (forwardData Z chpSel cert hchpSpec e) :=
  forwardData_partialIsEmbedding Z chpSel cert hchpSpec e

/-! ### The empty canonical query -/

include cert hchpSpec in
/-- **The empty query is answered at stage `0` with the empty tuple**, through the hereditary
property like any other. `PartialAgeIn` is empty-capable so that the canonical age's empty-tuple
member is a real member; this row keeps a nonemptiness assumption from entering the producer. -/
theorem test_empty_query {e : ℕ} (he : allTupleFor e = []) :
    forwardStage Z chpSel cert hchpSpec e = 0 ∧ forwardTuple Z chpSel cert hchpSpec e = [] := by
  have h := mem_rankTupleAtStagePart Z chpSel cert hchpSpec e
  rw [he, Z.rankTupleAtStagePart_nil, Part.mem_some_iff] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

include cert hchpSpec in
/-- And such a query exists: the code of the empty tuple. -/
theorem test_empty_query_exists :
    forwardStage Z chpSel cert hchpSpec (encode ([] : Tuple ℕ)) = 0 ∧
      forwardTuple Z chpSel cert hchpSpec (encode ([] : Tuple ℕ)) = [] :=
  test_empty_query Z chpSel cert hchpSpec (allTupleFor_encode [])

/-! ### Self-matching -/

include cert hchpSpec in
/-- **The list-level theorem**: the program carries the selected member's recorded generators onto
the query's tuple. Two coordinate families composed — the selection's and the pullback's. -/
theorem test_forall₂_gens (hrep : Z.RepresentedByRawRep) (e : ℕ) :
    List.Forall₂ (fun x y ↦ y ∈ forwardMap Z chpSel cert hchpSpec e x)
      (K.gens (forwardIndex Z chpSel cert hchpSpec e)) (allTupleFor e) :=
  forall₂_forwardMap_gens Z chpSel cert hchpSpec hrep e

include cert hchpSpec in
/-- **Self-matching — and this is where `RepresentedByRawRep` enters**, since it is where the
pullback's ω-image is identified with the query. Compare with
`test_answer_totality_needs_no_rep`: the stronger hypothesis is confined to this side of the
construction. -/
theorem test_self_matching_needs_rep (hrep : Z.RepresentedByRawRep)
    (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2) (e : ℕ) :
    (toSelectedEmbedding Z chpSel cert hchpSpec hchp).imageTuple e = allTupleFor e :=
  imageTuple_eq_allTupleFor Z chpSel cert hchpSpec hrep hchp e

/-! ### The cover -/

include cert hchpSpec in
/-- **The forward cover `𝕂_𝒟 → K`**, with its index map the hereditary property's selected
member — no inverse-index assumption anywhere. -/
theorem test_forwardCover (hrep : Z.RepresentedByRawRep)
    (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2) :
    Nonempty (RepresentationCoverIn O (limitStructure Z cert).canonicalAge K) ∧
      ∀ e, (forwardCover Z chpSel cert hchpSpec hrep hchp).indexMap e
        = forwardIndex Z chpSel cert hchpSpec e :=
  ⟨⟨forwardCover Z chpSel cert hchpSpec hrep hchp⟩, fun _ ↦ rfl⟩

include cert hchpSpec in
/-- **The payoff: the forward cover is generator-compatible**, by the generic theorem verbatim.
This is the compatibility CHMM's forward implication assumes and, per
`CanonicalAgeSeparationAudit`, cannot have for free; the reverse implication constructs it. -/
theorem test_forwardCover_generatorCompatible (hrep : Z.RepresentedByRawRep)
    (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2) :
    (forwardCover Z chpSel cert hchpSpec hrep hchp).GeneratorCompatible :=
  forwardCover_generatorCompatible Z chpSel cert hchpSpec hrep hchp

include cert hchpSpec in
/-- **Both directions, at one oracle, each generator-compatible.** The two covers are built
independently — neither is a symmetrization — and this row is what a `RepresentationIsoIn` will
consume. -/
theorem test_both_directions (hrep : Z.RepresentedByRawRep)
    (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2) :
    (forwardCover Z chpSel cert hchpSpec hrep hchp).GeneratorCompatible ∧
      (backwardCover Z cert).GeneratorCompatible :=
  ⟨forwardCover_generatorCompatible Z chpSel cert hchpSpec hrep hchp,
    backwardCover_generatorCompatible Z cert⟩

end Cover

end PartialAgeIn

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_chpSpec_extraction
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_query_validity
#assert_standard_axioms
  FirstOrder.Language.PartialAgeIn.test_answer_totality_needs_no_rep
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_one_answer
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_selection_is_actual
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_empty_query
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_empty_query_exists
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_forall₂_gens
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_self_matching_needs_rep
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_forwardCover
#assert_standard_axioms
  FirstOrder.Language.PartialAgeIn.test_forwardCover_generatorCompatible
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_both_directions
