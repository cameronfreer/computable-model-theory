/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CanonicalAgeBackwardCover
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the backward cover `K → 𝕂_𝒟`

Three rows carry the design; the rest is the cover itself.

**The guard.** `test_guard_diverges_off_carrier` says an off-carrier input diverges, and
`test_guard_needs_nothing_downstream` says the responsible direction of the domain law uses neither
the certificate nor any fact about `applyPotentialPart` or `rankStageMap`. Together they are the
statement that matters: divergence off the carrier does **not** depend on what the later partial
programs would have done, because the first bind never releases the input to them. Without the
guard `map_dom` would be one-way, and the induced `PartialCeIsoIn`'s `toFun_dom` field — an iff —
would be false.

**The target index.** `test_indexMap_eq_self_iff` converts "the cover silently returned its input
index" into a checkable statement about the image tuple: the index is `i` exactly when the image
tuple is `allTupleFor i`. So the index is computed from actual embedding values rather than copied,
and a reader can see what would have to be true for it to coincide with `i`.
`test_target_index_is_computed` exhibits those values coordinatewise.

**One oracle.** `test_backwardCover` is stated at a single `O` on both sides — not by convention but
because `RepresentationCoverIn E A B` takes `A` and `B` at one family oracle, so no cover exists
between a representation and the `𝕂_𝒟` of a limit built at a larger one. The base-oracle discipline
is enforced by this row's type.

`test_generatorCompatible` is the payoff, and its proof is the generated-image constructor's
theorem with no new coordinate argument.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {K : PartialAgeIn O L} {sel : ℕ → ℕ → PartialJointEmbeddingData} {baseIdx : ℕ}

/-! ### The carrier crossing -/

/-- **The crossing moves nothing.** Totalizing a scheduled member changes neither its carrier nor
its stored structure, so the family-side and chain-side carriers are the same values presented at
two layers. Both covers make this crossing; it is public API, not a private step. -/
theorem test_crossing_is_identity {hne : ∀ n, (K.domainAt (cjepSchedule sel baseIdx n)).Nonempty}
    {hOE : O ⊆ E} (n : ℕ) (x : (K.memberAt (cjepSchedule sel baseIdx n)).domain) :
    ((scheduledStageEquiv (hne := hne) (hOE := hOE) n x :
      (scheduledStage K sel baseIdx hne hOE n).domain) : ℕ) = (x : ℕ) :=
  rfl

section Cover

variable {hne : ∀ n, (K.domainAt (cjepSchedule sel baseIdx n)).Nonempty}
variable {hspec : K.JointSpec sel} {hsel : ComputableIn O fun p : ℕ × ℕ ↦ sel p.1 p.2}
variable (Z : (selfChain K sel baseIdx hne hspec hsel).LimitIn)
variable (cert : Z.presentation.InfinitudeCertificate)

/-! ### The guard -/

/-- **The responsible direction needs nothing downstream.** No certificate, and no fact about the
two partial programs the guard precedes. -/
theorem test_guard_needs_nothing_downstream {n x : ℕ} (h : (omegaMap Z n x).Dom) :
    x ∈ K.domainAt n :=
  mem_domainAt_of_omegaMap_dom Z h

/-- **An off-carrier input diverges** — whatever `applyPotentialPart` and `rankStageMap` would have
done with it, since the first bind never releases it to them. -/
theorem test_guard_diverges_off_carrier {n x : ℕ} (hx : x ∉ K.domainAt n) :
    ¬ (omegaMap Z n x).Dom :=
  fun h ↦ hx (mem_domainAt_of_omegaMap_dom Z h)

include cert in
/-- **The exact domain**, which is what `PartialCeIsoIn.toFun_dom` demands. One-way halting would
not do. -/
theorem test_map_dom (n x : ℕ) : (omegaMap Z n x).Dom ↔ x ∈ K.domainAt n :=
  omegaMap_dom Z cert n x

/-! ### The two sides -/

/-- **The semantic embedding and the program agree.** The three stages contribute one membership
each: the guard returns its input, the cofinal realizer is a value of `applyPotentialPart`, and the
recoded stage embedding is a value of `rankStageMap`. -/
theorem test_map_apply_mem (n : ℕ) (x : (K.memberAt n).domain) :
    omegaEmbedding Z cert n x ∈ omegaMap Z n (x : ℕ) :=
  omegaEmbedding_mem_omegaMap Z cert n x

/-- Uniformly partial recursive in the index — per-index proofs would not build a cover. -/
theorem test_map_uniform : RecursiveIn O fun p : ℕ × ℕ ↦ omegaMap Z p.1 p.2 :=
  omegaMap_uniform Z

/-! ### The target index -/

/-- **The target index is computed from embedding values**, coordinatewise: the image tuple is the
program's image of `K.gens i`. -/
theorem test_target_index_is_computed (i : ℕ) :
    List.Forall₂ (fun x y ↦ y ∈ omegaMap Z i x) (K.gens i)
        ((toLimitEmbedding Z cert).toSelected.imageTuple i) ∧
      (backwardCover Z cert).indexMap i = encode ((toLimitEmbedding Z cert).toSelected.imageTuple i) :=
  ⟨(toLimitEmbedding Z cert).toSelected.forall₂_imageTuple i, rfl⟩

/-- **The cover cannot silently use `i`.** Returning the input index is equivalent to the image
tuple being `allTupleFor i` — a checkable statement about the construction's output, not an
assumption about it. -/
theorem test_indexMap_eq_self_iff (i : ℕ) :
    (backwardCover Z cert).indexMap i = i ↔
      (toLimitEmbedding Z cert).toSelected.imageTuple i = allTupleFor i := by
  rw [backwardCover_indexMap]
  constructor
  · intro h
    exact ((congrArg allTupleFor h).symm.trans
      (allTupleFor_encode ((toLimitEmbedding Z cert).toSelected.imageTuple i))).symm
  · intro h
    rw [h, allTupleFor, Denumerable.encode_ofNat]

/-! ### The cover -/

/-- **The backward cover of CHMM Theorem 2.10(⇐).** Stated at a **single** oracle `O` on both
sides — the base-oracle discipline is enforced by this type, since `RepresentationCoverIn` admits
no cover between representations at different family oracles. -/
theorem test_backwardCover :
    Nonempty (RepresentationCoverIn O K (limitStructure Z cert).canonicalAge) :=
  ⟨backwardCover Z cert⟩

/-- **It is generator-compatible** — the constructor's theorem, with no new coordinate argument.
This is the half of Theorem 2.10(⇐)'s compatibility that `allTupleFor_encode` supplies; the other
half is CHP's, on the forward cover. -/
theorem test_generatorCompatible : (backwardCover Z cert).GeneratorCompatible :=
  backwardCover_generatorCompatible Z cert

end Cover

end PartialAgeIn

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_crossing_is_identity
#assert_standard_axioms
  FirstOrder.Language.PartialAgeIn.test_guard_needs_nothing_downstream
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_guard_diverges_off_carrier
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_map_dom
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_map_apply_mem
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_map_uniform
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_target_index_is_computed
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_indexMap_eq_self_iff
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_backwardCover
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_generatorCompatible
