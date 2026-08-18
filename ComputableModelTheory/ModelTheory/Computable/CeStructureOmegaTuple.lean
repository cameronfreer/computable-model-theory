/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureOmegaLimit

/-!
# The tuple pullback: a finite ω-tuple at one common stage

Given a finite tuple of ω-codes — the shape a CHP query arrives in — produce a stage and a tuple of
elements *of that stage* whose ω-images are the original codes. Two traversals composed:

```
s : List ℕ  ──listMapPart rankEnum──▶  raw  ──transportRawArgsPart──▶  out,  at stage rawStageBound raw
```

**The stage is returned with the tuple.** Returning `List ℕ` alone would discard the index needed to
query the scheduled family, forcing a consumer to re-search for a common stage it already computed.

**The certificate sits on halting only.** The definition and its `RecursiveIn` theorem are
certificate-free: `transportRawArgsPart` halts unconditionally, and the only thing that can diverge
is `rankEnum` at a rank the presentation does not reach. So infinitude is exactly the hypothesis
that the query's codes name limit elements at all.

The load-bearing result is `forall₂_omegaStageEmbedding`: the pulled-back tuple is not merely
carrier-valid at one stage — its ω-image is the original query **coordinatewise**. That equality is
what the CHP cover consumes, and it is the reason `stageEmbedding_transport` had to be proved for an
arbitrary transport: a tuple's entries reach the common stage from different depths, and nothing
records how far.

Effectivity of the coordinate theorem rests on `RepresentedByRawRep` — that the carrier codes are
named by their own raw representatives. It is a hypothesis here and a theorem for the canonical
limit (`toLimit_representedByRawRep`); a limit that named its elements some other way would still
have every other fact below.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace CeStructureChainIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {D : CeStructureChainIn O L}

namespace LimitIn

variable (Z : D.LimitIn)

/-! ### The pullback -/

/-- **Pull a tuple of ω-codes back to a common stage**, returning the stage alongside the tuple.
Certificate-free by construction: divergence can only come from `rankEnum`. -/
noncomputable def rankTupleAtStagePart (s : List ℕ) : Part (ℕ × List ℕ) :=
  (listMapPart Z.presentation.rankEnum s).bind fun raw ↦
    (D.toDomainChain.transportRawArgsPart raw).map fun out ↦
      (D.toDomainChain.rawStageBound raw, out)

/-- Partial recursive in the oracle, with no certificate. -/
theorem rankTupleAtStagePart_recursiveIn : RecursiveIn O Z.rankTupleAtStagePart := by
  have hA : RecursiveIn O fun s : List ℕ ↦ listMapPart Z.presentation.rankEnum s :=
    RecursiveIn.listMapPart Z.presentation.rankEnum_recursiveIn
  have hB : RecursiveIn O fun q : List ℕ × List ℕ ↦
      (D.toDomainChain.transportRawArgsPart q.2).map fun out ↦
        (D.toDomainChain.rawStageBound q.2, out) :=
    RecursiveIn.map
      (D.toDomainChain.transportRawArgsPart_recursiveIn.comp ComputableIn.snd)
      (((D.toDomainChain.rawStageBound_computableIn.comp
        (ComputableIn.snd.comp ComputableIn.fst)).pair ComputableIn.snd).to₂)
  exact RecursiveIn.bind hA hB.to₂

/-- **Membership, with the intermediate raw tuple exposed.** Consumers name `raw` and never reopen
either traversal. -/
theorem mem_rankTupleAtStagePart_iff {s : List ℕ} {p : ℕ × List ℕ} :
    p ∈ Z.rankTupleAtStagePart s ↔
      ∃ raw : List ℕ,
        List.Forall₂ (fun n a ↦ a ∈ Z.presentation.rankEnum n) s raw ∧
          p.1 = D.toDomainChain.rawStageBound raw ∧
          p.2 ∈ D.toDomainChain.transportRawArgsPart raw := by
  rw [rankTupleAtStagePart]
  constructor
  · intro h
    obtain ⟨raw, hraw, hmap⟩ := Part.mem_bind_iff.1 h
    obtain ⟨out, hout, rfl⟩ := (Part.mem_map_iff _).1 hmap
    exact ⟨raw, mem_listMapPart_iff.1 hraw, rfl, hout⟩
  · rintro ⟨raw, hraw, hstage, hout⟩
    refine Part.mem_bind_iff.2 ⟨raw, mem_listMapPart_iff.2 hraw, ?_⟩
    exact (Part.mem_map_iff _).2 ⟨p.2, hout, Prod.ext hstage.symm rfl⟩

/-- **Halting, under the certificate.** The one place infinitude enters: `transportRawArgsPart`
halts on every list, so only `rankEnum` can diverge. -/
theorem rankTupleAtStagePart_dom (cert : Z.presentation.InfinitudeCertificate) (s : List ℕ) :
    (Z.rankTupleAtStagePart s).Dom := by
  have h₁ : (listMapPart Z.presentation.rankEnum s).Dom :=
    listMapPart_dom_iff.2 fun n _ ↦
      (Z.presentation.rankEnum_dom_iff n).2 (cert.rankIdx_dom n)
  obtain ⟨raw, hraw⟩ := Part.dom_iff_mem.1 h₁
  obtain ⟨out, hout⟩ := Part.dom_iff_mem.1 (D.toDomainChain.transportRawArgsPart_dom raw)
  exact Part.dom_iff_mem.2 ⟨(D.toDomainChain.rawStageBound raw, out),
    Z.mem_rankTupleAtStagePart_iff.2 ⟨raw, mem_listMapPart_iff.1 hraw, rfl, hout⟩⟩

/-- **The boundary case**, with no certificate: the empty query is answered at stage `0`. Both
traversals return `[]` and `rawStageBound [] = 0`, so this is definitional — nullary data is
evaluated once, at the bottom of the chain. -/
@[simp]
theorem rankTupleAtStagePart_nil : Z.rankTupleAtStagePart [] = Part.some (0, []) := by
  rw [rankTupleAtStagePart, listMapPart_nil, Part.bind_some,
    CeDomainChainIn.transportRawArgsPart, listMapPart_nil, Part.map_some,
    CeDomainChainIn.rawStageBound, List.foldr_nil]

/-! ### Shape and validity -/

/-- The output tuple has the query's length. -/
theorem rankTupleAtStagePart_length {s : List ℕ} {p : ℕ × List ℕ}
    (h : p ∈ Z.rankTupleAtStagePart s) : p.2.length = s.length := by
  obtain ⟨raw, hraw, -, hout⟩ := Z.mem_rankTupleAtStagePart_iff.1 h
  exact (hraw.length_eq.trans
    (D.toDomainChain.mem_transportRawArgsPart_iff.1 hout).length_eq).symm

/-- **Every output entry lives at the returned stage** — the point of computing a common stage. -/
theorem mem_domainAt_of_mem_rankTupleAtStagePart {s : List ℕ} {p : ℕ × List ℕ}
    (h : p ∈ Z.rankTupleAtStagePart s) : ∀ y ∈ p.2, y ∈ (D.stageAt p.1).domain := by
  obtain ⟨raw, -, hstage, hout⟩ := Z.mem_rankTupleAtStagePart_iff.1 h
  rw [hstage]
  exact D.toDomainChain.mem_domainAt_of_mem_transportRawArgsPart hout

/-! ### The coordinate theorem -/

/-- The coordinate argument at a **fixed** bound `M`, so the `Forall₂` motive never mentions the
list being traversed — the same discipline `mem_domainAt_of_forall₂_transportTo` needs. The
per-entry chain is: `rankEnum` puts the entry in the carrier and `rankOf_rankEnum` records its rank;
`RepresentedByRawRep` turns the carrier code into a stage element; `stageEmbedding_transport` moves
that element to `M`; and the two `rankOf` memberships are then single-valued. -/
private theorem forall₂_omegaStageEmbedding_aux (hrep : Z.RepresentedByRawRep) {M : ℕ}
    {s raw out : List ℕ}
    (h₁ : List.Forall₂ (fun n a ↦ a ∈ Z.presentation.rankEnum n) s raw)
    (h₂ : List.Forall₂ (fun a y ↦ y ∈ D.toDomainChain.transportTo
      (D.toDomainChain.rawRep a).1 M (D.toDomainChain.rawRep a).2) raw out)
    (hle : ∀ a ∈ raw, (D.toDomainChain.rawRep a).1 ≤ M) :
    List.Forall₂ (fun n y ↦ ∃ hy : y ∈ (D.stageAt M).domain,
      Z.omegaStageEmbedding M ⟨y, hy⟩ = n) s out := by
  induction h₁ generalizing out with
  | nil =>
    rw [List.forall₂_nil_left_iff] at h₂
    subst h₂
    exact List.Forall₂.nil
  | @cons n a s' raw' hna h₁' ih =>
    rw [List.forall₂_cons_left_iff] at h₂
    obtain ⟨y, out', hay, h₂', rfl⟩ := h₂
    refine List.Forall₂.cons ?_
      (ih h₂' fun b hb ↦ hle b (List.mem_cons_of_mem _ hb))
    -- The carrier element named by rank `n`, and its rank.
    have hadom : a ∈ Z.presentation.domain := Z.presentation.mem_domain_of_mem_rankEnum hna
    have hrank : n ∈ Z.presentation.rankOf a := Z.presentation.rankOf_rankEnum hna
    -- Its own raw representative is a stage element mapping to it.
    obtain ⟨hstage, hcode⟩ := hrep ⟨a, hadom⟩
    -- Move that element to the common stage.
    obtain ⟨hy, htr⟩ := Z.stageEmbedding_transport
      (hle a List.mem_cons_self) hstage hay
    refine ⟨hy, ?_⟩
    have hval : Z.omegaStageEmbedding M ⟨y, hy⟩ = Z.rankEmbedding ⟨a, hadom⟩ := by
      simp only [omegaStageEmbedding_apply, ← htr, hcode]
    rw [hval]
    exact Part.mem_unique (Z.rankEmbedding_apply_mem ⟨a, hadom⟩) hrank

/-- **The load-bearing coordinate theorem.** The pulled-back tuple's ω-image is the original query,
entry by entry — not merely a tuple that happens to be valid at one stage. This is what the CHP
cover consumes; it should never need to unfold either traversal. -/
theorem forall₂_omegaStageEmbedding (hrep : Z.RepresentedByRawRep) {s : List ℕ}
    {p : ℕ × List ℕ} (h : p ∈ Z.rankTupleAtStagePart s) :
    List.Forall₂ (fun n y ↦ ∃ hy : y ∈ (D.stageAt p.1).domain,
      Z.omegaStageEmbedding p.1 ⟨y, hy⟩ = n) s p.2 := by
  obtain ⟨M, out⟩ := p
  obtain ⟨raw, hraw, hstage, hout⟩ := Z.mem_rankTupleAtStagePart_iff.1 h
  subst hstage
  exact Z.forall₂_omegaStageEmbedding_aux hrep hraw
    (D.toDomainChain.mem_transportRawArgsPart_iff.1 hout)
    fun _ ha ↦ D.toDomainChain.le_rawStageBound ha

end LimitIn

end CeStructureChainIn

end FirstOrder.Language
