/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.RepresentationIso
import ComputableModelTheory.ModelTheory.Computable.PartialPotentialTransport

/-!
# Conjugating potential embedding data along a cover

Semantic conjugation (`RepresentationCoverIn.conjEmbedding`) transports a member embedding of `A`
to one of `B`. This file transports the *code* — the potential embedding data — so that the
computational and semantic pictures match.

The pipeline is fixed by what a cover does and does not guarantee. CHMM does not require an
isomorphism to carry recorded generators to recorded generators, so the target member's recorded
generators are not forward images of the source's. The transported data must be indexed by the
**target's** generators, and the route back to `A` is therefore:

`targetGensPreimage` → elementwise `applyPotentialPart F` → `toTuplePart` at `F.codIdx` → package.

Three things worth stating about that route.

*One backward pass, not two.* `targetGensPreimage` is the only use of a cover's inverse; the
second and third stages both run forward. Conjugation is `isoAt d`'s inverse followed by `f`
followed by `isoAt a`, and the pipeline is exactly that, once.

*Nothing is totalized.* The result stays in `Part`. Halting is a theorem about actual data
(`conjugatePart_dom`), not a property of the operation, matching `applyPotentialPart`, which has
no exact-domain theorem.

*Realization is stated at named indices.* `PartialRealizesAt` records the two index equations as
ordinary conjuncts, so the conclusion typechecks for an opaque returned datum — `PartialRealizes`
would need the indices to match definitionally, which they do only after substitution.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- A right-hand entry of a `Forall₂` is related to some left-hand entry. Stated here because the
halting proof needs to read a traversal's output backwards. -/
private theorem exists_mem_of_forall₂ {α β : Type*} {R : α → β → Prop} {l : List α}
    {l' : List β} (h : List.Forall₂ R l l') {y : β} (hy : y ∈ l') : ∃ x ∈ l, R x y := by
  obtain ⟨n, hn⟩ := List.mem_iff_get.1 hy
  have hlt : (n : ℕ) < l.length := by rw [h.length_eq]; exact n.isLt
  exact ⟨l.get ⟨n, hlt⟩, List.get_mem _ _, hn ▸ h.get hlt n.isLt⟩

namespace RepresentationCoverIn

variable {A B : PartialAgeIn O L} (r : RepresentationCoverIn E A B)

/-- **Transport potential embedding data along a cover.** Pull the target member's recorded
generators back into `A`, apply the source data there, push the results forward at the matched
codomain index, and package the result with the mapped indices.

Deliberately `Part`-valued: `applyPotentialPart` has no exact-domain theorem, so no totalization
is available or wanted. -/
noncomputable def conjugatePart (F : PotentialEmbeddingData) : Part PotentialEmbeddingData :=
  ((listMapPart (A.applyPotentialPart F) (r.targetGensPreimage F.domIdx)).bind
    (r.toTuplePart F.codIdx)).map fun t ↦
      PotentialEmbeddingData.ofTriple (r.indexMap F.domIdx, r.indexMap F.codIdx, t)

/-! ### Computability

`O ⊆ E` enters once, and for the two reasons it always does: reading the families' recorded
generators (inside `targetGensPreimage`), and running `applyPotentialPart`, which is recursive in
the presentation oracle. Traversal itself needs no inclusion. -/

/-- The packaging step, extracted and fully typed: composing against the `ofEquiv` encoding of
`PotentialEmbeddingData` from inside the enclosing expression stalls at `whnf`. -/
private def conjugateTriple (r : RepresentationCoverIn E A B)
    (q : PotentialEmbeddingData × List ℕ) : ℕ × ℕ × Tuple ℕ :=
  (r.indexMap q.1.domIdx, r.indexMap q.1.codIdx, q.2)

private theorem conjugateTriple_computableIn :
    ComputableIn E (r.conjugateTriple) :=
  (((r.indexMap_computableIn.comp
        (PotentialEmbeddingData.domIdx_computable.comp ComputableIn.fst)).pair
      ((r.indexMap_computableIn.comp
        (PotentialEmbeddingData.codIdx_computable.comp ComputableIn.fst)).pair
        ComputableIn.snd))).of_eq fun _ ↦ rfl

private theorem conjugateStage₁_recursiveIn (hOE : O ⊆ E) :
    RecursiveIn E fun F : PotentialEmbeddingData ↦
      listMapPart (A.applyPotentialPart F) (r.targetGensPreimage F.domIdx) := by
  have hpre : ComputableIn E fun F : PotentialEmbeddingData ↦ r.targetGensPreimage F.domIdx :=
    (r.targetGensPreimage_computableIn hOE).comp PotentialEmbeddingData.domIdx_computable
  have happly : RecursiveIn E fun q : PotentialEmbeddingData × List ℕ ↦
      listMapPart (A.applyPotentialPart q.1) q.2 :=
    RecursiveIn.listMapPart₂ (g := fun F : PotentialEmbeddingData ↦ A.applyPotentialPart F)
      (RecursiveIn.mono hOE A.applyPotentialPart_recursiveIn)
  exact RecursiveIn.comp (O := E) (α := PotentialEmbeddingData)
    (β := PotentialEmbeddingData × List ℕ) (σ := List ℕ)
    (f := fun q : PotentialEmbeddingData × List ℕ ↦ listMapPart (A.applyPotentialPart q.1) q.2)
    (g := fun F : PotentialEmbeddingData ↦ (F, r.targetGensPreimage F.domIdx))
    happly (ComputableIn.id.pair hpre)

private theorem conjugateStage₂_recursiveIn :
    RecursiveIn E fun q : PotentialEmbeddingData × List ℕ ↦ r.toTuplePart q.1.codIdx q.2 :=
  RecursiveIn.comp (O := E) (α := PotentialEmbeddingData × List ℕ) (β := ℕ × List ℕ)
    (σ := List ℕ)
    (f := fun p : ℕ × List ℕ ↦ r.toTuplePart p.1 p.2)
    (g := fun q : PotentialEmbeddingData × List ℕ ↦ (q.1.codIdx, q.2))
    r.toTuplePart_recursiveIn
    ((PotentialEmbeddingData.codIdx_computable.comp ComputableIn.fst).pair ComputableIn.snd)

private theorem conjugatePack_computableIn :
    ComputableIn E fun q : PotentialEmbeddingData × List ℕ ↦
      PotentialEmbeddingData.ofTriple (r.indexMap q.1.domIdx, r.indexMap q.1.codIdx, q.2) :=
  ComputableIn.comp (O := E) (α := PotentialEmbeddingData × List ℕ) (β := ℕ × ℕ × Tuple ℕ)
    (σ := PotentialEmbeddingData)
    (f := PotentialEmbeddingData.ofTriple) (g := r.conjugateTriple)
    PotentialEmbeddingData.ofTriple_computableIn r.conjugateTriple_computableIn

/-- **Conjugation of data is partial recursive in the map oracle.** -/
theorem conjugatePart_recursiveIn (hOE : O ⊆ E) : RecursiveIn E r.conjugatePart :=
  (RecursiveIn.map
    (RecursiveIn.bind (r.conjugateStage₁_recursiveIn hOE) r.conjugateStage₂_recursiveIn.to₂)
    r.conjugatePack_computableIn.to₂).of_eq fun _ ↦ rfl

/-! ### Correctness, in two independent parts

Halting and realization are separated because they need different hypotheses and say different
things. Halting needs only that the data is realized by *something*, and concludes nothing about
the value; realization needs an explicit realizer, and holds of *whatever* value the pipeline
returns — including on data whose halting was accidental. -/

/-- **Actual data conjugates.** Every entry of the target's generator preimage lies in the source
member, so each application halts; each value then lies in the codomain member, so the forward
traversal halts too. -/
theorem conjugatePart_dom {F : PotentialEmbeddingData} (h : A.PartialIsEmbedding F) :
    (r.conjugatePart F).Dom := by
  have hs : (listMapPart (A.applyPotentialPart F) (r.targetGensPreimage F.domIdx)).Dom :=
    listMapPart_dom_iff.2 fun x hx ↦
      PartialAgeIn.applyPotentialPart_dom_of_partialIsEmbedding h
        (r.targetGensPreimage_mem_domainAt F.domIdx x hx)
  obtain ⟨s, hsm⟩ := Part.dom_iff_mem.1 hs
  have hsmem : ∀ y ∈ s, y ∈ A.domainAt F.codIdx := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := exists_mem_of_forall₂ (mem_listMapPart_iff.1 hsm) hy
    exact PartialAgeIn.applyPotentialPart_mem_domainAt_of_partialIsEmbedding h
      (r.targetGensPreimage_mem_domainAt F.domIdx x hx) hxy
  obtain ⟨t, htm⟩ := Part.dom_iff_mem.1 (r.toTuplePart_dom_iff.2 hsmem)
  exact Part.dom_iff_mem.2
    ⟨_, (Part.mem_map_iff _).2 ⟨t, Part.mem_bind_iff.2 ⟨s, hsm, htm⟩, rfl⟩⟩

/-- The indices of a conjugated datum are the mapped indices. -/
theorem conjugatePart_indices {F G : PotentialEmbeddingData} (hG : G ∈ r.conjugatePart F) :
    G.domIdx = r.indexMap F.domIdx ∧ G.codIdx = r.indexMap F.codIdx := by
  obtain ⟨t, -, rfl⟩ := (Part.mem_map_iff _).1 hG
  exact ⟨rfl, rfl⟩

/-- **The conjugated datum is realized by the conjugated embedding.** Stated through
`PartialRealizesAt`, whose index equations are ordinary conjuncts — the returned datum is opaque,
so `PartialRealizes` would not typecheck without first substituting it away.

The coordinate computation is the three pipeline stages read in order: the `k`-th generator
preimage *is* `isoAt F.domIdx`'s inverse image of the `k`-th target generator, the `k`-th
application value *is* `f` there, and the `k`-th forward image *is* `isoAt F.codIdx` of that. -/
theorem conjugatePart_realizesAt {F : PotentialEmbeddingData}
    {f : (A.memberAt F.domIdx).domain ↪[L] (A.memberAt F.codIdx).domain}
    (hf : A.PartialRealizes F f) {G : PotentialEmbeddingData} (hG : G ∈ r.conjugatePart F) :
    B.PartialRealizesAt G (r.indexMap F.domIdx) (r.indexMap F.codIdx) (r.conjEmbedding f) := by
  obtain ⟨t, htmem, rfl⟩ := (Part.mem_map_iff _).1 hG
  obtain ⟨s, hsm, htm⟩ := Part.mem_bind_iff.1 htmem
  -- the three stages, as `Forall₂` facts
  have hpre := r.mem_invTuplePart_iff.1 (r.mem_targetGensPreimage F.domIdx)
  have hs := mem_listMapPart_iff.1 hsm
  have ht := r.mem_toTuplePart_iff.1 htm
  refine ⟨rfl, rfl, (hpre.length_eq.trans (hs.length_eq.trans ht.length_eq)), fun k ↦ ?_⟩
  have h₁ : (k : ℕ) < (r.targetGensPreimage F.domIdx).length := by
    rw [← hpre.length_eq]; exact k.isLt
  have h₂ : (k : ℕ) < s.length := by rw [← hs.length_eq]; exact h₁
  have h₃ : (k : ℕ) < t.length := by rw [← ht.length_eq]; exact h₂
  -- stage 1: the preimage coordinate is the inverse image of the target generator
  set x : (A.memberAt F.domIdx).domain :=
    (r.isoAt F.domIdx).toEquiv.symm (B.gensView (r.indexMap F.domIdx) k) with hxdef
  have hxval : (x : ℕ) = (r.targetGensPreimage F.domIdx).get ⟨k, h₁⟩ :=
    Part.mem_unique ((r.isoAt F.domIdx).symm.toSubtypeFun_mem _) (hpre.get k.isLt h₁)
  -- stage 2: the application coordinate is the realizer's value there
  have hsval : s.get ⟨k, h₂⟩ = ((f x : (A.memberAt F.codIdx).domain) : ℕ) := by
    refine Part.mem_unique (hs.get h₁ h₂) ?_
    rw [← hxval]
    exact PartialAgeIn.applyPotentialPart_mem_realizer hf (x := (x : ℕ)) x.2
  -- stage 3: the forward coordinate is the conjugate's value
  have htval : t.get ⟨k, h₃⟩ =
      (((r.isoAt F.codIdx).toEquiv (f x) : (B.memberAt (r.indexMap F.codIdx)).domain) : ℕ) := by
    refine Part.mem_unique (ht.get h₂ h₃) ?_
    rw [hsval]
    exact (r.isoAt F.codIdx).toSubtypeFun_mem (f x)
  rw [r.conjEmbedding_apply]
  exact htval.symm

end RepresentationCoverIn

end FirstOrder.Language
