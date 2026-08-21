/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.RepresentationIso
import ComputableModelTheory.ModelTheory.Computable.PartialPotentialTransport
import ComputableModelTheory.Computability.ListSections

/-!
# Transporting potential embedding data between representations

Semantic conjugation (`PartialCeIsoIn.conjugate`) moves a member embedding; this file moves the
*code*, so the computational and semantic pictures agree.

**The primitive is two-ended.** A transport is parameterized by an isomorphism at each end,
supplied independently:

`B_{d'} → A_d → A_a → B_{a'}`

Tying both ends to one indexed family is the *diagonal* case, and it is not general enough. CHMM
Definition 2.3 supplies two covers with unrelated index maps and asserts no round trip, so a
witness queried at a `B`-index `e` cannot be answered by a single cover: `forward.indexMap` of
`backward.indexMap e` is not `e`, and nothing says it should be. The composites that do land
correctly mix the two covers, and each uses a *different* cover at its two ends — which is
expressible here precisely because `d'` and `a'` are independent.

The route within a transport is fixed by what a cover does not guarantee. CHMM does not require
an isomorphism to carry recorded generators to recorded generators, so the transported data must
be indexed by the **target** member's generators, and the pipeline is

`gensPreimage σ` → elementwise `applyPotentialPart F` → `listMapPart τ.toFun` → package.

Two further points. *Nothing is totalized*: the result stays in `Part`, and halting is a theorem
about actual data, matching `applyPotentialPart`, which has no exact-domain theorem. *Realization
is stated at named indices* through `PartialRealizesAt`, whose index equations are ordinary
conjuncts — the returned datum is opaque, and `PartialRealizes` would need those equations to
hold definitionally.

## What this machinery does not reach: CAP

`PartialCJEPIn` and the actual-span content of amalgamation transport along a representation
isomorphism. `PartialCAPIn` does not, and the gap is deliberate rather than pending.

Its *unconditional* clause promises `PartialWellFormed` of the right leg on arbitrary input,
where transport can offer nothing: `conjugateDataPart_dom` needs a realizer, and
`not_partialWellFormed_of_empty_codomain` shows some index pairs admit no well-formed datum at
all, so no total builder over index pairs exists either. There is also a convergence mismatch —
an input transformation would have to halt on every carrier-valid span while preserving
actualness on actual ones; `conjugateDataPart` preserves actualness but converges only on actual
data, a direct tuple map converges on carrier-valid data but need not preserve actualness once
generator tuples differ, and racing them cannot safely choose.

**This blocks the pointwise transport; it does not refute the implication.** Nothing here rules
out `A.PartialCAPIn E → B.PartialCAPIn E` by some altogether different selector choosing another
apex. The statement is therefore recorded as unsupported, not false, and no theorem asserts
either direction. The `PartialCAPIn` contract is unchanged.

Two honest recovery routes, neither taken here: specialize to the all-ℕ fragment, where
default-padded total transport is available and the empty-codomain obstruction cannot arise; or
add an explicit code-compatibility hypothesis — uniformly generator-respecting isomorphisms —
strictly stronger than `RepresentationIsoIn`, and kept out of the ordinary notion.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

section TwoEnded

variable {A B : PartialAgeIn O L} {d a d' a' : ℕ}

/-! ### The source end

The one place an inverse is used. Everything after it runs forward. -/

/-- The `σ`-preimages of the target member's recorded generators. Total: `σ`'s inverse halts
exactly on that member's carrier, and recorded generators are on-domain. -/
noncomputable def gensPreimage (σ : PartialCeIsoIn E (A.memberAt d) (B.memberAt d')) : List ℕ :=
  (listMapPart σ.invFun (B.gens d')).get
    (listMapPart_dom_iff.2 fun y hy ↦ (σ.invFun_dom y).2 (by
      obtain ⟨k, hk⟩ := List.mem_iff_get.1 hy
      exact hk ▸ B.gens_mem_domainAt k))

theorem mem_gensPreimage (σ : PartialCeIsoIn E (A.memberAt d) (B.memberAt d')) :
    gensPreimage σ ∈ listMapPart σ.invFun (B.gens d') :=
  Part.get_mem _

theorem gensPreimage_forall₂ (σ : PartialCeIsoIn E (A.memberAt d) (B.memberAt d')) :
    List.Forall₂ (fun y x ↦ x ∈ σ.invFun y) (B.gens d') (gensPreimage σ) :=
  mem_listMapPart_iff.1 (mem_gensPreimage σ)

theorem gensPreimage_length (σ : PartialCeIsoIn E (A.memberAt d) (B.memberAt d')) :
    (B.gens d').length = (gensPreimage σ).length :=
  (gensPreimage_forall₂ σ).length_eq

/-- The preimages are certified elements of the source member. -/
theorem gensPreimage_mem_domainAt (σ : PartialCeIsoIn E (A.memberAt d) (B.memberAt d'))
    {x : ℕ} (hx : x ∈ gensPreimage σ) : x ∈ (A.memberAt d).domain := by
  obtain ⟨y, -, hxy⟩ := List.Forall₂.exists_of_mem_right (gensPreimage_forall₂ σ) hx
  exact σ.invFun_mem hxy

/-- **The empty case explicitly.** A target member with no recorded generators gives the empty
preimage, even though the element map may be nowhere defined there. -/
theorem gensPreimage_of_gens_nil (σ : PartialCeIsoIn E (A.memberAt d) (B.memberAt d'))
    (h : B.gens d' = []) : gensPreimage σ = [] := by
  have hmem := mem_gensPreimage σ
  rw [h, listMapPart_nil] at hmem
  exact Part.mem_some_iff.1 hmem

/-- On the diagonal this is a cover's recorded generator preimage. -/
theorem gensPreimage_isoAt (r : RepresentationCoverIn E A B) (i : ℕ) :
    gensPreimage (r.isoAt i) = r.targetGensPreimage i := rfl

/-- Through a *backward* cover's inverse it is instead that cover's recorded generator **image**.
Both identifications hold on the nose, which is what lets the mixed composites inherit the
covers' uniform computability rather than needing their own. -/
theorem gensPreimage_isoAt_symm (s : RepresentationCoverIn E B A) (e : ℕ) :
    gensPreimage (s.isoAt e).symm = s.sourceGensImage e := rfl

/-! ### The transport -/

/-- **Two-ended transport of potential embedding data.** Pull the target member's recorded
generators back through `σ`, apply the source data there, push the results forward through `τ`,
and package with the two target indices. -/
noncomputable def conjugateDataPart (σ : PartialCeIsoIn E (A.memberAt d) (B.memberAt d'))
    (τ : PartialCeIsoIn E (A.memberAt a) (B.memberAt a')) (F : PotentialEmbeddingData) :
    Part PotentialEmbeddingData :=
  ((listMapPart (A.applyPotentialPart F) (gensPreimage σ)).bind
    (listMapPart τ.toFun)).map fun t ↦ PotentialEmbeddingData.ofTriple (d', a', t)

/-- The indices of a transported datum are the two target indices — read off the packaging, with
no appeal to either index map. -/
theorem conjugateDataPart_indices {σ : PartialCeIsoIn E (A.memberAt d) (B.memberAt d')}
    {τ : PartialCeIsoIn E (A.memberAt a) (B.memberAt a')} {F G : PotentialEmbeddingData}
    (hG : G ∈ conjugateDataPart σ τ F) : G.domIdx = d' ∧ G.codIdx = a' := by
  obtain ⟨t, -, rfl⟩ := (Part.mem_map_iff _).1 hG
  exact ⟨rfl, rfl⟩

/-- **Actual data transports.** Needs only that `F` is realized by *something*, and concludes
nothing about the value. The two index equations are what tie the opaque data to the two ends. -/
theorem conjugateDataPart_dom (σ : PartialCeIsoIn E (A.memberAt d) (B.memberAt d'))
    (τ : PartialCeIsoIn E (A.memberAt a) (B.memberAt a')) {F : PotentialEmbeddingData}
    (h : A.PartialIsEmbedding F) (hd : F.domIdx = d) (ha : F.codIdx = a) :
    (conjugateDataPart σ τ F).Dom := by
  subst hd
  subst ha
  have hs : (listMapPart (A.applyPotentialPart F) (gensPreimage σ)).Dom :=
    listMapPart_dom_iff.2 fun x hx ↦
      PartialAgeIn.applyPotentialPart_dom_of_partialIsEmbedding h (gensPreimage_mem_domainAt σ hx)
  obtain ⟨s, hsm⟩ := Part.dom_iff_mem.1 hs
  have hsmem : ∀ y ∈ s, (τ.toFun y).Dom := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := List.Forall₂.exists_of_mem_right (mem_listMapPart_iff.1 hsm) hy
    exact (τ.toFun_dom y).2
      (PartialAgeIn.applyPotentialPart_mem_domainAt_of_partialIsEmbedding h
        (gensPreimage_mem_domainAt σ hx) hxy)
  obtain ⟨t, htm⟩ := Part.dom_iff_mem.1 (listMapPart_dom_iff.2 hsmem)
  exact Part.dom_iff_mem.2
    ⟨_, (Part.mem_map_iff _).2 ⟨t, Part.mem_bind_iff.2 ⟨s, hsm, htm⟩, rfl⟩⟩

/-- **The transported datum is realized by the conjugated embedding**, at the two target indices.

The coordinate computation is the three stages read in order: the `k`-th preimage *is* `σ`'s
inverse image of the `k`-th target generator, the `k`-th application value *is* `f` there, and
the `k`-th forward image *is* `τ` of that. -/
theorem conjugateDataPart_realizesAt (σ : PartialCeIsoIn E (A.memberAt d) (B.memberAt d'))
    (τ : PartialCeIsoIn E (A.memberAt a) (B.memberAt a')) {F : PotentialEmbeddingData}
    {f : (A.memberAt d).domain ↪[L] (A.memberAt a).domain}
    (hf : A.PartialRealizesAt F d a f) {G : PotentialEmbeddingData}
    (hG : G ∈ conjugateDataPart σ τ F) :
    B.PartialRealizesAt G d' a' (PartialCeIsoIn.conjugate σ τ f) := by
  obtain ⟨rfl, rfl, hlen, hcoord⟩ := hf
  obtain ⟨t, htmem, rfl⟩ := (Part.mem_map_iff _).1 hG
  obtain ⟨s, hsm, htm⟩ := Part.mem_bind_iff.1 htmem
  have hpre := gensPreimage_forall₂ σ
  have hs := mem_listMapPart_iff.1 hsm
  have ht := mem_listMapPart_iff.1 htm
  refine ⟨rfl, rfl, hpre.length_eq.trans (hs.length_eq.trans ht.length_eq), fun k ↦ ?_⟩
  have h₁ : (k : ℕ) < (gensPreimage σ).length := by rw [← hpre.length_eq]; exact k.isLt
  have h₂ : (k : ℕ) < s.length := by rw [← hs.length_eq]; exact h₁
  have h₃ : (k : ℕ) < t.length := by rw [← ht.length_eq]; exact h₂
  set x : (A.memberAt F.domIdx).domain := σ.toEquiv.symm (B.gensView d' k) with hxdef
  -- stage 1: the preimage coordinate is `σ`'s inverse image of the target generator
  have hxval : (x : ℕ) = (gensPreimage σ).get ⟨k, h₁⟩ :=
    Part.mem_unique (σ.symm.toSubtypeFun_mem _) (hpre.get k.isLt h₁)
  -- stage 2: the application coordinate is the realizer's value there
  have hsval : s.get ⟨k, h₂⟩ = ((f x : (A.memberAt F.codIdx).domain) : ℕ) := by
    refine Part.mem_unique (hs.get h₁ h₂) ?_
    rw [← hxval]
    exact PartialAgeIn.applyPotentialPart_mem_realizer ⟨hlen, hcoord⟩ (x := (x : ℕ)) x.2
  -- stage 3: the forward coordinate is the conjugate's value
  have htval : t.get ⟨k, h₃⟩ = ((τ.toEquiv (f x) : (B.memberAt a').domain) : ℕ) := by
    refine Part.mem_unique (ht.get h₂ h₃) ?_
    rw [hsval]
    exact τ.toSubtypeFun_mem (f x)
  rw [PartialCeIsoIn.conjugate_apply]
  exact htval.symm

/-! ### Computability at fixed ends

`O ⊆ E` enters for the two reasons it always does: the transported operation
`applyPotentialPart` is recursive in the presentation oracle, and the source end's generator
preimage reads presentation data. Traversal itself needs no inclusion.

At *fixed* ends the preimage is a constant, so this statement is uniform in the data only.
Uniformity in the ends is a separate matter, and the covers' uniformity fields — not the
per-index isomorphisms — are what supply it. -/

private def conjugatePackTriple (d' a' : ℕ) (t : List ℕ) : ℕ × ℕ × Tuple ℕ := (d', a', t)

private theorem conjugatePackTriple_computableIn (d' a' : ℕ) :
    ComputableIn E (conjugatePackTriple d' a') :=
  (((ComputableIn.const d').pair ((ComputableIn.const a').pair ComputableIn.id))).of_eq
    fun _ ↦ rfl

private theorem conjugatePack_computableIn (d' a' : ℕ) :
    ComputableIn E fun t : List ℕ ↦ PotentialEmbeddingData.ofTriple (d', a', t) :=
  ComputableIn.comp (O := E) (α := List ℕ) (β := ℕ × ℕ × Tuple ℕ)
    (σ := PotentialEmbeddingData)
    (f := PotentialEmbeddingData.ofTriple) (g := conjugatePackTriple d' a')
    PotentialEmbeddingData.ofTriple_computableIn (conjugatePackTriple_computableIn d' a')

/-- **Transport at fixed ends is partial recursive in the map oracle.** -/
theorem conjugateDataPart_recursiveIn (hOE : O ⊆ E)
    (σ : PartialCeIsoIn E (A.memberAt d) (B.memberAt d'))
    (τ : PartialCeIsoIn E (A.memberAt a) (B.memberAt a')) :
    RecursiveIn E fun F : PotentialEmbeddingData ↦ conjugateDataPart σ τ F := by
  have happly : RecursiveIn E fun q : PotentialEmbeddingData × List ℕ ↦
      listMapPart (A.applyPotentialPart q.1) q.2 :=
    RecursiveIn.listMapPart₂ (g := fun F : PotentialEmbeddingData ↦ A.applyPotentialPart F)
      (RecursiveIn.mono hOE A.applyPotentialPart_recursiveIn)
  have hstage₁ : RecursiveIn E fun F : PotentialEmbeddingData ↦
      listMapPart (A.applyPotentialPart F) (gensPreimage σ) :=
    RecursiveIn.comp (O := E) (α := PotentialEmbeddingData)
      (β := PotentialEmbeddingData × List ℕ) (σ := List ℕ)
      (f := fun q : PotentialEmbeddingData × List ℕ ↦ listMapPart (A.applyPotentialPart q.1) q.2)
      (g := fun F : PotentialEmbeddingData ↦ (F, gensPreimage σ))
      happly (ComputableIn.id.pair (ComputableIn.const _))
  have hstage₂ : RecursiveIn E fun q : PotentialEmbeddingData × List ℕ ↦
      listMapPart τ.toFun q.2 :=
    (RecursiveIn.listMapPart τ.toFun_recursiveIn).comp ComputableIn.snd
  exact (RecursiveIn.map (RecursiveIn.bind hstage₁ hstage₂.to₂)
    ((conjugatePack_computableIn (E := E) d' a').comp ComputableIn.snd).to₂).of_eq fun _ ↦ rfl

end TwoEnded

/-! ### The diagonal case: one cover at both ends -/

namespace RepresentationCoverIn

variable {A B : PartialAgeIn O L} (r : RepresentationCoverIn E A B)

/-- **Transport along a single cover.** The diagonal instance of the two-ended transport, with
both ends taken from `r` at the data's own two indices. Adequate only when the answer is wanted
at `r`'s image indices — which is exactly the situation a *one*-cover statement describes. -/
noncomputable def conjugatePart (F : PotentialEmbeddingData) : Part PotentialEmbeddingData :=
  conjugateDataPart (r.isoAt F.domIdx) (r.isoAt F.codIdx) F

/-- Conjugation of an embedding along a single cover is the diagonal two-ended conjugate. -/
theorem conjEmbedding_eq_conjugate {c e : ℕ}
    (f : (A.memberAt c).domain ↪[L] (A.memberAt e).domain) :
    r.conjEmbedding f = PartialCeIsoIn.conjugate (r.isoAt c) (r.isoAt e) f := rfl

theorem conjugatePart_indices {F G : PotentialEmbeddingData} (hG : G ∈ r.conjugatePart F) :
    G.domIdx = r.indexMap F.domIdx ∧ G.codIdx = r.indexMap F.codIdx :=
  conjugateDataPart_indices hG

theorem conjugatePart_dom {F : PotentialEmbeddingData} (h : A.PartialIsEmbedding F) :
    (r.conjugatePart F).Dom :=
  conjugateDataPart_dom _ _ h rfl rfl

theorem conjugatePart_realizesAt {F : PotentialEmbeddingData}
    {f : (A.memberAt F.domIdx).domain ↪[L] (A.memberAt F.codIdx).domain}
    (hf : A.PartialRealizes F f) {G : PotentialEmbeddingData} (hG : G ∈ r.conjugatePart F) :
    B.PartialRealizesAt G (r.indexMap F.domIdx) (r.indexMap F.codIdx) (r.conjEmbedding f) :=
  conjugateDataPart_realizesAt _ _ ⟨rfl, rfl, hf⟩ hG

/-! #### Computability along a cover

Unlike the fixed-end statement, here both ends move with the data, so the *uniformity* fields of
the cover do the work — a family of per-index proofs would not suffice. -/

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

/-- **Conjugation along a cover is partial recursive in the map oracle.** -/
theorem conjugatePart_recursiveIn (hOE : O ⊆ E) : RecursiveIn E r.conjugatePart :=
  (RecursiveIn.map
    (RecursiveIn.bind (r.conjugateStage₁_recursiveIn hOE) r.conjugateStage₂_recursiveIn.to₂)
    r.conjugatePack_computableIn.to₂).of_eq fun _ ↦ rfl

end RepresentationCoverIn

/-! ### The two mixed composites

A witness queried at a `B`-index `e` cannot be transported by either cover alone. These are the
two composites that land where the query asks, and each uses **both** covers — the forward one at
the `A`-side index it names, the backward one at `e`. No round-trip equation is used or needed,
which is what keeps the two-cover asymmetry structural rather than a side condition. -/

namespace RepresentationIsoIn

variable {A B : PartialAgeIn O L} (r : RepresentationIsoIn E A B)

/-- **Into a queried index.** `B_{forward c} → A_c → A_{backward e} → B_e`: the CHP-shaped
composite, whose *codomain* is the queried member. -/
noncomputable def transportInto (c e : ℕ) (F : PotentialEmbeddingData) :
    Part PotentialEmbeddingData :=
  conjugateDataPart (r.forward.isoAt c) (r.backward.isoAt e).symm F

/-- **Out of a queried index.** `B_e → A_{backward e} → A_a → B_{forward a}`: the CJEP-shaped
composite, whose *domain* is the queried member. -/
noncomputable def transportOutOf (e a : ℕ) (F : PotentialEmbeddingData) :
    Part PotentialEmbeddingData :=
  conjugateDataPart (r.backward.isoAt e).symm (r.forward.isoAt a) F

/-- The queried index is reached exactly, with no round trip. -/
theorem transportInto_indices {c e : ℕ} {F G : PotentialEmbeddingData}
    (hG : G ∈ r.transportInto c e F) :
    G.domIdx = r.forward.indexMap c ∧ G.codIdx = e :=
  conjugateDataPart_indices hG

theorem transportOutOf_indices {e a : ℕ} {F G : PotentialEmbeddingData}
    (hG : G ∈ r.transportOutOf e a F) :
    G.domIdx = e ∧ G.codIdx = r.forward.indexMap a :=
  conjugateDataPart_indices hG

theorem transportInto_dom {c e : ℕ} {F : PotentialEmbeddingData}
    (h : A.PartialIsEmbedding F) (hd : F.domIdx = c) (ha : F.codIdx = r.backward.indexMap e) :
    (r.transportInto c e F).Dom :=
  conjugateDataPart_dom _ _ h hd ha

theorem transportOutOf_dom {e a : ℕ} {F : PotentialEmbeddingData}
    (h : A.PartialIsEmbedding F) (hd : F.domIdx = r.backward.indexMap e) (ha : F.codIdx = a) :
    (r.transportOutOf e a F).Dom :=
  conjugateDataPart_dom _ _ h hd ha

theorem transportInto_realizesAt {c e : ℕ} {F : PotentialEmbeddingData}
    {f : (A.memberAt c).domain ↪[L] (A.memberAt (r.backward.indexMap e)).domain}
    (hf : A.PartialRealizesAt F c (r.backward.indexMap e) f)
    {G : PotentialEmbeddingData} (hG : G ∈ r.transportInto c e F) :
    B.PartialRealizesAt G (r.forward.indexMap c) e
      (PartialCeIsoIn.conjugate (r.forward.isoAt c) (r.backward.isoAt e).symm f) :=
  conjugateDataPart_realizesAt _ _ hf hG

theorem transportOutOf_realizesAt {e a : ℕ} {F : PotentialEmbeddingData}
    {f : (A.memberAt (r.backward.indexMap e)).domain ↪[L] (A.memberAt a).domain}
    (hf : A.PartialRealizesAt F (r.backward.indexMap e) a f)
    {G : PotentialEmbeddingData} (hG : G ∈ r.transportOutOf e a F) :
    B.PartialRealizesAt G e (r.forward.indexMap a)
      (PartialCeIsoIn.conjugate (r.backward.isoAt e).symm (r.forward.isoAt a) f) :=
  conjugateDataPart_realizesAt _ _ hf hG

theorem transportInto_recursiveIn (hOE : O ⊆ E) (c e : ℕ) :
    RecursiveIn E (r.transportInto c e) :=
  conjugateDataPart_recursiveIn hOE _ _

theorem transportOutOf_recursiveIn (hOE : O ⊆ E) (e a : ℕ) :
    RecursiveIn E (r.transportOutOf e a) :=
  conjugateDataPart_recursiveIn hOE _ _

/-! #### Uniformity in the indices

The fixed-end statements above are not enough for a selector, which must vary its indices with
its input. Uniformity comes from the covers' `toFun_uniform` / `invFun_uniform` fields — a family
of per-index proofs would not supply it — and it reaches each composite through the two
identifications `gensPreimage_isoAt` and `gensPreimage_isoAt_symm`, which hold on the nose. Each
composite therefore runs one cover's traversal at its source end and the *other* cover's at its
target end, exactly as its type says. -/

private def transportIntoTriple (r : RepresentationIsoIn E A B)
    (z : ((ℕ × ℕ) × PotentialEmbeddingData) × List ℕ) : ℕ × ℕ × Tuple ℕ :=
  (r.forward.indexMap z.1.1.1, z.1.1.2, z.2)

private def transportOutOfTriple (r : RepresentationIsoIn E A B)
    (z : ((ℕ × ℕ) × PotentialEmbeddingData) × List ℕ) : ℕ × ℕ × Tuple ℕ :=
  (z.1.1.1, r.forward.indexMap z.1.1.2, z.2)

private theorem transportIntoPack_computableIn :
    ComputableIn E fun z : ((ℕ × ℕ) × PotentialEmbeddingData) × List ℕ ↦
      PotentialEmbeddingData.ofTriple (r.forward.indexMap z.1.1.1, z.1.1.2, z.2) :=
  ComputableIn.comp (O := E) (α := ((ℕ × ℕ) × PotentialEmbeddingData) × List ℕ)
    (β := ℕ × ℕ × Tuple ℕ) (σ := PotentialEmbeddingData)
    (f := PotentialEmbeddingData.ofTriple) (g := r.transportIntoTriple)
    PotentialEmbeddingData.ofTriple_computableIn
    ((((r.forward.indexMap_computableIn.comp
          (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst))).pair
        ((ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)).pair
          ComputableIn.snd))).of_eq fun _ ↦ rfl)

private theorem transportOutOfPack_computableIn :
    ComputableIn E fun z : ((ℕ × ℕ) × PotentialEmbeddingData) × List ℕ ↦
      PotentialEmbeddingData.ofTriple (z.1.1.1, r.forward.indexMap z.1.1.2, z.2) :=
  ComputableIn.comp (O := E) (α := ((ℕ × ℕ) × PotentialEmbeddingData) × List ℕ)
    (β := ℕ × ℕ × Tuple ℕ) (σ := PotentialEmbeddingData)
    (f := PotentialEmbeddingData.ofTriple) (g := r.transportOutOfTriple)
    PotentialEmbeddingData.ofTriple_computableIn
    ((((ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst)).pair
        ((r.forward.indexMap_computableIn.comp
          (ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst))).pair
          ComputableIn.snd))).of_eq fun _ ↦ rfl)

private theorem applyStage_recursiveIn (hOE : O ⊆ E) :
    RecursiveIn E fun z : PotentialEmbeddingData × List ℕ ↦
      listMapPart (A.applyPotentialPart z.1) z.2 :=
  RecursiveIn.listMapPart₂ (g := fun F : PotentialEmbeddingData ↦ A.applyPotentialPart F)
    (RecursiveIn.mono hOE A.applyPotentialPart_recursiveIn)

/-- **Transport into a queried index is uniform in both indices and the data.** -/
theorem transportInto_uniform_recursiveIn (hOE : O ⊆ E) :
    RecursiveIn E fun q : (ℕ × ℕ) × PotentialEmbeddingData ↦
      r.transportInto q.1.1 q.1.2 q.2 := by
  have hstage₁ : RecursiveIn E fun q : (ℕ × ℕ) × PotentialEmbeddingData ↦
      listMapPart (A.applyPotentialPart q.2) (r.forward.targetGensPreimage q.1.1) :=
    RecursiveIn.comp (O := E) (α := (ℕ × ℕ) × PotentialEmbeddingData)
      (β := PotentialEmbeddingData × List ℕ) (σ := List ℕ)
      (f := fun z : PotentialEmbeddingData × List ℕ ↦ listMapPart (A.applyPotentialPart z.1) z.2)
      (g := fun q : (ℕ × ℕ) × PotentialEmbeddingData ↦
        (q.2, r.forward.targetGensPreimage q.1.1))
      (applyStage_recursiveIn (A := A) hOE)
      (ComputableIn.snd.pair ((r.forward.targetGensPreimage_computableIn hOE).comp
        (ComputableIn.fst.comp ComputableIn.fst)))
  have hstage₂ : RecursiveIn E fun z : ((ℕ × ℕ) × PotentialEmbeddingData) × List ℕ ↦
      r.backward.invTuplePart z.1.1.2 z.2 :=
    RecursiveIn.comp (O := E) (α := ((ℕ × ℕ) × PotentialEmbeddingData) × List ℕ)
      (β := ℕ × List ℕ) (σ := List ℕ)
      (f := fun p : ℕ × List ℕ ↦ r.backward.invTuplePart p.1 p.2)
      (g := fun z : ((ℕ × ℕ) × PotentialEmbeddingData) × List ℕ ↦ (z.1.1.2, z.2))
      r.backward.invTuplePart_recursiveIn
      ((ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)).pair ComputableIn.snd)
  exact (RecursiveIn.map (RecursiveIn.bind hstage₁ hstage₂.to₂)
    r.transportIntoPack_computableIn.to₂).of_eq fun _ ↦ rfl

/-- **Transport out of a queried index is uniform in both indices and the data.** -/
theorem transportOutOf_uniform_recursiveIn (hOE : O ⊆ E) :
    RecursiveIn E fun q : (ℕ × ℕ) × PotentialEmbeddingData ↦
      r.transportOutOf q.1.1 q.1.2 q.2 := by
  have hstage₁ : RecursiveIn E fun q : (ℕ × ℕ) × PotentialEmbeddingData ↦
      listMapPart (A.applyPotentialPart q.2) (r.backward.sourceGensImage q.1.1) :=
    RecursiveIn.comp (O := E) (α := (ℕ × ℕ) × PotentialEmbeddingData)
      (β := PotentialEmbeddingData × List ℕ) (σ := List ℕ)
      (f := fun z : PotentialEmbeddingData × List ℕ ↦ listMapPart (A.applyPotentialPart z.1) z.2)
      (g := fun q : (ℕ × ℕ) × PotentialEmbeddingData ↦
        (q.2, r.backward.sourceGensImage q.1.1))
      (applyStage_recursiveIn (A := A) hOE)
      (ComputableIn.snd.pair ((r.backward.sourceGensImage_computableIn hOE).comp
        (ComputableIn.fst.comp ComputableIn.fst)))
  have hstage₂ : RecursiveIn E fun z : ((ℕ × ℕ) × PotentialEmbeddingData) × List ℕ ↦
      r.forward.toTuplePart z.1.1.2 z.2 :=
    RecursiveIn.comp (O := E) (α := ((ℕ × ℕ) × PotentialEmbeddingData) × List ℕ)
      (β := ℕ × List ℕ) (σ := List ℕ)
      (f := fun p : ℕ × List ℕ ↦ r.forward.toTuplePart p.1 p.2)
      (g := fun z : ((ℕ × ℕ) × PotentialEmbeddingData) × List ℕ ↦ (z.1.1.2, z.2))
      r.forward.toTuplePart_recursiveIn
      ((ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)).pair ComputableIn.snd)
  exact (RecursiveIn.map (RecursiveIn.bind hstage₁ hstage₂.to₂)
    r.transportOutOfPack_computableIn.to₂).of_eq fun _ ↦ rfl

end RepresentationIsoIn

end FirstOrder.Language
