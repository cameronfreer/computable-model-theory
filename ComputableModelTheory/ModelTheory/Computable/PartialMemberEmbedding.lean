/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialAgeSemantics
import ComputableModelTheory.ModelTheory.Computable.PotentialSpan

/-!
# Member embeddings of a Definition 2.1 family, and their rigidity

The semantic layer the amalgamation interface needs. Its point is **coherence between
existential witnesses**: `PartialIsEmbedding` asserts that *some* member embedding realizes a
piece of potential embedding data, and a commuting-square condition has to talk about several
such witnesses at once. That is only meaningful because the witness is unique.

Uniqueness is `memberEmbedding_ext_of_gens`: a member's carrier is the term closure of its
recorded generators (the family's generation law), and an embedding commutes with term
realization, so two member embeddings agreeing on the generators agree everywhere. Hence

* `PartialRealizes B F f` — `f` goes between the indicated members and carries the domain's
  recorded generators coordinatewise onto `F`'s range tuple;
* `PartialIsEmbedding B F := ∃ f, PartialRealizes B F f` — the partial-family analogue of
  `PotentialEmbeddingData.IsEmbedding`;
* `PartialRealizes.unique` — any two realizers of the same data are *equal*, so statements
  quantifying over realizers are independent of the choice.

With rigidity in hand a commuting square can be stated semantically, as an equation between
composites of realizers, with no coherence side conditions.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace PartialAgeIn

variable (B : PartialAgeIn O L)

/-- The recorded generator tuple of a member, viewed inside that member's own carrier. The
lift is available because the generators are on-domain. -/
def gensView (i : ℕ) : Fin (B.gens i).length → (B.memberAt i).domain :=
  fun k ↦ ⟨(B.gens i).get k, B.gens_mem_domainAt k⟩

@[simp]
theorem gensView_coe (i : ℕ) (k : Fin (B.gens i).length) :
    ((B.gensView i k : (B.memberAt i).domain) : ℕ) = (B.gens i).get k :=
  rfl

variable {B}

/-- Every element of a member's carrier is a term value over its recorded generators, read
**inside** the member. The generation law, lifted to the carrier subtype. -/
theorem exists_realize_gensView {i : ℕ} (x : (B.memberAt i).domain) :
    ∃ T : L.Term (Fin (B.gens i).length), T.realize (B.gensView i) = x := by
  obtain ⟨T, hT⟩ := (B.mem_domainAt_iff_term).1 x.2
  exact ⟨T, Subtype.ext
    (((B.memberAt i).realize_domain_val (B.gensView i) T).trans hT.symm)⟩

/-- **Member embeddings are rigid on generators.** Two embeddings of one member's carrier into
another that agree on the recorded generators are equal: the carrier is the term closure of
those generators, and embeddings commute with term realization. -/
theorem memberEmbedding_ext_of_gens {i j : ℕ}
    {f g : (B.memberAt i).domain ↪[L] (B.memberAt j).domain}
    (h : ∀ k, f (B.gensView i k) = g (B.gensView i k)) : f = g := by
  refine DFunLike.ext _ _ fun x ↦ ?_
  obtain ⟨T, rfl⟩ := exists_realize_gensView x
  rw [← HomClass.realize_term (L := L) f, ← HomClass.realize_term (L := L) g,
    show (⇑f ∘ B.gensView i) = (⇑g ∘ B.gensView i) from funext h]

/-- **Cross-family rigidity.** Two embeddings from a member of `A` into a member of `B` that
agree on `A`'s recorded generators are equal. Only the *source* family's generation law is used,
so nothing here requires the two families to coincide. -/
theorem memberEmbedding_ext_of_gens' {A B : PartialAgeIn O L} {i j : ℕ}
    {f g : (A.memberAt i).domain ↪[L] (B.memberAt j).domain}
    (h : ∀ k, f (A.gensView i k) = g (A.gensView i k)) : f = g := by
  refine DFunLike.ext _ _ fun x ↦ ?_
  obtain ⟨T, rfl⟩ := exists_realize_gensView x
  rw [← HomClass.realize_term (L := L) f, ← HomClass.realize_term (L := L) g,
    show (⇑f ∘ A.gensView i) = (⇑g ∘ A.gensView i) from funext h]

/-! ### Realizing potential embedding data -/

/-- A member embedding **realizes** potential embedding data: it runs between the indicated
members and carries the domain's recorded generators coordinatewise onto the range tuple. -/
def PartialRealizes (B : PartialAgeIn O L) (F : PotentialEmbeddingData)
    (f : (B.memberAt F.domIdx).domain ↪[L] (B.memberAt F.codIdx).domain) : Prop :=
  ∃ hlen : (B.gens F.domIdx).length = F.rangeTuple.length,
    ∀ k : Fin (B.gens F.domIdx).length,
      ((f (B.gensView F.domIdx k) : (B.memberAt F.codIdx).domain) : ℕ) =
        F.rangeTuple.get (Fin.cast hlen k)

/-- **Cross-family realization.** The same length-and-coordinate contract as `PartialRealizes`,
but with the source member drawn from `A` and the target from `B`.

Needed because transport along a computable isomorphism of representations moves data *between*
families, where the single-family predicate does not typecheck. No existential companion is
provided: conjugation uses explicit composites, and a cover already supplies an explicit induced
equivalence, so an existential would discard exactly the information those proofs rely on. -/
def PartialRealizesBetween (A B : PartialAgeIn O L) (F : PotentialEmbeddingData)
    (f : (A.memberAt F.domIdx).domain ↪[L] (B.memberAt F.codIdx).domain) : Prop :=
  ∃ hlen : (A.gens F.domIdx).length = F.rangeTuple.length,
    ∀ k : Fin (A.gens F.domIdx).length,
      ((f (A.gensView F.domIdx k) : (B.memberAt F.codIdx).domain) : ℕ) =
        F.rangeTuple.get (Fin.cast hlen k)

/-- At a single family this is exactly `PartialRealizes`. -/
theorem partialRealizesBetween_self {F : PotentialEmbeddingData}
    {f : (B.memberAt F.domIdx).domain ↪[L] (B.memberAt F.codIdx).domain} :
    PartialRealizesBetween B B F f ↔ B.PartialRealizes F f :=
  Iff.rfl

/-- The cross-family realizer is unique, by cross-family rigidity. -/
theorem PartialRealizesBetween.unique {A B : PartialAgeIn O L} {F : PotentialEmbeddingData}
    {f g : (A.memberAt F.domIdx).domain ↪[L] (B.memberAt F.codIdx).domain}
    (hf : PartialRealizesBetween A B F f) (hg : PartialRealizesBetween A B F g) : f = g := by
  obtain ⟨hlf, hfk⟩ := hf
  obtain ⟨hlg, hgk⟩ := hg
  exact memberEmbedding_ext_of_gens' fun k ↦ Subtype.ext ((hfk k).trans (hgk k).symm)

/-- The partial-family analogue of `PotentialEmbeddingData.IsEmbedding`: the data is realized
by some member embedding. -/
def PartialIsEmbedding (B : PartialAgeIn O L) (F : PotentialEmbeddingData) : Prop :=
  ∃ f, B.PartialRealizes F f

/-- **A length-and-coordinate witness *is* a realization.** `PartialRealizes` at
`ofTriple (c, e, s)` unfolds to exactly the data `MappedPartialCHPIn` produces for a query
`(e, s)` — same length equation, same coordinatewise equations — so a hereditary-property answer
supplies potential embedding data with no repackaging, and `applyPotentialPart` can be run on it.

The three `ofTriple` projections are `rfl`, which is why this is a constructor application rather
than a proof. -/
theorem partialIsEmbedding_ofTriple {B : PartialAgeIn O L} {c e : ℕ} {s : Tuple ℕ}
    (hlen : (B.gens c).length = s.length)
    (f : (B.memberAt c).domain ↪[L] (B.memberAt e).domain)
    (hf : ∀ k : Fin (B.gens c).length,
      ((f (B.gensView c k) : (B.memberAt e).domain) : ℕ) = s.get (Fin.cast hlen k)) :
    B.PartialIsEmbedding (PotentialEmbeddingData.ofTriple (c, e, s)) :=
  ⟨f, hlen, hf⟩

/-- **The realizer is unique.** Any two member embeddings realizing the same potential
embedding data are equal, so anything said about "the" realizer is independent of the
existential witness chosen — which is what lets a commuting square be stated as an equation
between composites. -/
theorem PartialRealizes.unique {F : PotentialEmbeddingData}
    {f g : (B.memberAt F.domIdx).domain ↪[L] (B.memberAt F.codIdx).domain}
    (hf : B.PartialRealizes F f) (hg : B.PartialRealizes F g) : f = g := by
  obtain ⟨hlenf, hfk⟩ := hf
  obtain ⟨hleng, hgk⟩ := hg
  exact memberEmbedding_ext_of_gens fun k ↦ Subtype.ext ((hfk k).trans (hgk k).symm)

/-- The length equation recorded by any realizer. -/
theorem PartialRealizes.length {F : PotentialEmbeddingData}
    {f : (B.memberAt F.domIdx).domain ↪[L] (B.memberAt F.codIdx).domain}
    (hf : B.PartialRealizes F f) : (B.gens F.domIdx).length = F.rangeTuple.length :=
  hf.choose

theorem PartialIsEmbedding.length {F : PotentialEmbeddingData}
    (h : B.PartialIsEmbedding F) : (B.gens F.domIdx).length = F.rangeTuple.length :=
  h.choose_spec.length

/-! ### Well-formedness in the partial setting

In the all-ℕ setting well-formedness of potential embedding data is just the length equation:
every natural is in every carrier, so a range tuple cannot point outside. Here it can, so
**carrier validity is part of well-formedness** — length alone is insufficient. -/

/-- Every entry of the range tuple lies in the indicated codomain member. -/
def CarrierValid (B : PartialAgeIn O L) (F : PotentialEmbeddingData) : Prop :=
  ∀ x ∈ F.rangeTuple, x ∈ B.domainAt F.codIdx

/-- Well-formedness of potential embedding data over a Definition 2.1 family: the range tuple
has the width of the domain's recorded generators **and** lands in the codomain member. -/
def PartialWellFormed (B : PartialAgeIn O L) (F : PotentialEmbeddingData) : Prop :=
  B.CarrierValid F ∧ (B.gens F.domIdx).length = F.rangeTuple.length

theorem PartialWellFormed.carrierValid {F : PotentialEmbeddingData}
    (h : B.PartialWellFormed F) : B.CarrierValid F :=
  h.1

theorem PartialWellFormed.length {F : PotentialEmbeddingData}
    (h : B.PartialWellFormed F) : (B.gens F.domIdx).length = F.rangeTuple.length :=
  h.2

/-- **Well-formedness can be unsatisfiable at a given index pair.** If the domain member records
a generator while the codomain member is empty, *no* datum at those indices is well-formed — the
length equation forces a nonempty range tuple, and carrier validity has nowhere to put it.

This is a statement about the index pair alone, so it bounds what any construction can return
there, transporting or otherwise. It has content precisely because Definition 2.1 permits empty
and finitely-generated members in one family; at the all-ℕ fragment every carrier is inhabited
and the situation cannot arise. -/
theorem not_partialWellFormed_of_empty_codomain {F : PotentialEmbeddingData}
    (hgens : B.gens F.domIdx ≠ []) (hempty : ∀ x, x ∉ B.domainAt F.codIdx) :
    ¬ B.PartialWellFormed F := by
  rintro ⟨hvalid, hlen⟩
  have hne : F.rangeTuple ≠ [] := by
    intro h
    exact hgens (List.eq_nil_of_length_eq_zero (by rw [hlen, h, List.length_nil]))
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
  exact hempty x (hvalid x hx)

/-- A realizer forces well-formedness: its coordinate equations exhibit every range entry as
the image of a generator, hence as an element of the codomain member. -/
theorem PartialRealizes.partialWellFormed {F : PotentialEmbeddingData}
    {f : (B.memberAt F.domIdx).domain ↪[L] (B.memberAt F.codIdx).domain}
    (hf : B.PartialRealizes F f) : B.PartialWellFormed F := by
  obtain ⟨hlen, hcoord⟩ := hf
  refine ⟨fun x hx ↦ ?_, hlen⟩
  obtain ⟨n, hn⟩ := List.mem_iff_get.1 hx
  have hk := hcoord (Fin.cast hlen.symm n)
  rw [show Fin.cast hlen (Fin.cast hlen.symm n) = n from rfl] at hk
  rw [← hn, ← hk]
  exact (f (B.gensView F.domIdx (Fin.cast hlen.symm n))).2

theorem PartialIsEmbedding.partialWellFormed {F : PotentialEmbeddingData}
    (h : B.PartialIsEmbedding F) : B.PartialWellFormed F :=
  h.choose_spec.partialWellFormed

/-! ### Realization at named indices, and the commuting square

To compose realizers into a square, their types must line up, and the indices come from
shape equations rather than from projections — the motive-sensitive situation
`exists_memberEmbedding_of_isEmbedding'` already dealt with. `PartialRealizesAt` therefore
names the two indices as **variables** and records the identifications as ordinary
conjuncts, so composites like `gl.comp fl` typecheck with no transport anywhere. -/

/-- `f` realizes `F` as a map from member `d` to member `a`: the indices match and the
domain's recorded generators go coordinatewise onto `F`'s range tuple. -/
def PartialRealizesAt (B : PartialAgeIn O L) (F : PotentialEmbeddingData) (d a : ℕ)
    (f : (B.memberAt d).domain ↪[L] (B.memberAt a).domain) : Prop :=
  F.domIdx = d ∧ F.codIdx = a ∧
    ∃ hlen : (B.gens d).length = F.rangeTuple.length,
      ∀ k : Fin (B.gens d).length,
        ((f (B.gensView d k) : (B.memberAt a).domain) : ℕ) =
          F.rangeTuple.get (Fin.cast hlen k)

/-- At its own indices, indexed realization is realization. -/
theorem partialRealizesAt_self {F : PotentialEmbeddingData}
    {f : (B.memberAt F.domIdx).domain ↪[L] (B.memberAt F.codIdx).domain} :
    B.PartialRealizesAt F F.domIdx F.codIdx f ↔ B.PartialRealizes F f :=
  ⟨fun h ↦ h.2.2, fun h ↦ ⟨rfl, rfl, h⟩⟩

/-- **Indexed realizers are unique too.** The rigidity that makes a square's commutativity
independent of which realizers witness it. -/
theorem PartialRealizesAt.unique {F : PotentialEmbeddingData} {d a : ℕ}
    {f g : (B.memberAt d).domain ↪[L] (B.memberAt a).domain}
    (hf : B.PartialRealizesAt F d a f) (hg : B.PartialRealizesAt F d a g) : f = g := by
  obtain ⟨-, -, hlenf, hfk⟩ := hf
  obtain ⟨-, -, hleng, hgk⟩ := hg
  exact memberEmbedding_ext_of_gens fun k ↦ Subtype.ext ((hfk k).trans (hgk k).symm)

/-- An indexed realizer witnesses actualness. The indices are variables, so they substitute away
and the realizer becomes one at the data's own indices. -/
theorem PartialRealizesAt.partialIsEmbedding {F : PotentialEmbeddingData} {d a : ℕ}
    {f : (B.memberAt d).domain ↪[L] (B.memberAt a).domain}
    (h : B.PartialRealizesAt F d a f) : B.PartialIsEmbedding F := by
  obtain ⟨rfl, rfl, h'⟩ := h
  exact ⟨f, h'⟩

/-- Read a realizer at *named* indices, given equations placing them. The transport along the
equations is explicit in the statement because the realizer's type mentions the indices; consumers
that already substituted get it definitionally. -/
theorem PartialRealizes.realizesAt_of_eq {F : PotentialEmbeddingData}
    {f : (B.memberAt F.domIdx).domain ↪[L] (B.memberAt F.codIdx).domain}
    (h : B.PartialRealizes F f) {d a : ℕ} (hd : F.domIdx = d) (ha : F.codIdx = a) :
    B.PartialRealizesAt F d a (ha ▸ hd ▸ f) := by
  subst hd
  subst ha
  exact ⟨rfl, rfl, h⟩

/-- The reverse-facing companion of `PartialRealizes.realizesAt_of_eq`, at the same
motive-sensitive boundary: read a realizer back into the coordinate form the witness interfaces
state, at an index and tuple given by *equations* rather than definitionally.

The interfaces name `(sel …).apexIdx` and `(sel …).leftImage` literally, and a transported
selector's output is a `Part.get` — reducible to neither. Taking the two as equational hypotheses
lets them be substituted away inside this lemma, where they are variables. -/
theorem PartialRealizesAt.coords_of_eq {G : PotentialEmbeddingData} {i q q' : ℕ}
    {t : Tuple ℕ} {g : (B.memberAt i).domain ↪[L] (B.memberAt q).domain}
    (hg : B.PartialRealizesAt G i q g) (hq : q' = q) (ht : t = G.rangeTuple) :
    ∃ hlen : (B.gens i).length = t.length,
      ∃ F : (B.memberAt i).domain ↪[L] (B.memberAt q').domain,
        ∀ k : Fin (B.gens i).length,
          ((F ⟨(B.gens i).get k, B.gens_mem_domainAt k⟩ : (B.memberAt q').domain) : ℕ) =
            t.get (Fin.cast hlen k) :=
  hq ▸ ht ▸ ⟨hg.2.2.choose, g, hg.2.2.choose_spec⟩

/-- Semantic commutativity of an amalgamation square: there are realizers for all four legs —
the span's two and the diagram's two — whose composites agree as member embeddings. The apex
and middle indices are named, so both composites live in the same type.

By `PartialRealizesAt.unique` the choice of realizers is immaterial
(`partialCommutes_iff_of_realizers`), so this existential form carries no hidden choice and no
coherence side condition. -/
def PartialCommutes (B : PartialAgeIn O L) (S : PotentialSpanData)
    (D : AmalgamationDiagramData) : Prop :=
  ∃ (d m₁ m₂ apex : ℕ)
    (fl : (B.memberAt d).domain ↪[L] (B.memberAt m₁).domain)
    (fr : (B.memberAt d).domain ↪[L] (B.memberAt m₂).domain)
    (gl : (B.memberAt m₁).domain ↪[L] (B.memberAt apex).domain)
    (gr : (B.memberAt m₂).domain ↪[L] (B.memberAt apex).domain),
    B.PartialRealizesAt S.left d m₁ fl ∧ B.PartialRealizesAt S.right d m₂ fr ∧
      B.PartialRealizesAt D.leftToApex m₁ apex gl ∧
      B.PartialRealizesAt D.rightToApex m₂ apex gr ∧
      gl.comp fl = gr.comp fr

/-- **Commutativity does not depend on the realizers.** Given *any* realizers for the four
legs at matching indices, the square commutes exactly when their composites agree — so the
existential in `PartialCommutes` may be discharged with whichever witnesses are at hand. -/
theorem partialCommutes_iff_of_realizers {S : PotentialSpanData}
    {D : AmalgamationDiagramData} {d m₁ m₂ apex : ℕ}
    {fl : (B.memberAt d).domain ↪[L] (B.memberAt m₁).domain}
    {fr : (B.memberAt d).domain ↪[L] (B.memberAt m₂).domain}
    {gl : (B.memberAt m₁).domain ↪[L] (B.memberAt apex).domain}
    {gr : (B.memberAt m₂).domain ↪[L] (B.memberAt apex).domain}
    (hfl : B.PartialRealizesAt S.left d m₁ fl) (hfr : B.PartialRealizesAt S.right d m₂ fr)
    (hgl : B.PartialRealizesAt D.leftToApex m₁ apex gl)
    (hgr : B.PartialRealizesAt D.rightToApex m₂ apex gr) :
    B.PartialCommutes S D ↔ gl.comp fl = gr.comp fr := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨d, m₁, m₂, apex, fl, fr, gl, gr, hfl, hfr, hgl, hgr, h⟩⟩
  obtain ⟨d', m₁', m₂', apex', fl', fr', gl', gr', hfl', hfr', hgl', hgr', hsq⟩ := h
  obtain rfl : d' = d := (hfl'.1).symm.trans hfl.1
  obtain rfl : m₁' = m₁ := (hfl'.2.1).symm.trans hfl.2.1
  obtain rfl : m₂' = m₂ := (hfr'.2.1).symm.trans hfr.2.1
  obtain rfl : apex' = apex := (hgl'.2.1).symm.trans hgl.2.1
  rw [hfl'.unique hfl, hfr'.unique hfr, hgl'.unique hgl, hgr'.unique hgr] at hsq
  exact hsq

/-! ### Spans -/

/-- Every entry of both legs' range tuples lies in the indicated member. This is the
**halting** condition of the amalgamation selector, and nothing else. -/
def CarrierValidSpan (B : PartialAgeIn O L) (S : PotentialSpanData) : Prop :=
  B.CarrierValid S.left ∧ B.CarrierValid S.right

/-- Actualness of a span over a Definition 2.1 family: well-shaped, with both legs realized. -/
def PartialSpanActual (B : PartialAgeIn O L) (S : PotentialSpanData) : Prop :=
  S.WellShaped ∧ B.PartialIsEmbedding S.left ∧ B.PartialIsEmbedding S.right

/-- An actual span is carrier-valid — so the halting condition is implied by actualness, but
strictly weaker than it. -/
theorem PartialSpanActual.carrierValidSpan {S : PotentialSpanData}
    (h : B.PartialSpanActual S) : B.CarrierValidSpan S :=
  ⟨h.2.1.partialWellFormed.carrierValid, h.2.2.partialWellFormed.carrierValid⟩

end PartialAgeIn

end FirstOrder.Language
