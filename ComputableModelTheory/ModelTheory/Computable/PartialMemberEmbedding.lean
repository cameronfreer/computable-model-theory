/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialAgeSemantics
import ComputableModelTheory.ModelTheory.Computable.PotentialEmbedding

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

/-! ### Realizing potential embedding data -/

/-- A member embedding **realizes** potential embedding data: it runs between the indicated
members and carries the domain's recorded generators coordinatewise onto the range tuple. -/
def PartialRealizes (B : PartialAgeIn O L) (F : PotentialEmbeddingData)
    (f : (B.memberAt F.domIdx).domain ↪[L] (B.memberAt F.codIdx).domain) : Prop :=
  ∃ hlen : (B.gens F.domIdx).length = F.rangeTuple.length,
    ∀ k : Fin (B.gens F.domIdx).length,
      ((f (B.gensView F.domIdx k) : (B.memberAt F.codIdx).domain) : ℕ) =
        F.rangeTuple.get (Fin.cast hlen k)

/-- The partial-family analogue of `PotentialEmbeddingData.IsEmbedding`: the data is realized
by some member embedding. -/
def PartialIsEmbedding (B : PartialAgeIn O L) (F : PotentialEmbeddingData) : Prop :=
  ∃ f, B.PartialRealizes F f

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

end PartialAgeIn

end FirstOrder.Language
