/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ComputablyHomogeneous
import ComputableModelTheory.ModelTheory.Computable.CanonicalRange
import ComputableModelTheory.ModelTheory.Computable.PartialCAP

/-!
# The canonical age of a computably homogeneous structure has CAP

CHMM Theorem 3.9's converse direction, **at the canonical representation**. Given a computably
homogeneous computable structure `F`, its canonical age `𝕂_F` has CAP, with no further hypothesis
and in particular no `O ⊆ E`.

## This is not the published converse

CHMM states Theorem 3.9 as an `iff` and proves `⇒` by *"we can assume that `K = K_F` since CAP is
preserved under computable isomorphisms of sets of structures"*. That step is selector-level CAP
transport along a computable isomorphism of representations, which this library does not have — see
the #4 boundary, where general CAP transport is obstructed pointwise (never refuted). What is proved
here is the statement **at `F.canonicalAge` itself**; a converse concluding CAP for an arbitrary `K`
that is a canonical age of `F` still needs a hypothesis-specific selector theorem, and none is
claimed.

## The construction

Amalgamate a span by extending the right member into the left one, one recorded generator at a time,
using Definition 3.1's selector. A `foldl` over the right member's generators carries only
`(processed, chosen)`; the two tuples the queries need are derived,

```
dom := S.left.rangeTuple  ++ chosen      img := S.right.rangeTuple ++ processed
```

so that at the start they are the two span range tuples — which is exactly what makes the square
commute at the end. Each answer's returned point is appended to `chosen`.

The apex is `allTupleFor S.left.codIdx ++ chosen`: the **left member's own recorded generators**
followed by the chosen images. It cannot be `S.left.rangeTuple ++ chosen`, because well-shapedness
forces the left leg to map out of the whole left member and the span's left leg may hit only part of
it.

## Why the unconditional clauses are unconditional

The left leg is the canonical inclusion of a prefix, so it is actual on **every** input. The right
leg has exactly one chosen image per recorded generator, and every one of them is literally an entry
of the apex, so it is well-formed on every input. Neither uses actualness of the span, and neither
uses `imageOfNewPoint_mem`. Malformed spans are therefore answered, not guarded against — which is
what `PartialCAPIn` asks for.

Only soundness consumes `extension_actual`, through the invariant

```
A(dom, img) :  PartialIsEmbedding (ofTriple (encode dom, encode img, img))
```

which **is** the next query's `originalMap`, so the antecedent is available at each step with no
repackaging.

## Two different index arguments

Closing the two legs uses the same realizer at two different positions, and the arguments must not
be conflated:

* the **offset** argument — the right member's `k`-th generator sits at
  `S.right.rangeTuple.length + k` in `img`, and that is what gives the right leg's coordinates;
* the **prefix** argument — the two accumulators still begin with the two span range tuples, read at
  position `k < S.right.rangeTuple.length`, and that is what makes the square commute.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace ComputablyHomogeneousIn

variable {F : ComputableStructureIn O L} (H : ComputablyHomogeneousIn E F)

/-! ### The fold -/

/-- One step: record the generator just processed, and the point homogeneity chose for it. The
query's two tuples are derived from the accumulator, never stored. -/
noncomputable def capStep (S : PotentialSpanData) (acc : Tuple ℕ × Tuple ℕ) (x : ℕ) :
    Tuple ℕ × Tuple ℕ :=
  (acc.1 ++ [x],
    acc.2 ++ [H.imageOfNewPoint
      ⟨S.left.rangeTuple ++ acc.2, S.right.rangeTuple ++ acc.1, x⟩])

/-- The whole fold, over the **right** member's recorded generators. Total and proof-free. -/
noncomputable def capFold (S : PotentialSpanData) : Tuple ℕ × Tuple ℕ :=
  List.foldl (fun acc x ↦ H.capStep S acc x) ([], []) (allTupleFor S.right.codIdx)

/-- The chosen images, one per recorded generator of the right member. -/
noncomputable def capChosen (S : PotentialSpanData) : Tuple ℕ := (H.capFold S).2

/-- The apex tuple: the left member's own generators, then the chosen images. -/
noncomputable def capApex (S : PotentialSpanData) : Tuple ℕ :=
  allTupleFor S.left.codIdx ++ H.capChosen S

/-- The left leg: the left member into the apex, identically on values. -/
noncomputable def capLeft (S : PotentialSpanData) : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple
    (S.left.codIdx, encode (H.capApex S), allTupleFor S.left.codIdx)

/-- The right leg: the right member into the apex, generator `k` to the `k`-th chosen image. -/
noncomputable def capRight (S : PotentialSpanData) : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple (S.right.codIdx, encode (H.capApex S), H.capChosen S)

/-- The selector. -/
noncomputable def capSelect (S : PotentialSpanData) : AmalgamationDiagramData :=
  AmalgamationDiagramData.ofPair (H.capLeft S, H.capRight S)

/-! ### What the fold produces -/

private theorem foldl_spec (S : PotentialSpanData) :
    ∀ (l p q : Tuple ℕ),
      (List.foldl (fun acc x ↦ H.capStep S acc x) (p, q) l).1 = p ++ l ∧
        (List.foldl (fun acc x ↦ H.capStep S acc x) (p, q) l).2.length
          = q.length + l.length := by
  intro l
  induction l with
  | nil => intro p q; simp
  | cons a l ih =>
    intro p q
    obtain ⟨h1, h2⟩ := ih (p ++ [a])
      (q ++ [H.imageOfNewPoint ⟨S.left.rangeTuple ++ q, S.right.rangeTuple ++ p, a⟩])
    refine ⟨?_, ?_⟩
    · show (List.foldl (fun acc x ↦ H.capStep S acc x) (H.capStep S (p, q) a) l).1 = _
      rw [capStep, h1, List.append_assoc]
      rfl
    · show (List.foldl (fun acc x ↦ H.capStep S acc x) (H.capStep S (p, q) a) l).2.length = _
      rw [capStep, h2]
      simp
      omega

theorem capFold_fst (S : PotentialSpanData) :
    (H.capFold S).1 = allTupleFor S.right.codIdx := by
  rw [capFold, (H.foldl_spec S _ [] []).1, List.nil_append]

theorem capChosen_length (S : PotentialSpanData) :
    (H.capChosen S).length = (allTupleFor S.right.codIdx).length := by
  rw [capChosen, capFold, (H.foldl_spec S _ [] []).2]
  simp

/-! ### The unconditional clauses -/

/-- Every entry of the apex tuple lies in the apex member. -/
private theorem mem_apex {S : PotentialSpanData} {x : ℕ} (hx : x ∈ H.capApex S) :
    x ∈ F.canonicalAge.domainAt (encode (H.capApex S)) :=
  F.mem_canonicalAge_domainAt_of_mem_gens (by rwa [allTupleFor_encode])

theorem capSelect_wellShaped (S : PotentialSpanData) : (H.capSelect S).WellShapedFor S :=
  ⟨rfl, rfl, rfl⟩

/-- **The left leg is actual, unconditionally.** The apex begins with the left member's own recorded
generators, so the leg is the canonical inclusion. -/
theorem capLeft_isEmbedding (S : PotentialSpanData) :
    F.canonicalAge.PartialIsEmbedding (H.capLeft S) := by
  have hsub : F.canonicalAge.domainAt S.left.codIdx
      ⊆ F.canonicalAge.domainAt (encode (H.capApex S)) := by
    refine F.canonicalAge_domainAt_subset fun x hx ↦ ?_
    exact H.mem_apex (List.mem_append_left _ hx)
  refine ⟨PartialAgeIn.memberEmbedding rfl hsub, ?_⟩
  refine PartialAgeIn.realizes_of_getElem? rfl ?_
  intro k x hx
  exact hx

/-- **The right leg is well-formed, unconditionally.** One chosen image per recorded generator, each
literally an entry of the apex. -/
theorem capRight_wellFormed (S : PotentialSpanData) :
    F.canonicalAge.PartialWellFormed (H.capRight S) := by
  refine ⟨fun x hx ↦ H.mem_apex (List.mem_append_right _ hx), ?_⟩
  show (allTupleFor S.right.codIdx).length = (H.capChosen S).length
  rw [H.capChosen_length]

/-! ### The invariant -/

/-- The invariant carried through the fold: the accumulated domain tuple embeds into the accumulated
image tuple, positionally. This is the next query's `originalMap`. -/
private def CapInv (F : ComputableStructureIn O L) (S : PotentialSpanData)
    (p q : Tuple ℕ) : Prop :=
  F.canonicalAge.PartialIsEmbedding (PotentialEmbeddingData.ofTriple
    (encode (S.left.rangeTuple ++ q), encode (S.right.rangeTuple ++ p),
      S.right.rangeTuple ++ p))

/-- **The base case.** Corestrict both span legs, invert the *left*, and compose with the right:
`D_left.rangeTuple ≃ D_mid ≃ D_right.rangeTuple`. The middle is tight, so the composition's
alignment is the trivial one. -/
private theorem capInv_nil {S : PotentialSpanData}
    (hact : F.canonicalAge.PartialSpanActual S) : CapInv F S [] [] := by
  obtain ⟨hws, hL, hR⟩ := hact
  obtain ⟨fl, hfl⟩ := hL
  obtain ⟨fr, hfr⟩ := hR
  have hlenL : (F.canonicalAge.gens S.left.domIdx).length = S.left.rangeTuple.length := hfl.choose
  have hlenR : (F.canonicalAge.gens S.right.domIdx).length = S.right.rangeTuple.length :=
    hfr.choose
  obtain ⟨g1, hg1⟩ : ∃ f, PartialAgeIn.PartialRealizesBetween F.canonicalAge F.canonicalAge
      (PotentialEmbeddingData.ofTriple
        (encode S.left.rangeTuple, S.left.domIdx, allTupleFor S.left.domIdx)) f :=
    ⟨_, PartialAgeIn.PartialRealizesBetween.toCanonicalRangeEquiv_symm_realizes hfl⟩
  obtain ⟨g2, hg2⟩ : ∃ f, PartialAgeIn.PartialRealizesBetween F.canonicalAge F.canonicalAge
      (PotentialEmbeddingData.ofTriple
        (S.left.domIdx, encode S.right.rangeTuple, S.right.rangeTuple)) f :=
    PartialAgeIn.exists_partialRealizesBetween_congr (by rw [hws])
      ⟨_, PartialAgeIn.PartialRealizesBetween.toCanonicalRangeEquiv_realizes hfr⟩
  have hcomp : ∃ f, PartialAgeIn.PartialRealizesBetween F.canonicalAge F.canonicalAge
      (PotentialEmbeddingData.ofTriple
        (encode S.left.rangeTuple, encode S.right.rangeTuple, S.right.rangeTuple)) f :=
    ⟨_, PartialAgeIn.realizes_comp hg1 hg2 (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (by
      show (allTupleFor (encode S.left.rangeTuple)).length = S.right.rangeTuple.length
      rw [allTupleFor_encode, ← hlenL, hws, hlenR])⟩
  refine PartialAgeIn.exists_partialRealizesBetween_congr ?_ hcomp
  show PotentialEmbeddingData.ofTriple
      (encode S.left.rangeTuple, encode S.right.rangeTuple, S.right.rangeTuple) = _
  simp

/-- **The step.** The antecedent is the invariant itself; `extension_actual` returns the extension
in the image-to-domain direction, so corestricting and inverting once restores the orientation. -/
private theorem capInv_step {S : PotentialSpanData} {p q : Tuple ℕ} (x : ℕ)
    (h : CapInv F S p q) :
    CapInv F S (p ++ [x])
      (q ++ [H.imageOfNewPoint ⟨S.left.rangeTuple ++ q, S.right.rangeTuple ++ p, x⟩]) := by
  obtain ⟨f, hf⟩ := H.extension_actual
    ⟨S.left.rangeTuple ++ q, S.right.rangeTuple ++ p, x⟩ h
  refine PartialAgeIn.exists_partialRealizesBetween_congr ?_
    ⟨_, PartialAgeIn.PartialRealizesBetween.toCanonicalRangeEquiv_symm_realizes hf⟩
  change PotentialEmbeddingData.ofTriple
      (encode ((S.left.rangeTuple ++ q) ++
        [H.imageOfNewPoint ⟨S.left.rangeTuple ++ q, S.right.rangeTuple ++ p, x⟩]),
        encode ((S.right.rangeTuple ++ p) ++ [x]),
        allTupleFor (encode ((S.right.rangeTuple ++ p) ++ [x]))) = _
  rw [allTupleFor_encode, List.append_assoc, List.append_assoc]

private theorem capInv_foldl (S : PotentialSpanData) :
    ∀ (l p q : Tuple ℕ), CapInv F S p q →
      CapInv F S (List.foldl (fun acc x ↦ H.capStep S acc x) (p, q) l).1
        (List.foldl (fun acc x ↦ H.capStep S acc x) (p, q) l).2 := by
  intro l
  induction l with
  | nil => intro p q h; exact h
  | cons a l ih =>
    intro p q h
    exact ih _ _ (H.capInv_step a h)

/-- The invariant at the end of the fold. -/
private theorem capInv_final {S : PotentialSpanData}
    (hact : F.canonicalAge.PartialSpanActual S) :
    CapInv F S (allTupleFor S.right.codIdx) (H.capChosen S) := by
  have h := H.capInv_foldl S (allTupleFor S.right.codIdx) [] [] (capInv_nil hact)
  rwa [← capFold, ← capChosen, H.capFold_fst] at h


/-! ### The right leg, by the offset argument -/

/-- **The right leg is actual on an actual span.** The final invariant, inverted, sends the right
member's `k`-th recorded generator — which sits at position `S.right.rangeTuple.length + k` of
the accumulated image tuple — to the `k`-th chosen image. That offset is the whole content; the
two inclusions on either side move no values. -/
theorem capRight_isEmbedding_of_actual {S : PotentialSpanData}
    (hact : F.canonicalAge.PartialSpanActual S) :
    F.canonicalAge.PartialIsEmbedding (H.capRight S) := by
  obtain ⟨hws, hL, hR⟩ := hact
  obtain ⟨fl, hfl⟩ := hL
  obtain ⟨fr, hfr⟩ := hR
  have hlenL : (F.canonicalAge.gens S.left.domIdx).length = S.left.rangeTuple.length := hfl.choose
  have hlenR : (F.canonicalAge.gens S.right.domIdx).length = S.right.rangeTuple.length :=
    hfr.choose
  have hpre : S.left.rangeTuple.length = S.right.rangeTuple.length := by
    rw [← hlenL, hws, hlenR]
  -- the final invariant, inverted
  obtain ⟨e, he⟩ := capInv_final (H := H) ⟨hws, ⟨fl, hfl⟩, ⟨fr, hfr⟩⟩
  obtain ⟨e', he'⟩ : ∃ f, PartialAgeIn.PartialRealizesBetween F.canonicalAge F.canonicalAge
      (PotentialEmbeddingData.ofTriple
        (encode (S.right.rangeTuple ++ allTupleFor S.right.codIdx),
          encode (S.left.rangeTuple ++ H.capChosen S),
          S.left.rangeTuple ++ H.capChosen S)) f :=
    PartialAgeIn.exists_partialRealizesBetween_congr (by
        change PotentialEmbeddingData.ofTriple
          (encode (S.right.rangeTuple ++ allTupleFor S.right.codIdx),
            encode (S.left.rangeTuple ++ H.capChosen S),
            allTupleFor (encode (S.left.rangeTuple ++ H.capChosen S))) = _
        rw [allTupleFor_encode])
      ⟨_, PartialAgeIn.PartialRealizesBetween.toCanonicalRangeEquiv_symm_realizes he⟩
  -- the two inclusions
  have hsub₁ : F.canonicalAge.domainAt S.right.codIdx
      ⊆ F.canonicalAge.domainAt (encode (S.right.rangeTuple ++ allTupleFor S.right.codIdx)) := by
    refine F.canonicalAge_domainAt_subset fun x hx ↦ ?_
    refine F.mem_canonicalAge_domainAt_of_mem_gens ?_
    rw [allTupleFor_encode]
    exact List.mem_append_right _ hx
  have hsubApex : F.canonicalAge.domainAt S.left.codIdx
      ⊆ F.canonicalAge.domainAt (encode (H.capApex S)) := by
    refine F.canonicalAge_domainAt_subset fun x hx ↦ ?_
    exact H.mem_apex (List.mem_append_left _ hx)
  have hsub₂ : F.canonicalAge.domainAt (encode (S.left.rangeTuple ++ H.capChosen S))
      ⊆ F.canonicalAge.domainAt (encode (H.capApex S)) := by
    refine F.canonicalAge_domainAt_subset fun x hx ↦ ?_
    rw [allTupleFor_encode] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hsubApex (hfl.partialWellFormed.carrierValid x hx)
    · exact H.mem_apex (List.mem_append_right _ hx)
  refine ⟨(PartialAgeIn.memberEmbedding (B := F.canonicalAge)
      (c := encode (S.left.rangeTuple ++ H.capChosen S))
      (e := encode (H.capApex S)) rfl hsub₂).comp
    (e'.comp (PartialAgeIn.memberEmbedding (B := F.canonicalAge)
      (c := S.right.codIdx)
      (e := encode (S.right.rangeTuple ++ allTupleFor S.right.codIdx)) rfl hsub₁)), ?_⟩
  refine PartialAgeIn.realizes_of_getElem? (by
    show (allTupleFor S.right.codIdx).length = (H.capChosen S).length
    rw [H.capChosen_length]) ?_
  intro k x hx
  -- the offset: the k-th generator of the right member is at `|S.right.rangeTuple| + k`
  have himg := PartialAgeIn.getElem?_of_realizes (k := S.right.rangeTuple.length + k)
    (x := PartialAgeIn.memberEmbedding (B := F.canonicalAge) (c := S.right.codIdx)
      (e := encode (S.right.rangeTuple ++ allTupleFor S.right.codIdx)) rfl hsub₁ x) he' (by
      show (allTupleFor (encode (S.right.rangeTuple ++ allTupleFor S.right.codIdx)))[
        S.right.rangeTuple.length + k]? = some ((x : ℕ))
      rw [allTupleFor_encode, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact hx)
  rw [show (PotentialEmbeddingData.ofTriple
      (encode (S.right.rangeTuple ++ allTupleFor S.right.codIdx),
        encode (S.left.rangeTuple ++ H.capChosen S),
        S.left.rangeTuple ++ H.capChosen S)).rangeTuple
      = S.left.rangeTuple ++ H.capChosen S from rfl,
    ← hpre, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at himg
  exact himg

end ComputablyHomogeneousIn

end FirstOrder.Language
