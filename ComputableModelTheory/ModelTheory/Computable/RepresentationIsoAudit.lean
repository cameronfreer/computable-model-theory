/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.RepresentationConjugation
import ComputableModelTheory.ModelTheory.Computable.GraphExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for computable isomorphism of representations

One fixture: the **constant empty family** over the graph language, every member of which has an
empty carrier. The graph language has no function symbols, so `Term (Fin 0)` is uninhabited and
the generation law holds with an empty carrier — over a language with constants no such family
could exist.

It tests two independent things at once.

*Reflexivity is genuinely nowhere defined* on empty members. A total identity would satisfy the
type but violate the halting law, and this row is what distinguishes them.

*Arbitrary computable index maps still yield covers*, because all indexed members are
definitionally identical. Composition is therefore checked with two **different** affine index
maps, chosen so the correct reverse-order backward composite is numerically different from the
wrong order — not merely symbolically different.

The two identity mechanisms are kept apart on purpose: the production `refl` is used only where
the index map really is the identity, and a small audit-local `emptyCover` supplies nonidentity
index maps, so no row pretends `refl` supports them.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

section

variable {O : Set (ℕ →. ℕ)}

attribute [local instance] pathGraphStructure

/-- The constant empty family over the graph language: no member enumerates anything, and every
member's recorded generator tuple is empty. -/
noncomputable def emptyGraphAge : PartialAgeIn O Language.graph where
  structureAt _ := pathGraphStructure
  enum? _ _ := Option.none
  enum?_computableIn := ComputableIn.const _
  gens _ := []
  gens_computableIn := ComputableIn.const _
  funEval _ _ := Part.none
  funEval_recursiveIn := RecursiveIn.none
  funEval_correct := fun _ d _ ↦ isEmptyElim d
  relEval _ _ := Part.none
  relEval_recursiveIn := RecursiveIn.none
  relEval_correct := fun _ d h ↦ by
    match d with
    | ⟨2, _, _⟩ =>
      obtain ⟨m, hm⟩ := h 0
      exact (Option.some_ne_none _ hm.symm).elim
    | ⟨0, r, _⟩ => exact isEmptyElim r
    | ⟨1, r, _⟩ => exact isEmptyElim r
    | ⟨n + 3, r, _⟩ => exact isEmptyElim r
  generates := fun i x ↦ by
    constructor
    · rintro ⟨m, hm⟩
      exact (Option.some_ne_none _ hm.symm).elim
    · rintro ⟨T, -⟩
      induction T with
      | var k => exact k.elim0
      | func f _ _ => exact isEmptyElim f

/-- Every member of the empty family has an empty carrier. -/
theorem not_mem_emptyGraphAge_domainAt (i x : ℕ) :
    x ∉ (emptyGraphAge (O := O)).domainAt i := by
  rintro ⟨m, hm⟩
  exact (Option.some_ne_none _ hm.symm).elim

/-! ### Gate 1: reflexivity is nowhere defined on empty members -/

/-- **Reflexivity halts nowhere** on the empty family. A total identity map would typecheck but
break the halting law; this is the row that tells them apart. -/
theorem test_refl_nowhere_defined (hOE : O ⊆ O) (i x : ℕ) :
    ¬ (((RepresentationIsoIn.refl (emptyGraphAge (O := O)) hOE).forward.isoAt i).toFun x).Dom :=
  fun h ↦ not_mem_emptyGraphAge_domainAt (O := O) i x
    ((((RepresentationIsoIn.refl (emptyGraphAge (O := O)) hOE).forward.isoAt
      i).toFun_dom x).1 h)

/-- And reflexivity's index map really is the identity. -/
theorem test_refl_indexMap (hOE : O ⊆ O) (i : ℕ) :
    (RepresentationIsoIn.refl (emptyGraphAge (O := O)) hOE).forward.indexMap i = i := rfl

/-! ### An audit-local cover with an arbitrary index map

All members of the empty family are definitionally identical, so *any* computable index map
gives a cover. The maps are nowhere defined, which is exactly right on empty carriers. -/

/-- A cover of the empty family by itself along an arbitrary computable index map. -/
noncomputable def emptyCover (σ : ℕ → ℕ) (hσ : ComputableIn O σ) :
    RepresentationCoverIn O (emptyGraphAge (O := O)) (emptyGraphAge (O := O)) where
  indexMap := σ
  indexMap_computableIn := hσ
  isoAt j :=
    { toFun _ := Part.none
      invFun _ := Part.none
      toFun_recursiveIn := RecursiveIn.none
      invFun_recursiveIn := RecursiveIn.none
      toFun_dom := fun x ↦
        ⟨fun h ↦ h.elim, fun h ↦ (not_mem_emptyGraphAge_domainAt (O := O) j x h).elim⟩
      invFun_dom := fun y ↦
        ⟨fun h ↦ h.elim, fun h ↦ (not_mem_emptyGraphAge_domainAt (O := O) (σ j) y h).elim⟩
      toFun_mem := fun h ↦ h.fst.elim
      invFun_toFun := fun h ↦ h.fst.elim
      toFun_invFun := fun h ↦ h.fst.elim
      toFun_funMap := fun _ f _ _ _ ↦ isEmptyElim f
      toFun_relMap := fun n R _ _ hw ↦ by
        match n, R with
        | 2, _ => exact (hw 0).fst.elim
        | 0, R => exact isEmptyElim R
        | 1, R => exact isEmptyElim R
        | m + 3, R => exact isEmptyElim R }
  toFun_uniform := RecursiveIn.none
  invFun_uniform := RecursiveIn.none

/-! ### Gate 2: composition order

The two affine maps are chosen so that the correct reverse-order backward composite differs
**numerically** from the wrong order. Backward composition is `r.backward ∘ s.backward`, so at
`0` the correct answer is `3 * (2 * 0) + 1 = 1`, whereas composing in the forward order would
give `2 * (3 * 0 + 1) = 2`. A symbolic-only difference would not catch an accidental rewrite. -/

/-- The bidirectional isomorphism carrying index map `σ` forward and `τ` backward. -/
noncomputable def emptyIso (σ τ : ℕ → ℕ) (hσ : ComputableIn O σ) (hτ : ComputableIn O τ) :
    RepresentationIsoIn O (emptyGraphAge (O := O)) (emptyGraphAge (O := O)) where
  forward := emptyCover σ hσ
  backward := emptyCover τ hτ

/-- **Forward covers compose in order.** -/
theorem test_trans_forward_order :
    ((emptyIso (O := O) (fun n ↦ 2 * n) (fun n ↦ 3 * n + 1)
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp.computableIn
        ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
          (Primrec.const 1)).to_comp.computableIn)).trans
      (emptyIso (fun n ↦ 3 * n + 1) (fun n ↦ 2 * n)
        ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
          (Primrec.const 1)).to_comp.computableIn)
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp.computableIn)).forward.indexMap
      1 = 7 := rfl

/-- **Backward covers compose in REVERSE order** — the wrong order would give `2`, not `1`. -/
theorem test_trans_backward_order :
    ((emptyIso (O := O) (fun n ↦ 2 * n) (fun n ↦ 3 * n + 1)
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp.computableIn
        ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
          (Primrec.const 1)).to_comp.computableIn)).trans
      (emptyIso (fun n ↦ 3 * n + 1) (fun n ↦ 2 * n)
        ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
          (Primrec.const 1)).to_comp.computableIn)
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp.computableIn)).backward.indexMap
      0 = 1 := rfl

/-! ### Gate 3: symmetry, and the semantic consequence -/

/-- **Symmetry swaps the covers**: the new forward index map is the old backward one. -/
theorem test_symm_forward_eq_backward (σ τ : ℕ → ℕ) (hσ : ComputableIn O σ)
    (hτ : ComputableIn O τ) (i : ℕ) :
    (emptyIso (O := O) σ τ hσ hτ).symm.forward.indexMap i =
      (emptyIso (O := O) σ τ hσ hτ).backward.indexMap i := rfl

/-- **The semantic consequence**, with no oracle hypothesis. -/
theorem test_sameClass (σ τ : ℕ → ℕ) (hσ : ComputableIn O σ) (hτ : ComputableIn O τ) :
    (emptyGraphAge (O := O)).SameClass (emptyGraphAge (O := O)) :=
  (emptyIso σ τ hσ hτ).sameClass

/-! ### Gate 4: the recovered CHMM sequence -/

/-- **The packaged pair sequence is computable.** -/
theorem test_generatorEmbeddingData_computableIn {L : Language} [L.EffectiveLanguage]
    {A B : PartialAgeIn O L}
    (r : RepresentationCoverIn O A B) (hOE : O ⊆ O) :
    ComputableIn O r.generatorEmbeddingData :=
  r.generatorEmbeddingData_computableIn hOE

/-- **The recovered tuple is realized by the induced equivalence itself** — cross-family, since
the two indices refer to different families. -/
theorem test_generatorEmbeddingData_realized {L : Language} [L.EffectiveLanguage]
    {A B : PartialAgeIn O L}
    (r : RepresentationCoverIn O A B) (i : ℕ) :
    A.PartialRealizesBetween B (r.generatorEmbeddingData i)
      (r.isoAt i).toEquiv.toEmbedding :=
  r.generatorEmbeddingData_realized i

/-- **Empty source generators give an empty range tuple** — on the empty family, where the
element map is nowhere defined. -/
theorem test_generatorEmbeddingData_rangeTuple_nil (σ : ℕ → ℕ) (hσ : ComputableIn O σ) (i : ℕ) :
    ((emptyCover σ hσ).generatorEmbeddingData i).rangeTuple = [] :=
  (emptyCover σ hσ).sourceGensImage_of_gens_nil (i := i) rfl

/-! ### Gate 5: conjugating potential embedding data along a cover -/

/-- **Conjugation of data is partial recursive in the map oracle.** -/
theorem test_conjugatePart_recursiveIn {L : Language} [L.EffectiveLanguage]
    {A B : PartialAgeIn O L} (r : RepresentationCoverIn O A B) (hOE : O ⊆ O) :
    RecursiveIn O r.conjugatePart :=
  r.conjugatePart_recursiveIn hOE

/-- **Actual data conjugates** — halting, with no claim about the value. -/
theorem test_conjugatePart_dom {L : Language} [L.EffectiveLanguage] {A B : PartialAgeIn O L}
    (r : RepresentationCoverIn O A B) {F : PotentialEmbeddingData}
    (h : A.PartialIsEmbedding F) : (r.conjugatePart F).Dom :=
  r.conjugatePart_dom h

/-- **The conjugated datum is realized by the conjugated embedding**, at the mapped indices. -/
theorem test_conjugatePart_realizesAt {L : Language} [L.EffectiveLanguage]
    {A B : PartialAgeIn O L} (r : RepresentationCoverIn O A B) {F : PotentialEmbeddingData}
    {f : (A.memberAt F.domIdx).domain ↪[L] (A.memberAt F.codIdx).domain}
    (hf : A.PartialRealizes F f) {G : PotentialEmbeddingData} (hG : G ∈ r.conjugatePart F) :
    B.PartialRealizesAt G (r.indexMap F.domIdx) (r.indexMap F.codIdx) (r.conjEmbedding f) :=
  r.conjugatePart_realizesAt hf hG

/-- **The empty case goes all the way through.** Over the empty family every element map is
nowhere defined, yet conjugation halts — on the empty range tuple, at the mapped indices. This is
the sharpest check that no nonempty-carrier fallback has crept into any of the three stages. -/
theorem test_conjugate_empty (σ : ℕ → ℕ) (hσ : ComputableIn O σ) (F : PotentialEmbeddingData) :
    PotentialEmbeddingData.ofTriple (σ F.domIdx, σ F.codIdx, []) ∈
      (emptyCover σ hσ).conjugatePart F := by
  rw [RepresentationCoverIn.conjugatePart, conjugateDataPart,
    gensPreimage_of_gens_nil ((emptyCover σ hσ).isoAt F.domIdx) rfl]
  simp only [listMapPart_nil, Part.bind_some, Part.map_some, Part.mem_some_iff]
  rfl

/-! ### Gate 6: the two-ended transport, and the two mixed composites

The load-bearing rows for a two-cover setting. A transport queried at a `B`-index `e` must land
**at `e`**, and no round-trip equation is available to put it there — so the composite has to mix
the covers. The concrete rows below use the same numerically-distinguishable affine maps as gate
2, chosen so that the single-cover answer is a *different number*, not merely a different
expression. -/

private theorem hdouble : ComputableIn O fun n ↦ 2 * n :=
  (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp.computableIn

private theorem haffine : ComputableIn O fun n ↦ 3 * n + 1 :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
    (Primrec.const 1)).to_comp.computableIn

/-- **The general two-ended transport is realized at its two target indices**, which are supplied
independently and need not be related by any index map. -/
theorem test_conjugateDataPart_realizesAt {L : Language} [L.EffectiveLanguage]
    {A B : PartialAgeIn O L} {d a d' a' : ℕ}
    (σ : PartialCeIsoIn O (A.memberAt d) (B.memberAt d'))
    (τ : PartialCeIsoIn O (A.memberAt a) (B.memberAt a'))
    {F : PotentialEmbeddingData} {f : (A.memberAt d).domain ↪[L] (A.memberAt a).domain}
    (hf : A.PartialRealizesAt F d a f) {G : PotentialEmbeddingData}
    (hG : G ∈ conjugateDataPart σ τ F) :
    B.PartialRealizesAt G d' a' (PartialCeIsoIn.conjugate σ τ f) :=
  conjugateDataPart_realizesAt σ τ hf hG

/-- **Transport along one cover is the diagonal instance** — and its source stage is the cover's
own recorded generator preimage, so the two layers are literally the same program. -/
theorem test_conjugatePart_is_diagonal {L : Language} [L.EffectiveLanguage]
    {A B : PartialAgeIn O L} (r : RepresentationCoverIn O A B) (F : PotentialEmbeddingData)
    (i : ℕ) :
    r.conjugatePart F = conjugateDataPart (r.isoAt F.domIdx) (r.isoAt F.codIdx) F ∧
      gensPreimage (r.isoAt i) = r.targetGensPreimage i :=
  ⟨rfl, rfl⟩

/-- **Into a queried index, exactly.** Forward `n ↦ 2n`, backward `n ↦ 3n+1`. Transporting into
`e = 1` from `c = 3` lands at `(6, 1)`. A single-cover transport would answer at
`forward (backward 1) = 8`, so the codomain row fails numerically if the composite ever collapses
to one cover. -/
theorem test_transportInto_lands_at_query (F G : PotentialEmbeddingData)
    (hG : G ∈ (emptyIso (O := O) (fun n ↦ 2 * n) (fun n ↦ 3 * n + 1)
      hdouble haffine).transportInto 3 1 F) :
    G.domIdx = 6 ∧ G.codIdx = 1 :=
  RepresentationIsoIn.transportInto_indices _ hG

/-- **Out of a queried index, exactly.** The domain is the queried member `e = 2`, and the
codomain is `forward 4 = 8`. Here the single-cover answer for the domain would be
`forward (backward 2) = 14`. -/
theorem test_transportOutOf_lands_at_query (F G : PotentialEmbeddingData)
    (hG : G ∈ (emptyIso (O := O) (fun n ↦ 2 * n) (fun n ↦ 3 * n + 1)
      hdouble haffine).transportOutOf 2 4 F) :
    G.domIdx = 2 ∧ G.codIdx = 8 :=
  RepresentationIsoIn.transportOutOf_indices _ hG

/-- **Both mixed composites are partial recursive in the map oracle.** -/
theorem test_transport_recursiveIn {L : Language} [L.EffectiveLanguage] {A B : PartialAgeIn O L}
    (r : RepresentationIsoIn O A B) (hOE : O ⊆ O) (c e a : ℕ) :
    RecursiveIn O (r.transportInto c e) ∧ RecursiveIn O (r.transportOutOf e a) :=
  ⟨r.transportInto_recursiveIn hOE c e, r.transportOutOf_recursiveIn hOE e a⟩

end

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_refl_nowhere_defined
#assert_standard_axioms FirstOrder.Language.test_refl_indexMap
#assert_standard_axioms FirstOrder.Language.test_trans_forward_order
#assert_standard_axioms FirstOrder.Language.test_trans_backward_order
#assert_standard_axioms FirstOrder.Language.test_symm_forward_eq_backward
#assert_standard_axioms FirstOrder.Language.test_sameClass
#assert_standard_axioms FirstOrder.Language.test_generatorEmbeddingData_computableIn
#assert_standard_axioms FirstOrder.Language.test_generatorEmbeddingData_realized
#assert_standard_axioms FirstOrder.Language.test_generatorEmbeddingData_rangeTuple_nil
#assert_standard_axioms FirstOrder.Language.test_conjugatePart_recursiveIn
#assert_standard_axioms FirstOrder.Language.test_conjugatePart_dom
#assert_standard_axioms FirstOrder.Language.test_conjugatePart_realizesAt
#assert_standard_axioms FirstOrder.Language.test_conjugate_empty
#assert_standard_axioms FirstOrder.Language.test_conjugateDataPart_realizesAt
#assert_standard_axioms FirstOrder.Language.test_conjugatePart_is_diagonal
#assert_standard_axioms FirstOrder.Language.test_transportInto_lands_at_query
#assert_standard_axioms FirstOrder.Language.test_transportOutOf_lands_at_query
#assert_standard_axioms FirstOrder.Language.test_transport_recursiveIn
