/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialComputableIso
import ComputableModelTheory.ModelTheory.Computable.PartialAgeSteps
import ComputableModelTheory.ModelTheory.Computable.PartialMemberEmbedding

/-!
# Covers of one representation by another

CHMM Definition 2.3 asks for **one computable sequence in each direction**: for every member of
each representation, an index in the other together with an isomorphism, uniformly computable.
It does *not* ask that the two index maps be inverse to one another, and it does not prevent a
representation from containing different numbers of copies of an isomorphism type.

A `RepresentationCoverIn` is exactly **one** of those two directions. It claims that every member
of the source is matched, and claims nothing about which target indices are hit — a cover need
not be surjective on indices, and has no meaningful `symm`. The paper-facing notion is the
bidirectional wrapper built from two independently supplied covers.

The uniformity fields are not derivable from the per-index isomorphisms: each `isoAt i` carries
its own recursiveness proof, but a family of proofs is not a proof about the family. This is the
same trap `UniformCeIsoFamilyIn` records at the nonempty layer.

The map oracle `E` is separate from the family oracle `O`, inherited from `PartialCeIsoIn`.
The oracle facts for the wrapper's groupoid operations:

* symmetry needs **no** oracle inclusion — it swaps the two stored covers;
* reflexivity needs `O ⊆ E`, since the domain-restricted identity has to recognize an `O`-c.e.
  member domain and is therefore not automatically `E`-recursive;
* transitivity needs no inclusion once both covers are already in `E`.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- **One direction of CHMM Definition 2.3.** A computable index map together with a uniformly
computable family of isomorphisms matching each member of `A` to a member of `B`.

No claim is made about coverage of arbitrary indices of `B`. -/
structure RepresentationCoverIn (E : Set (ℕ →. ℕ)) (A B : PartialAgeIn O L) where
  /-- Where each source member is matched. -/
  indexMap : ℕ → ℕ
  indexMap_computableIn : ComputableIn E indexMap
  /-- The matching isomorphism at each index. -/
  isoAt : ∀ i, PartialCeIsoIn E (A.memberAt i) (B.memberAt (indexMap i))
  /-- Uniformity of the forward maps. Not implied by the per-index proofs in `isoAt`. -/
  toFun_uniform : RecursiveIn E fun p : ℕ × ℕ ↦ (isoAt p.1).toFun p.2
  /-- Uniformity of the backward maps. -/
  invFun_uniform : RecursiveIn E fun p : ℕ × ℕ ↦ (isoAt p.1).invFun p.2

/-! ### The uniform partial identity

One program, used both per-index and as the uniformity witness, so the two are literally the
same rather than merely extensionally equal. It halts exactly on the member's carrier — a total
identity would overclaim the domain — and the oracle lift happens once, at the boundary. -/

/-- The domain-restricted identity of a family: search for an enumeration witness, then return
the queried value. -/
noncomputable def PartialAgeIn.idFun (A : PartialAgeIn O L) (p : ℕ × ℕ) : Part ℕ :=
  (A.firstStepFor p.1 p.2).map fun _ ↦ p.2

theorem PartialAgeIn.idFun_recursiveIn (A : PartialAgeIn O L) :
    RecursiveIn O A.idFun :=
  RecursiveIn.map A.firstStepFor_recursiveIn
    (ComputableIn.snd.comp ComputableIn.fst).to₂

theorem PartialAgeIn.idFun_dom (A : PartialAgeIn O L) (i x : ℕ) :
    (A.idFun (i, x)).Dom ↔ x ∈ A.domainAt i :=
  A.firstStepFor_dom_iff

theorem PartialAgeIn.mem_idFun (A : PartialAgeIn O L) {i x y : ℕ} :
    y ∈ A.idFun (i, x) ↔ y = x ∧ x ∈ A.domainAt i := by
  rw [PartialAgeIn.idFun, Part.mem_map_iff]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨rfl, A.firstStepFor_dom_iff.1 (Part.dom_iff_mem.2 ⟨m, hm⟩)⟩
  · rintro ⟨rfl, hx⟩
    obtain ⟨m, hm⟩ := Part.dom_iff_mem.1 (A.firstStepFor_dom_iff.2 hx)
    exact ⟨m, hm, rfl⟩

namespace RepresentationCoverIn

variable {A B C : PartialAgeIn O L}

/-- Covers compose. There is deliberately no `symm`: a cover claims nothing about which target
indices are hit. -/
noncomputable def trans (r : RepresentationCoverIn E A B)
    (s : RepresentationCoverIn E B C) : RepresentationCoverIn E A C where
  indexMap i := s.indexMap (r.indexMap i)
  indexMap_computableIn := s.indexMap_computableIn.comp r.indexMap_computableIn
  isoAt i := (r.isoAt i).trans (s.isoAt (r.indexMap i))
  toFun_uniform := by
    have hg : RecursiveIn₂ E fun (p : ℕ × ℕ) (y : ℕ) ↦
        (s.isoAt (r.indexMap p.1)).toFun y :=
      (s.toFun_uniform.comp
        ((r.indexMap_computableIn.comp (ComputableIn.fst.comp ComputableIn.fst)).pair
          ComputableIn.snd)).to₂
    exact RecursiveIn.bind r.toFun_uniform hg
  invFun_uniform := by
    have hg : RecursiveIn₂ E fun (p : ℕ × ℕ) (y : ℕ) ↦ (r.isoAt p.1).invFun y :=
      (r.invFun_uniform.comp
        ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd)).to₂
    have hs : RecursiveIn E fun p : ℕ × ℕ ↦ (s.isoAt (r.indexMap p.1)).invFun p.2 :=
      s.invFun_uniform.comp
        ((r.indexMap_computableIn.comp ComputableIn.fst).pair ComputableIn.snd)
    exact RecursiveIn.bind hs hg

/-- **Reflexivity.** Needs `O ⊆ E`: the identity has to recognize an `O`-c.e. member domain, so
it is not automatically `E`-recursive. Every `isoAt i` is the one uniform program applied at `i`,
so the per-index maps and the uniformity fields are literally the same program. -/
noncomputable def refl (A : PartialAgeIn O L) (hOE : O ⊆ E) :
    RepresentationCoverIn E A A :=
  -- the oracle lift happens exactly once, and every use below is this same proof
  let hId : RecursiveIn E A.idFun := RecursiveIn.mono hOE A.idFun_recursiveIn
  { indexMap := fun i ↦ i
    indexMap_computableIn := ComputableIn.id
    isoAt := fun i ↦
    { toFun := fun x ↦ A.idFun (i, x)
      invFun := fun x ↦ A.idFun (i, x)
      toFun_recursiveIn := hId.comp ((ComputableIn.const i).pair ComputableIn.id)
      invFun_recursiveIn := hId.comp ((ComputableIn.const i).pair ComputableIn.id)
      toFun_dom := fun x ↦ A.idFun_dom i x
      invFun_dom := fun x ↦ A.idFun_dom i x
      toFun_mem := fun h ↦ by
        obtain ⟨rfl, hx⟩ := A.mem_idFun.1 h
        exact hx
      invFun_toFun := fun h ↦ by
        obtain ⟨rfl, hx⟩ := A.mem_idFun.1 h
        exact A.mem_idFun.2 ⟨rfl, hx⟩
      toFun_invFun := fun h ↦ by
        obtain ⟨rfl, hx⟩ := A.mem_idFun.1 h
        exact A.mem_idFun.2 ⟨rfl, hx⟩
      toFun_funMap := fun n f v w hw ↦ by
        have hvw : ∀ k, w k = v k := fun k ↦ (A.mem_idFun.1 (hw k)).1
        have hv : ∀ k, v k ∈ A.domainAt i := fun k ↦ (A.mem_idFun.1 (hw k)).2
        rw [show w = v from funext hvw]
        exact A.mem_idFun.2 ⟨rfl, A.domainAt_closed f hv⟩
      toFun_relMap := fun n R v w hw ↦ by
        have hvw : ∀ k, w k = v k := fun k ↦ (A.mem_idFun.1 (hw k)).1
        rw [show w = v from funext hvw] }
    toFun_uniform := hId
    invFun_uniform := hId }

@[simp] theorem refl_indexMap (A : PartialAgeIn O L) (hOE : O ⊆ E) (i : ℕ) :
    (RepresentationCoverIn.refl A hOE (E := E)).indexMap i = i := rfl

@[simp] theorem trans_indexMap (r : RepresentationCoverIn E A B)
    (s : RepresentationCoverIn E B C) (i : ℕ) :
    (r.trans s).indexMap i = s.indexMap (r.indexMap i) := rfl

end RepresentationCoverIn

/-! ### Tuple traversal along a cover

One layer below generator images. `Forall₂` is the stable semantic API: length preservation and
coordinate facts follow from it without introducing casts early.

The oracle split here is deliberate. Traversal itself is `RecursiveIn E` with **no** `O ⊆ E` —
it only runs the stored maps. Reading either family's recorded generators is what touches
presentation data, so the *computability* of the total generator-image functions below needs the
inclusion — the functions themselves do not. -/

namespace RepresentationCoverIn

variable {A B : PartialAgeIn O L} (r : RepresentationCoverIn E A B)

/-- Map a whole tuple forward along the isomorphism at index `i`. -/
noncomputable def toTuplePart (i : ℕ) (s : List ℕ) : Part (List ℕ) :=
  listMapPart (r.isoAt i).toFun s

/-- Map a whole tuple backward. -/
noncomputable def invTuplePart (i : ℕ) (s : List ℕ) : Part (List ℕ) :=
  listMapPart (r.isoAt i).invFun s

theorem toTuplePart_recursiveIn :
    RecursiveIn E fun p : ℕ × List ℕ ↦ r.toTuplePart p.1 p.2 :=
  RecursiveIn.listMapPart₂ (g := fun i ↦ (r.isoAt i).toFun) r.toFun_uniform

theorem invTuplePart_recursiveIn :
    RecursiveIn E fun p : ℕ × List ℕ ↦ r.invTuplePart p.1 p.2 :=
  RecursiveIn.listMapPart₂ (g := fun i ↦ (r.isoAt i).invFun) r.invFun_uniform

/-- **The `Forall₂` specification** of forward traversal. -/
theorem mem_toTuplePart_iff {i : ℕ} {s t : List ℕ} :
    t ∈ r.toTuplePart i s ↔ List.Forall₂ (fun x y ↦ y ∈ (r.isoAt i).toFun x) s t :=
  mem_listMapPart_iff

theorem mem_invTuplePart_iff {i : ℕ} {s t : List ℕ} :
    t ∈ r.invTuplePart i s ↔ List.Forall₂ (fun y x ↦ x ∈ (r.isoAt i).invFun y) s t :=
  mem_listMapPart_iff

/-- **Exact domain of forward traversal**: every entry lies in the source member's carrier. -/
theorem toTuplePart_dom_iff {i : ℕ} {s : List ℕ} :
    (r.toTuplePart i s).Dom ↔ ∀ x ∈ s, x ∈ A.domainAt i := by
  rw [toTuplePart, listMapPart_dom_iff]
  exact forall₂_congr fun x _ ↦ (r.isoAt i).toFun_dom x

/-- **Exact domain of backward traversal**: every entry lies in the matched member's carrier. -/
theorem invTuplePart_dom_iff {i : ℕ} {s : List ℕ} :
    (r.invTuplePart i s).Dom ↔ ∀ y ∈ s, y ∈ B.domainAt (r.indexMap i) := by
  rw [invTuplePart, listMapPart_dom_iff]
  exact forall₂_congr fun y _ ↦ (r.isoAt i).invFun_dom y

/-- **The empty tuple always maps to the empty tuple** — including when the element map is
nowhere defined. This is the sharpest check that no nonempty-carrier fallback has crept in. -/
@[simp] theorem toTuplePart_nil (i : ℕ) : r.toTuplePart i [] = Part.some [] := rfl

@[simp] theorem invTuplePart_nil (i : ℕ) : r.invTuplePart i [] = Part.some [] := rfl

/-- Forward traversal lands in the matched member's carrier. -/
theorem mem_domainAt_of_mem_toTuplePart {i : ℕ} {s t : List ℕ}
    (h : t ∈ r.toTuplePart i s) : ∀ y ∈ t, y ∈ B.domainAt (r.indexMap i) := by
  have hf := r.mem_toTuplePart_iff.1 h
  clear h
  induction hf with
  | nil => simp
  | cons hxy _ ih =>
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact (r.isoAt i).toFun_mem hxy
    · exact ih y hy

/-! ### Derived generator images

**Derived, never stored.** A cover already determines these; recording them would be redundant
data that could drift from the isomorphisms.

`sourceGensImage` is the tuple appearing in the paper's cover sequence. `targetGensPreimage` is
*not* additional representation data either, but it is needed later: the matched target's
recorded generators need not be forward images of the source's recorded generators, since CHMM
does not require an isomorphism to carry recorded generators to recorded generators.

Both are total *values*, needing no oracle hypothesis. The **computability** of the total
generator-image functions is what needs `O ⊆ E`, since reading either family's generator list
touches presentation data — unlike traversal itself, which only runs the stored maps. -/

/-- The forward images of the source member's recorded generators. -/
noncomputable def sourceGensImage (i : ℕ) : List ℕ :=
  (r.toTuplePart i (A.gens i)).get
    (r.toTuplePart_dom_iff.2 fun x hx ↦ by
      obtain ⟨k, hk⟩ := List.mem_iff_get.1 hx
      exact hk ▸ A.gens_mem_domainAt k)

/-- The backward images of the matched member's recorded generators. -/
noncomputable def targetGensPreimage (i : ℕ) : List ℕ :=
  (r.invTuplePart i (B.gens (r.indexMap i))).get
    (r.invTuplePart_dom_iff.2 fun y hy ↦ by
      obtain ⟨k, hk⟩ := List.mem_iff_get.1 hy
      exact hk ▸ B.gens_mem_domainAt k)

theorem mem_sourceGensImage (i : ℕ) :
    r.sourceGensImage i ∈ r.toTuplePart i (A.gens i) :=
  Part.get_mem _

theorem mem_targetGensPreimage (i : ℕ) :
    r.targetGensPreimage i ∈ r.invTuplePart i (B.gens (r.indexMap i)) :=
  Part.get_mem _

/-- The generator images land in the matched member's carrier. -/
theorem sourceGensImage_mem_domainAt (i : ℕ) :
    ∀ y ∈ r.sourceGensImage i, y ∈ B.domainAt (r.indexMap i) :=
  r.mem_domainAt_of_mem_toTuplePart (r.mem_sourceGensImage i)

/-- Length is preserved — read off the `Forall₂` specification, with no casts. -/
theorem sourceGensImage_length (i : ℕ) :
    (r.sourceGensImage i).length = (A.gens i).length :=
  (List.Forall₂.length_eq (r.mem_toTuplePart_iff.1 (r.mem_sourceGensImage i))).symm

theorem targetGensPreimage_length (i : ℕ) :
    (r.targetGensPreimage i).length = (B.gens (r.indexMap i)).length :=
  (List.Forall₂.length_eq (r.mem_invTuplePart_iff.1 (r.mem_targetGensPreimage i))).symm

/-- Backward traversal lands in the source member's carrier. -/
theorem mem_domainAt_of_mem_invTuplePart {i : ℕ} {s t : List ℕ}
    (h : t ∈ r.invTuplePart i s) : ∀ x ∈ t, x ∈ A.domainAt i := by
  have hf := r.mem_invTuplePart_iff.1 h
  clear h
  induction hf with
  | nil => simp
  | cons hxy _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact (r.isoAt i).invFun_mem hxy
    · exact ih x hx

/-- The generator preimages are certified elements of the **source** member — needed when
conjugating an arbitrary embedding. -/
theorem targetGensPreimage_mem_domainAt (i : ℕ) :
    ∀ x ∈ r.targetGensPreimage i, x ∈ A.domainAt i :=
  r.mem_domainAt_of_mem_invTuplePart (r.mem_targetGensPreimage i)

/-! #### Coordinates -/

/-- Coordinatewise: the `n`-th generator image is the isomorphism's value at the `n`-th
generator. Stated on `get` with both bounds explicit, so no cast is introduced. -/
theorem sourceGensImage_get (i : ℕ) {n : ℕ} (h₁ : n < (A.gens i).length)
    (h₂ : n < (r.sourceGensImage i).length) :
    (r.sourceGensImage i).get ⟨n, h₂⟩ ∈ (r.isoAt i).toFun ((A.gens i).get ⟨n, h₁⟩) :=
  (r.mem_toTuplePart_iff.1 (r.mem_sourceGensImage i)).get h₁ h₂

theorem targetGensPreimage_get (i : ℕ) {n : ℕ}
    (h₁ : n < (B.gens (r.indexMap i)).length) (h₂ : n < (r.targetGensPreimage i).length) :
    (r.targetGensPreimage i).get ⟨n, h₂⟩ ∈
      (r.isoAt i).invFun ((B.gens (r.indexMap i)).get ⟨n, h₁⟩) :=
  (r.mem_invTuplePart_iff.1 (r.mem_targetGensPreimage i)).get h₁ h₂

/-- **The empty case explicitly.** A member with no recorded generators maps to the empty tuple,
even though the element map is nowhere defined there. -/
theorem sourceGensImage_of_gens_nil {i : ℕ} (h : A.gens i = []) :
    r.sourceGensImage i = [] := by
  have := r.mem_sourceGensImage i
  rw [h, r.toTuplePart_nil] at this
  exact Part.mem_some_iff.1 this

/-! #### Computability

`O ⊆ E` enters exactly here, and only to read presentation data: the source generators, and the
target generators at the mapped index. Each proof names its partial program first, then applies
`computableIn_get` once. -/

/-- The generator-image function is computable, given that the map oracle sees the presentation
oracle. -/
theorem sourceGensImage_computableIn (hOE : O ⊆ E) :
    ComputableIn E r.sourceGensImage := by
  have hgens : ComputableIn E A.gens := RecursiveIn.mono hOE A.gens_computableIn
  have hSourcePart : RecursiveIn E fun i ↦ r.toTuplePart i (A.gens i) :=
    r.toTuplePart_recursiveIn.comp (ComputableIn.id.pair hgens)
  exact hSourcePart.computableIn_get _

/-- The generator-preimage function is computable under the same hypothesis. -/
theorem targetGensPreimage_computableIn (hOE : O ⊆ E) :
    ComputableIn E r.targetGensPreimage := by
  have hgens : ComputableIn E fun i ↦ B.gens (r.indexMap i) :=
    (RecursiveIn.mono hOE B.gens_computableIn).comp r.indexMap_computableIn
  have hTargetPart : RecursiveIn E fun i ↦ r.invTuplePart i (B.gens (r.indexMap i)) :=
    r.invTuplePart_recursiveIn.comp (ComputableIn.id.pair hgens)
  exact hTargetPart.computableIn_get _

/-! #### The recovered CHMM sequence

The paper presents a computable isomorphism of representations by a sequence of *tuples*. The
stored isomorphisms recover exactly that sequence, and — crucially — the tuple is realized by the
**induced equivalence itself**, not merely by some isomorphism between the same two members. -/

/-- The potential embedding data determined by a cover at index `i`. Note the two indices refer
to **different families** — `domIdx` to `A`, `codIdx` to `B` — so `PartialAgeIn.PartialIsEmbedding`,
which is single-family, does not express its actualness. The cross-family statement is
`sourceGensImage_realized` below. -/
noncomputable def generatorEmbeddingData (i : ℕ) : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple (i, r.indexMap i, r.sourceGensImage i)

@[simp] theorem generatorEmbeddingData_domIdx (i : ℕ) :
    (r.generatorEmbeddingData i).domIdx = i := rfl

@[simp] theorem generatorEmbeddingData_codIdx (i : ℕ) :
    (r.generatorEmbeddingData i).codIdx = r.indexMap i := rfl

@[simp] theorem generatorEmbeddingData_rangeTuple (i : ℕ) :
    (r.generatorEmbeddingData i).rangeTuple = r.sourceGensImage i := rfl

/-- **The CHMM pair sequence is computable.** Implied by computability of `indexMap` and
`sourceGensImage` separately, but this packaged form is the kernel-checked statement.

Routed through the triple and `encode`, per the note at `PotentialEmbedding.lean`: composing
directly against the `ofEquiv` encoding of `PotentialEmbeddingData` diverges at `whnf`. Note
this is *not* `of_encode_eq`, which compares two functions of the same result type — here the
intermediate returns a triple and the target returns `PotentialEmbeddingData`. -/
theorem generatorEmbeddingData_computableIn (hOE : O ⊆ E) :
    ComputableIn E r.generatorEmbeddingData := by
  have htriple : ComputableIn E fun i : ℕ ↦ (i, r.indexMap i, r.sourceGensImage i) :=
    ComputableIn.id.pair
      (r.indexMap_computableIn.pair (r.sourceGensImage_computableIn hOE))
  have henc : ComputableIn E fun i : ℕ ↦ encode (r.generatorEmbeddingData i) :=
    (ComputableIn.encode.comp htriple).of_eq fun _ ↦ rfl
  exact ComputableIn.encode_iff.mp henc

/-- **The recovered tuple is realized by the induced equivalence itself.** Not merely: some
isomorphism between these two members sends the generators there — but *this* one does. That is
what makes the computational tuple and the semantic equivalence the same map.

Stated through the named cross-family predicate, so conjugation can consume it without
re-expanding a coordinate formula. -/
theorem generatorEmbeddingData_realized (i : ℕ) :
    A.PartialRealizesBetween B (r.generatorEmbeddingData i)
      (r.isoAt i).toEquiv.toEmbedding := by
  refine ⟨(r.sourceGensImage_length i).symm, fun k ↦ ?_⟩
  refine Part.mem_unique ((r.isoAt i).toSubtypeFun_mem (A.gensView i k)) ?_
  exact r.sourceGensImage_get i k.isLt (by rw [r.sourceGensImage_length i]; exact k.isLt)


end RepresentationCoverIn

/-! ### The paper-facing notion

CHMM Definition 2.3: two covers, one in each direction, **independently supplied**. No equation
relates the two index maps. That is not an omission — the paper allows the representations to
contain different numbers of copies of an isomorphism type, so requiring the index maps to be
mutually inverse would be strictly stronger than the definition. -/

/-- **Computable isomorphism of representations** (CHMM Definition 2.3): a cover in each
direction. -/
structure RepresentationIsoIn (E : Set (ℕ →. ℕ)) (A B : PartialAgeIn O L) where
  /-- Every member of `A` is matched in `B`. -/
  forward : RepresentationCoverIn E A B
  /-- Every member of `B` is matched in `A`. -/
  backward : RepresentationCoverIn E B A

namespace RepresentationIsoIn

variable {A B C : PartialAgeIn O L}

/-- Symmetry: swap the two stored covers. Needs no oracle hypothesis, and — crucially — could
not be obtained from `forward` alone, since a cover has no inverse. -/
def symm (r : RepresentationIsoIn E A B) : RepresentationIsoIn E B A where
  forward := r.backward
  backward := r.forward

@[simp] theorem symm_forward (r : RepresentationIsoIn E A B) :
    r.symm.forward = r.backward := rfl

@[simp] theorem symm_backward (r : RepresentationIsoIn E A B) :
    r.symm.backward = r.forward := rfl

@[simp] theorem symm_symm (r : RepresentationIsoIn E A B) : r.symm.symm = r := rfl

/-- Composition: forward covers compose in order, backward covers in the **reverse** order. -/
noncomputable def trans (r : RepresentationIsoIn E A B)
    (s : RepresentationIsoIn E B C) : RepresentationIsoIn E A C where
  forward := r.forward.trans s.forward
  backward := s.backward.trans r.backward

@[simp] theorem trans_forward_indexMap (r : RepresentationIsoIn E A B)
    (s : RepresentationIsoIn E B C) (i : ℕ) :
    (r.trans s).forward.indexMap i = s.forward.indexMap (r.forward.indexMap i) := rfl

@[simp] theorem trans_backward_indexMap (r : RepresentationIsoIn E A B)
    (s : RepresentationIsoIn E B C) (i : ℕ) :
    (r.trans s).backward.indexMap i = r.backward.indexMap (s.backward.indexMap i) := rfl

/-- **Reflexivity**, reusing one cover for both directions. -/
noncomputable def refl (A : PartialAgeIn O L) (hOE : O ⊆ E) : RepresentationIsoIn E A A :=
  let c := RepresentationCoverIn.refl A hOE
  { forward := c, backward := c }

/-- **The semantic consequence.** A computable isomorphism of representations presents the same
class of structures. No oracle hypothesis: each direction reads off the stored index map and
wraps the corresponding member isomorphism's induced first-order equivalence. -/
theorem sameClass (r : RepresentationIsoIn E A B) : A.SameClass B :=
  ⟨fun i ↦ ⟨r.forward.indexMap i, ⟨(r.forward.isoAt i).toEquiv⟩⟩,
    fun j ↦ ⟨r.backward.indexMap j, ⟨(r.backward.isoAt j).toEquiv⟩⟩⟩

end RepresentationIsoIn

end FirstOrder.Language
