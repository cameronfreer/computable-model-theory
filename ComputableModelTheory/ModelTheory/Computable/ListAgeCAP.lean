/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ListAgeExample
import ComputableModelTheory.ModelTheory.Computable.PartialSelectorSpecs

/-!
# A CAP witness for the list age: the pushout of finite pure sets

A spine fixture for the homogeneity-selector audit, which needs the run to exist for an age with
proper extensions. The selector is total and primitive recursive. On a span `S = (F, G)` it glues
the right member onto the left one:

* the apex lists the left member's entries, followed by the glued images of the right member's;
* a right entry `z` naming the `t`-th coordinate of `G`'s range tuple (by its first occurrence) is
  glued to the `t`-th coordinate of `F`'s; any other `z` goes to a fresh value `M + 1 + z`, where
  `M` bounds the left data;
* the left leg is the inclusion, and the right leg is the glue.

The left leg is actual and the right leg well-formed on every span. On an actual span the glue is
injective — two coordinates of `G` naming the same point name the same generator, since `G` is
injective, and `F` then agrees on them — and the square commutes, because every element of a member
of this age is a recorded generator.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

namespace listAge

variable (O : Set (ℕ →. ℕ))

/-! ### The pushout -/

/-- A bound on the left data of a span: the left member's entries and the left range tuple. -/
def spanBound (S : PotentialSpanData) : ℕ :=
  (listOf S.left.codIdx ++ S.left.rangeTuple).sum

/-- The glue: a right entry named by `G`'s range tuple goes where `F` sends that coordinate; any
other entry goes to a fresh value. -/
def glue (S : PotentialSpanData) (z : ℕ) : ℕ :=
  if S.right.rangeTuple.idxOf z < S.right.rangeTuple.length then
    S.left.rangeTuple.getD (S.right.rangeTuple.idxOf z) 0
  else spanBound S + 1 + z

/-- The apex: the left member's entries, then the glued right entries. -/
def apexList (S : PotentialSpanData) : List ℕ :=
  listOf S.left.codIdx ++ (listOf S.right.codIdx).map (glue S)

/-- **The pushout diagram**: the inclusion on the left, the glue on the right. -/
def pushout (S : PotentialSpanData) : AmalgamationDiagramData :=
  ⟨PotentialEmbeddingData.ofTriple (S.left.codIdx, encode (apexList S), listOf S.left.codIdx),
    PotentialEmbeddingData.ofTriple
      (S.right.codIdx, encode (apexList S), (listOf S.right.codIdx).map (glue S))⟩

theorem le_sum_of_mem : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ l.sum
  | a :: l, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · rw [List.sum_cons]; omega
    · have := le_sum_of_mem h
      rw [List.sum_cons]; omega

theorem le_spanBound {S : PotentialSpanData} {x : ℕ} (hx : x ∈ S.left.rangeTuple) :
    x ≤ spanBound S :=
  le_sum_of_mem (List.mem_append_right _ hx)

theorem mem_apexList_of_mem_left {S : PotentialSpanData} {x : ℕ} (hx : x ∈ listOf S.left.codIdx) :
    x ∈ apexList S :=
  List.mem_append_left _ hx

theorem glue_mem_apexList {S : PotentialSpanData} {z : ℕ} (hz : z ∈ listOf S.right.codIdx) :
    glue S z ∈ apexList S :=
  List.mem_append_right _ (List.mem_map_of_mem hz)

/-! ### Effectivity -/

private theorem primrec_leftCod : Primrec fun S : PotentialSpanData ↦ S.left.codIdx :=
  PotentialEmbeddingData.primrec_codIdx.comp PotentialSpanData.primrec_left

private theorem primrec_rightCod : Primrec fun S : PotentialSpanData ↦ S.right.codIdx :=
  PotentialEmbeddingData.primrec_codIdx.comp PotentialSpanData.primrec_right

private theorem primrec_leftRange : Primrec fun S : PotentialSpanData ↦ S.left.rangeTuple :=
  PotentialEmbeddingData.primrec_rangeTuple.comp PotentialSpanData.primrec_left

private theorem primrec_rightRange : Primrec fun S : PotentialSpanData ↦ S.right.rangeTuple :=
  PotentialEmbeddingData.primrec_rangeTuple.comp PotentialSpanData.primrec_right

theorem primrec_spanBound : Primrec spanBound :=
  (Primrec.list_foldr (Primrec.list_append.comp (primrec_listOf.comp primrec_leftCod)
    primrec_leftRange) (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    fun S ↦ by rw [spanBound, List.sum_eq_foldr]

theorem primrec_glue : Primrec₂ glue := by
  have hidx : Primrec₂ fun (S : PotentialSpanData) (z : ℕ) ↦ S.right.rangeTuple.idxOf z :=
    Primrec.list_idxOf.comp Primrec.snd (primrec_rightRange.comp Primrec.fst)
  exact Primrec.ite (Primrec.nat_lt.comp hidx
      (Primrec.list_length.comp (primrec_rightRange.comp Primrec.fst)))
    ((Primrec.list_getD 0).comp (primrec_leftRange.comp Primrec.fst) hidx)
    (Primrec.nat_add.comp (Primrec.nat_add.comp (primrec_spanBound.comp Primrec.fst)
      (Primrec.const 1)) Primrec.snd)

theorem primrec_apexList : Primrec apexList :=
  Primrec.list_append.comp (primrec_listOf.comp primrec_leftCod)
    (Primrec.list_map (primrec_listOf.comp primrec_rightCod) primrec_glue)

theorem primrec_pushout : Primrec pushout := by
  have hA : Primrec fun S ↦ encode (apexList S) := Primrec.encode.comp primrec_apexList
  have hL : Primrec fun S : PotentialSpanData ↦
      PotentialEmbeddingData.ofTriple (S.left.codIdx, encode (apexList S), listOf S.left.codIdx) :=
    PotentialEmbeddingData.primrec_ofTriple.comp
      (Primrec.pair primrec_leftCod (Primrec.pair hA (primrec_listOf.comp primrec_leftCod)))
  have hR : Primrec fun S : PotentialSpanData ↦ PotentialEmbeddingData.ofTriple
      (S.right.codIdx, encode (apexList S), (listOf S.right.codIdx).map (glue S)) :=
    PotentialEmbeddingData.primrec_ofTriple.comp
      (Primrec.pair primrec_rightCod (Primrec.pair hA
        (Primrec.list_map (primrec_listOf.comp primrec_rightCod) primrec_glue)))
  exact (AmalgamationDiagramData.primrec_ofPair.comp (Primrec.pair hL hR)).of_eq fun _ ↦ rfl

/-! ### The glue on an actual span -/

variable {O}

/-- An element of a member is the recorded generator at its first position. -/
theorem eq_gensView_idxOf {d : ℕ} (x : ((listAge O).memberAt d).domain) :
    ∃ ht : (listOf d).idxOf x.1 < ((listAge O).gens d).length,
      x = (listAge O).gensView d ⟨_, ht⟩ :=
  have hx : x.1 ∈ listOf d := (mem_domainAt_iff O).1 x.2
  ⟨List.idxOf_lt_length_of_mem hx, Subtype.ext (List.getElem_idxOf _).symm⟩

section Realizers

variable {S : PotentialSpanData} {d : ℕ}
  {f : ((listAge O).memberAt d).domain ↪[Language.empty]
    ((listAge O).memberAt S.left.codIdx).domain}
  (hf : (listAge O).PartialRealizesAt S.left d S.left.codIdx f)
  {g : ((listAge O).memberAt d).domain ↪[Language.empty]
    ((listAge O).memberAt S.right.codIdx).domain}
  (hg : (listAge O).PartialRealizesAt S.right d S.right.codIdx g)

include hg in
/-- `G` read at a position of the source's generators. -/
theorem right_getElem {t : ℕ} (ht : t < ((listAge O).gens d).length) :
    ∃ ht' : t < S.right.rangeTuple.length,
      S.right.rangeTuple[t] = ((g ((listAge O).gensView d ⟨t, ht⟩) :
        ((listAge O).memberAt S.right.codIdx).domain) : ℕ) := by
  obtain ⟨-, -, hlen, hcoord⟩ := hg
  exact ⟨hlen ▸ ht, (hcoord ⟨t, ht⟩).symm⟩

include hf in
theorem left_getElem {t : ℕ} (ht : t < ((listAge O).gens d).length) :
    ∃ ht' : t < S.left.rangeTuple.length,
      S.left.rangeTuple[t] = ((f ((listAge O).gensView d ⟨t, ht⟩) :
        ((listAge O).memberAt S.left.codIdx).domain) : ℕ) := by
  obtain ⟨-, -, hlen, hcoord⟩ := hf
  exact ⟨hlen ▸ ht, (hcoord ⟨t, ht⟩).symm⟩

include hf hg in
/-- **A glued coordinate is `F`'s value**: a right entry named by `G` at its first occurrence `t'`
is `g` of the `t'`-th generator, and `F` sends that generator where the glue does. -/
theorem glue_of_mem_right {z : ℕ} (hz : S.right.rangeTuple.idxOf z < S.right.rangeTuple.length) :
    ∃ ht : S.right.rangeTuple.idxOf z < ((listAge O).gens d).length,
      glue S z = ((f ((listAge O).gensView d ⟨_, ht⟩) :
          ((listAge O).memberAt S.left.codIdx).domain) : ℕ) ∧
        z = ((g ((listAge O).gensView d ⟨_, ht⟩) :
          ((listAge O).memberAt S.right.codIdx).domain) : ℕ) := by
  have hlen : ((listAge O).gens d).length = S.right.rangeTuple.length := hg.2.2.1
  have ht : S.right.rangeTuple.idxOf z < ((listAge O).gens d).length := hlen ▸ hz
  obtain ⟨htl, hl⟩ := left_getElem hf ht
  obtain ⟨_, hr⟩ := right_getElem hg ht
  refine ⟨ht, ?_, ?_⟩
  · rw [glue, if_pos hz, List.getD_eq_getElem _ _ htl, hl]
  · rw [← hr, List.getElem_idxOf]

include hf hg in
/-- **The glue carries `g` to `f`.** Every element of the source is a recorded generator. -/
theorem glue_apply (x : ((listAge O).memberAt d).domain) :
    glue S (g x : ((listAge O).memberAt S.right.codIdx).domain) =
      (f x : ((listAge O).memberAt S.left.codIdx).domain) := by
  obtain ⟨ht, hx⟩ := eq_gensView_idxOf x
  suffices h : ∀ (t : ℕ) (ht : t < ((listAge O).gens d).length),
      glue S (g ((listAge O).gensView d ⟨t, ht⟩) :
        ((listAge O).memberAt S.right.codIdx).domain) =
        (f ((listAge O).gensView d ⟨t, ht⟩) : ((listAge O).memberAt S.left.codIdx).domain) by
    have := h _ ht
    rwa [← hx] at this
  intro t ht
  obtain ⟨_, hr⟩ := right_getElem hg ht
  have hmem : S.right.rangeTuple.idxOf
      ((g ((listAge O).gensView d ⟨_, ht⟩) : ((listAge O).memberAt S.right.codIdx).domain) : ℕ) <
        S.right.rangeTuple.length :=
    List.idxOf_lt_length_of_mem (hr ▸ List.getElem_mem _)
  obtain ⟨_, hglue, hz⟩ := glue_of_mem_right hf hg hmem
  rw [hglue]
  exact congrArg Subtype.val (congrArg f (g.injective (Subtype.ext hz.symm)))

include hf hg in
/-- **The glue is injective** on an actual span. -/
theorem glue_injective : Function.Injective (glue S) := by
  intro z₁ z₂ h
  by_cases h₁ : S.right.rangeTuple.idxOf z₁ < S.right.rangeTuple.length <;>
    by_cases h₂ : S.right.rangeTuple.idxOf z₂ < S.right.rangeTuple.length
  · obtain ⟨_, hg₁, hz₁⟩ := glue_of_mem_right hf hg h₁
    obtain ⟨_, hg₂, hz₂⟩ := glue_of_mem_right hf hg h₂
    rw [hg₁, hg₂] at h
    rw [hz₁, hz₂, f.injective (Subtype.ext h)]
  · have hle : glue S z₁ ≤ spanBound S := by
      rw [glue, if_pos h₁]
      obtain ⟨htl, -⟩ := left_getElem hf (hg.2.2.1 ▸ h₁)
      rw [List.getD_eq_getElem _ _ htl]
      exact le_spanBound (List.getElem_mem _)
    rw [h, glue, if_neg h₂] at hle
    omega
  · have hle : glue S z₂ ≤ spanBound S := by
      rw [glue, if_pos h₂]
      obtain ⟨htl, -⟩ := left_getElem hf (hg.2.2.1 ▸ h₂)
      rw [List.getD_eq_getElem _ _ htl]
      exact le_spanBound (List.getElem_mem _)
    rw [← h, glue, if_neg h₁] at hle
    omega
  · rw [glue, if_neg h₁, glue, if_neg h₂] at h
    omega

end Realizers

/-! ### The witness -/

theorem apex_mem_domainAt_iff {S : PotentialSpanData} {x : ℕ} :
    x ∈ (listAge O).domainAt (encode (apexList S)) ↔ x ∈ apexList S := by
  rw [mem_domainAt_iff, listOf_encode]

/-- The left leg: the inclusion into the apex. -/
noncomputable def leftLeg (S : PotentialSpanData) :
    ((listAge O).memberAt S.left.codIdx).domain ↪[Language.empty]
      ((listAge O).memberAt (encode (apexList S))).domain :=
  inclusion O fun _ hx ↦ by rw [listOf_encode]; exact mem_apexList_of_mem_left hx

theorem leftLeg_realizesAt (S : PotentialSpanData) :
    (listAge O).PartialRealizesAt (pushout S).leftToApex S.left.codIdx (encode (apexList S))
      (leftLeg S) :=
  ⟨rfl, rfl, rfl, fun _ ↦ rfl⟩

/-- The right leg, given an injective glue. -/
noncomputable def rightLeg (S : PotentialSpanData) (hinj : Function.Injective (glue S)) :
    ((listAge O).memberAt S.right.codIdx).domain ↪[Language.empty]
      ((listAge O).memberAt (encode (apexList S))).domain :=
  emptyEmbedding
    ⟨fun z ↦ ⟨glue S z, (apex_mem_domainAt_iff (O := O)).2
        (glue_mem_apexList ((mem_domainAt_iff O).1 z.2))⟩,
      fun _ _ h ↦ Subtype.ext (hinj (congrArg Subtype.val h))⟩

theorem rightLeg_coe (S : PotentialSpanData) (hinj : Function.Injective (glue S))
    (z : ((listAge O).memberAt S.right.codIdx).domain) :
    ((rightLeg S hinj z : ((listAge O).memberAt (encode (apexList S))).domain) : ℕ) = glue S z :=
  rfl

theorem rightLeg_realizesAt (S : PotentialSpanData) (hinj : Function.Injective (glue S)) :
    (listAge O).PartialRealizesAt (pushout S).rightToApex S.right.codIdx (encode (apexList S))
      (rightLeg S hinj) :=
  ⟨rfl, rfl, (List.length_map _).symm, fun k ↦ by
    rw [rightLeg_coe]
    change _ = ((listOf S.right.codIdx).map (glue S)).get _
    rw [List.get_eq_getElem, List.getElem_map]
    rfl⟩

variable (O) in
/-- **The CAP witness of the list age**: the pushout, total and primitive recursive. -/
noncomputable def capWitness : PartialCAPWitness O (listAge O) where
  sel S := Part.some (pushout S)
  recursiveIn := primrec_pushout.to_comp.computableIn
  halts _ _ := trivial
  unconditional S D hD := by
    obtain rfl := Part.mem_some_iff.1 hD
    refine ⟨⟨rfl, rfl, rfl⟩, (leftLeg_realizesAt S).partialIsEmbedding, fun x hx ↦ ?_,
      (List.length_map _).symm⟩
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    exact apex_mem_domainAt_iff.2 (glue_mem_apexList hz)
  sound S D hD hact := by
    obtain rfl := Part.mem_some_iff.1 hD
    obtain ⟨hshape, ⟨f, hf⟩, ⟨g, hg⟩⟩ := hact
    have hfAt := (PartialAgeIn.partialRealizesAt_self (B := listAge O)).2 hf
    obtain ⟨g', hg'⟩ : ∃ g' : ((listAge O).memberAt S.left.domIdx).domain ↪[Language.empty]
        ((listAge O).memberAt S.right.codIdx).domain,
        (listAge O).PartialRealizesAt S.right S.left.domIdx S.right.codIdx g' :=
      ⟨_, hg.realizesAt_of_eq hshape.symm rfl⟩
    have hinj := glue_injective hfAt hg'
    refine ⟨(rightLeg_realizesAt S hinj).partialIsEmbedding,
      ⟨S.left.domIdx, S.left.codIdx, S.right.codIdx, encode (apexList S), f, g', leftLeg S,
        rightLeg S hinj, hfAt, hg', leftLeg_realizesAt S, rightLeg_realizesAt S hinj, ?_⟩⟩
    refine DFunLike.ext _ _ fun x ↦ Subtype.ext ?_
    exact (glue_apply hfAt hg' x).symm

/-- **The CHP selector of the list age**: a tuple drawn from a member is the recorded generator
list of the member it codes. -/
def chpSel (_ : ℕ) (s : List ℕ) : Part ℕ := Part.some (encode s)

theorem chpSel_recursiveIn : RecursiveIn O fun p : ℕ × List ℕ ↦ chpSel p.1 p.2 :=
  (Primrec.encode.comp Primrec.snd).to_comp.computableIn

theorem mappedCHPSpec : (listAge O).MappedCHPSpec chpSel := by
  intro e s hs
  have hs' : ∀ x ∈ listOf (encode s), x ∈ listOf e := by
    rw [listOf_encode]
    exact fun x hx ↦ (mem_domainAt_iff O).1 (hs x hx)
  refine ⟨encode s, Part.mem_some _, inclusion O hs', congrArg List.length (listOf_encode s),
    fun k ↦ ?_⟩
  change (listOf (encode s)).get k = s.get _
  exact List.get_of_eq (listOf_encode s) k

/-- **The CJEP selector of the list age**: concatenation, with both legs inclusions. -/
def jointSel (i j : ℕ) : PartialJointEmbeddingData :=
  PartialJointEmbeddingData.ofTriple (encode (listOf i ++ listOf j), listOf i, listOf j)

theorem jointSel_computableIn : ComputableIn O fun p : ℕ × ℕ ↦ jointSel p.1 p.2 :=
  (PartialJointEmbeddingData.primrec_ofTriple.comp
    (Primrec.pair (Primrec.encode.comp (Primrec.list_append.comp (primrec_listOf.comp Primrec.fst)
      (primrec_listOf.comp Primrec.snd)))
      (Primrec.pair (primrec_listOf.comp Primrec.fst) (primrec_listOf.comp Primrec.snd)))).to_comp
    |>.computableIn

theorem jointSpec : (listAge O).JointSpec jointSel := by
  intro i j
  have hl : ∀ x ∈ listOf i, x ∈ listOf (encode (listOf i ++ listOf j)) := fun x hx ↦ by
    rw [listOf_encode]; exact List.mem_append_left _ hx
  have hr : ∀ x ∈ listOf j, x ∈ listOf (encode (listOf i ++ listOf j)) := fun x hx ↦ by
    rw [listOf_encode]; exact List.mem_append_right _ hx
  exact ⟨⟨inclusion O hl, rfl, fun _ ↦ rfl⟩, ⟨inclusion O hr, rfl, fun _ ↦ rfl⟩⟩

/-! ### The run on the list age -/

theorem base_nonempty : ((listAge O).domainAt (encode [0])).Nonempty :=
  ⟨0, by rw [mem_domainAt_iff, listOf_encode]; exact List.mem_singleton_self _⟩

variable (O) in
/-- **The run's chain** on the list age, from the member `{0}`, with the pushout witness. -/
noncomputable abbrev runChain : CeStructureChainIn O Language.empty :=
  PartialAgeIn.runChain (listAge O) (capWitness O) (encode [0]) (le_refl O) base_nonempty

variable (O) in
/-- **Its canonical limit.** -/
noncomputable abbrev runLimit : (runChain O).LimitIn :=
  (runChain O).toLimit
    (PartialAgeIn.runChain_uniformEvaluators (listAge O) (capWitness O) (encode [0]) (le_refl O)
      base_nonempty)

variable (O) in
/-- The run's limit is a Fraïssé limit of the finite pure sets. -/
theorem runLimit_isFraisseLimit :
    Language.empty.IsFraisseLimit (listAge O).classSet (runLimit O).presentation.domain :=
  PartialAgeIn.run_isFraisseLimit (le_refl O) base_nonempty (runLimit O) (hasMappedHP O)
    (hasJEP O)

variable (O) in
/-- **The limit is infinite**: the member `{0, …, N}` embeds into it for every `N`. -/
theorem runLimit_infinite : (runLimit O).presentation.domain.Infinite := by
  intro hfin
  haveI := hfin.fintype
  set N := Fintype.card (runLimit O).presentation.domain
  have hmem : (listAge O).memberBundled (segIdx N) ∈
      Language.empty.age (runLimit O).presentation.domain := by
    rw [(runLimit_isFraisseLimit O).age]
    exact (listAge O).memberBundled_mem_classSet _
  obtain ⟨e⟩ := hmem.2
  have hinj : Function.Injective fun j : Fin (N + 1) ↦
      e ⟨(j : ℕ), (mem_domainAt_segIdx O).2 j.2⟩ :=
    fun j₁ j₂ h ↦ Fin.ext (congrArg Subtype.val (e.injective h))
  have := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin] at this
  omega

variable (O) in
/-- **The infinitude certificate** of the run's limit. -/
theorem runLimit_cert : (runLimit O).presentation.InfinitudeCertificate :=
  CePresentationIn.infinitudeCertificate_of_infinite _ (runLimit_infinite O)

end listAge

end FirstOrder.Language
