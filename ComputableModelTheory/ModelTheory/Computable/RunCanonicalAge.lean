/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.HomogeneitySelector
import ComputableModelTheory.ModelTheory.Computable.GeneratedImageIso

/-!
# The run's limit represents its own age: Theorem 3.9, effective canonicality

`RepresentationIsoIn O F.canonicalAge K` for `F := Z.omegaStructure cert`, the ω structure of the
run's limit, with **both covers generator-compatible**. Everything is at one oracle `O`: the family,
the CAP witness, the CHP and CJEP selectors, and so the run's chain and its limit. With a separate
witness oracle the conclusion would need the rebased family `K.mono hOE`, and that is a separate
result.

The two covers are constructed independently, for this run's limit, and both go through the
generated-image constructors of `GeneratedImageIso` — so every structure law, the uniformity of both
halves, and generator compatibility come from there, and each program carries the `idFun` guard that
turns sufficient halting into the exact domain those constructors require.

* **Forward, `F.canonicalAge → K`.** A canonical query names a tuple of ω-codes; the tuple pullback
  moves it to one stage `r`; CHP at the stage's member index selects the member it generates there.
  Self-matching (`RepresentedByRawRep`) makes the image tuple the query's own tuple.
* **Backward, `K → F.canonicalAge`.** Member `j` is covered by computed extensions, not by the
  semantic extension property. CJEP embeds the base member `A_{i₀}` and `A_j` into an apex `A_c`.
  The prefix iteration then climbs `A_c`'s generators one at a time: at prefix `t` it holds a member
  `c_t` representing `L ++ (gens c).take t` in `A_c` (`L` the image of `A_{i₀}`'s generators), a
  stage `s_t` and the images `H_t` of `c_t`'s generators there. The step represents the next prefix
  by CHP, forms the one-point requirement with positional target tuple, searches for its firing, and
  recomputes the payload; the new images are the payload's right range tuple. At the last prefix
  the images of `A_c`'s generators are `H_T.drop n`, with no inverse computed, and composing with
  CJEP's right leg embeds `A_j`.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace PartialAgeIn

/-! ### The forward cover `F.canonicalAge → K` -/

section Forward

variable {K : PartialAgeIn O L} {W : PartialCAPWitness O K} {i : ℕ}
  {h0 : (K.domainAt i).Nonempty} (Z : (runChain K W i (Set.Subset.refl O) h0).LimitIn)
  (chpSel : ℕ → List ℕ →. ℕ)

/-- **The forward answer to a canonical query**: the pullback of its tuple to a common stage, and
the member CHP selects there. Returned together, totalized together. -/
noncomputable def runForwardAnswerPart (e : ℕ) : Part ((ℕ × List ℕ) × ℕ) :=
  (Z.rankTupleAtStagePart (allTupleFor e)).bind fun p ↦
    (chpSel (memberIdx K W i p.1) p.2).map fun c ↦ (p, c)

theorem runForwardAnswerPart_dom (cert : Z.presentation.InfinitudeCertificate)
    (hchpSpec : K.MappedCHPSpec chpSel) (e : ℕ) : (runForwardAnswerPart Z chpSel e).Dom := by
  obtain ⟨p, hp⟩ := Part.dom_iff_mem.1 (Z.rankTupleAtStagePart_dom cert (allTupleFor e))
  obtain ⟨c, hc, -⟩ := hchpSpec _ _ (mem_domainAt_of_mem_pull Z hp)
  exact Part.dom_iff_mem.2 ⟨(p, c), Part.mem_bind_iff.2
    ⟨p, hp, (Part.mem_map_iff _).2 ⟨c, hc, rfl⟩⟩⟩

theorem runForwardAnswerPart_recursiveIn
    (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2) :
    RecursiveIn O (runForwardAnswerPart Z chpSel) := by
  have hA : RecursiveIn O fun e : ℕ ↦ Z.rankTupleAtStagePart (allTupleFor e) :=
    Z.rankTupleAtStagePart_recursiveIn.comp allTupleFor_computableIn
  have hB : RecursiveIn O fun q : ℕ × (ℕ × List ℕ) ↦
      (chpSel (memberIdx K W i q.2.1) q.2.2).map fun c ↦ (q.2, c) :=
    RecursiveIn.map
      (hchp.comp
        (((memberIdx_computableIn K W i (Set.Subset.refl O)).comp
          (ComputableIn.fst.comp ComputableIn.snd)).pair
          (ComputableIn.snd.comp ComputableIn.snd)))
      (((ComputableIn.snd.comp ComputableIn.fst).pair ComputableIn.snd).to₂)
  exact RecursiveIn.bind hA hB.to₂

variable (cert : Z.presentation.InfinitudeCertificate) (hchpSpec : K.MappedCHPSpec chpSel)

include cert hchpSpec in
/-- The forward answer, totalized **once**. -/
noncomputable def runForwardAnswer (e : ℕ) : (ℕ × List ℕ) × ℕ :=
  (runForwardAnswerPart Z chpSel e).get (runForwardAnswerPart_dom Z chpSel cert hchpSpec e)

/-- The common stage. -/
noncomputable def runForwardStage (e : ℕ) : ℕ := (runForwardAnswer Z chpSel cert hchpSpec e).1.1

/-- The pulled-back tuple. -/
noncomputable def runForwardTuple (e : ℕ) : List ℕ :=
  (runForwardAnswer Z chpSel cert hchpSpec e).1.2

/-- The member CHP selected: the forward cover's source index. -/
noncomputable def runForwardIndex (e : ℕ) : ℕ := (runForwardAnswer Z chpSel cert hchpSpec e).2

theorem runForward_mem (e : ℕ) :
    (runForwardStage Z chpSel cert hchpSpec e, runForwardTuple Z chpSel cert hchpSpec e) ∈
        Z.rankTupleAtStagePart (allTupleFor e) ∧
      runForwardIndex Z chpSel cert hchpSpec e ∈
        chpSel (memberIdx K W i (runForwardStage Z chpSel cert hchpSpec e))
          (runForwardTuple Z chpSel cert hchpSpec e) := by
  obtain ⟨p, hp, hmap⟩ := Part.mem_bind_iff.1
    (Part.get_mem (runForwardAnswerPart_dom Z chpSel cert hchpSpec e))
  obtain ⟨c, hc, heq⟩ := (Part.mem_map_iff _).1 hmap
  have h₁ : runForwardAnswer Z chpSel cert hchpSpec e = (p, c) := heq.symm
  simp only [runForwardStage, runForwardTuple, runForwardIndex, h₁]
  exact ⟨hp, hc⟩

/-- The selection, as potential embedding data into the stage's member. -/
noncomputable def runForwardData (e : ℕ) : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple (runForwardIndex Z chpSel cert hchpSpec e,
    memberIdx K W i (runForwardStage Z chpSel cert hchpSpec e),
    runForwardTuple Z chpSel cert hchpSpec e)

theorem runForwardData_partialIsEmbedding (e : ℕ) :
    K.PartialIsEmbedding (runForwardData Z chpSel cert hchpSpec e) := by
  obtain ⟨hp, hc⟩ := runForward_mem Z chpSel cert hchpSpec e
  obtain ⟨c, hc', hemb⟩ := hchpSpec _ _ (mem_domainAt_of_mem_pull Z hp)
  obtain rfl := Part.mem_unique hc' hc
  exact hemb

/-- The realizer of the selection. -/
noncomputable def runForwardRealizer (e : ℕ) :
    (K.memberAt (runForwardIndex Z chpSel cert hchpSpec e)).domain ↪[L]
      (K.memberAt (memberIdx K W i (runForwardStage Z chpSel cert hchpSpec e))).domain :=
  (runForwardData_partialIsEmbedding Z chpSel cert hchpSpec e).choose

theorem runForwardRealizer_spec (e : ℕ) :
    K.PartialRealizes (runForwardData Z chpSel cert hchpSpec e)
      (runForwardRealizer Z chpSel cert hchpSpec e) :=
  (runForwardData_partialIsEmbedding Z chpSel cert hchpSpec e).choose_spec

/-- **The program, guarded**: the domain guard, the selected embedding, the recoded stage map. -/
noncomputable def runForwardMap (e : ℕ) : ℕ →. ℕ :=
  fun x ↦ (K.idFun (runForwardIndex Z chpSel cert hchpSpec e, x)).bind fun x' ↦
    (K.applyPotentialPart (runForwardData Z chpSel cert hchpSpec e) x').bind fun y ↦
      Z.rankStageMap (runForwardStage Z chpSel cert hchpSpec e) y

/-- **The semantic embedding** of the selected member into ω. -/
noncomputable def runForwardEmbedding (e : ℕ) :
    @Language.Embedding L (K.memberAt (runForwardIndex Z chpSel cert hchpSpec e)).domain ℕ _
      (Z.omegaStructure cert).inst :=
  letI : L.Structure ℕ := Z.presentation.rankStr
  (omegaMember Z (runForwardStage Z chpSel cert hchpSpec e)).comp
    (runForwardRealizer Z chpSel cert hchpSpec e)

theorem runForwardEmbedding_mem (e : ℕ)
    (x : (K.memberAt (runForwardIndex Z chpSel cert hchpSpec e)).domain) :
    runForwardEmbedding Z chpSel cert hchpSpec e x ∈
      runForwardMap Z chpSel cert hchpSpec e (x : ℕ) := by
  refine Part.mem_bind_iff.2 ⟨(x : ℕ), K.mem_idFun.2 ⟨rfl, x.2⟩, ?_⟩
  refine Part.mem_bind_iff.2 ⟨_, applyPotentialPart_mem_realizer
    (runForwardRealizer_spec Z chpSel cert hchpSpec e) x.2, ?_⟩
  exact omegaMember_mem_rankStageMap Z _ _

theorem runForwardMap_dom (e x : ℕ) :
    (runForwardMap Z chpSel cert hchpSpec e x).Dom ↔
      x ∈ K.domainAt (runForwardIndex Z chpSel cert hchpSpec e) := by
  refine ⟨fun h ↦ ?_, fun hx ↦ Part.dom_iff_mem.2 ⟨_, runForwardEmbedding_mem Z chpSel cert
    hchpSpec e ⟨x, hx⟩⟩⟩
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 h
  obtain ⟨x', hx', -⟩ := Part.mem_bind_iff.1 hy
  exact (K.mem_idFun.1 hx').2

section Effectivity

variable (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2)

include hchp in
theorem runForwardAnswer_computableIn : ComputableIn O (runForwardAnswer Z chpSel cert hchpSpec) :=
  RecursiveIn.computableIn_get (runForwardAnswerPart_recursiveIn Z chpSel hchp)
    (runForwardAnswerPart_dom Z chpSel cert hchpSpec)

include hchp in
theorem runForwardIndex_computableIn : ComputableIn O (runForwardIndex Z chpSel cert hchpSpec) :=
  (Primrec.snd.to_comp.computableIn).comp
    (runForwardAnswer_computableIn Z chpSel cert hchpSpec hchp)

include hchp in
theorem runForwardStage_computableIn : ComputableIn O (runForwardStage Z chpSel cert hchpSpec) :=
  ((Primrec.fst.comp Primrec.fst).to_comp.computableIn).comp
    (runForwardAnswer_computableIn Z chpSel cert hchpSpec hchp)

include hchp in
theorem runForwardData_computableIn : ComputableIn O (runForwardData Z chpSel cert hchpSpec) := by
  have hans := runForwardAnswer_computableIn Z chpSel cert hchpSpec hchp
  have hstage : ComputableIn O fun e ↦ memberIdx K W i (runForwardStage Z chpSel cert hchpSpec e) :=
    (memberIdx_computableIn K W i (Set.Subset.refl O)).comp
      (runForwardStage_computableIn Z chpSel cert hchpSpec hchp)
  have htuple : ComputableIn O (runForwardTuple Z chpSel cert hchpSpec) :=
    ((Primrec.snd.comp Primrec.fst).to_comp.computableIn).comp hans
  exact (PotentialEmbeddingData.primrec_ofTriple.to_comp.computableIn).comp
    ((runForwardIndex_computableIn Z chpSel cert hchpSpec hchp).pair (hstage.pair htuple))

include hchp in
theorem runForwardMap_uniform :
    RecursiveIn O fun p : ℕ × ℕ ↦ runForwardMap Z chpSel cert hchpSpec p.1 p.2 := by
  have hidx := runForwardIndex_computableIn Z chpSel cert hchpSpec hchp
  have hdata := runForwardData_computableIn Z chpSel cert hchpSpec hchp
  have hstage := runForwardStage_computableIn Z chpSel cert hchpSpec hchp
  have h₁ : RecursiveIn O fun p : ℕ × ℕ ↦
      K.idFun (runForwardIndex Z chpSel cert hchpSpec p.1, p.2) :=
    K.idFun_recursiveIn.comp ((hidx.comp ComputableIn.fst).pair ComputableIn.snd)
  have h₂ : RecursiveIn O fun q : (ℕ × ℕ) × ℕ ↦
      K.applyPotentialPart (runForwardData Z chpSel cert hchpSpec q.1.1) q.2 :=
    RecursiveIn.comp (O := O) (α := (ℕ × ℕ) × ℕ) (β := PotentialEmbeddingData × ℕ) (σ := ℕ)
      (f := fun r : PotentialEmbeddingData × ℕ ↦ K.applyPotentialPart r.1 r.2)
      (g := fun q : (ℕ × ℕ) × ℕ ↦ (runForwardData Z chpSel cert hchpSpec q.1.1, q.2))
      K.applyPotentialPart_recursiveIn
      ((hdata.comp (ComputableIn.fst.comp ComputableIn.fst)).pair ComputableIn.snd)
  have h₃ : RecursiveIn O fun r : ((ℕ × ℕ) × ℕ) × ℕ ↦
      Z.rankStageMap (runForwardStage Z chpSel cert hchpSpec r.1.1.1) r.2 :=
    RecursiveIn.comp (O := O) (α := ((ℕ × ℕ) × ℕ) × ℕ) (β := ℕ × ℕ) (σ := ℕ)
      (f := fun p : ℕ × ℕ ↦ Z.rankStageMap p.1 p.2)
      (g := fun r : ((ℕ × ℕ) × ℕ) × ℕ ↦ (runForwardStage Z chpSel cert hchpSpec r.1.1.1, r.2))
      Z.rankStageMap_recursiveIn
      ((hstage.comp (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst))).pair
        ComputableIn.snd)
  exact RecursiveIn.bind h₁ (RecursiveIn.bind h₂ h₃.to₂).to₂

/-- **The selected embedding of `K` into the run's ω structure**, indexed by canonical queries. -/
noncomputable def runToSelectedEmbedding :
    UniformSelectedEmbeddingIntoIn O K (Z.omegaStructure cert) where
  sourceIndex := runForwardIndex Z chpSel cert hchpSpec
  sourceIndex_computableIn := runForwardIndex_computableIn Z chpSel cert hchpSpec hchp
  embedding := runForwardEmbedding Z chpSel cert hchpSpec
  map := runForwardMap Z chpSel cert hchpSpec
  map_uniform := runForwardMap_uniform Z chpSel cert hchpSpec hchp
  map_dom := runForwardMap_dom Z chpSel cert hchpSpec
  map_apply_mem := runForwardEmbedding_mem Z chpSel cert hchpSpec

/-- **Self-matching.** The program carries the selected member's generators onto the query's own
tuple: CHP's coordinates composed with the pullback's (`RepresentedByRawRep`). -/
theorem runImageTuple_eq_allTupleFor (hrep : Z.RepresentedByRawRep) (e : ℕ) :
    (runToSelectedEmbedding Z chpSel cert hchpSpec hchp).imageTuple e = allTupleFor e := by
  refine Part.mem_unique (Part.get_mem _) (mem_listMapPart_iff.2 ?_)
  obtain ⟨hlen, hF⟩ := runForwardRealizer_spec Z chpSel cert hchpSpec e
  have hco := Z.forall₂_omegaStageEmbedding hrep (runForward_mem Z chpSel cert hchpSpec e).1
  obtain ⟨hcoLen, hcoGet⟩ := List.forall₂_iff_get.1 hco
  refine List.forall₂_iff_get.2 ⟨?_, fun m h₁ h₂ ↦ ?_⟩
  · change (K.gens (runForwardIndex Z chpSel cert hchpSpec e)).length = _
    rw [show (K.gens (runForwardIndex Z chpSel cert hchpSpec e)).length =
      (runForwardTuple Z chpSel cert hchpSpec e).length from hlen, ← hcoLen]
  have hlt : m < (runForwardTuple Z chpSel cert hchpSpec e).length := by
    rw [← show (K.gens (runForwardIndex Z chpSel cert hchpSpec e)).length =
      (runForwardTuple Z chpSel cert hchpSpec e).length from hlen]; exact h₁
  obtain ⟨hy, hyeq⟩ := hcoGet m h₂ hlt
  have hx : (K.gens (runForwardIndex Z chpSel cert hchpSpec e)).get ⟨m, h₁⟩ ∈
      K.domainAt (runForwardIndex Z chpSel cert hchpSpec e) := K.gens_mem_domainAt ⟨m, h₁⟩
  refine Part.mem_bind_iff.2 ⟨_, K.mem_idFun.2 ⟨rfl, hx⟩, ?_⟩
  refine Part.mem_bind_iff.2 ⟨(runForwardTuple Z chpSel cert hchpSpec e).get ⟨m, hlt⟩, ?_, ?_⟩
  · have hmem := applyPotentialPart_mem_realizer
      (runForwardRealizer_spec Z chpSel cert hchpSpec e) hx
    have hval : ((runForwardRealizer Z chpSel cert hchpSpec e ⟨_, hx⟩ :
          (K.memberAt (memberIdx K W i (runForwardStage Z chpSel cert hchpSpec e))).domain) : ℕ)
        = (runForwardTuple Z chpSel cert hchpSpec e).get ⟨m, hlt⟩ := hF ⟨m, h₁⟩
    exact hval ▸ hmem
  · rw [← hyeq]
    exact Z.omegaStageEmbedding_apply_mem _ ⟨_, hy⟩

/-- **The forward cover `F.canonicalAge → K`**, from the generated-image constructor. -/
noncomputable def runForwardCover (hrep : Z.RepresentedByRawRep) :
    RepresentationCoverIn O (Z.omegaStructure cert).canonicalAge K :=
  (runToSelectedEmbedding Z chpSel cert hchpSpec hchp).fromCanonicalAgeCover (Set.Subset.refl O)
    (runImageTuple_eq_allTupleFor Z chpSel cert hchpSpec hchp hrep)

theorem runForwardCover_generatorCompatible (hrep : Z.RepresentedByRawRep) :
    (runForwardCover Z chpSel cert hchpSpec hchp hrep).GeneratorCompatible :=
  (runToSelectedEmbedding Z chpSel cert hchpSpec hchp).fromCanonicalAgeCover_generatorCompatible
    (Set.Subset.refl O) (runImageTuple_eq_allTupleFor Z chpSel cert hchpSpec hchp hrep)

end Effectivity

end Forward

/-! ### Prefix factoring -/

section Factor

variable {K : PartialAgeIn O L}

/-- **Prefix factoring.** If `A_a` and `A_b` represent tuples `P` and `P ++ P''` of one member
`A_c`, the first `|gens a|` generators of `A_b` are the images of `A_a`'s under an actual
embedding. -/
theorem partialIsEmbedding_take_of_prefix {a b c : ℕ} {P P' : List ℕ}
    (ha : K.PartialIsEmbedding (PotentialEmbeddingData.ofTriple (a, c, P)))
    (hb : K.PartialIsEmbedding (PotentialEmbeddingData.ofTriple (b, c, P'))) (hP : P <+: P') :
    K.PartialIsEmbedding
      (PotentialEmbeddingData.ofTriple (a, b, (K.gens b).take (K.gens a).length)) := by
  obtain ⟨e, he⟩ : ∃ e : (K.memberAt a).domain ↪[L] (K.memberAt c).domain,
      K.PartialRealizes (PotentialEmbeddingData.ofTriple (a, c, P)) e := ha
  obtain ⟨e', he'⟩ : ∃ e' : (K.memberAt b).domain ↪[L] (K.memberAt c).domain,
      K.PartialRealizes (PotentialEmbeddingData.ofTriple (b, c, P')) e' := hb
  obtain ⟨P'', rfl⟩ := hP
  have hla : (K.gens a).length = P.length := he.length
  have hlb : (K.gens b).length = (P ++ P'').length := he'.length
  have hab : (K.gens a).length ≤ (K.gens b).length := by
    rw [hla, hlb, List.length_append]; omega
  -- the generators of `A_a` and the first ones of `A_b` name the same points of `A_c`
  have hsame : ∀ (k : ℕ) (z : (K.memberAt a).domain), (K.gens a)[k]? = Option.some (z : ℕ) →
      ∃ w : (K.memberAt b).domain, (K.gens b)[k]? = Option.some (w : ℕ) ∧ e' w = e z := by
    intro k z hz
    have hk : k < (K.gens b).length := by
      have := (List.getElem?_eq_some_iff.1 hz).1; omega
    refine ⟨⟨(K.gens b)[k], K.mem_domainAt_of_mem_gens (List.getElem_mem hk)⟩,
      List.getElem?_eq_getElem hk, Subtype.ext ?_⟩
    have h₁ := getElem?_of_realizes (partialRealizesBetween_self.2 he) hz
    have h₂ := getElem?_of_realizes (partialRealizesBetween_self.2 he')
      (x := ⟨(K.gens b)[k], K.mem_domainAt_of_mem_gens (List.getElem_mem hk)⟩)
      (List.getElem?_eq_getElem hk)
    change P[k]? = _ at h₁
    change (P ++ P'')[k]? = _ at h₂
    rw [List.getElem?_append_left (by rw [← hla]; exact (List.getElem?_eq_some_iff.1 hz).1),
      h₁] at h₂
    exact (Option.some.inj h₂).symm
  obtain ⟨θ, hθ⟩ := exists_embedding_factor e e'
    (memberEmbedding_mem_range_of_gens e e' fun k ↦ by
      obtain ⟨w, -, hw⟩ := hsame k (K.gensView a k) (List.getElem?_eq_getElem (l := K.gens a) k.2)
      exact ⟨w, hw⟩)
  refine ⟨θ, partialRealizesBetween_self.1 (realizes_of_getElem? ?_ fun k z hz ↦ ?_)⟩
  · rw [List.length_take]; omega
  · have hk : k < (K.gens a).length := (List.getElem?_eq_some_iff.1 hz).1
    obtain ⟨w, hw, hwe⟩ := hsame k z hz
    rw [List.getElem?_take_of_lt hk, hw, ← e'.injective (hwe.trans (hθ z).symm)]

end Factor

/-! ### The backward cover `K → F.canonicalAge`: the prefix iteration -/

section Prefix

variable (K : PartialAgeIn O L) (W : PartialCAPWitness O K) (i : ℕ)
  (chpSel : ℕ → List ℕ →. ℕ) (sel : ℕ → ℕ → PartialJointEmbeddingData)

/-- The `t`-th prefix tuple for member `j`: the base member's generators in the CJEP apex, then the
apex's first `t` generators. -/
def prefixList (j t : ℕ) : List ℕ :=
  (sel i j).leftImage ++ (K.gens (sel i j).apexIdx).take t

/-- The one-point requirement of a prefix step, from state `(c_t, s_t, H_t)` to the representative
`c'` of the next prefix. Its target tuple is positional: `c'`'s first `|gens c_t|` generators. -/
def prefixRequirement (st : ℕ × ℕ × List ℕ) (c' : ℕ) : RequirementData :=
  ⟨st.1, st.2.1, c', st.2.2, (K.gens c').take (K.gens st.1).length⟩

/-- **One prefix step**: represent the next prefix by CHP, search for the requirement's firing,
recompute its payload, and read the new images off the right leg. -/
noncomputable def prefixStep (j t : ℕ) (st : ℕ × ℕ × List ℕ) : Part (ℕ × ℕ × List ℕ) :=
  (chpSel (sel i j).apexIdx (prefixList K i sel j (t + 1))).bind fun c' ↦
    (firingSearch K W i (encode (prefixRequirement K st c'))).bind fun s ↦
      (payloadPart K W i s (prefixRequirement K st c')).map fun D ↦
        (c', s + 1, D.rightToApex.rangeTuple)

/-- **The prefix iteration** for member `j`, from the base member at stage `0` with its own
generators. -/
noncomputable def prefixPart (j : ℕ) : ℕ → Part (ℕ × ℕ × List ℕ)
  | 0 => Part.some (i, 0, K.gens i)
  | t + 1 => (prefixPart j t).bind (prefixStep K W i chpSel sel j t)

/-- **The backward answer** for member `j`: the stage reached at the last prefix, and the images of
`A_j`'s generators there — CJEP's right leg composed with `H_T.drop n`. -/
noncomputable def backwardAnswerPart (j : ℕ) : Part (ℕ × List ℕ) :=
  (prefixPart K W i chpSel sel j (K.gens (sel i j).apexIdx).length).bind fun st ↦
    (listMapPart (K.applyPotentialPart (PotentialEmbeddingData.ofTriple
      ((sel i j).apexIdx, memberIdx K W i st.2.1, st.2.2.drop (K.gens i).length)))
        (sel i j).rightImage).map fun v ↦ (st.2.1, v)

end Prefix

section PrefixEffectivity

variable {K : PartialAgeIn O L} {W : PartialCAPWitness O K} {i : ℕ}
  {chpSel : ℕ → List ℕ →. ℕ} {sel : ℕ → ℕ → PartialJointEmbeddingData}
  (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2)
  (hsel : ComputableIn O fun p : ℕ × ℕ ↦ sel p.1 p.2)

/-- The step's input: member, prefix, state. -/
private abbrev StepIn : Type := (ℕ × ℕ) × (ℕ × ℕ × List ℕ)

include hsel in
private theorem apex_computableIn : ComputableIn O fun j ↦ (sel i j).apexIdx :=
  (PartialJointEmbeddingData.primrec_apexIdx.to_comp.computableIn (O := O)).comp
    (hsel.comp ((ComputableIn.const i).pair ComputableIn.id))

include hsel in
private theorem prefixList_computableIn :
    ComputableIn O fun p : ℕ × ℕ ↦ prefixList K i sel p.1 p.2 := by
  have hleft : ComputableIn O fun p : ℕ × ℕ ↦ (sel i p.1).leftImage :=
    (PartialJointEmbeddingData.primrec_leftImage.to_comp.computableIn (O := O)).comp
      (hsel.comp ((ComputableIn.const i).pair ComputableIn.fst))
  have hgens : ComputableIn O fun p : ℕ × ℕ ↦ K.gens (sel i p.1).apexIdx :=
    K.gens_computableIn.comp ((apex_computableIn hsel).comp ComputableIn.fst)
  exact ((Primrec.list_append.to_comp.computableIn₂ (O := O)).comp hleft
    (((Primrec₂.swap Primrec.list_take).to_comp.computableIn₂ (O := O)).comp hgens
      ComputableIn.snd)).of_eq fun _ ↦ rfl

private theorem prefixRequirement_computableIn :
    ComputableIn O fun p : (ℕ × ℕ × List ℕ) × ℕ ↦ prefixRequirement K p.1 p.2 := by
  have hgens₁ : ComputableIn O fun p : (ℕ × ℕ × List ℕ) × ℕ ↦ (K.gens p.1.1).length :=
    (Primrec.list_length.to_comp.computableIn (O := O)).comp
      (K.gens_computableIn.comp (ComputableIn.fst.comp ComputableIn.fst))
  have htake : ComputableIn O fun p : (ℕ × ℕ × List ℕ) × ℕ ↦
      (K.gens p.2).take (K.gens p.1.1).length :=
    ((Primrec₂.swap Primrec.list_take).to_comp.computableIn₂ (O := O)).comp
      (K.gens_computableIn.comp ComputableIn.snd) hgens₁
  exact ComputableIn.encode_iff.1
    ((ComputableIn.encode.comp
      ((ComputableIn.fst.comp ComputableIn.fst).pair
        ((ComputableIn.fst.comp (ComputableIn.snd.comp ComputableIn.fst)).pair
          (ComputableIn.snd.pair
            ((ComputableIn.snd.comp (ComputableIn.snd.comp ComputableIn.fst)).pair
              htake))))).of_eq fun _ ↦ rfl)

include hchp hsel in
theorem prefixStep_recursiveIn :
    RecursiveIn O fun x : StepIn ↦ prefixStep K W i chpSel sel x.1.1 x.1.2 x.2 := by
  have hj : ComputableIn O fun x : StepIn ↦ x.1.1 := ComputableIn.fst.comp ComputableIn.fst
  have hapex : ComputableIn O fun x : StepIn ↦ (sel i x.1.1).apexIdx :=
    ComputableIn.comp (α := StepIn) (β := ℕ) (σ := ℕ) (f := fun j ↦ (sel i j).apexIdx)
      (g := fun x ↦ x.1.1) (apex_computableIn hsel) hj
  have hpre : ComputableIn O fun x : StepIn ↦ prefixList K i sel x.1.1 (x.1.2 + 1) :=
    ComputableIn.comp (α := StepIn) (β := ℕ × ℕ) (σ := List ℕ)
      (f := fun p ↦ prefixList K i sel p.1 p.2) (g := fun x ↦ (x.1.1, x.1.2 + 1))
      (prefixList_computableIn hsel)
      (ComputableIn.pair (α := StepIn) (β := ℕ) (γ := ℕ) (f := fun x ↦ x.1.1)
        (g := fun x ↦ x.1.2 + 1) hj
        (ComputableIn.comp (α := StepIn) (β := ℕ) (σ := ℕ) (f := Nat.succ) (g := fun x ↦ x.1.2)
          (Primrec.succ.to_comp.computableIn (O := O)) (ComputableIn.snd.comp ComputableIn.fst)))
  have hchp₁ : RecursiveIn O fun x : StepIn ↦
      chpSel (sel i x.1.1).apexIdx (prefixList K i sel x.1.1 (x.1.2 + 1)) :=
    RecursiveIn.comp (α := StepIn) (β := ℕ × List ℕ) (σ := ℕ) (f := fun q ↦ chpSel q.1 q.2)
      (g := fun x ↦ ((sel i x.1.1).apexIdx, prefixList K i sel x.1.1 (x.1.2 + 1))) hchp
      (ComputableIn.pair (α := StepIn) (β := ℕ) (γ := List ℕ) (f := fun x ↦ (sel i x.1.1).apexIdx)
        (g := fun x ↦ prefixList K i sel x.1.1 (x.1.2 + 1)) hapex hpre)
  have hreq : ComputableIn O fun y : StepIn × ℕ ↦ prefixRequirement K y.1.2 y.2 :=
    ComputableIn.comp (α := StepIn × ℕ) (β := (ℕ × ℕ × List ℕ) × ℕ) (σ := RequirementData)
      (f := fun p ↦ prefixRequirement K p.1 p.2) (g := fun y ↦ (y.1.2, y.2))
      prefixRequirement_computableIn
      (ComputableIn.pair (α := StepIn × ℕ) (β := ℕ × ℕ × List ℕ) (γ := ℕ) (f := fun y ↦ y.1.2)
        (g := fun y ↦ y.2) (ComputableIn.snd.comp ComputableIn.fst) ComputableIn.snd)
  have hsearch : RecursiveIn O fun y : StepIn × ℕ ↦
      firingSearch K W i (encode (prefixRequirement K y.1.2 y.2)) :=
    RecursiveIn.comp (α := StepIn × ℕ) (β := ℕ) (σ := ℕ) (f := firingSearch K W i)
      (g := fun y ↦ encode (prefixRequirement K y.1.2 y.2))
      (firingSearch_recursiveIn (Set.Subset.refl O))
      (ComputableIn.comp (α := StepIn × ℕ) (β := RequirementData) (σ := ℕ) (f := encode)
        (g := fun y ↦ prefixRequirement K y.1.2 y.2) ComputableIn.encode hreq)
  have hpay : RecursiveIn O fun z : (StepIn × ℕ) × ℕ ↦
      payloadPart K W i z.2 (prefixRequirement K z.1.1.2 z.1.2) :=
    RecursiveIn.comp (α := (StepIn × ℕ) × ℕ) (β := ℕ × RequirementData)
      (σ := AmalgamationDiagramData) (f := fun p ↦ payloadPart K W i p.1 p.2)
      (g := fun z ↦ (z.2, prefixRequirement K z.1.1.2 z.1.2))
      (payloadPart_recursiveIn (Set.Subset.refl O))
      (ComputableIn.pair (α := (StepIn × ℕ) × ℕ) (β := ℕ) (γ := RequirementData)
        (f := fun z ↦ z.2) (g := fun z ↦ prefixRequirement K z.1.1.2 z.1.2) ComputableIn.snd
        (ComputableIn.comp (α := (StepIn × ℕ) × ℕ) (β := StepIn × ℕ) (σ := RequirementData)
          (f := fun y ↦ prefixRequirement K y.1.2 y.2) (g := fun z ↦ z.1) hreq ComputableIn.fst))
  have hrange : ComputableIn O fun w : ((StepIn × ℕ) × ℕ) × AmalgamationDiagramData ↦
      w.2.rightToApex.rangeTuple :=
    ComputableIn.comp (α := ((StepIn × ℕ) × ℕ) × AmalgamationDiagramData)
      (β := PotentialEmbeddingData) (σ := List ℕ) (f := PotentialEmbeddingData.rangeTuple)
      (g := fun w ↦ w.2.rightToApex)
      (PotentialEmbeddingData.primrec_rangeTuple.to_comp.computableIn (O := O))
      (ComputableIn.comp (α := ((StepIn × ℕ) × ℕ) × AmalgamationDiagramData)
        (β := AmalgamationDiagramData) (σ := PotentialEmbeddingData)
        (f := AmalgamationDiagramData.rightToApex) (g := fun w ↦ w.2)
        AmalgamationDiagramData.rightToApex_computable ComputableIn.snd)
  have hs : ComputableIn O fun w : ((StepIn × ℕ) × ℕ) × AmalgamationDiagramData ↦ w.1.2 + 1 :=
    ComputableIn.comp (α := ((StepIn × ℕ) × ℕ) × AmalgamationDiagramData) (β := ℕ) (σ := ℕ)
      (f := Nat.succ) (g := fun w ↦ w.1.2) (Primrec.succ.to_comp.computableIn (O := O))
      (ComputableIn.snd.comp ComputableIn.fst)
  have hout : ComputableIn O fun w : ((StepIn × ℕ) × ℕ) × AmalgamationDiagramData ↦
      (w.1.1.2, w.1.2 + 1, w.2.rightToApex.rangeTuple) :=
    ComputableIn.pair (α := ((StepIn × ℕ) × ℕ) × AmalgamationDiagramData) (β := ℕ)
      (γ := ℕ × List ℕ) (f := fun w ↦ w.1.1.2)
      (g := fun w ↦ (w.1.2 + 1, w.2.rightToApex.rangeTuple))
      (ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst))
      (ComputableIn.pair (α := ((StepIn × ℕ) × ℕ) × AmalgamationDiagramData) (β := ℕ)
        (γ := List ℕ) (f := fun w ↦ w.1.2 + 1) (g := fun w ↦ w.2.rightToApex.rangeTuple) hs
        hrange)
  have h₃ : RecursiveIn O fun z : (StepIn × ℕ) × ℕ ↦
      (payloadPart K W i z.2 (prefixRequirement K z.1.1.2 z.1.2)).map fun D ↦
        (z.1.2, z.2 + 1, D.rightToApex.rangeTuple) :=
    RecursiveIn.map (α := (StepIn × ℕ) × ℕ) (β := AmalgamationDiagramData)
      (σ := ℕ × ℕ × List ℕ) (f := fun z ↦ payloadPart K W i z.2 (prefixRequirement K z.1.1.2 z.1.2))
      (g := fun z D ↦ (z.1.2, z.2 + 1, D.rightToApex.rangeTuple)) hpay hout.to₂
  have h₂ := RecursiveIn.bind hsearch h₃.to₂
  exact (RecursiveIn.bind hchp₁ h₂.to₂).of_eq fun _ ↦ rfl

include hchp hsel in
theorem prefixPart_recursiveIn :
    RecursiveIn O fun p : ℕ × ℕ ↦ prefixPart K W i chpSel sel p.1 p.2 := by
  have hh : RecursiveIn₂ O fun (p : ℕ × ℕ) (q : ℕ × (ℕ × ℕ × List ℕ)) ↦
      prefixStep K W i chpSel sel p.1 q.1 q.2 :=
    RecursiveIn.comp (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ × List ℕ))) (β := StepIn)
      (σ := ℕ × ℕ × List ℕ) (f := fun x ↦ prefixStep K W i chpSel sel x.1.1 x.1.2 x.2)
      (g := fun y ↦ ((y.1.1, y.2.1), y.2.2)) (prefixStep_recursiveIn hchp hsel)
      (ComputableIn.pair (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ × List ℕ))) (β := ℕ × ℕ)
        (γ := ℕ × ℕ × List ℕ) (f := fun y ↦ (y.1.1, y.2.1)) (g := fun y ↦ y.2.2)
        (ComputableIn.pair (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ × List ℕ))) (β := ℕ) (γ := ℕ)
          (f := fun y ↦ y.1.1) (g := fun y ↦ y.2.1) (ComputableIn.fst.comp ComputableIn.fst)
          (ComputableIn.fst.comp ComputableIn.snd))
        (ComputableIn.snd.comp ComputableIn.snd))
  have h := RecursiveIn.nat_rec (O := O) (α := ℕ × ℕ) (σ := ℕ × ℕ × List ℕ) (f := fun p ↦ p.2)
    (g := fun _ ↦ Part.some (i, 0, K.gens i))
    (h := fun p q ↦ prefixStep K W i chpSel sel p.1 q.1 q.2) ComputableIn.snd
    (RecursiveIn.comp RecursiveIn.some (ComputableIn.const (i, 0, K.gens i))) hh
  refine h.of_eq fun p ↦ ?_
  obtain ⟨j, t⟩ := p
  induction t with
  | zero => rfl
  | succ t ih =>
    change _ = (prefixPart K W i chpSel sel j t).bind _
    rw [← ih]

end PrefixEffectivity

/-! ### The prefix iteration, semantically -/

section PrefixSemantics

variable {K : PartialAgeIn O L} {W : PartialCAPWitness O K} {i : ℕ}

/-- **Conditional right-leg actualness at a recomputed payload**, with no limit in sight: when the
requirement's coded maps are actual, the payload's right leg is. -/
theorem rightToApex_actual_of_mem_payloadPart {q : RequirementData} {s : ℕ}
    (hfire : (schedule K W i).FiresAt (encode q) s) {D : AmalgamationDiagramData}
    (hD : D ∈ payloadPart K W i s q) (hf : K.PartialIsEmbedding (q.chainMap (memberIdx K W i)))
    (hg : K.PartialIsEmbedding q.targetMap) : K.PartialIsEmbedding D.rightToApex := by
  have hp := firesAt_iff_pick.1 hfire
  obtain ⟨q', hq', hr, -⟩ := exists_decode_of_pick hp
  rw [RequirementData.decode_encode] at hq'
  obtain rfl := Option.some.inj hq'
  have hf' : K.PartialIsEmbedding (q.chainMap (run K W i s).dHist) := by
    rw [chainMap_run_eq hr]; exact hf
  obtain ⟨δ, hδ, F, hF, D', hD', -, hright, -⟩ :=
    exists_square_of_fire (W := W) (run_runInvariant s) hp (RequirementData.decode_encode q) hf' hg
  obtain ⟨δ₀, hδ₀, F₀, hF₀, hsel⟩ := mem_payloadPart_iff.1 hD
  obtain rfl := Part.mem_unique hδ₀ hδ
  obtain rfl := Part.mem_unique hF₀ hF
  rw [Part.mem_unique hsel hD']
  exact hright

variable (K W i) in
/-- **The prefix invariant** at prefix `t`: the state's member represents the `t`-th prefix tuple in
the apex, and its generators' images at the state's stage are an actual embedding. -/
def PrefixInv (sel : ℕ → ℕ → PartialJointEmbeddingData) (j t : ℕ) (st : ℕ × ℕ × List ℕ) : Prop :=
  K.PartialIsEmbedding
      (PotentialEmbeddingData.ofTriple (st.1, (sel i j).apexIdx, prefixList K i sel j t)) ∧
    K.PartialIsEmbedding (PotentialEmbeddingData.ofTriple (st.1, memberIdx K W i st.2.1, st.2.2))

variable {chpSel : ℕ → List ℕ →. ℕ} {sel : ℕ → ℕ → PartialJointEmbeddingData}
  (hchpSpec : K.MappedCHPSpec chpSel) (hjoint : K.JointSpec sel)

theorem prefixList_length {j t : ℕ} (ht : t ≤ (K.gens (sel i j).apexIdx).length) :
    (prefixList K i sel j t).length = (sel i j).leftImage.length + t := by
  rw [prefixList, List.length_append, List.length_take, Nat.min_eq_left ht]

theorem prefixList_prefix (j t : ℕ) : prefixList K i sel j t <+: prefixList K i sel j (t + 1) :=
  ⟨(K.gens (sel i j).apexIdx)[t]?.toList, by
    rw [prefixList, prefixList, List.take_add_one, List.append_assoc]⟩

include hjoint in
theorem mem_domainAt_of_mem_prefixList (j t : ℕ) :
    ∀ x ∈ prefixList K i sel j t, x ∈ K.domainAt (sel i j).apexIdx := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact (hjoint i j).1.partialWellFormed.carrierValid x hx
  · exact K.mem_domainAt_of_mem_gens (List.mem_of_mem_take hx)

/-- **The step's requirement is admissible, with actual coded maps**, for any representative `c'` of
the next prefix. -/
theorem prefixRequirement_spec {j t : ℕ} {st : ℕ × ℕ × List ℕ}
    (hinv : PrefixInv K W i sel j t st) (ht : t < (K.gens (sel i j).apexIdx).length) {c' : ℕ}
    (hA : K.PartialIsEmbedding
      (PotentialEmbeddingData.ofTriple (c', (sel i j).apexIdx, prefixList K i sel j (t + 1)))) :
    K.PartialIsEmbedding ((prefixRequirement K st c').chainMap (memberIdx K W i)) ∧
      K.PartialIsEmbedding (prefixRequirement K st c').targetMap ∧
        K.Admissible (memberIdx K W i) (prefixRequirement K st c') := by
  have hf : K.PartialIsEmbedding ((prefixRequirement K st c').chainMap (memberIdx K W i)) := hinv.2
  have hg : K.PartialIsEmbedding (prefixRequirement K st c').targetMap :=
    partialIsEmbedding_take_of_prefix hinv.1 hA (prefixList_prefix j t)
  have hw₁ : (K.gens st.1).length = (prefixList K i sel j t).length := hinv.1.length
  have hw₂ : (K.gens c').length = (prefixList K i sel j (t + 1)).length := hA.length
  rw [prefixList_length ht.le] at hw₁
  rw [prefixList_length ht] at hw₂
  refine ⟨hf, hg, ⟨?_, ?_, ?_⟩, hf.partialWellFormed.carrierValid,
    hg.partialWellFormed.carrierValid⟩
  · exact hinv.2.length.symm
  · change ((K.gens c').take (K.gens st.1).length).length = (K.gens st.1).length
    rw [List.length_take]; omega
  · change (K.gens c').length = (K.gens st.1).length + 1
    omega

include hchpSpec hjoint in
/-- **One step halts and preserves the invariant.** -/
theorem prefixStep_spec {j t : ℕ} {st : ℕ × ℕ × List ℕ} (hinv : PrefixInv K W i sel j t st)
    (ht : t < (K.gens (sel i j).apexIdx).length) :
    (prefixStep K W i chpSel sel j t st).Dom ∧
      ∀ st' ∈ prefixStep K W i chpSel sel j t st, PrefixInv K W i sel j (t + 1) st' := by
  obtain ⟨c'', hc'', hA''⟩ := hchpSpec _ _ (mem_domainAt_of_mem_prefixList hjoint j (t + 1))
  refine ⟨?_, fun st' hst' ↦ ?_⟩
  · obtain ⟨-, -, hadm⟩ := prefixRequirement_spec hinv ht hA''
    obtain ⟨s₀, hfire₀⟩ := exists_firesAt_of_admissible (K := K) (W := W) (i := i) hadm
    obtain ⟨s, hs⟩ := Part.dom_iff_mem.1 (firingSearch_dom hfire₀)
    obtain ⟨D, hD⟩ := Part.dom_iff_mem.1 (payloadPart_spec (firesAt_of_mem_firingSearch hs)).1
    exact Part.dom_iff_mem.2 ⟨_, Part.mem_bind_iff.2 ⟨c'', hc'', Part.mem_bind_iff.2
      ⟨s, hs, (Part.mem_map_iff _).2 ⟨D, hD, rfl⟩⟩⟩⟩
  obtain ⟨c', hc', hrest⟩ := Part.mem_bind_iff.1 hst'
  obtain rfl := Part.mem_unique hc' hc''
  obtain ⟨s, hs, hmap⟩ := Part.mem_bind_iff.1 hrest
  obtain ⟨D, hD, rfl⟩ := (Part.mem_map_iff _).1 hmap
  obtain ⟨hf, hg, -⟩ := prefixRequirement_spec hinv ht hA''
  have hfire := firesAt_of_mem_firingSearch hs
  obtain ⟨-, hdom, hcod, -⟩ := payloadPart_unconditional hfire hD
  have hright := rightToApex_actual_of_mem_payloadPart hfire hD hf hg
  have heta : PotentialEmbeddingData.ofTriple
      (D.rightToApex.domIdx, D.rightToApex.codIdx, D.rightToApex.rangeTuple) = D.rightToApex := rfl
  rw [hdom, hcod] at heta
  exact ⟨hA'', heta ▸ hright⟩

include hchpSpec hjoint in
/-- **The iteration halts and keeps the invariant up to the last prefix.** -/
theorem prefixPart_spec (j : ℕ) :
    ∀ t ≤ (K.gens (sel i j).apexIdx).length, (prefixPart K W i chpSel sel j t).Dom ∧
      ∀ st ∈ prefixPart K W i chpSel sel j t, PrefixInv K W i sel j t st := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨trivial, fun st hst ↦ ?_⟩
    obtain rfl := Part.mem_some_iff.1 hst
    refine ⟨?_, ?_⟩
    · change K.PartialIsEmbedding (PotentialEmbeddingData.ofTriple
        (i, (sel i j).apexIdx, (sel i j).leftImage ++ (K.gens (sel i j).apexIdx).take 0))
      rw [List.take_zero, List.append_nil]
      exact (hjoint i j).1
    · change K.PartialIsEmbedding (PotentialEmbeddingData.ofTriple (i, memberIdx K W i 0, K.gens i))
      rw [memberIdx_zero]
      exact K.idData_partialIsEmbedding i
  | succ t ih =>
    intro ht
    obtain ⟨hdom, hinv⟩ := ih (Nat.le_of_succ_le ht)
    obtain ⟨st, hst⟩ := Part.dom_iff_mem.1 hdom
    refine ⟨?_, fun st' hst' ↦ ?_⟩
    · obtain ⟨st', h⟩ := Part.dom_iff_mem.1 (prefixStep_spec hchpSpec hjoint (hinv st hst) ht).1
      exact Part.dom_iff_mem.2 ⟨st', Part.mem_bind_iff.2 ⟨st, hst, h⟩⟩
    · obtain ⟨st₀, hst₀, h⟩ := Part.mem_bind_iff.1 hst'
      exact (prefixStep_spec hchpSpec hjoint (hinv st₀ hst₀) ht).2 st' h

include hjoint in
/-- **At the last prefix, the apex embeds** — its generators going to `H_T.drop n`. The realizer is
the state's embedding composed with the inverse of the representation onto the apex; nothing
inverse is computed, because the apex's generators sit at positions `n + k` of the last prefix. -/
theorem finalData_partialIsEmbedding {j : ℕ} {st : ℕ × ℕ × List ℕ}
    (hinv : PrefixInv K W i sel j (K.gens (sel i j).apexIdx).length st) :
    K.PartialIsEmbedding (PotentialEmbeddingData.ofTriple
      ((sel i j).apexIdx, memberIdx K W i st.2.1, st.2.2.drop (K.gens i).length)) := by
  obtain ⟨e, he⟩ : ∃ e : (K.memberAt st.1).domain ↪[L] (K.memberAt (sel i j).apexIdx).domain,
      K.PartialRealizes (PotentialEmbeddingData.ofTriple
        (st.1, (sel i j).apexIdx, prefixList K i sel j (K.gens (sel i j).apexIdx).length)) e :=
    hinv.1
  obtain ⟨h, hh⟩ : ∃ h : (K.memberAt st.1).domain ↪[L] (K.memberAt (memberIdx K W i st.2.1)).domain,
      K.PartialRealizes (PotentialEmbeddingData.ofTriple
        (st.1, memberIdx K W i st.2.1, st.2.2)) h := hinv.2
  have hn : (K.gens i).length = (sel i j).leftImage.length := (hjoint i j).1.length
  have hP : prefixList K i sel j (K.gens (sel i j).apexIdx).length =
      (sel i j).leftImage ++ K.gens (sel i j).apexIdx := by
    rw [prefixList, List.take_length]
  have hwe : (K.gens st.1).length = (K.gens i).length + (K.gens (sel i j).apexIdx).length := by
    have := he.length
    change (K.gens st.1).length = (prefixList K i sel j _).length at this
    rw [this, hP, List.length_append, hn]
  have hwh : (K.gens st.1).length = st.2.2.length := hh.length
  -- the apex's `k`-th generator is `e` of the state's `(n + k)`-th
  have hbd : ∀ k, k < (K.gens (sel i j).apexIdx).length →
      (K.gens i).length + k < (K.gens st.1).length := fun k hk ↦ by omega
  have hx : ∀ (k : ℕ) (hk : k < (K.gens (sel i j).apexIdx).length),
      (K.gens st.1)[(K.gens i).length + k]? = Option.some
        ((⟨(K.gens st.1)[(K.gens i).length + k],
          K.mem_domainAt_of_mem_gens (List.getElem_mem (hbd k hk))⟩ :
            (K.memberAt st.1).domain) : ℕ) :=
    fun k hk ↦ List.getElem?_eq_getElem (hbd k hk)
  -- the apex's `k`-th generator is `e` of the state's `(n + k)`-th
  have hgen : ∀ (k : ℕ) (hk : k < (K.gens (sel i j).apexIdx).length),
      e ⟨(K.gens st.1)[(K.gens i).length + k],
        K.mem_domainAt_of_mem_gens (List.getElem_mem (hbd k hk))⟩ =
      ⟨(K.gens (sel i j).apexIdx)[k], K.mem_domainAt_of_mem_gens (List.getElem_mem hk)⟩ := by
    intro k hk
    refine Subtype.ext ?_
    have h₁ := getElem?_of_realizes (partialRealizesBetween_self.2 he) (hx k hk)
    change (prefixList K i sel j _)[(K.gens i).length + k]? = _ at h₁
    rw [hP, List.getElem?_append_right (by omega), show (K.gens i).length + k -
      (sel i j).leftImage.length = k by omega, List.getElem?_eq_getElem hk] at h₁
    exact (Option.some.inj h₁).symm
  have hsurj : Function.Surjective e :=
    memberEmbedding_surjective_of_gens e fun k ↦ ⟨_, hgen k k.2⟩
  refine ⟨h.comp (e.equivOfSurjective hsurj).symm.toEmbedding,
    partialRealizesBetween_self.1 (realizes_of_getElem? ?_ fun k z hz ↦ ?_)⟩
  · rw [List.length_drop, ← hwh]; omega
  · have hk : k < (K.gens (sel i j).apexIdx).length := (List.getElem?_eq_some_iff.1 hz).1
    have hz' : z = ⟨(K.gens (sel i j).apexIdx)[k],
        K.mem_domainAt_of_mem_gens (List.getElem_mem hk)⟩ :=
      Subtype.ext (Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hz)).symm
    have hinvz : (e.equivOfSurjective hsurj).symm z =
        ⟨(K.gens st.1)[(K.gens i).length + k],
          K.mem_domainAt_of_mem_gens (List.getElem_mem (hbd k hk))⟩ := by
      rw [hz', ← hgen k hk]
      exact Embedding.equivOfSurjective_symm_apply e hsurj _
    change (st.2.2.drop (K.gens i).length)[k]? =
      Option.some ((h ((e.equivOfSurjective hsurj).symm z) :
        (K.memberAt (memberIdx K W i st.2.1)).domain) : ℕ)
    rw [hinvz, List.getElem?_drop]
    exact getElem?_of_realizes (partialRealizesBetween_self.2 hh) (hx k hk)

include hchpSpec hjoint in
/-- **The backward answer halts, and names an actual embedding of `A_j`** into the member at its
stage: CJEP's right leg composed with the apex's embedding at the last prefix. -/
theorem backwardAnswerPart_spec (j : ℕ) :
    (backwardAnswerPart K W i chpSel sel j).Dom ∧ ∀ ans ∈ backwardAnswerPart K W i chpSel sel j,
      K.PartialIsEmbedding (PotentialEmbeddingData.ofTriple (j, memberIdx K W i ans.1, ans.2)) := by
  obtain ⟨hdom, hinv⟩ := prefixPart_spec hchpSpec hjoint j _ le_rfl
  obtain ⟨st, hst⟩ := Part.dom_iff_mem.1 hdom
  obtain ⟨H, hH, -, -, hHemb⟩ := K.compPart_partialIsEmbedding
    (G := PotentialEmbeddingData.ofTriple
      ((sel i j).apexIdx, memberIdx K W i st.2.1, st.2.2.drop (K.gens i).length))
    (F := PotentialEmbeddingData.ofTriple (j, (sel i j).apexIdx, (sel i j).rightImage)) rfl
    (hjoint i j).2 (finalData_partialIsEmbedding hjoint (hinv st hst))
  obtain ⟨v, hv, rfl⟩ := K.mem_compPart_iff.1 hH
  have hvmem := mem_listMapPart_iff.2 hv
  refine ⟨Part.dom_iff_mem.2 ⟨(st.2.1, v), Part.mem_bind_iff.2
    ⟨st, hst, (Part.mem_map_iff _).2 ⟨v, hvmem, rfl⟩⟩⟩, fun ans hans ↦ ?_⟩
  obtain ⟨st', hst', hmap⟩ := Part.mem_bind_iff.1 hans
  obtain rfl := Part.mem_unique hst' hst
  obtain ⟨v', hv', rfl⟩ := (Part.mem_map_iff _).1 hmap
  obtain rfl := Part.mem_unique hv' hvmem
  exact hHemb

end PrefixSemantics

section BackwardEffectivity

variable {K : PartialAgeIn O L} {W : PartialCAPWitness O K} {i : ℕ}
  {chpSel : ℕ → List ℕ →. ℕ} {sel : ℕ → ℕ → PartialJointEmbeddingData}
  (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2)
  (hsel : ComputableIn O fun p : ℕ × ℕ ↦ sel p.1 p.2)

include hchp hsel in
theorem backwardAnswerPart_recursiveIn : RecursiveIn O (backwardAnswerPart K W i chpSel sel) := by
  have hapex : ComputableIn O fun j ↦ (sel i j).apexIdx := apex_computableIn hsel
  have hT : ComputableIn O fun j ↦ (K.gens (sel i j).apexIdx).length :=
    (Primrec.list_length.to_comp.computableIn (O := O)).comp (K.gens_computableIn.comp hapex)
  have hpre : RecursiveIn O fun j ↦
      prefixPart K W i chpSel sel j (K.gens (sel i j).apexIdx).length :=
    RecursiveIn.comp (α := ℕ) (β := ℕ × ℕ) (σ := ℕ × ℕ × List ℕ)
      (f := fun p ↦ prefixPart K W i chpSel sel p.1 p.2)
      (g := fun j ↦ (j, (K.gens (sel i j).apexIdx).length)) (prefixPart_recursiveIn hchp hsel)
      (ComputableIn.pair (α := ℕ) (β := ℕ) (γ := ℕ) (f := fun j ↦ j)
        (g := fun j ↦ (K.gens (sel i j).apexIdx).length) ComputableIn.id hT)
  have hG : ComputableIn O fun y : ℕ × (ℕ × ℕ × List ℕ) ↦ PotentialEmbeddingData.ofTriple
      ((sel i y.1).apexIdx, memberIdx K W i y.2.2.1, y.2.2.2.drop (K.gens i).length) :=
    (PotentialEmbeddingData.primrec_ofTriple.to_comp.computableIn (O := O)).comp
      ((hapex.comp ComputableIn.fst).pair
        (((memberIdx_computableIn K W i (Set.Subset.refl O)).comp
          (ComputableIn.fst.comp (ComputableIn.snd.comp ComputableIn.snd))).pair
          (((Primrec₂.swap Primrec.list_drop).to_comp.computableIn₂ (O := O)).comp
            (ComputableIn.snd.comp (ComputableIn.snd.comp ComputableIn.snd))
            (ComputableIn.const (K.gens i).length))))
  have hR : ComputableIn O fun y : ℕ × (ℕ × ℕ × List ℕ) ↦ (sel i y.1).rightImage :=
    (PartialJointEmbeddingData.primrec_rightImage.to_comp.computableIn (O := O)).comp
      (hsel.comp ((ComputableIn.const i).pair ComputableIn.fst))
  have hlist := RecursiveIn₂.comp (α := ℕ × (ℕ × ℕ × List ℕ)) (β := PotentialEmbeddingData)
    (γ := List ℕ) (σ := List ℕ) (f := fun G l ↦ listMapPart (K.applyPotentialPart G) l)
    (RecursiveIn.listMapPart₂ (g := K.applyPotentialPart) K.applyPotentialPart_recursiveIn) hG hR
  have hout : ComputableIn O fun w : (ℕ × (ℕ × ℕ × List ℕ)) × List ℕ ↦ (w.1.2.2.1, w.2) :=
    (ComputableIn.fst.comp (ComputableIn.snd.comp (ComputableIn.snd.comp ComputableIn.fst))).pair
      ComputableIn.snd
  have hmap := RecursiveIn.map hlist hout.to₂
  exact (RecursiveIn.bind hpre hmap.to₂).of_eq fun _ ↦ rfl

end BackwardEffectivity

/-! ### The backward cover -/

section Backward

variable {K : PartialAgeIn O L} {W : PartialCAPWitness O K} {i : ℕ}
  {h0 : (K.domainAt i).Nonempty} (Z : (runChain K W i (Set.Subset.refl O) h0).LimitIn)
  (cert : Z.presentation.InfinitudeCertificate)
  {chpSel : ℕ → List ℕ →. ℕ} {sel : ℕ → ℕ → PartialJointEmbeddingData}
  (hchpSpec : K.MappedCHPSpec chpSel) (hjoint : K.JointSpec sel)

variable (W i) in
include hchpSpec hjoint in
/-- The backward answer, totalized **once**. -/
noncomputable def runBackwardAnswer (j : ℕ) : ℕ × List ℕ :=
  (backwardAnswerPart K W i chpSel sel j).get (backwardAnswerPart_spec hchpSpec hjoint j).1

variable (W i) in
/-- The stage the member is embedded at. -/
noncomputable def runBackwardStage (j : ℕ) : ℕ := (runBackwardAnswer W i hchpSpec hjoint j).1

variable (W i) in
/-- The embedding of member `j` into the member at that stage, as potential embedding data. -/
noncomputable def runBackwardData (j : ℕ) : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple (j, memberIdx K W i (runBackwardStage W i hchpSpec hjoint j),
    (runBackwardAnswer W i hchpSpec hjoint j).2)

variable (W i) in
theorem runBackwardData_partialIsEmbedding (j : ℕ) :
    K.PartialIsEmbedding (runBackwardData W i hchpSpec hjoint j) :=
  (backwardAnswerPart_spec hchpSpec hjoint j).2 _ (Part.get_mem _)

variable (W i) in
/-- Its realizer. -/
noncomputable def runBackwardRealizer (j : ℕ) :
    (K.memberAt j).domain ↪[L]
      (K.memberAt (memberIdx K W i (runBackwardStage W i hchpSpec hjoint j))).domain :=
  (runBackwardData_partialIsEmbedding W i hchpSpec hjoint j).choose

variable (W i) in
theorem runBackwardRealizer_spec (j : ℕ) :
    K.PartialRealizes (runBackwardData W i hchpSpec hjoint j)
      (runBackwardRealizer W i hchpSpec hjoint j) :=
  (runBackwardData_partialIsEmbedding W i hchpSpec hjoint j).choose_spec

/-- **The semantic embedding** of member `j` into ω. -/
noncomputable def runBackwardEmbedding (j : ℕ) :
    @Language.Embedding L (K.memberAt j).domain ℕ _ (Z.omegaStructure cert).inst :=
  letI : L.Structure ℕ := Z.presentation.rankStr
  (omegaMember Z (runBackwardStage W i hchpSpec hjoint j)).comp
    (runBackwardRealizer W i hchpSpec hjoint j)

/-- **The program, guarded.** -/
noncomputable def runBackwardMap (j : ℕ) : ℕ →. ℕ :=
  fun x ↦ (K.idFun (j, x)).bind fun x' ↦
    (K.applyPotentialPart (runBackwardData W i hchpSpec hjoint j) x').bind fun y ↦
      Z.rankStageMap (runBackwardStage W i hchpSpec hjoint j) y

theorem runBackwardEmbedding_mem (j : ℕ) (x : (K.memberAt j).domain) :
    runBackwardEmbedding Z cert hchpSpec hjoint j x ∈
      runBackwardMap Z hchpSpec hjoint j (x : ℕ) := by
  refine Part.mem_bind_iff.2 ⟨(x : ℕ), K.mem_idFun.2 ⟨rfl, x.2⟩, ?_⟩
  refine Part.mem_bind_iff.2 ⟨_, applyPotentialPart_mem_realizer
    (runBackwardRealizer_spec W i hchpSpec hjoint j) x.2, ?_⟩
  exact omegaMember_mem_rankStageMap Z _ _

include cert in
theorem runBackwardMap_dom (j x : ℕ) :
    (runBackwardMap Z hchpSpec hjoint j x).Dom ↔ x ∈ K.domainAt j := by
  refine ⟨fun h ↦ ?_, fun hx ↦ Part.dom_iff_mem.2
    ⟨_, runBackwardEmbedding_mem Z cert hchpSpec hjoint j ⟨x, hx⟩⟩⟩
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 h
  obtain ⟨x', hx', -⟩ := Part.mem_bind_iff.1 hy
  exact (K.mem_idFun.1 hx').2

variable (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2)
  (hsel : ComputableIn O fun p : ℕ × ℕ ↦ sel p.1 p.2)

include hchp hsel in
theorem runBackwardAnswer_computableIn : ComputableIn O (runBackwardAnswer W i hchpSpec hjoint) :=
  RecursiveIn.computableIn_get (backwardAnswerPart_recursiveIn hchp hsel)
    fun j ↦ (backwardAnswerPart_spec hchpSpec hjoint j).1

include hchp hsel in
theorem runBackwardStage_computableIn : ComputableIn O (runBackwardStage W i hchpSpec hjoint) :=
  (Primrec.fst.to_comp.computableIn).comp
    (runBackwardAnswer_computableIn (W := W) (i := i) hchpSpec hjoint hchp hsel)

include hchp hsel in
theorem runBackwardData_computableIn : ComputableIn O (runBackwardData W i hchpSpec hjoint) :=
  (PotentialEmbeddingData.primrec_ofTriple.to_comp.computableIn).comp
    (ComputableIn.id.pair (((memberIdx_computableIn K W i (Set.Subset.refl O)).comp
      (runBackwardStage_computableIn (W := W) (i := i) hchpSpec hjoint hchp hsel)).pair
      ((Primrec.snd.to_comp.computableIn).comp
        (runBackwardAnswer_computableIn (W := W) (i := i) hchpSpec hjoint hchp hsel))))

include hchp hsel in
theorem runBackwardMap_uniform :
    RecursiveIn O fun p : ℕ × ℕ ↦ runBackwardMap Z hchpSpec hjoint p.1 p.2 := by
  have hdata := runBackwardData_computableIn (W := W) (i := i) hchpSpec hjoint hchp hsel
  have hstage := runBackwardStage_computableIn (W := W) (i := i) hchpSpec hjoint hchp hsel
  have h₁ : RecursiveIn O fun p : ℕ × ℕ ↦ K.idFun (p.1, p.2) := K.idFun_recursiveIn
  have h₂ : RecursiveIn O fun q : (ℕ × ℕ) × ℕ ↦
      K.applyPotentialPart (runBackwardData W i hchpSpec hjoint q.1.1) q.2 :=
    RecursiveIn.comp (O := O) (α := (ℕ × ℕ) × ℕ) (β := PotentialEmbeddingData × ℕ) (σ := ℕ)
      (f := fun r : PotentialEmbeddingData × ℕ ↦ K.applyPotentialPart r.1 r.2)
      (g := fun q : (ℕ × ℕ) × ℕ ↦ (runBackwardData W i hchpSpec hjoint q.1.1, q.2))
      K.applyPotentialPart_recursiveIn
      ((hdata.comp (ComputableIn.fst.comp ComputableIn.fst)).pair ComputableIn.snd)
  have h₃ : RecursiveIn O fun r : ((ℕ × ℕ) × ℕ) × ℕ ↦
      Z.rankStageMap (runBackwardStage W i hchpSpec hjoint r.1.1.1) r.2 :=
    RecursiveIn.comp (O := O) (α := ((ℕ × ℕ) × ℕ) × ℕ) (β := ℕ × ℕ) (σ := ℕ)
      (f := fun p : ℕ × ℕ ↦ Z.rankStageMap p.1 p.2)
      (g := fun r : ((ℕ × ℕ) × ℕ) × ℕ ↦ (runBackwardStage W i hchpSpec hjoint r.1.1.1, r.2))
      Z.rankStageMap_recursiveIn
      ((hstage.comp (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst))).pair
        ComputableIn.snd)
  exact RecursiveIn.bind h₁ (RecursiveIn.bind h₂ h₃.to₂).to₂

/-- **Every member of `K` embeds into the run's ω structure**, uniformly, by computed extensions. -/
noncomputable def runToLimitEmbedding : UniformEmbeddingIntoIn O K (Z.omegaStructure cert) where
  embedding := runBackwardEmbedding Z cert hchpSpec hjoint
  map := runBackwardMap Z hchpSpec hjoint
  map_uniform := runBackwardMap_uniform Z hchpSpec hjoint hchp hsel
  map_dom := runBackwardMap_dom Z cert hchpSpec hjoint
  map_apply_mem := runBackwardEmbedding_mem Z cert hchpSpec hjoint

/-- **The backward cover `K → F.canonicalAge`**, from the generated-image constructor. -/
noncomputable def runBackwardCover :
    RepresentationCoverIn O K (Z.omegaStructure cert).canonicalAge :=
  (runToLimitEmbedding Z cert hchpSpec hjoint hchp hsel).toCanonicalAgeCover (Set.Subset.refl O)

theorem runBackwardCover_generatorCompatible :
    (runBackwardCover Z cert hchpSpec hjoint hchp hsel).GeneratorCompatible :=
  (runToLimitEmbedding Z cert hchpSpec hjoint hchp hsel).toCanonicalAgeCover_generatorCompatible
    (Set.Subset.refl O)

end Backward

/-! ### Effective canonicality -/

section Canonical

variable {K : PartialAgeIn O L} {W : PartialCAPWitness O K} {i : ℕ}
  {h0 : (K.domainAt i).Nonempty} (Z : (runChain K W i (Set.Subset.refl O) h0).LimitIn)
  (cert : Z.presentation.InfinitudeCertificate)
  {chpSel : ℕ → List ℕ →. ℕ} {sel : ℕ → ℕ → PartialJointEmbeddingData}
  (hchpSpec : K.MappedCHPSpec chpSel) (hjoint : K.JointSpec sel)
  (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2)
  (hsel : ComputableIn O fun p : ℕ × ℕ ↦ sel p.1 p.2) (hrep : Z.RepresentedByRawRep)

/-- **Theorem 3.9, effective canonicality**: the run's ω structure's canonical age is computably
isomorphic to `K`, by the two independently constructed covers. -/
noncomputable def runCanonicalIso :
    RepresentationIsoIn O (Z.omegaStructure cert).canonicalAge K where
  forward := runForwardCover Z chpSel cert hchpSpec hchp hrep
  backward := runBackwardCover Z cert hchpSpec hjoint hchp hsel

/-- **Generator-compatible in both directions.** -/
theorem runCanonicalIso_generatorCompatible :
    (runCanonicalIso Z cert hchpSpec hjoint hchp hsel hrep).forward.GeneratorCompatible ∧
      (runCanonicalIso Z cert hchpSpec hjoint hchp hsel hrep).backward.GeneratorCompatible :=
  ⟨runForwardCover_generatorCompatible Z chpSel cert hchpSpec hchp hrep,
    runBackwardCover_generatorCompatible Z cert hchpSpec hjoint hchp hsel⟩

end Canonical

section Corollaries

variable {K : PartialAgeIn O L} {W : PartialCAPWitness O K} {i : ℕ}
  {h0 : (K.domainAt i).Nonempty}

/-- **From the paper's selector properties**: CHP and CJEP at the family's oracle give a
generator-compatible representation isomorphism, for any limit of the run naming its codes by raw
representatives. -/
theorem exists_runCanonicalIso (Z : (runChain K W i (Set.Subset.refl O) h0).LimitIn)
    (hCHP : MappedPartialCHPIn O K) (hCJEP : K.PartialCJEPIn O) (hrep : Z.RepresentedByRawRep)
    (cert : Z.presentation.InfinitudeCertificate) :
    ∃ r : RepresentationIsoIn O (Z.omegaStructure cert).canonicalAge K,
      r.forward.GeneratorCompatible ∧ r.backward.GeneratorCompatible := by
  obtain ⟨chpSel, hchp, hchpSpec⟩ := hCHP.exists_chpSpec
  obtain ⟨sel, hsel, hjoint⟩ := hCJEP.exists_jointSpec
  exact ⟨_, runCanonicalIso_generatorCompatible Z cert hchpSpec hjoint hchp hsel hrep⟩

/-- **At the run's canonical limit**: `K` is a canonical representation of the age of the run's ω
structure (CHMM Definition 2.4), compatibly. -/
theorem toLimit_exists_runCanonicalIso (hCHP : MappedPartialCHPIn O K)
    (hCJEP : K.PartialCJEPIn O)
    (cert : CePresentationIn.InfinitudeCertificate ((runChain K W i (Set.Subset.refl O) h0).toLimit
      (runChain_uniformEvaluators K W i (Set.Subset.refl O) h0)).presentation) :
    ∃ r : RepresentationIsoIn O
        (((runChain K W i (Set.Subset.refl O) h0).toLimit
          (runChain_uniformEvaluators K W i (Set.Subset.refl O) h0)).omegaStructure
            cert).canonicalAge K,
      r.forward.GeneratorCompatible ∧ r.backward.GeneratorCompatible :=
  exists_runCanonicalIso _ hCHP hCJEP (CeStructureChainIn.toLimit_representedByRawRep _ _) cert

end Corollaries

end PartialAgeIn

end FirstOrder.Language
