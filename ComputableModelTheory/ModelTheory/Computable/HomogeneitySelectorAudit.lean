/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.HomogeneitySelector
import ComputableModelTheory.ModelTheory.Computable.ListAgeCAP
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the homogeneity selector of Theorem 3.9's construction

**The program.** `test_selectPart_recursiveIn` is the selector as a partial recursive program, with
no certificate and no representation hypothesis: the pullback, the CHP calls, the firing search,
the recomputed payload and the answer are all executable. `test_selectPart_dom` is halting, under
the certificate alone.

**No semantic choice.** `test_admissible` is admissibility of the constructed requirement with no
actualness hypothesis — the reason the search halts on malformed input. `test_payload_is_runs`
identifies the recomputed payload with the diagram the run extended by, as a theorem about the
program rather than a replacement for it. `test_fallback` pins the length-mismatch branch.

**`γ` and `y`.** `test_gamma_is_apex` is the canonical member of `γ` as the ω-image of the apex
member — `γ` comes from the apex's own recorded generators. `test_y_from_right_leg` is `y` as the ω-
image of the right range tuple's last coordinate, from well-formedness alone.

**The package.** `test_computablyHomogeneous` and `test_nonempty_of_selectors` are
`ComputablyHomogeneousIn` for the ω structure of the run's limit.

**On the list age.** `test_listAge_computablyHomogeneous` discharges every hypothesis on a run with
proper extensions (the pushout CAP witness of `ListAgeCAP`). `test_new_point_outside_left_leg` is
the contract's proper-extension pin: on every matched query whose new point is not among the images,
the selector's `y` lies outside the canonical member of the **left leg's** range tuple — so taking
`γ` from the left leg would fail `imageOfNewPoint_mem`. `test_pin_nonvacuous` exhibits such a query.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

section General

open PartialAgeIn

variable {K : PartialAgeIn O L} {W : PartialCAPWitness E K} {i : ℕ} {hOE : O ⊆ E}
  {h0 : (K.domainAt i).Nonempty} (Z : (runChain K W i hOE h0).LimitIn)
  (chpSel : ℕ → List ℕ →. ℕ)

/-- **The selector is a program**: partial recursive, with no certificate and no representation
hypothesis. -/
theorem test_selectPart_recursiveIn (hchp : RecursiveIn E fun p : ℕ × List ℕ ↦ chpSel p.1 p.2) :
    RecursiveIn E (selectPart Z chpSel) :=
  selectPart_recursiveIn Z chpSel hchp

/-- **Halting**, under the certificate. -/
theorem test_selectPart_dom (hchpSpec : K.MappedCHPSpec chpSel)
    (cert : Z.presentation.InfinitudeCertificate) (q : HomogeneityQueryData) :
    (selectPart Z chpSel q).Dom :=
  selectPart_dom Z chpSel hchpSpec cert q

/-- **Admissibility needs no actualness**: the constructed requirement of every matched query is
admissible. -/
theorem test_admissible (hchpSpec : K.MappedCHPSpec chpSel) {q : HomogeneityQueryData}
    (hlen : q.domainTuple.length = q.imageTuple.length) {p : ℕ × List ℕ}
    (hp : p ∈ Z.rankTupleAtStagePart q.fullTuple) {a k : ℕ}
    (ha : a ∈ chpSel (memberIdx K W i p.1) (p.2.take q.domainTuple.length))
    (hk : k ∈ chpSel (memberIdx K W i p.1) (p.2.drop q.domainTuple.length)) :
    K.Admissible (memberIdx K W i) (queryRequirement K q.domainTuple.length p a k) :=
  queryRequirement_admissible Z chpSel hchpSpec hlen hp ha hk

/-- **The recomputed payload is the run's diagram.** -/
theorem test_payload_is_runs {q : RequirementData} {s : ℕ}
    (hfire : (schedule K W i).FiresAt (encode q) s) :
    (payloadPart K W i s q).Dom ∧ ∀ D ∈ payloadPart K W i s q,
      run K W i (s + 1) = (run K W i s).capExtension (encode q) D :=
  payloadPart_spec hfire

/-- **The fallback on a length mismatch.** -/
theorem test_fallback (hchpSpec : K.MappedCHPSpec chpSel)
    (cert : Z.presentation.InfinitudeCertificate) {q : HomogeneityQueryData}
    (hlen : ¬ q.domainTuple.length = q.imageTuple.length) :
    homogeneitySelect Z chpSel hchpSpec cert q = ⟨q.domainTuple ++ [q.newPoint], q.newPoint⟩ :=
  homogeneitySelect_of_not_matched Z chpSel hchpSpec cert hlen

/-- **`γ` names the apex member**: its canonical member is the ω-image of the member at `s + 1`. -/
theorem test_gamma_is_apex (cert : Z.presentation.InfinitudeCertificate) {s : ℕ} {γ : List ℕ}
    (hγ : γ ∈ listMapPart (Z.rankStageMap (s + 1)) (K.gens (memberIdx K W i (s + 1)))) :
    (Z.omegaStructure cert).canonicalAge.domainAt (encode γ) =
      Set.range (omegaMember Z (s + 1)) :=
  canonicalAge_domainAt_γ Z cert hγ

/-- **`y` is the right leg's last coordinate in ω**, which lies in the apex member by
well-formedness alone. -/
theorem test_y_from_right_leg (hchpSpec : K.MappedCHPSpec chpSel) {q : HomogeneityQueryData}
    (hlen : q.domainTuple.length = q.imageTuple.length) {p : ℕ × List ℕ}
    (hp : p ∈ Z.rankTupleAtStagePart q.fullTuple) {a k : ℕ}
    (ha : a ∈ chpSel (memberIdx K W i p.1) (p.2.take q.domainTuple.length))
    (hk : k ∈ chpSel (memberIdx K W i p.1) (p.2.drop q.domainTuple.length)) {s : ℕ}
    (hs : s ∈ firingSearch K W i (encode (queryRequirement K q.domainTuple.length p a k)))
    {D : AmalgamationDiagramData}
    (hD : D ∈ payloadPart K W i s (queryRequirement K q.domainTuple.length p a k)) {y : ℕ}
    (hy : y ∈ Z.rankStageMap (s + 1) (D.rightToApex.rangeTuple.getLastD 0)) :
    ∃ hw : D.rightToApex.rangeTuple.getLastD 0 ∈ K.domainAt (memberIdx K W i (s + 1)),
      D.rightToApex.rangeTuple[q.domainTuple.length]? =
          Option.some (D.rightToApex.rangeTuple.getLastD 0) ∧
        y = omegaMember Z (s + 1) ⟨_, hw⟩ := by
  obtain ⟨-, hlast, hw⟩ := getLastD_mem_domainAt Z chpSel hchpSpec hlen hp ha hk hs hD
  exact ⟨hw, hlast, eq_omegaMember_of_mem_rankStageMap Z hw hy⟩

/-- **The package**: the ω structure of the run's limit is computably homogeneous. -/
noncomputable def test_computablyHomogeneous (hchpSpec : K.MappedCHPSpec chpSel)
    (cert : Z.presentation.InfinitudeCertificate) (hrep : Z.RepresentedByRawRep)
    (hchp : RecursiveIn E fun p : ℕ × List ℕ ↦ chpSel p.1 p.2) :
    ComputablyHomogeneousIn E (Z.omegaStructure cert) :=
  computablyHomogeneous Z chpSel hchpSpec cert hrep hchp

/-- From the paper's hereditary selector, at the run's canonical limit. -/
theorem test_nonempty_of_selectors (hCHP : MappedPartialCHPIn E K)
    (cert : ((runChain K W i hOE h0).toLimit
      (runChain_uniformEvaluators K W i hOE h0)).presentation.InfinitudeCertificate) :
    Nonempty (ComputablyHomogeneousIn E
      (((runChain K W i hOE h0).toLimit (runChain_uniformEvaluators K W i hOE h0)).omegaStructure
        cert)) :=
  toLimit_computablyHomogeneousIn hCHP cert

end General

/-! ### On the list age -/

section Fixture

variable (O : Set (ℕ →. ℕ))

/-- **Computable homogeneity on a run with proper extensions**, every hypothesis discharged. -/
noncomputable def test_listAge_computablyHomogeneous :
    ComputablyHomogeneousIn O ((listAge.runLimit O).omegaStructure (listAge.runLimit_cert O)) :=
  PartialAgeIn.computablyHomogeneous (listAge.runLimit O) listAge.chpSel listAge.mappedCHPSpec
    (listAge.runLimit_cert O) (CeStructureChainIn.toLimit_representedByRawRep _ _)
    listAge.chpSel_recursiveIn

/-- The list-age run's member index. -/
local notation "listIdx" =>
  PartialAgeIn.memberIdx (listAge O) (listAge.capWitness O) (encode [0])

/-- The list-age run's requirement of a query. -/
local notation "listReq" => PartialAgeIn.queryRequirement (listAge O)

/-- **The proper-extension pin.** On a matched query whose new point is not among the images, the
selector's `y` lies outside the canonical member of the left leg's range tuple carried into ω. So
`γ` taken from the left leg — which names the old stage's generators — would fail
`imageOfNewPoint_mem`; the selector takes it from the apex member instead. -/
theorem test_new_point_outside_left_leg {q : HomogeneityQueryData}
    (hlen : q.domainTuple.length = q.imageTuple.length) (hx : q.newPoint ∉ q.imageTuple)
    {p : ℕ × List ℕ} (hp : p ∈ (listAge.runLimit O).rankTupleAtStagePart q.fullTuple) {a k : ℕ}
    (ha : a ∈ listAge.chpSel (listIdx p.1) (p.2.take q.domainTuple.length))
    (hk : k ∈ listAge.chpSel (listIdx p.1) (p.2.drop q.domainTuple.length)) {s : ℕ}
    (hs : s ∈ PartialAgeIn.firingSearch (listAge O) (listAge.capWitness O) (encode [0])
      (encode (listReq q.domainTuple.length p a k)))
    {D : AmalgamationDiagramData}
    (hD : D ∈ PartialAgeIn.payloadPart (listAge O) (listAge.capWitness O) (encode [0]) s
      (listReq q.domainTuple.length p a k)) {y : ℕ}
    (hy : y ∈ (listAge.runLimit O).rankStageMap (s + 1) (D.rightToApex.rangeTuple.getLastD 0))
    {γL : List ℕ}
    (hγL : γL ∈ listMapPart ((listAge.runLimit O).rankStageMap (s + 1)) D.leftToApex.rangeTuple) :
    y ∉ ((listAge.runLimit O).omegaStructure (listAge.runLimit_cert O)).canonicalAge.domainAt
      (encode γL) := by
  intro hmem
  letI : Language.empty.Structure ℕ := (listAge.runLimit O).presentation.rankStr
  set n := q.domainTuple.length with hn
  have hfire := PartialAgeIn.firesAt_of_mem_firingSearch hs
  -- in the empty language a canonical member is its tuple's entries
  have hyγ : y ∈ γL := by
    rw [ComputableStructureIn.canonicalAge_domainAt_eq_closure, allTupleFor_encode,
      SetLike.mem_coe, Substructure.mem_closure_iff_of_isRelational] at hmem
    obtain ⟨j, rfl⟩ := hmem
    rw [Tuple.view_eq_get]
    exact List.get_mem _ _
  -- so `y` is the ω-image of a coordinate `z` of the left range tuple
  obtain ⟨j, hjlt, hj⟩ := List.getElem_of_mem hyγ
  obtain ⟨z, hz, hyz⟩ := (mem_listMapPart_iff.1 hγL).exists_getElem?_left
    (List.getElem?_eq_some_iff.2 ⟨hjlt, hj⟩)
  obtain ⟨δ, -, F, -, hsel⟩ := PartialAgeIn.mem_payloadPart_iff.1 hD
  obtain ⟨-, hleft, -⟩ := (listAge.capWitness O).unconditional _ D hsel
  have hcodL : D.leftToApex.codIdx = listIdx (s + 1) := by
    rw [← PartialAgeIn.runStep_eq_of_mem_payloadPart hfire hD, PartialAgeIn.runStep_codIdx]
  have hzdom : z ∈ (listAge O).domainAt (listIdx (s + 1)) :=
    hcodL ▸ hleft.partialWellFormed.carrierValid z (List.mem_of_getElem? hz)
  obtain ⟨-, hlast, hw⟩ := PartialAgeIn.getLastD_mem_domainAt (listAge.runLimit O) listAge.chpSel
    listAge.mappedCHPSpec hlen hp ha hk hs hD
  have hzl : z = D.rightToApex.rangeTuple.getLastD 0 := by
    have h₁ := PartialAgeIn.eq_omegaMember_of_mem_rankStageMap (listAge.runLimit O) hzdom hyz
    have h₂ := PartialAgeIn.eq_omegaMember_of_mem_rankStageMap (listAge.runLimit O) hw hy
    exact congrArg Subtype.val ((PartialAgeIn.omegaMember (listAge.runLimit O) (s + 1)).injective
      (h₁.symm.trans h₂))
  -- the diagram is the pushout, and `k` records the pulled `c⃗ ++ [x]`
  have hDeq := Part.mem_some_iff.1 hsel
  obtain rfl := Part.mem_some_iff.1 hk
  have hu := (PartialAgeIn.query_widths (listAge.runLimit O) listAge.chpSel listAge.mappedCHPSpec
    hlen hp (by exact ha) (Part.mem_some _)).1
  have hlistk : listOf (encode (p.2.drop n)) = p.2.drop n := listOf_encode _
  -- the last right coordinate is the glue of the pulled `x`
  have h2n : 2 * n < p.2.length := by omega
  have hlastv : D.rightToApex.rangeTuple.getLastD 0 = listAge.glue
      (PotentialSpanData.ofPair (F, (listReq n p a (encode (p.2.drop n))).targetMap))
      p.2[2 * n] := by
    have h := hlast
    rw [hDeq] at h ⊢
    change ((listOf (encode (p.2.drop n))).map _)[n]? = _ at h
    rw [hlistk, List.getElem?_map, List.getElem?_drop,
      show n + n = 2 * n by omega, List.getElem?_eq_getElem h2n] at h
    exact (Option.some.inj h).symm
  -- the pulled `x` is not among the pulled `c⃗`, since `x ∉ c⃗`
  have hnotin : ¬ (PotentialSpanData.ofPair
      (F, (listReq n p a (encode (p.2.drop n))).targetMap)).right.rangeTuple.idxOf p.2[2 * n] <
      (PotentialSpanData.ofPair
        (F, (listReq n p a (encode (p.2.drop n))).targetMap)).right.rangeTuple.length := by
    intro hlt
    have hmemx := List.idxOf_lt_length_iff.1 hlt
    change p.2[2 * n] ∈ (listOf (encode (p.2.drop n))).take n at hmemx
    rw [hlistk] at hmemx
    obtain ⟨t, htlt, ht⟩ := List.getElem_of_mem hmemx
    rw [List.getElem_take, List.getElem_drop] at ht
    have htn : t < n := by simp at htlt; omega
    have hco := (listAge.runLimit O).forall₂_omegaStageEmbedding
      (CeStructureChainIn.toLimit_representedByRawRep _ _) hp
    obtain ⟨a₁, ha₁, hy₁, hv₁⟩ := hco.exists_getElem?_left
      (List.getElem?_eq_some_iff.2 ⟨by omega, ht⟩)
    obtain ⟨a₂, ha₂, hy₂, hv₂⟩ := hco.exists_getElem?_left
      (List.getElem?_eq_getElem (l := p.2) h2n)
    have ha : a₁ = a₂ := hv₁.symm.trans hv₂
    rw [HomogeneityQueryData.fullTuple, List.append_assoc,
      List.getElem?_append_right (by omega), List.getElem?_append_left (by omega)] at ha₁
    rw [HomogeneityQueryData.fullTuple, List.append_assoc,
      List.getElem?_append_right (by omega), show 2 * n - n = n by omega,
      List.getElem?_append_right (by omega), show n - q.imageTuple.length = 0 by omega,
      List.getElem?_cons_zero] at ha₂
    rw [ha, ← Option.some.inj ha₂, show n + t - n = t by omega] at ha₁
    exact hx (List.mem_of_getElem? ha₁)
  -- the glue sends it past every left entry
  have hzle : z ≤ listAge.spanBound (PotentialSpanData.ofPair
      (F, (listReq n p a (encode (p.2.drop n))).targetMap)) := by
    rw [hDeq] at hz
    exact listAge.le_sum_of_mem (List.mem_append_left _ (List.mem_of_getElem? hz))
  rw [hzl, hlastv, listAge.glue, if_neg hnotin] at hzle
  omega

/-- **The pin is not vacuous**: on the query `(d⃗, c⃗, x) = ([], [], 0)` the packaged selector's `y`
lies in its own `γ`'s canonical member, and outside the canonical member of the left leg's range
tuple at the firing that produced it. -/
theorem test_pin_nonvacuous :
    ((test_listAge_computablyHomogeneous O).select ⟨[], [], 0⟩).imageOfNewPoint ∈
        ((listAge.runLimit O).omegaStructure (listAge.runLimit_cert O)).canonicalAge.domainAt
          (encode ((test_listAge_computablyHomogeneous O).select ⟨[], [], 0⟩).extensionTuple) ∧
      ∃ (p : ℕ × List ℕ) (a k s : ℕ) (D : AmalgamationDiagramData) (γL : List ℕ),
        p ∈ (listAge.runLimit O).rankTupleAtStagePart [0] ∧
        s ∈ PartialAgeIn.firingSearch (listAge O) (listAge.capWitness O) (encode [0])
          (encode (listReq 0 p a k)) ∧
        D ∈ PartialAgeIn.payloadPart (listAge O) (listAge.capWitness O) (encode [0]) s
          (listReq 0 p a k) ∧
        γL ∈ listMapPart ((listAge.runLimit O).rankStageMap (s + 1)) D.leftToApex.rangeTuple ∧
        ((test_listAge_computablyHomogeneous O).select ⟨[], [], 0⟩).imageOfNewPoint ∉
          ((listAge.runLimit O).omegaStructure (listAge.runLimit_cert O)).canonicalAge.domainAt
            (encode γL) := by
  have hlen : ([] : List ℕ).length = ([] : List ℕ).length := rfl
  obtain ⟨p, hp, a, ha, k, hk, s, hs, D, hD, γ, hγ, y, hy, hsel⟩ :=
    PartialAgeIn.exists_trace_of_matched (listAge.runLimit O) listAge.chpSel listAge.mappedCHPSpec
      (listAge.runLimit_cert O) (q := ⟨[], [], 0⟩) hlen
  have hsel' : (test_listAge_computablyHomogeneous O).select ⟨[], [], 0⟩ = ⟨γ, y⟩ := hsel
  refine ⟨(test_listAge_computablyHomogeneous O).imageOfNewPoint_mem _, ?_⟩
  rw [hsel']
  -- the left leg's range tuple lies in the apex member, so its ω-image exists
  obtain ⟨δ, -, F, -, hselD⟩ := PartialAgeIn.mem_payloadPart_iff.1 hD
  obtain ⟨-, hleft, -⟩ := (listAge.capWitness O).unconditional _ D hselD
  have hcodL : D.leftToApex.codIdx = listIdx (s + 1) := by
    rw [← PartialAgeIn.runStep_eq_of_mem_payloadPart (PartialAgeIn.firesAt_of_mem_firingSearch hs)
      hD, PartialAgeIn.runStep_codIdx]
  obtain ⟨γL, hγL⟩ := Part.dom_iff_mem.1 (listMapPart_dom_iff.2 fun z hz ↦ Part.dom_iff_mem.2
    ⟨_, PartialAgeIn.omegaMember_mem_rankStageMap (listAge.runLimit O) (s + 1)
      ⟨z, hcodL ▸ hleft.partialWellFormed.carrierValid z hz⟩⟩)
  exact ⟨p, a, k, s, D, γL, hp, hs, hD, hγL,
    test_new_point_outside_left_leg O hlen (List.not_mem_nil) hp ha hk hs hD hy hγL⟩

end Fixture

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_selectPart_recursiveIn
#assert_standard_axioms FirstOrder.Language.test_selectPart_dom
#assert_standard_axioms FirstOrder.Language.test_admissible
#assert_standard_axioms FirstOrder.Language.test_payload_is_runs
#assert_standard_axioms FirstOrder.Language.test_fallback
#assert_standard_axioms FirstOrder.Language.test_gamma_is_apex
#assert_standard_axioms FirstOrder.Language.test_y_from_right_leg
#assert_standard_axioms FirstOrder.Language.test_computablyHomogeneous
#assert_standard_axioms FirstOrder.Language.test_nonempty_of_selectors
#assert_standard_axioms FirstOrder.Language.test_listAge_computablyHomogeneous
#assert_standard_axioms FirstOrder.Language.test_new_point_outside_left_leg
#assert_standard_axioms FirstOrder.Language.test_pin_nonvacuous
