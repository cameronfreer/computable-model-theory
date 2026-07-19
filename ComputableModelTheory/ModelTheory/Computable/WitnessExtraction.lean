/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.EffectiveWitnesses
import ComputableModelTheory.ModelTheory.Computable.EmbeddingInformation

/-!
# Witness extraction: abstract search and the EI-route specializations

The extraction scheme behind effective hereditary/joint-embedding/amalgamation
witnesses, separated into the agreed bands:

* **Free directions** live with the interfaces (`HPWitnessIn.indexedHP` …,
  `CAPWitnessIn.toAPWitnessIn`); nothing here re-proves them.
* **Abstract search** (`exists_computableIn_selector`): from classical existence plus an
  *explicitly decidable* candidate predicate, μ-search over codes produces a selector
  computable in the oracle set together with its soundness — the common scheme
  "candidate predicate → decidability → existence → total search → semantic
  equations".
* **EI-route specializations**: candidate decidability discharged by
  `EmbeddingInformationComputableIn E K`. For hereditary and joint-embedding witnesses
  the candidate touches no `O`-computable presentation data — its non-EI conjuncts are
  absolute index checks — so no oracle-lifting hypothesis appears. For the CAP witness
  the candidate computes with `K`'s data twice (well-formedness reads `K.gens`; coded
  commutativity computes `K.compData`), so the extraction **explicitly carries the
  oracle-lifting assumption `O ⊆ E`**: EI decidability alone does not make the age's
  `O`-computable presentation data available in `E`.

The finite-language/finite-carrier route for discharging candidate decidability belongs
with the CHMM-representation reconciliation over c.e./finite carriers, not here.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

section AbstractSearch

variable {α β : Type*} [Primcodable α] [Primcodable β] [Inhabited β]
variable {E : Set (ℕ →. ℕ)}

/-- Abstract selector extraction: a total selector, computable in the oracle set, from
classical existence plus an explicitly decidable candidate predicate — by μ-search over
codes of candidate outputs. -/
theorem exists_computableIn_selector {cand : α → β → Prop}
    (hdec : ComputablePredIn E fun p : α × β ↦ cand p.1 p.2)
    (hex : ∀ a, ∃ b, cand a b) :
    ∃ select : α → β, ComputableIn E select ∧ ∀ a, cand a (select a) := by
  obtain ⟨D, hB⟩ := hdec
  have hf : ComputableIn E fun q : α × ℕ ↦
      (decode (α := β) q.2).elim false fun b ↦
        @decide (cand q.1 b) (D (q.1, b)) :=
    (ComputableIn.option_casesOn
      ((Computable.decode.computableIn).comp ComputableIn.snd)
      (ComputableIn.const false)
      ((hB.comp
        ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd)).to₂)).of_eq
      fun q ↦ by
        rcases decode (α := β) q.2 with - | b
        · rfl
        · exact decide_eq_decide.2 Iff.rfl
  have hex' : ∀ a, ∃ n, ((decode (α := β) n).elim false fun b ↦
      @decide (cand a b) (D (a, b))) = true := by
    intro a
    obtain ⟨b, hb⟩ := hex a
    exact ⟨encode b, by rw [encodek]; exact @decide_eq_true _ (D (a, b)) hb⟩
  refine ⟨fun a ↦ (decode (α := β) (Nat.find (hex' a))).getD default, ?_, ?_⟩
  · exact ComputableIn.option_getD
      ((Computable.decode.computableIn).comp (ComputableIn.find hf.to₂ hex'))
      (ComputableIn.const default)
  · intro a
    have hspec := Nat.find_spec (hex' a)
    rcases hd : decode (α := β) (Nat.find (hex' a)) with - | b
    · rw [hd] at hspec
      exact absurd hspec (by simp)
    · rw [hd] at hspec
      have hb : cand a b := @of_decide_eq_true _ (D (a, b)) hspec
      simpa [hd] using hb

end AbstractSearch

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {E : Set (ℕ →. ℕ)} {K : ComputableAgeIn O L}

instance : Inhabited PotentialEmbeddingData :=
  ⟨⟨0, 0, []⟩⟩

instance : Inhabited JointEmbeddingData :=
  ⟨⟨default, default⟩⟩

instance : Inhabited AmalgamationDiagramData :=
  ⟨⟨default, default⟩⟩

/-- Actualness of assembled potential data, as a candidate predicate over
index-tuple-index triples: decidable in `E` from the EI-decision interface alone —
the assembly is absolutely computable, and no `O`-computable presentation data
enters. -/
theorem isEmbedding_assembled_computablePredIn
    (hEI : EmbeddingInformationComputableIn E K) :
    ComputablePredIn E fun q : (ℕ × Tuple ℕ) × ℕ ↦
      (⟨q.2, q.1.1, q.1.2⟩ : PotentialEmbeddingData).IsEmbedding K :=
  (hEI.comp
    (PotentialEmbeddingData.ofTriple_computableIn.comp
      ((ComputableIn.snd).pair
        ((ComputableIn.fst.comp ComputableIn.fst).pair
          (ComputableIn.snd.comp ComputableIn.fst))))).of_eq
    fun _ ↦ Iff.rfl

/-- EI-route extraction of a hereditary witness: from the indexed hereditary property
and EI decidability in `E`. The candidate touches no `O`-computable presentation data,
so no oracle-lifting hypothesis is needed. -/
theorem ComputableAgeIn.IndexedHP.exists_hpWitnessIn
    (h : K.IndexedHP) (hEI : EmbeddingInformationComputableIn E K) :
    Nonempty (HPWitnessIn E K) := by
  obtain ⟨select, hsel, hsound⟩ :=
    exists_computableIn_selector (E := E)
      (cand := fun p : ℕ × Tuple ℕ ↦ fun j : ℕ ↦
        (⟨j, p.1, p.2⟩ : PotentialEmbeddingData).IsEmbedding K)
      (isEmbedding_assembled_computablePredIn hEI)
      (fun p ↦ h p.1 p.2)
  exact ⟨⟨select, hsel, fun i a ↦ hsound (i, a)⟩⟩

/-- Joint-embedding of selected data, as a candidate predicate: decidable in `E` from
the EI-decision interface alone — the shape conjuncts are absolute index checks. -/
theorem isJointEmbeddingOf_computablePredIn
    (hEI : EmbeddingInformationComputableIn E K) :
    ComputablePredIn E fun q : (ℕ × ℕ) × JointEmbeddingData ↦
      q.2.IsJointEmbeddingOf K q.1.1 q.1.2 := by
  have hshape : ComputablePredIn E fun q : (ℕ × ℕ) × JointEmbeddingData ↦
      q.2.WellShapedFor q.1.1 q.1.2 := by
    refine ComputablePredIn.and (ComputablePredIn.and ?_ ?_) ?_ |>.of_eq
      fun q ↦ ⟨fun ⟨⟨h1, h2⟩, h3⟩ ↦ ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨⟨h1, h2⟩, h3⟩⟩
    · exact ⟨fun _ ↦ instDecidableEqNat _ _,
        ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := E)).comp
          (PotentialEmbeddingData.primrec_domIdx.to_comp.computableIn.comp
            (JointEmbeddingData.leftInto_computable.comp ComputableIn.snd))
          (ComputableIn.fst.comp ComputableIn.fst)⟩
    · exact ⟨fun _ ↦ instDecidableEqNat _ _,
        ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := E)).comp
          (PotentialEmbeddingData.primrec_domIdx.to_comp.computableIn.comp
            (JointEmbeddingData.rightInto_computable.comp ComputableIn.snd))
          (ComputableIn.snd.comp ComputableIn.fst)⟩
    · exact ⟨fun _ ↦ instDecidableEqNat _ _,
        ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := E)).comp
          (PotentialEmbeddingData.primrec_codIdx.to_comp.computableIn.comp
            (JointEmbeddingData.leftInto_computable.comp ComputableIn.snd))
          (PotentialEmbeddingData.primrec_codIdx.to_comp.computableIn.comp
            (JointEmbeddingData.rightInto_computable.comp ComputableIn.snd))⟩
  have hleft : ComputablePredIn E fun q : (ℕ × ℕ) × JointEmbeddingData ↦
      q.2.leftInto.IsEmbedding K :=
    hEI.comp (JointEmbeddingData.leftInto_computable.comp ComputableIn.snd)
  have hright : ComputablePredIn E fun q : (ℕ × ℕ) × JointEmbeddingData ↦
      q.2.rightInto.IsEmbedding K :=
    hEI.comp (JointEmbeddingData.rightInto_computable.comp ComputableIn.snd)
  exact (hshape.and (hleft.and hright)).of_eq fun q ↦ Iff.rfl

/-- EI-route extraction of a joint-embedding witness: from the indexed joint embedding
property and EI decidability in `E`. No oracle-lifting hypothesis is needed. -/
theorem ComputableAgeIn.IndexedJEP.exists_jepWitnessIn
    (h : K.IndexedJEP) (hEI : EmbeddingInformationComputableIn E K) :
    Nonempty (JEPWitnessIn E K) := by
  obtain ⟨select, hsel, hsound⟩ :=
    exists_computableIn_selector (E := E)
      (cand := fun p : ℕ × ℕ ↦ fun J : JointEmbeddingData ↦
        J.IsJointEmbeddingOf K p.1 p.2)
      (isJointEmbeddingOf_computablePredIn hEI)
      (fun p ↦ h p.1 p.2)
  exact ⟨⟨select, hsel, fun i j ↦ hsound (i, j)⟩⟩

section CAPExtraction

-- `compData`/`transportValue` are consumed only through their computability contracts
-- here; keeping them opaque makes the compositions compare by congruence instead of
-- unfolding the term-code search (cf. the composition module's elaboration notes).
attribute [local irreducible] ComputableAgeIn.transportValue ComputableAgeIn.compData

/-- Equality of composed potential data, as a candidate conjunct: decidable in `E`
**given the oracle lifting `O ⊆ E`** — computing `compData` runs the age's
`O`-computable transport. Every combinator is fully pinned, per the composition
module's elaboration notes. -/
theorem compData_eq_computablePredIn (hOE : O ⊆ E) :
    ComputablePredIn E fun q : PotentialSpanData × AmalgamationDiagramData ↦
      K.compData q.2.leftToApex q.1.left = K.compData q.2.rightToApex q.1.right := by
  have hcomp : ComputableIn E fun p : PotentialEmbeddingData × PotentialEmbeddingData ↦
      K.compData p.1 p.2 :=
    RecursiveIn.mono hOE K.compData_computableIn
  have hL : ComputableIn E fun q : PotentialSpanData × AmalgamationDiagramData ↦
      K.compData q.2.leftToApex q.1.left :=
    ComputableIn.comp
      (α := PotentialSpanData × AmalgamationDiagramData)
      (β := PotentialEmbeddingData × PotentialEmbeddingData)
      (σ := PotentialEmbeddingData)
      (f := fun p ↦ K.compData p.1 p.2)
      (g := fun q ↦ (q.2.leftToApex, q.1.left))
      hcomp
      (ComputableIn.pair
        (α := PotentialSpanData × AmalgamationDiagramData)
        (β := PotentialEmbeddingData) (γ := PotentialEmbeddingData)
        (f := fun q ↦ q.2.leftToApex) (g := fun q ↦ q.1.left)
        (ComputableIn.comp
          (α := PotentialSpanData × AmalgamationDiagramData)
          (β := AmalgamationDiagramData) (σ := PotentialEmbeddingData)
          (f := AmalgamationDiagramData.leftToApex) (g := Prod.snd)
          AmalgamationDiagramData.leftToApex_computable ComputableIn.snd)
        (ComputableIn.comp
          (α := PotentialSpanData × AmalgamationDiagramData)
          (β := PotentialSpanData) (σ := PotentialEmbeddingData)
          (f := PotentialSpanData.left) (g := Prod.fst)
          PotentialSpanData.left_computable ComputableIn.fst))
  have hR : ComputableIn E fun q : PotentialSpanData × AmalgamationDiagramData ↦
      K.compData q.2.rightToApex q.1.right :=
    ComputableIn.comp
      (α := PotentialSpanData × AmalgamationDiagramData)
      (β := PotentialEmbeddingData × PotentialEmbeddingData)
      (σ := PotentialEmbeddingData)
      (f := fun p ↦ K.compData p.1 p.2)
      (g := fun q ↦ (q.2.rightToApex, q.1.right))
      hcomp
      (ComputableIn.pair
        (α := PotentialSpanData × AmalgamationDiagramData)
        (β := PotentialEmbeddingData) (γ := PotentialEmbeddingData)
        (f := fun q ↦ q.2.rightToApex) (g := fun q ↦ q.1.right)
        (ComputableIn.comp
          (α := PotentialSpanData × AmalgamationDiagramData)
          (β := AmalgamationDiagramData) (σ := PotentialEmbeddingData)
          (f := AmalgamationDiagramData.rightToApex) (g := Prod.snd)
          AmalgamationDiagramData.rightToApex_computable ComputableIn.snd)
        (ComputableIn.comp
          (α := PotentialSpanData × AmalgamationDiagramData)
          (β := PotentialSpanData) (σ := PotentialEmbeddingData)
          (f := PotentialSpanData.right) (g := Prod.fst)
          PotentialSpanData.right_computable ComputableIn.fst))
  have hencL : ComputableIn E fun q : PotentialSpanData × AmalgamationDiagramData ↦
      encode (K.compData q.2.leftToApex q.1.left) :=
    ComputableIn.comp
      (α := PotentialSpanData × AmalgamationDiagramData)
      (β := PotentialEmbeddingData) (σ := ℕ)
      (f := fun F ↦ encode F)
      (g := fun q ↦ K.compData q.2.leftToApex q.1.left)
      ComputableIn.encode hL
  have hencR : ComputableIn E fun q : PotentialSpanData × AmalgamationDiagramData ↦
      encode (K.compData q.2.rightToApex q.1.right) :=
    ComputableIn.comp
      (α := PotentialSpanData × AmalgamationDiagramData)
      (β := PotentialEmbeddingData) (σ := ℕ)
      (f := fun F ↦ encode F)
      (g := fun q ↦ K.compData q.2.rightToApex q.1.right)
      ComputableIn.encode hR
  have hB : ComputableIn E fun q : PotentialSpanData × AmalgamationDiagramData ↦
      decide (encode (K.compData q.2.leftToApex q.1.left)
        = encode (K.compData q.2.rightToApex q.1.right)) :=
    ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := E)).comp hencL hencR
  refine ⟨fun q ↦ decidable_of_iff _ Encodable.encode_injective.eq_iff, ?_⟩
  exact hB.of_eq fun q ↦ decide_eq_decide.2 Encodable.encode_injective.eq_iff

/-- An index-equality test between two computable ℕ-projections, as a candidate
conjunct. -/
private theorem projEq_computablePredIn {γ : Type*} [Primcodable γ]
    {f g : γ → ℕ} (hf : ComputableIn E f) (hg : ComputableIn E g) :
    ComputablePredIn E fun c ↦ f c = g c :=
  ⟨fun _ ↦ instDecidableEqNat _ _,
    ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := E)).comp hf hg⟩

/-- Diagram shape for a span, as a candidate conjunct: absolute index checks. -/
theorem wellShapedFor_computablePredIn :
    ComputablePredIn E fun q : PotentialSpanData × AmalgamationDiagramData ↦
      q.2.WellShapedFor q.1 := by
  have h1 := projEq_computablePredIn (E := E)
    (f := fun q : PotentialSpanData × AmalgamationDiagramData ↦
      q.2.leftToApex.domIdx)
    (g := fun q ↦ q.1.left.codIdx)
    (PotentialEmbeddingData.primrec_domIdx.to_comp.computableIn.comp
      (AmalgamationDiagramData.leftToApex_computable.comp ComputableIn.snd))
    (PotentialEmbeddingData.primrec_codIdx.to_comp.computableIn.comp
      (PotentialSpanData.left_computable.comp ComputableIn.fst))
  have h2 := projEq_computablePredIn (E := E)
    (f := fun q : PotentialSpanData × AmalgamationDiagramData ↦
      q.2.rightToApex.domIdx)
    (g := fun q ↦ q.1.right.codIdx)
    (PotentialEmbeddingData.primrec_domIdx.to_comp.computableIn.comp
      (AmalgamationDiagramData.rightToApex_computable.comp ComputableIn.snd))
    (PotentialEmbeddingData.primrec_codIdx.to_comp.computableIn.comp
      (PotentialSpanData.right_computable.comp ComputableIn.fst))
  have h3 := projEq_computablePredIn (E := E)
    (f := fun q : PotentialSpanData × AmalgamationDiagramData ↦
      q.2.leftToApex.codIdx)
    (g := fun q ↦ q.2.rightToApex.codIdx)
    (PotentialEmbeddingData.primrec_codIdx.to_comp.computableIn.comp
      (AmalgamationDiagramData.leftToApex_computable.comp ComputableIn.snd))
    (PotentialEmbeddingData.primrec_codIdx.to_comp.computableIn.comp
      (AmalgamationDiagramData.rightToApex_computable.comp ComputableIn.snd))
  exact ((h1.and h2).and h3).of_eq fun q ↦
    ⟨fun ⟨⟨a, b⟩, c⟩ ↦ ⟨a, b, c⟩, fun ⟨a, b, c⟩ ↦ ⟨⟨a, b⟩, c⟩⟩

/-- Span actualness, as a candidate hypothesis conjunct: an absolute index check plus
two EI decisions. -/
theorem isActual_computablePredIn (hEI : EmbeddingInformationComputableIn E K) :
    ComputablePredIn E fun q : PotentialSpanData × AmalgamationDiagramData ↦
      q.1.IsActual K := by
  have hshape := projEq_computablePredIn (E := E)
    (f := fun q : PotentialSpanData × AmalgamationDiagramData ↦ q.1.left.domIdx)
    (g := fun q ↦ q.1.right.domIdx)
    (PotentialEmbeddingData.primrec_domIdx.to_comp.computableIn.comp
      (PotentialSpanData.left_computable.comp ComputableIn.fst))
    (PotentialEmbeddingData.primrec_domIdx.to_comp.computableIn.comp
      (PotentialSpanData.right_computable.comp ComputableIn.fst))
  have hl : ComputablePredIn E fun q : PotentialSpanData × AmalgamationDiagramData ↦
      q.1.left.IsEmbedding K :=
    hEI.comp (PotentialSpanData.left_computable.comp ComputableIn.fst)
  have hr : ComputablePredIn E fun q : PotentialSpanData × AmalgamationDiagramData ↦
      q.1.right.IsEmbedding K :=
    hEI.comp (PotentialSpanData.right_computable.comp ComputableIn.fst)
  exact (hshape.and (hl.and hr)).of_eq fun q ↦ Iff.rfl

/-- The full CAP candidate: the unconditional clauses plus soundness guarded by span
actualness. Decidable in `E` from EI plus the oracle lifting. -/
theorem capCandidate_computablePredIn (hOE : O ⊆ E)
    (hEI : EmbeddingInformationComputableIn E K) :
    ComputablePredIn E fun q : PotentialSpanData × AmalgamationDiagramData ↦
      q.2.WellShapedFor q.1 ∧ q.2.leftToApex.IsEmbedding K ∧
        q.2.rightToApex.WellFormed K ∧
        (q.1.IsActual K → q.2.IsAmalgamationOf K q.1) := by
  have hWSF := wellShapedFor_computablePredIn (E := E)
  have hlemb : ComputablePredIn E
      fun q : PotentialSpanData × AmalgamationDiagramData ↦
        q.2.leftToApex.IsEmbedding K :=
    hEI.comp (AmalgamationDiagramData.leftToApex_computable.comp ComputableIn.snd)
  have hremb : ComputablePredIn E
      fun q : PotentialSpanData × AmalgamationDiagramData ↦
        q.2.rightToApex.IsEmbedding K :=
    hEI.comp (AmalgamationDiagramData.rightToApex_computable.comp ComputableIn.snd)
  have hrwf : ComputablePredIn E
      fun q : PotentialSpanData × AmalgamationDiagramData ↦
        q.2.rightToApex.WellFormed K :=
    (K.wellFormed_computablePredIn.mono hOE).comp
      (AmalgamationDiagramData.rightToApex_computable.comp ComputableIn.snd)
  have hamalg : ComputablePredIn E
      fun q : PotentialSpanData × AmalgamationDiagramData ↦
        q.2.IsAmalgamationOf K q.1 :=
    (hWSF.and (hlemb.and (hremb.and (compData_eq_computablePredIn hOE)))).of_eq
      fun q ↦ Iff.rfl
  exact hWSF.and (hlemb.and (hrwf.and
    ((isActual_computablePredIn hEI).imp hamalg)))

/-- EI-route extraction of a CAP witness: from the indexed amalgamation property, EI
decidability in `E`, **and the oracle lifting `O ⊆ E`** — the candidate reads `K.gens`
(well-formedness) and computes `K.compData` (coded commutativity), so EI decidability
alone would not suffice. Off actual spans the search is fed by the identity/generator
fallback diagram, which satisfies every unconditional clause. -/
theorem ComputableAgeIn.IndexedAP.exists_capWitnessIn
    (h : K.IndexedAP) (hOE : O ⊆ E) (hEI : EmbeddingInformationComputableIn E K) :
    Nonempty (CAPWitnessIn E K) := by
  have hex : ∀ S : PotentialSpanData, ∃ D : AmalgamationDiagramData,
      D.WellShapedFor S ∧ D.leftToApex.IsEmbedding K ∧
        D.rightToApex.WellFormed K ∧ (S.IsActual K → D.IsAmalgamationOf K S) := by
    intro S
    by_cases hS : S.IsActual K
    · obtain ⟨D, hD⟩ := h S hS
      obtain ⟨hrwf, -⟩ := hD.isEmbedding_rightToApex
      exact ⟨D, hD.wellShapedFor, hD.isEmbedding_leftToApex, hrwf, fun _ ↦ hD⟩
    · refine ⟨⟨PotentialEmbeddingData.id K S.left.codIdx,
        ⟨S.right.codIdx, S.left.codIdx, K.gens S.right.codIdx⟩⟩,
        ⟨rfl, rfl, rfl⟩, PotentialEmbeddingData.id_isEmbedding K _, rfl,
        fun hS' ↦ absurd hS' hS⟩
  obtain ⟨select, hsel, hsound⟩ :=
    exists_computableIn_selector (E := E)
      (cand := fun S D ↦ D.WellShapedFor S ∧ D.leftToApex.IsEmbedding K ∧
        D.rightToApex.WellFormed K ∧ (S.IsActual K → D.IsAmalgamationOf K S))
      ((capCandidate_computablePredIn hOE hEI).of_eq fun _ ↦ Iff.rfl)
      hex
  exact ⟨⟨select, hsel, fun S ↦ (hsound S).1, fun S ↦ (hsound S).2.1,
    fun S ↦ (hsound S).2.2.1, fun S hS ↦ (hsound S).2.2.2 hS⟩⟩

/-- The derived AP-witness extraction, through `toAPWitnessIn`. -/
theorem ComputableAgeIn.IndexedAP.exists_apWitnessIn
    (h : K.IndexedAP) (hOE : O ⊆ E) (hEI : EmbeddingInformationComputableIn E K) :
    Nonempty (APWitnessIn E K) :=
  (h.exists_capWitnessIn hOE hEI).map CAPWitnessIn.toAPWitnessIn

end CAPExtraction

end FirstOrder.Language
