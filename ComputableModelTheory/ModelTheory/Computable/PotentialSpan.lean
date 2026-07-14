/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PotentialComposition

/-!
# Potential spans and amalgamation diagrams

Span and amalgamation-diagram data are pure code data — two potential embeddings each —
with all proof obligations kept outside the types, so both are `Primcodable` independently
of any age. Shape conditions are separate predicates: a span is well-shaped when its legs
share their domain index, and a diagram is well-shaped for a span when each output map's
domain is the corresponding leg's codomain and the output maps share their codomain (the
apex). Both shape predicates are pure index conditions, independent of any age.

Actualness of a span (`IsActual`) is well-shapedness with both legs actual. A diagram
amalgamates a span (`IsAmalgamationOf`) when it is well-shaped for it, both output maps
are actual, and the two coded composites agree as potential data. `IsAmalgamationOf`
deliberately does not require the span's actualness: witness selectors are total on
arbitrary codes, so actualness of the input span belongs in the AP soundness hypothesis,
not in the output predicate.

The acceptance gate is the coded↔realized commutativity theorem
(`isAmalgamationOf_iff_toEmbedding_comm`): on an actual span with actual, well-shaped
output maps, equality of the coded composites is exactly pointwise commutativity of the
realized embeddings over `ℕ`. It is stated pointwise, not as an equality of bundled
embeddings: the bundled presentation carriers are defeq to `ℕ` only at default
transparency, so all rewriting happens on `transportValue` (ℕ-stated), crossing to
`toEmbedding` only through `transportValue_eq_toEmbedding` (cf. `toEmbedding_compData`).
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- Potential span data: two potential embeddings intended to share their domain. Pure
code data with no proof obligations. -/
structure PotentialSpanData where
  /-- The left leg of the span. -/
  left : PotentialEmbeddingData
  /-- The right leg of the span. -/
  right : PotentialEmbeddingData

/-- The code-level packaging of potential span data. -/
private def spanEquiv : PotentialSpanData ≃ PotentialEmbeddingData × PotentialEmbeddingData where
  toFun S := (S.left, S.right)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable PotentialSpanData :=
  Primcodable.ofEquiv _ spanEquiv

theorem PotentialSpanData.primrec_left : Primrec PotentialSpanData.left :=
  (Primrec.fst.comp (Primrec.of_equiv (e := spanEquiv))).of_eq fun _ ↦ rfl

theorem PotentialSpanData.primrec_right : Primrec PotentialSpanData.right :=
  (Primrec.snd.comp (Primrec.of_equiv (e := spanEquiv))).of_eq fun _ ↦ rfl

theorem PotentialSpanData.left_computable :
    ComputableIn O PotentialSpanData.left :=
  PotentialSpanData.primrec_left.to_comp.computableIn

theorem PotentialSpanData.right_computable :
    ComputableIn O PotentialSpanData.right :=
  PotentialSpanData.primrec_right.to_comp.computableIn

/-- The named pair → data factory (`spanEquiv.symm`), the analogue of
`PotentialEmbeddingData.ofTriple` for spans: witness extraction will assemble span codes
through it, crossing the `ofEquiv` encoding via `ComputableIn.encode_iff` when needed. -/
def PotentialSpanData.ofPair (p : PotentialEmbeddingData × PotentialEmbeddingData) :
    PotentialSpanData :=
  spanEquiv.symm p

@[simp]
theorem PotentialSpanData.ofPair_left (p : PotentialEmbeddingData × PotentialEmbeddingData) :
    (PotentialSpanData.ofPair p).left = p.1 :=
  rfl

@[simp]
theorem PotentialSpanData.ofPair_right (p : PotentialEmbeddingData × PotentialEmbeddingData) :
    (PotentialSpanData.ofPair p).right = p.2 :=
  rfl

theorem PotentialSpanData.primrec_ofPair : Primrec PotentialSpanData.ofPair :=
  Primrec.of_equiv_symm

theorem PotentialSpanData.ofPair_computableIn :
    ComputableIn O PotentialSpanData.ofPair :=
  PotentialSpanData.primrec_ofPair.to_comp.computableIn

/-- Amalgamation diagram data: two potential embeddings intended to close a span into a
common apex. Pure code data with no proof obligations. -/
structure AmalgamationDiagramData where
  /-- The output map out of the left leg's codomain. -/
  leftToApex : PotentialEmbeddingData
  /-- The output map out of the right leg's codomain. -/
  rightToApex : PotentialEmbeddingData

/-- The code-level packaging of amalgamation diagram data. -/
private def diagEquiv :
    AmalgamationDiagramData ≃ PotentialEmbeddingData × PotentialEmbeddingData where
  toFun D := (D.leftToApex, D.rightToApex)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable AmalgamationDiagramData :=
  Primcodable.ofEquiv _ diagEquiv

theorem AmalgamationDiagramData.primrec_leftToApex :
    Primrec AmalgamationDiagramData.leftToApex :=
  (Primrec.fst.comp (Primrec.of_equiv (e := diagEquiv))).of_eq fun _ ↦ rfl

theorem AmalgamationDiagramData.primrec_rightToApex :
    Primrec AmalgamationDiagramData.rightToApex :=
  (Primrec.snd.comp (Primrec.of_equiv (e := diagEquiv))).of_eq fun _ ↦ rfl

theorem AmalgamationDiagramData.leftToApex_computable :
    ComputableIn O AmalgamationDiagramData.leftToApex :=
  AmalgamationDiagramData.primrec_leftToApex.to_comp.computableIn

theorem AmalgamationDiagramData.rightToApex_computable :
    ComputableIn O AmalgamationDiagramData.rightToApex :=
  AmalgamationDiagramData.primrec_rightToApex.to_comp.computableIn

/-- The named pair → data factory (`diagEquiv.symm`), the analogue of
`PotentialEmbeddingData.ofTriple` for diagrams: AP witness selectors will assemble their
output codes through it. -/
def AmalgamationDiagramData.ofPair
    (p : PotentialEmbeddingData × PotentialEmbeddingData) : AmalgamationDiagramData :=
  diagEquiv.symm p

@[simp]
theorem AmalgamationDiagramData.ofPair_leftToApex
    (p : PotentialEmbeddingData × PotentialEmbeddingData) :
    (AmalgamationDiagramData.ofPair p).leftToApex = p.1 :=
  rfl

@[simp]
theorem AmalgamationDiagramData.ofPair_rightToApex
    (p : PotentialEmbeddingData × PotentialEmbeddingData) :
    (AmalgamationDiagramData.ofPair p).rightToApex = p.2 :=
  rfl

theorem AmalgamationDiagramData.primrec_ofPair : Primrec AmalgamationDiagramData.ofPair :=
  Primrec.of_equiv_symm

theorem AmalgamationDiagramData.ofPair_computableIn :
    ComputableIn O AmalgamationDiagramData.ofPair :=
  AmalgamationDiagramData.primrec_ofPair.to_comp.computableIn

namespace PotentialSpanData

/-- Well-shapedness of a span: the legs share their domain index. A pure index condition,
independent of any age. -/
def WellShaped (S : PotentialSpanData) : Prop :=
  S.left.domIdx = S.right.domIdx

/-- Actualness of a span over an age: well-shaped, with both legs actual. -/
def IsActual (S : PotentialSpanData) (K : ComputableAgeIn O L) : Prop :=
  S.WellShaped ∧ S.left.IsEmbedding K ∧ S.right.IsEmbedding K

theorem IsActual.wellShaped {S : PotentialSpanData} {K : ComputableAgeIn O L}
    (h : S.IsActual K) : S.WellShaped :=
  h.1

theorem IsActual.isEmbedding_left {S : PotentialSpanData} {K : ComputableAgeIn O L}
    (h : S.IsActual K) : S.left.IsEmbedding K :=
  h.2.1

theorem IsActual.isEmbedding_right {S : PotentialSpanData} {K : ComputableAgeIn O L}
    (h : S.IsActual K) : S.right.IsEmbedding K :=
  h.2.2

/-- The identity span at an index: both legs are the identity potential embedding. -/
def id (K : ComputableAgeIn O L) (i : ℕ) : PotentialSpanData :=
  ⟨PotentialEmbeddingData.id K i, PotentialEmbeddingData.id K i⟩

@[simp]
theorem id_left (K : ComputableAgeIn O L) (i : ℕ) :
    (id K i).left = PotentialEmbeddingData.id K i :=
  rfl

@[simp]
theorem id_right (K : ComputableAgeIn O L) (i : ℕ) :
    (id K i).right = PotentialEmbeddingData.id K i :=
  rfl

/-- The identity span is actual. -/
theorem id_isActual (K : ComputableAgeIn O L) (i : ℕ) : (id K i).IsActual K :=
  ⟨rfl, PotentialEmbeddingData.id_isEmbedding K i, PotentialEmbeddingData.id_isEmbedding K i⟩

end PotentialSpanData

namespace AmalgamationDiagramData

/-- Well-shapedness of a diagram for a span: each output map's domain is the
corresponding leg's codomain, and the output maps share their codomain (the apex). A pure
index condition, independent of any age. -/
def WellShapedFor (D : AmalgamationDiagramData) (S : PotentialSpanData) : Prop :=
  D.leftToApex.domIdx = S.left.codIdx ∧ D.rightToApex.domIdx = S.right.codIdx ∧
    D.leftToApex.codIdx = D.rightToApex.codIdx

/-- `D` amalgamates `S` over `K`: well-shaped for `S`, both output maps actual, and the
two coded composites equal as potential data. Deliberately does not require
`S.IsActual K`: witness selectors are total on arbitrary codes, so the span's actualness
belongs in the AP soundness hypothesis. -/
def IsAmalgamationOf (D : AmalgamationDiagramData) (K : ComputableAgeIn O L)
    (S : PotentialSpanData) : Prop :=
  D.WellShapedFor S ∧ D.leftToApex.IsEmbedding K ∧ D.rightToApex.IsEmbedding K ∧
    K.compData D.leftToApex S.left = K.compData D.rightToApex S.right

variable {D : AmalgamationDiagramData} {S : PotentialSpanData} {K : ComputableAgeIn O L}

theorem IsAmalgamationOf.wellShapedFor (h : D.IsAmalgamationOf K S) : D.WellShapedFor S :=
  h.1

theorem IsAmalgamationOf.isEmbedding_leftToApex (h : D.IsAmalgamationOf K S) :
    D.leftToApex.IsEmbedding K :=
  h.2.1

theorem IsAmalgamationOf.isEmbedding_rightToApex (h : D.IsAmalgamationOf K S) :
    D.rightToApex.IsEmbedding K :=
  h.2.2.1

theorem IsAmalgamationOf.compData_eq (h : D.IsAmalgamationOf K S) :
    K.compData D.leftToApex S.left = K.compData D.rightToApex S.right :=
  h.2.2.2

/-- The identity diagram amalgamates the identity span: the two composites are the same
code on the nose. -/
theorem id_isAmalgamationOf (K : ComputableAgeIn O L) (i : ℕ) :
    (⟨PotentialEmbeddingData.id K i, PotentialEmbeddingData.id K i⟩ :
      AmalgamationDiagramData).IsAmalgamationOf K (PotentialSpanData.id K i) :=
  ⟨⟨rfl, rfl, rfl⟩, PotentialEmbeddingData.id_isEmbedding K i,
    PotentialEmbeddingData.id_isEmbedding K i, rfl⟩

end AmalgamationDiagramData

namespace ComputableAgeIn

variable (K : ComputableAgeIn O L) {S : PotentialSpanData} {D : AmalgamationDiagramData}

/-- With all indices fixed by the shape hypotheses, equality of the coded composites is
equality of their range tuples — the "equal range tuples after all indices are fixed"
form of coded commutativity. -/
theorem compData_span_eq_iff_rangeTuple_eq (hSd : S.WellShaped)
    (hshape : D.WellShapedFor S) :
    K.compData D.leftToApex S.left = K.compData D.rightToApex S.right ↔
      (K.compData D.leftToApex S.left).rangeTuple
        = (K.compData D.rightToApex S.right).rangeTuple := by
  constructor
  · intro h
    rw [h]
  · intro h
    refine PotentialEmbeddingData.ext ?_ ?_ h
    · exact hSd
    · exact hshape.2.2

/-- Coded commutativity is pointwise commutativity of the transports: on an actual span
with actual, well-shaped output maps, the two coded composites agree iff transporting any
value through the left leg then the left output map agrees with the right route. The
forward direction is functoriality (`transportValue_compData`) plus congruence; the
converse recovers the range tuples entry-by-entry from the shared domain generators
(`transportValue_gens`), so pointwise agreement on `ℕ` already pins the codes. -/
theorem compData_span_eq_iff_transportValue_comm (hS : S.IsActual K)
    (hshape : D.WellShapedFor S) (hl : D.leftToApex.IsEmbedding K)
    (hr : D.rightToApex.IsEmbedding K) :
    K.compData D.leftToApex S.left = K.compData D.rightToApex S.right ↔
      ∀ x : ℕ, K.transportValue D.leftToApex (K.transportValue S.left x)
        = K.transportValue D.rightToApex (K.transportValue S.right x) := by
  obtain ⟨hSd, hSl, hSr⟩ := hS
  constructor
  · intro hcode x
    rw [← K.transportValue_compData hshape.1.symm hSl hl x,
      ← K.transportValue_compData hshape.2.1.symm hSr hr x, hcode]
  · intro hcomm
    obtain ⟨hSlwf, hSlAE⟩ := hSl
    obtain ⟨hSrwf, hSrAE⟩ := hSr
    refine PotentialEmbeddingData.ext ?_ ?_ ?_
    · exact hSd
    · exact hshape.2.2
    · simp only [compData_rangeTuple]
      apply List.ext_getElem
      · simp only [List.length_map]
        rw [hSlwf, hSrwf, hSd]
      · intro n h1 h2
        rw [List.length_map] at h1 h2
        have hnl : n < (K.gens S.left.domIdx).length := by rwa [hSlwf] at h1
        have hnr : n < (K.gens S.right.domIdx).length := by rwa [hSrwf] at h2
        have hgl : K.transportValue S.left ((K.gens S.left.domIdx)[n]'hnl)
            = S.left.rangeTuple[n]'h1 := by
          simpa [Tuple.view_eq_get, List.get_eq_getElem, PotentialEmbeddingData.targetView,
            Fin.val_cast] using K.transportValue_gens hSlwf hSlAE ⟨n, hnl⟩
        have hgr : K.transportValue S.right ((K.gens S.right.domIdx)[n]'hnr)
            = S.right.rangeTuple[n]'h2 := by
          simpa [Tuple.view_eq_get, List.get_eq_getElem, PotentialEmbeddingData.targetView,
            Fin.val_cast] using K.transportValue_gens hSrwf hSrAE ⟨n, hnr⟩
        have hgen : (K.gens S.left.domIdx)[n]'hnl = (K.gens S.right.domIdx)[n]'hnr :=
          List.getElem_of_eq (congrArg K.gens hSd) hnl
        calc (S.left.rangeTuple.map (K.transportValue D.leftToApex))[n]
            = K.transportValue D.leftToApex (S.left.rangeTuple[n]'h1) :=
              List.getElem_map ..
          _ = K.transportValue D.leftToApex
                (K.transportValue S.left ((K.gens S.left.domIdx)[n]'hnl)) := by rw [hgl]
          _ = K.transportValue D.rightToApex
                (K.transportValue S.right ((K.gens S.left.domIdx)[n]'hnl)) :=
              hcomm ((K.gens S.left.domIdx)[n]'hnl)
          _ = K.transportValue D.rightToApex
                (K.transportValue S.right ((K.gens S.right.domIdx)[n]'hnr)) := by rw [hgen]
          _ = K.transportValue D.rightToApex (S.right.rangeTuple[n]'h2) := by rw [hgr]
          _ = (S.right.rangeTuple.map (K.transportValue D.rightToApex))[n] :=
              (List.getElem_map ..).symm

end ComputableAgeIn

namespace AmalgamationDiagramData

variable {K : ComputableAgeIn O L} {S : PotentialSpanData} {D : AmalgamationDiagramData}

/-- Coded commutativity matches realized commutativity: on an actual span (given through
its well-formedness/atomic-equivalence witnesses) with actual, well-shaped output maps,
`D` amalgamates `S` iff the realized embeddings commute pointwise over `ℕ`. Stated
pointwise, not as an equality of bundled embeddings: the crossing to `toEmbedding` goes
through `transportValue_eq_toEmbedding`, keeping all rewriting ℕ-stated. -/
theorem isAmalgamationOf_iff_toEmbedding_comm (hSd : S.WellShaped)
    (hshape : D.WellShapedFor S)
    (hSlwf : S.left.WellFormed K)
    (hSlAE : @AtomicEquivalent L ℕ ℕ (K.structureAt S.left.domIdx)
      (K.structureAt S.left.codIdx) _ (K.gens S.left.domIdx).view (S.left.targetView hSlwf))
    (hSrwf : S.right.WellFormed K)
    (hSrAE : @AtomicEquivalent L ℕ ℕ (K.structureAt S.right.domIdx)
      (K.structureAt S.right.codIdx) _ (K.gens S.right.domIdx).view
      (S.right.targetView hSrwf))
    (hlwf : D.leftToApex.WellFormed K)
    (hlAE : @AtomicEquivalent L ℕ ℕ (K.structureAt D.leftToApex.domIdx)
      (K.structureAt D.leftToApex.codIdx) _ (K.gens D.leftToApex.domIdx).view
      (D.leftToApex.targetView hlwf))
    (hrwf : D.rightToApex.WellFormed K)
    (hrAE : @AtomicEquivalent L ℕ ℕ (K.structureAt D.rightToApex.domIdx)
      (K.structureAt D.rightToApex.codIdx) _ (K.gens D.rightToApex.domIdx).view
      (D.rightToApex.targetView hrwf)) :
    D.IsAmalgamationOf K S ↔
      ∀ x : ℕ, D.leftToApex.toEmbedding hlwf hlAE (S.left.toEmbedding hSlwf hSlAE x)
        = D.rightToApex.toEmbedding hrwf hrAE (S.right.toEmbedding hSrwf hSrAE x) := by
  have hS : S.IsActual K := ⟨hSd, ⟨hSlwf, hSlAE⟩, ⟨hSrwf, hSrAE⟩⟩
  have hiff := K.compData_span_eq_iff_transportValue_comm hS hshape ⟨hlwf, hlAE⟩ ⟨hrwf, hrAE⟩
  constructor
  · intro h x
    rw [← K.transportValue_eq_toEmbedding hSlwf hSlAE,
      ← K.transportValue_eq_toEmbedding hSrwf hSrAE,
      ← K.transportValue_eq_toEmbedding hlwf hlAE,
      ← K.transportValue_eq_toEmbedding hrwf hrAE]
    exact hiff.1 h.compData_eq x
  · intro hcomm
    refine ⟨hshape, ⟨hlwf, hlAE⟩, ⟨hrwf, hrAE⟩, hiff.2 fun x ↦ ?_⟩
    rw [K.transportValue_eq_toEmbedding hSlwf hSlAE x,
      K.transportValue_eq_toEmbedding hSrwf hSrAE x,
      K.transportValue_eq_toEmbedding hlwf hlAE,
      K.transportValue_eq_toEmbedding hrwf hrAE]
    exact hcomm x

end AmalgamationDiagramData

end FirstOrder.Language
