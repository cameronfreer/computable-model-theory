/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PotentialSpan
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for potential spans and amalgamation diagrams

Named acceptance tests for span and diagram code data, their shape and actualness
predicates, and the coded↔realized commutativity theorem, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/PotentialSpanAudit.lean
```

Coverage: `Primcodable` instances for both structures; computable projections and pair
factories; actualness of the identity span; the identity diagram amalgamating the
identity span (non-vacuity); the range-tuple form of coded commutativity; the transport
form; and the realized-embedding acceptance gate.
-/

open Encodable FirstOrder Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {K : ComputableAgeIn O L} {S : PotentialSpanData} {D : AmalgamationDiagramData}

/-- Span data is primitively codable independently of any age. -/
@[reducible]
def test_potentialSpanData_primcodable : Primcodable PotentialSpanData :=
  inferInstance

/-- Diagram data is primitively codable independently of any age. -/
@[reducible]
def test_amalgamationDiagramData_primcodable : Primcodable AmalgamationDiagramData :=
  inferInstance

/-- The span projections and pair factory are computable in the oracle. -/
theorem test_spanData_computable (O : Set (ℕ →. ℕ)) :
    ComputableIn O PotentialSpanData.left ∧ ComputableIn O PotentialSpanData.right ∧
      ComputableIn O PotentialSpanData.ofPair :=
  ⟨PotentialSpanData.left_computable, PotentialSpanData.right_computable,
    PotentialSpanData.ofPair_computableIn⟩

/-- The diagram projections and pair factory are computable in the oracle. -/
theorem test_diagramData_computable (O : Set (ℕ →. ℕ)) :
    ComputableIn O AmalgamationDiagramData.leftToApex ∧
      ComputableIn O AmalgamationDiagramData.rightToApex ∧
      ComputableIn O AmalgamationDiagramData.ofPair :=
  ⟨AmalgamationDiagramData.leftToApex_computable,
    AmalgamationDiagramData.rightToApex_computable,
    AmalgamationDiagramData.ofPair_computableIn⟩

/-- The identity span is actual. -/
theorem test_id_span_isActual (i : ℕ) : (PotentialSpanData.id K i).IsActual K :=
  PotentialSpanData.id_isActual K i

/-- The identity diagram amalgamates the identity span (non-vacuity). -/
theorem test_id_isAmalgamationOf (i : ℕ) :
    (⟨PotentialEmbeddingData.id K i, PotentialEmbeddingData.id K i⟩ :
      AmalgamationDiagramData).IsAmalgamationOf K (PotentialSpanData.id K i) :=
  AmalgamationDiagramData.id_isAmalgamationOf K i

/-- With indices fixed by shape, coded commutativity is range-tuple equality. -/
theorem test_compData_span_eq_iff_rangeTuple_eq (hSd : S.WellShaped)
    (hshape : D.WellShapedFor S) :
    K.compData D.leftToApex S.left = K.compData D.rightToApex S.right ↔
      (K.compData D.leftToApex S.left).rangeTuple
        = (K.compData D.rightToApex S.right).rangeTuple :=
  K.compData_span_eq_iff_rangeTuple_eq hSd hshape

/-- Coded commutativity is pointwise commutativity of the transports. -/
theorem test_compData_span_eq_iff_transportValue_comm (hS : S.IsActual K)
    (hshape : D.WellShapedFor S) (hl : D.leftToApex.IsEmbedding K)
    (hr : D.rightToApex.IsEmbedding K) :
    K.compData D.leftToApex S.left = K.compData D.rightToApex S.right ↔
      ∀ x : ℕ, K.transportValue D.leftToApex (K.transportValue S.left x)
        = K.transportValue D.rightToApex (K.transportValue S.right x) :=
  K.compData_span_eq_iff_transportValue_comm hS hshape hl hr

/-- The acceptance gate: coded commutativity matches realized commutativity. -/
theorem test_isAmalgamationOf_iff_toEmbedding_comm (hSd : S.WellShaped)
    (hshape : D.WellShapedFor S) (hSlwf : S.left.WellFormed K)
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
        = D.rightToApex.toEmbedding hrwf hrAE (S.right.toEmbedding hSrwf hSrAE x) :=
  D.isAmalgamationOf_iff_toEmbedding_comm hSd hshape hSlwf hSlAE hSrwf hSrAE hlwf hlAE
    hrwf hrAE

end

section ConcreteSpan

variable (O : Set (ℕ →. ℕ))

/-- The identity span of the successor age is actual. -/
theorem test_succ_id_span_isActual :
    (PotentialSpanData.id (succAge O) 0).IsActual (succAge O) :=
  PotentialSpanData.id_isActual (succAge O) 0

/-- A span with a malformed left leg is never actual. -/
theorem test_succ_malformed_span_not_isActual :
    ¬(⟨⟨0, 0, []⟩, PotentialEmbeddingData.id (succAge O) 0⟩ :
      PotentialSpanData).IsActual (succAge O) :=
  fun h ↦ PotentialEmbeddingData.not_isEmbedding_of_not_wellFormed
    (by simp [PotentialEmbeddingData.WellFormed, succAge]) h.isEmbedding_left

end ConcreteSpan

#assert_standard_axioms test_potentialSpanData_primcodable
#assert_standard_axioms test_amalgamationDiagramData_primcodable
#assert_standard_axioms test_spanData_computable
#assert_standard_axioms test_diagramData_computable
#assert_standard_axioms test_id_span_isActual
#assert_standard_axioms test_id_isAmalgamationOf
#assert_standard_axioms test_compData_span_eq_iff_rangeTuple_eq
#assert_standard_axioms test_compData_span_eq_iff_transportValue_comm
#assert_standard_axioms test_isAmalgamationOf_iff_toEmbedding_comm
#assert_standard_axioms test_succ_id_span_isActual
#assert_standard_axioms test_succ_malformed_span_not_isActual
