/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.Primcodable
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for syntax codability

Named acceptance tests for the syntax `Primcodable`/`Encodable` instances, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Syntax/PrimcodableAudit.lean
```
-/

open Encodable FirstOrder Language

section

variable {L : Language} {α : Type*} [Primcodable α] [L.EffectiveLanguage]

/-- The roadmap acceptance gate: the term instance typeclass-infers. -/
@[reducible] def test_term_primcodable : Primcodable (L.Term α) :=
  inferInstance

/-- The sentence acceptance gate, at the `Encodable` level reached this stage. -/
@[reducible] def test_sentence_encodable : Encodable L.Sentence :=
  inferInstance

/-- Bounded formulas over all variable counts are encodable. -/
@[reducible] def test_sigma_boundedFormula_encodable :
    Encodable (Σ n, L.BoundedFormula α n) :=
  inferInstance

/-- Terms round-trip through their codes. -/
theorem test_term_encodek (t : L.Term α) : decode (encode t) = some t :=
  Encodable.encodek t

/-- Formulas round-trip through their codes. -/
theorem test_formula_encodek (φ : L.Formula α) : decode (encode φ) = some φ :=
  Encodable.encodek φ

omit [Primcodable α] [L.EffectiveLanguage] in
/-- The stack machine underlying the term instance is exactly `listDecode` viewed on
`listEncode`-images. -/
theorem test_decodeStack_semantics (l : List (α ⊕ (Σ i, L.Functions i))) :
    Term.decodeStack l = (Term.listDecode l).map Term.listEncode :=
  Term.decodeStack_eq_map_listEncode l

/-- Decoding of term codes is primitive recursive on the encoded side. -/
theorem test_primrec_decodeStack : Primrec (Term.decodeStack (L := L) (α := α)) :=
  Term.primrec_decodeStack

end

#assert_standard_axioms test_term_primcodable
#assert_standard_axioms test_sentence_encodable
#assert_standard_axioms test_sigma_boundedFormula_encodable
#assert_standard_axioms test_term_encodek
#assert_standard_axioms test_formula_encodek
#assert_standard_axioms test_decodeStack_semantics
#assert_standard_axioms test_primrec_decodeStack
