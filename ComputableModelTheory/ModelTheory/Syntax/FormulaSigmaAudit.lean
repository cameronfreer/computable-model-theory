/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.FormulaSigma
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for the formula alphabet and stack machine

Named acceptance tests for the formula stack machine and the `Primcodable` instances for
formulas, checked by `#assert_standard_axioms`. Outside the root import spine; CI checks
it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Syntax/FormulaSigmaAudit.lean
```
-/

open Encodable FirstOrder Language Language.BoundedFormula

section

variable {L : Language} {α : Type*} [Primcodable α] [L.EffectiveLanguage]

omit [Primcodable α] [L.EffectiveLanguage] in
/-- The exact bridge: the machine computes `listDecode` in the pair representation,
preserving the `default` results on mismatched indices. -/
theorem test_decodeStack_eq_map_listEncode (l : List (FormulaSymbol L α)) :
    decodeStack l = (listDecode l).map sigmaRepr :=
  decodeStack_eq_map_listEncode l

/-- The formula stack machine is primitive recursive. -/
theorem test_primrec_decodeStack : Primrec (decodeStack (L := L) (α := α)) :=
  primrec_decodeStack

/-- Packaged bounded formulas are primitively codable. -/
@[reducible] def test_sigma_boundedFormula_primcodable :
    Primcodable (Σ n, L.BoundedFormula α n) :=
  inferInstance

/-- Formulas are primitively codable. -/
@[reducible] def test_formula_primcodable : Primcodable (L.Formula α) :=
  inferInstance

/-- The roadmap acceptance gate: sentences are primitively codable. -/
@[reducible] def test_sentence_primcodable : Primcodable L.Sentence :=
  inferInstance

/-- No-diamond gate: the formula code is the code of its index-`0` packaging (the
existing left injection), definitionally. -/
theorem test_encode_formula_eq_encode_sigma (φ : L.Formula α) :
    encode φ = encode (⟨0, φ⟩ : Σ n, L.BoundedFormula α n) :=
  rfl

/-- No-diamond gate: the packaged-formula code is the code of its symbol list,
definitionally. -/
theorem test_encode_sigma_eq_encode_listEncode (s : Σ n, L.BoundedFormula α n) :
    encode s = encode s.2.listEncode :=
  rfl

/-- Packaged bounded formulas round-trip through their codes. -/
theorem test_sigma_boundedFormula_encodek (s : Σ n, L.BoundedFormula α n) :
    decode (encode s) = some s :=
  encodek s

/-- Formulas round-trip through their codes. -/
theorem test_formula_encodek (φ : L.Formula α) : decode (encode φ) = some φ :=
  encodek φ

/-- Sentences round-trip through their codes. -/
theorem test_sentence_encodek (ψ : L.Sentence) : decode (encode ψ) = some ψ :=
  encodek ψ

end

#assert_standard_axioms test_decodeStack_eq_map_listEncode
#assert_standard_axioms test_primrec_decodeStack
#assert_standard_axioms test_sigma_boundedFormula_primcodable
#assert_standard_axioms test_formula_primcodable
#assert_standard_axioms test_sentence_primcodable
#assert_standard_axioms test_encode_formula_eq_encode_sigma
#assert_standard_axioms test_encode_sigma_eq_encode_listEncode
#assert_standard_axioms test_sigma_boundedFormula_encodek
#assert_standard_axioms test_formula_encodek
#assert_standard_axioms test_sentence_encodek
