/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.ApplicationDataComputable
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for relative application-data assembly

Named acceptance tests for the oracle-relative `ofSymbolArgs?` wrappers, checked by
`#assert_standard_axioms`. Each wrapper gets a computability gate; the semantic content of
`ofSymbolArgs?` itself is audited where it is defined. Outside the root import spine; CI checks
it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Syntax/ApplicationDataComputableAudit.lean
```
-/

open FirstOrder Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {α : Type*} [Primcodable α] {M : Type*} [Primcodable M]

/-- Function application data assembles from an oracle-computable symbol/arguments pair. -/
theorem test_functionApplicationData_ofSymbolArgs?_computableIn
    {p : α → L.FunctionSymbol × List M} (hp : ComputableIn O p) :
    ComputableIn O fun a ↦ FunctionApplicationData.ofSymbolArgs? (p a) :=
  FunctionApplicationData.ofSymbolArgs?_computableIn hp

/-- Relation application data assembles from an oracle-computable symbol/arguments pair. -/
theorem test_relationApplicationData_ofSymbolArgs?_computableIn
    {p : α → L.RelationSymbol × List M} (hp : ComputableIn O p) :
    ComputableIn O fun a ↦ RelationApplicationData.ofSymbolArgs? (p a) :=
  RelationApplicationData.ofSymbolArgs?_computableIn hp

/-- The identity instance: assembling from the input pair itself. -/
theorem test_ofSymbolArgs?_computableIn_id :
    ComputableIn O fun p : L.FunctionSymbol × List M ↦
      FunctionApplicationData.ofSymbolArgs? p :=
  FunctionApplicationData.ofSymbolArgs?_computableIn ComputableIn.id

end

#assert_standard_axioms test_functionApplicationData_ofSymbolArgs?_computableIn
#assert_standard_axioms test_relationApplicationData_ofSymbolArgs?_computableIn
#assert_standard_axioms test_ofSymbolArgs?_computableIn_id
