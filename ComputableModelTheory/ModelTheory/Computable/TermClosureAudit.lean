/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.TermClosure
import ComputableModelTheory.ModelTheory.Computable.SuccExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for effective term enumeration

Named acceptance tests for decode-and-evaluate and r.e. closure membership, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/TermClosureAudit.lean
```
-/

open Encodable FirstOrder Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage] [L.Structure ℕ] {k : ℕ}

/-- Decode-and-evaluate is oracle-computable. -/
theorem test_termValue?_computableIn [IsComputableStructureIn O L] :
    ComputableIn₂ O (termValue? (L := L) (k := k)) :=
  termValue?_computableIn O k

/-- Decode-and-evaluate returns the value on term codes. -/
theorem test_termValue?_encode (a : Fin k → ℕ) (t : L.Term (Fin k)) :
    termValue? (L := L) a (@encode (L.Term (Fin k)) Primcodable.toEncodable t) =
      some (t.realize a) :=
  termValue?_encode a t

/-- The enumeration range is exactly the tuple closure. -/
theorem test_termValue?_range_iff (a : Fin k → ℕ) (x : ℕ) :
    (∃ c, termValue? (L := L) a c = some x) ↔
      x ∈ Substructure.closure L (Set.range a) :=
  termValue?_eq_some_iff_mem_closure a x

/-- Membership in a fixed tuple's closure is r.e. in the oracle. -/
theorem test_closure_mem_rePredIn [IsComputableStructureIn O L] (a : Fin k → ℕ) :
    REPredIn O fun x : ℕ ↦ x ∈ Substructure.closure L (Set.range a) :=
  closure_mem_rePredIn O a

/-- The list form: membership in a fixed list tuple's closure is r.e. -/
theorem test_tuple_closure_mem_rePredIn [IsComputableStructureIn O L] (a : Tuple ℕ) :
    REPredIn O fun x : ℕ ↦ x ∈ Tuple.closure L a :=
  tuple_closure_mem_rePredIn O a

end

section ConcreteEnumeration

attribute [local instance] succStructure

/-- Membership in the successor closure of the tuple `0` is r.e. in any oracle. -/
theorem test_succ_closure_rePredIn (O : Set (ℕ →. ℕ)) :
    REPredIn O fun x : ℕ ↦ x ∈ Substructure.closure succLang (Set.range ![(0 : ℕ)]) :=
  closure_mem_rePredIn O ![0]

end ConcreteEnumeration

#assert_standard_axioms test_termValue?_computableIn
#assert_standard_axioms test_termValue?_encode
#assert_standard_axioms test_termValue?_range_iff
#assert_standard_axioms test_closure_mem_rePredIn
#assert_standard_axioms test_tuple_closure_mem_rePredIn
#assert_standard_axioms test_succ_closure_rePredIn
