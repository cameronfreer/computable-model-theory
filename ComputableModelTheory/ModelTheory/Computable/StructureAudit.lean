/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.GraphExample
import ComputableModelTheory.ModelTheory.Computable.Structure
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for computable structures

Named acceptance tests for `IsComputableStructureIn`/`IsCEStructureIn`, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/StructureAudit.lean
```
-/

open FirstOrder Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage] [L.Structure ℕ]

/-- Fixed-arity function-symbol fibers are primitively codable. -/
@[reducible] def test_functions_primcodable (n : ℕ) : Primcodable (L.Functions n) :=
  inferInstance

/-- Fixed-arity relation-symbol fibers are primitively codable. -/
@[reducible] def test_relations_primcodable (n : ℕ) : Primcodable (L.Relations n) :=
  inferInstance

/-- Computable structures are c.e. -/
theorem test_to_ce [IsComputableStructureIn O L] : IsCEStructureIn O L :=
  IsComputableStructureIn.to_ce O L

/-- The function graph of a computable structure is a computable predicate. -/
theorem test_funGraph [IsComputableStructureIn O L] (n : ℕ) :
    ComputablePredIn O
      fun p : (L.Functions n × (Fin n → ℕ)) × ℕ ↦ Structure.funMap p.1.1 p.1.2 = p.2 :=
  funGraph_computablePredIn O L n

/-- The roadmap acceptance gate: the empty language on `ℕ` is a computable structure. -/
theorem test_empty_computable {O : Set (ℕ →. ℕ)} :
    IsComputableStructureIn O Language.empty :=
  inferInstance

/-- The bundled empty-language computable structure. -/
@[reducible] def test_bundled_empty {O : Set (ℕ →. ℕ)} :
    ComputableStructureIn O Language.empty :=
  ⟨inferInstance⟩

/-- The graph language is effective. -/
@[reducible] def test_graph_effective : Language.graph.EffectiveLanguage :=
  inferInstance

/-- The roadmap acceptance gate: a finite graph language with a computable edge
relation, namely the path graph on `ℕ`. -/
theorem test_pathGraph_computable {O : Set (ℕ →. ℕ)} :
    letI := pathGraphStructure
    IsComputableStructureIn O Language.graph :=
  pathGraph_isComputable

end

#assert_standard_axioms test_functions_primcodable
#assert_standard_axioms test_relations_primcodable
#assert_standard_axioms test_graph_effective
#assert_standard_axioms test_pathGraph_computable
#assert_standard_axioms test_to_ce
#assert_standard_axioms test_funGraph
#assert_standard_axioms test_empty_computable
#assert_standard_axioms test_bundled_empty
