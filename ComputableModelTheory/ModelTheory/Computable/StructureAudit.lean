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

/-- Function application data is primitively codable. -/
@[reducible] def test_funApplicationData_primcodable :
    Primcodable (FunctionApplicationData L ℕ) :=
  inferInstance

/-- Relation application data is primitively codable. -/
@[reducible] def test_relApplicationData_primcodable :
    Primcodable (RelationApplicationData L ℕ) :=
  inferInstance

/-- The uniform contract: one algorithm interprets every function symbol on its
application data. -/
theorem test_uniform_funMap [IsComputableStructureIn O L] :
    ComputableIn O (FunctionApplicationData.funMap (L := L) (M := ℕ)) :=
  IsComputableStructureIn.funMap_computableIn

/-- The uniform contract: one algorithm decides every relation symbol on its
application data. -/
theorem test_uniform_relMap [IsComputableStructureIn O L] :
    ComputablePredIn O (RelationApplicationData.relMap (L := L) (M := ℕ)) :=
  IsComputableStructureIn.relMap_computablePredIn

/-- The derived fixed-arity contract for function symbols. -/
theorem test_funMap_fixed [IsComputableStructureIn O L] (n : ℕ) :
    ComputableIn O fun p : L.Functions n × (Fin n → ℕ) ↦ Structure.funMap p.1 p.2 :=
  funMap_computableIn O L n

/-- The derived fixed-arity contract for relation symbols. -/
theorem test_relMap_fixed [IsComputableStructureIn O L] (n : ℕ) :
    ComputablePredIn O fun p : L.Relations n × (Fin n → ℕ) ↦ Structure.RelMap p.1 p.2 :=
  relMap_computablePredIn O L n

/-- Computable structures are c.e. -/
theorem test_to_ce [IsComputableStructureIn O L] : IsCEStructureIn O L :=
  IsComputableStructureIn.to_ce O L

/-- The uniform function graph of a computable structure is a computable predicate. -/
theorem test_uniform_funGraph [IsComputableStructureIn O L] :
    ComputablePredIn O fun p : FunctionApplicationData L ℕ × ℕ ↦ p.1.funMap = p.2 :=
  uniformFunGraph_computablePredIn O L

/-- The function graph of a computable structure is a computable predicate, arity by
arity. -/
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
#assert_standard_axioms test_funApplicationData_primcodable
#assert_standard_axioms test_relApplicationData_primcodable
#assert_standard_axioms test_uniform_funMap
#assert_standard_axioms test_uniform_relMap
#assert_standard_axioms test_funMap_fixed
#assert_standard_axioms test_relMap_fixed
#assert_standard_axioms test_to_ce
#assert_standard_axioms test_uniform_funGraph
#assert_standard_axioms test_funGraph
#assert_standard_axioms test_empty_computable
#assert_standard_axioms test_bundled_empty
