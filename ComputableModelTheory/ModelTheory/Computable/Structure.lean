/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.OraclePred
import ComputableModelTheory.ModelTheory.Syntax.EffectiveLanguage

/-!
# ω-presented computable structures

A structure on carrier `ℕ` for an effective language is *computable in `O`* when its
interpretations of function and relation symbols are computable in `O`, arity by arity
(`IsComputableStructureIn`), and *c.e. in `O`* when its positive and negative relation
diagrams and its function graph are r.e. in `O` (`IsCEStructureIn`). Computable
structures are c.e. (`IsComputableStructureIn.to_ce`). A bundled version
(`ComputableStructureIn`) packages the structure data with its computability, for use in
age entries later.

The file also provides `Primcodable` instances for the symbols of each fixed arity, as
fibers of the arity map, and the computable empty-language structure on `ℕ`.

Following the roadmap, normalization results (the paper's Lemma 4.3) are deferred.
-/


open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {L : Language} [L.EffectiveLanguage]

/-- The function symbols of a fixed arity, as the fiber of the arity map. -/
def functionsEquivSubtype (n : ℕ) :
    L.Functions n ≃ { s : L.FunctionSymbol // s.arity = n } where
  toFun f := ⟨⟨n, f⟩, rfl⟩
  invFun s := s.2 ▸ s.1.2
  right_inv s := by obtain ⟨⟨m, f⟩, h⟩ := s; subst h; rfl

/-- The relation symbols of a fixed arity, as the fiber of the arity map. -/
def relationsEquivSubtype (n : ℕ) :
    L.Relations n ≃ { s : L.RelationSymbol // s.arity = n } where
  toFun R := ⟨⟨n, R⟩, rfl⟩
  invFun s := s.2 ▸ s.1.2
  right_inv s := by obtain ⟨⟨m, R⟩, h⟩ := s; subst h; rfl

/-- Function symbols of each fixed arity are primitively codable. -/
instance instPrimcodableFunctions (n : ℕ) : Primcodable (L.Functions n) :=
  haveI : Primcodable { s : L.FunctionSymbol // s.arity = n } :=
    Primcodable.subtype
      (Primrec.eq.comp primrec_functionSymbol_arity (Primrec.const n))
  Primcodable.ofEquiv _ (functionsEquivSubtype n)

/-- Relation symbols of each fixed arity are primitively codable. -/
instance instPrimcodableRelations (n : ℕ) : Primcodable (L.Relations n) :=
  haveI : Primcodable { s : L.RelationSymbol // s.arity = n } :=
    Primcodable.subtype
      (Primrec.eq.comp primrec_relationSymbol_arity (Primrec.const n))
  Primcodable.ofEquiv _ (relationsEquivSubtype n)

end FirstOrder.Language

section

variable (O : Set (ℕ →. ℕ)) (L : Language) [L.EffectiveLanguage] [L.Structure ℕ]

/-- An ω-presented structure is computable in `O` when its interpretation of every
function symbol and its interpretation of every relation symbol are computable in `O`,
arity by arity. -/
class IsComputableStructureIn : Prop where
  funMap_computableIn :
    ∀ n, ComputableIn O fun p : L.Functions n × (Fin n → ℕ) ↦ Structure.funMap p.1 p.2
  relMap_computablePredIn :
    ∀ n, ComputablePredIn O fun p : L.Relations n × (Fin n → ℕ) ↦ Structure.RelMap p.1 p.2

/-- An ω-presented structure is c.e. in `O` when its positive and negative relation
diagrams and its function graph are r.e. in `O`, arity by arity. -/
class IsCEStructureIn : Prop where
  relMap_rePredIn :
    ∀ n, REPredIn O fun p : L.Relations n × (Fin n → ℕ) ↦ Structure.RelMap p.1 p.2
  relMap_compl_rePredIn :
    ∀ n, REPredIn O fun p : L.Relations n × (Fin n → ℕ) ↦ ¬Structure.RelMap p.1 p.2
  funGraph_rePredIn :
    ∀ n, REPredIn O
      fun p : (L.Functions n × (Fin n → ℕ)) × ℕ ↦ Structure.funMap p.1.1 p.1.2 = p.2

/-- The graph of a computable interpretation is a computable predicate. -/
theorem funGraph_computablePredIn [IsComputableStructureIn O L] (n : ℕ) :
    ComputablePredIn O
      fun p : (L.Functions n × (Fin n → ℕ)) × ℕ ↦ Structure.funMap p.1.1 p.1.2 = p.2 :=
  (ComputablePred.computablePredIn
      (PrimrecPred.computablePred (Primrec.eq (α := ℕ)))).comp
    (((IsComputableStructureIn.funMap_computableIn (O := O) (L := L) n).comp
        ComputableIn.fst).pair ComputableIn.snd)

/-- Computable structures are c.e.: positive and negative diagrams and the function graph
are r.e. -/
theorem IsComputableStructureIn.to_ce [IsComputableStructureIn O L] : IsCEStructureIn O L where
  relMap_rePredIn n := (relMap_computablePredIn (O := O) (L := L) n).to_rePredIn
  relMap_compl_rePredIn n := (relMap_computablePredIn (O := O) (L := L) n).not.to_rePredIn
  funGraph_rePredIn n := (funGraph_computablePredIn O L n).to_rePredIn

end

/-- A bundled ω-presented computable structure: structure data on `ℕ` together with its
computability. -/
structure ComputableStructureIn (O : Set (ℕ →. ℕ)) (L : Language) [L.EffectiveLanguage] where
  [inst : L.Structure ℕ]
  isComputable : IsComputableStructureIn O L

namespace FirstOrder.Language

instance (n : ℕ) : IsEmpty (Language.empty.Functions n) := ⟨fun f ↦ nomatch f⟩

instance (n : ℕ) : IsEmpty (Language.empty.Relations n) := ⟨fun R ↦ nomatch R⟩

/-- The canonical (unique) empty-language structure on `ℕ`. -/
instance : Language.empty.Structure ℕ := emptyStructure

/-- The empty-language structure on `ℕ` is computable in any oracle set. -/
instance {O : Set (ℕ →. ℕ)} : IsComputableStructureIn O Language.empty where
  funMap_computableIn _ := (Computable.of_isEmpty _).computableIn
  relMap_computablePredIn _ :=
    ⟨fun p ↦ isEmptyElim p.1, (Computable.of_isEmpty _).computableIn⟩

end FirstOrder.Language
