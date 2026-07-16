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

Presentation-normalization results are deferred.
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

section

variable {M : Type*} [Primcodable M]

namespace FunctionApplicationData

/-- Assembling fixed-arity application data is primitive recursive: the assembly is a
re-association of codes. -/
theorem primrec_ofFixed (n : ℕ) :
    Primrec fun p : L.Functions n × (Fin n → M) ↦ ofFixed p.1 p.2 := by
  letI : Primcodable { s : L.FunctionSymbol // s.arity = n } :=
    Primcodable.subtype (Primrec.eq.comp primrec_functionSymbol_arity (Primrec.const n))
  have hsym : Primrec fun f : L.Functions n ↦ (functionsEquivSubtype n f).val :=
    Primrec.subtype_val.comp (Primrec.of_equiv (e := functionsEquivSubtype n))
  have hlist : Primrec fun v : Fin n → M ↦ List.ofFn v :=
    (Primrec.vector_toList.comp Primrec.vector_ofFn').of_eq fun v ↦
      List.Vector.toList_ofFn v
  have hmk : Primrec fun p : L.Functions n × (Fin n → M) ↦
      (⟨((functionsEquivSubtype n p.1).val, List.ofFn p.2),
        (List.length_ofFn).trans (functionsEquivSubtype n p.1).2.symm⟩ :
        { q : L.FunctionSymbol × List M // q.2.length = q.1.arity }) :=
    Primrec.subtype_mk ((hsym.comp Primrec.fst).pair (hlist.comp Primrec.snd))
  exact (Primrec.of_equiv_symm.comp hmk).of_eq fun p ↦
    equivSubtype.left_inv (ofFixed p.1 p.2)

end FunctionApplicationData

namespace RelationApplicationData

/-- Assembling fixed-arity application data is primitive recursive: the assembly is a
re-association of codes. -/
theorem primrec_ofFixed (n : ℕ) :
    Primrec fun p : L.Relations n × (Fin n → M) ↦ ofFixed p.1 p.2 := by
  letI : Primcodable { s : L.RelationSymbol // s.arity = n } :=
    Primcodable.subtype (Primrec.eq.comp primrec_relationSymbol_arity (Primrec.const n))
  have hsym : Primrec fun r : L.Relations n ↦ (relationsEquivSubtype n r).val :=
    Primrec.subtype_val.comp (Primrec.of_equiv (e := relationsEquivSubtype n))
  have hlist : Primrec fun v : Fin n → M ↦ List.ofFn v :=
    (Primrec.vector_toList.comp Primrec.vector_ofFn').of_eq fun v ↦
      List.Vector.toList_ofFn v
  have hmk : Primrec fun p : L.Relations n × (Fin n → M) ↦
      (⟨((relationsEquivSubtype n p.1).val, List.ofFn p.2),
        (List.length_ofFn).trans (relationsEquivSubtype n p.1).2.symm⟩ :
        { q : L.RelationSymbol × List M // q.2.length = q.1.arity }) :=
    Primrec.subtype_mk ((hsym.comp Primrec.fst).pair (hlist.comp Primrec.snd))
  exact (Primrec.of_equiv_symm.comp hmk).of_eq fun p ↦
    equivSubtype.left_inv (ofFixed p.1 p.2)

end RelationApplicationData

end

end FirstOrder.Language

section

variable (O : Set (ℕ →. ℕ)) (L : Language) [L.EffectiveLanguage] [L.Structure ℕ]

/-- An ω-presented structure is computable in `O` when a single `O`-computable algorithm
interprets every function symbol on its application data, and likewise a single
`O`-computable algorithm decides every relation symbol on its application data. The
uniformity over arities is essential: arity-by-arity computability does not provide the
single machine that term evaluation and diagrams require (the fixed-arity statements are
recovered as `funMap_computableIn` and `relMap_computablePredIn`). -/
class IsComputableStructureIn : Prop where
  funMap_computableIn :
    ComputableIn O (FunctionApplicationData.funMap (L := L) (M := ℕ))
  relMap_computablePredIn :
    ComputablePredIn O (RelationApplicationData.relMap (L := L) (M := ℕ))

/-- An ω-presented structure is c.e. in `O` when its positive and negative relation
diagrams and its function graph are r.e. in `O`, uniformly over application data. -/
class IsCEStructureIn : Prop where
  relMap_rePredIn : REPredIn O (RelationApplicationData.relMap (L := L) (M := ℕ))
  relMap_compl_rePredIn :
    REPredIn O fun d : RelationApplicationData L ℕ ↦ ¬d.relMap
  funGraph_rePredIn :
    REPredIn O fun p : FunctionApplicationData L ℕ × ℕ ↦ p.1.funMap = p.2

/-- The arity-specific interpretation of function symbols, derived from the uniform
field through the fixed-arity embedding into application data. -/
theorem funMap_computableIn [IsComputableStructureIn O L] (n : ℕ) :
    ComputableIn O fun p : L.Functions n × (Fin n → ℕ) ↦ Structure.funMap p.1 p.2 :=
  ((IsComputableStructureIn.funMap_computableIn (O := O) (L := L)).comp
    ((FunctionApplicationData.primrec_ofFixed n).to_comp.computableIn.of_eq
      fun _ ↦ rfl)).of_eq fun _ ↦ rfl

/-- The arity-specific interpretation of relation symbols, derived from the uniform
field through the fixed-arity embedding into application data. -/
theorem relMap_computablePredIn [IsComputableStructureIn O L] (n : ℕ) :
    ComputablePredIn O fun p : L.Relations n × (Fin n → ℕ) ↦ Structure.RelMap p.1 p.2 :=
  ((IsComputableStructureIn.relMap_computablePredIn (O := O) (L := L)).comp
    ((RelationApplicationData.primrec_ofFixed n).to_comp.computableIn.of_eq
      fun _ ↦ rfl)).of_eq fun _ ↦ Iff.rfl

/-- The graph of a computable interpretation is a computable predicate, uniformly over
application data. -/
theorem uniformFunGraph_computablePredIn [IsComputableStructureIn O L] :
    ComputablePredIn O fun p : FunctionApplicationData L ℕ × ℕ ↦ p.1.funMap = p.2 :=
  (ComputablePred.computablePredIn
      (PrimrecPred.computablePred (Primrec.eq (α := ℕ)))).comp
    (((IsComputableStructureIn.funMap_computableIn (O := O) (L := L)).comp
        ComputableIn.fst).pair ComputableIn.snd)

/-- The graph of a computable interpretation is a computable predicate, arity by
arity. -/
theorem funGraph_computablePredIn [IsComputableStructureIn O L] (n : ℕ) :
    ComputablePredIn O
      fun p : (L.Functions n × (Fin n → ℕ)) × ℕ ↦ Structure.funMap p.1.1 p.1.2 = p.2 :=
  (ComputablePred.computablePredIn
      (PrimrecPred.computablePred (Primrec.eq (α := ℕ)))).comp
    (((funMap_computableIn O L n).comp ComputableIn.fst).pair ComputableIn.snd)

/-- Computable structures are c.e.: positive and negative diagrams and the function graph
are r.e. -/
theorem IsComputableStructureIn.to_ce [IsComputableStructureIn O L] : IsCEStructureIn O L where
  relMap_rePredIn :=
    (IsComputableStructureIn.relMap_computablePredIn (O := O) (L := L)).to_rePredIn
  relMap_compl_rePredIn :=
    (IsComputableStructureIn.relMap_computablePredIn (O := O) (L := L)).not.to_rePredIn
  funGraph_rePredIn := (uniformFunGraph_computablePredIn O L).to_rePredIn

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

instance : IsEmpty (FunctionApplicationData Language.empty ℕ) :=
  ⟨fun d ↦ isEmptyElim d.symbol⟩

instance : IsEmpty (RelationApplicationData Language.empty ℕ) :=
  ⟨fun d ↦ isEmptyElim d.symbol⟩

/-- The empty-language structure on `ℕ` is computable in any oracle set. -/
instance {O : Set (ℕ →. ℕ)} : IsComputableStructureIn O Language.empty where
  funMap_computableIn := (Computable.of_isEmpty _).computableIn
  relMap_computablePredIn :=
    ⟨fun d ↦ isEmptyElim d, (Computable.of_isEmpty _).computableIn⟩

end FirstOrder.Language
