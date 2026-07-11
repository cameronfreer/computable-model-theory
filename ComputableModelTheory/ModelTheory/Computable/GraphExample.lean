/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.Structure
import Mathlib.ModelTheory.Graph

/-!
# The graph language is effective; the path graph on ℕ is computable

Mathlib's graph language (one binary relation) is an effective language, and the path
graph on `ℕ` — consecutive naturals adjacent — is a computable structure in any oracle
set. This is the finite-graph half of the roadmap's acceptance criterion for computable
structures (the empty-language half lives with the structure definitions).
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

instance (n : ℕ) : IsEmpty (Language.graph.Functions n) := ⟨fun f ↦ nomatch f⟩

instance : IsEmpty Language.graph.FunctionSymbol := ⟨fun s ↦ nomatch s.2⟩

instance : Primcodable Language.graph.FunctionSymbol :=
  Primcodable.ofEquiv Empty (Equiv.equivEmpty _)

instance (n : ℕ) : IsEmpty (Language.graph.Relations (n + 3)) := ⟨fun r ↦ nomatch r⟩

instance : IsEmpty (Language.graph.Relations 0) := ⟨fun r ↦ nomatch r⟩

instance : IsEmpty (Language.graph.Relations 1) := ⟨fun r ↦ nomatch r⟩

/-- The packaged relation symbols of the graph language form a singleton. -/
def graphRelationSymbolEquiv : Language.graph.RelationSymbol ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨2, .adj⟩
  left_inv s := by rcases s with ⟨_, r⟩; cases r; rfl

instance : Primcodable Language.graph.RelationSymbol :=
  Primcodable.ofEquiv Unit graphRelationSymbolEquiv

/-- The graph language is effective. -/
instance : EffectiveLanguage Language.graph where
  primrec_functionArity := Primrec.of_isEmpty _
  primrec_relationArity :=
    (Primrec.const 2).of_eq fun s ↦ by rcases s with ⟨_, r⟩; cases r; rfl

/-- The path graph on `ℕ`: consecutive naturals are adjacent. -/
@[reducible] def pathGraphStructure : Language.graph.Structure ℕ where
  RelMap | .adj => fun x ↦ x 0 + 1 = x 1 ∨ x 1 + 1 = x 0

section

attribute [local instance] pathGraphStructure

instance : IsEmpty (FunctionApplicationData Language.graph ℕ) :=
  ⟨fun d ↦ isEmptyElim d.symbol⟩

private theorem pathGraph_relMap_iff (d : RelationApplicationData Language.graph ℕ) :
    (d.argsList[0]! + 1 = d.argsList[1]! ∨ d.argsList[1]! + 1 = d.argsList[0]!) ↔
      d.relMap :=
  match d with
  | ⟨0, r, _⟩ => isEmptyElim r
  | ⟨1, r, _⟩ => isEmptyElim r
  | ⟨2, .adj, _⟩ => Iff.rfl
  | ⟨_ + 3, r, _⟩ => isEmptyElim r

instance : DecidablePred fun d : RelationApplicationData Language.graph ℕ ↦ d.relMap :=
  fun d ↦ match d with
  | ⟨0, r, _⟩ => isEmptyElim r
  | ⟨1, r, _⟩ => isEmptyElim r
  | ⟨2, .adj, v⟩ => inferInstanceAs (Decidable (v 0 + 1 = v 1 ∨ v 1 + 1 = v 0))
  | ⟨_ + 3, r, _⟩ => isEmptyElim r

/-- The path graph on `ℕ` is a computable structure in any oracle set: the roadmap's
finite-graph-language acceptance example. The uniform relation decider reads the two
arguments off the application data's argument list. -/
instance pathGraph_isComputable {O : Set (ℕ →. ℕ)} :
    IsComputableStructureIn O Language.graph where
  funMap_computableIn := (Computable.of_isEmpty _).computableIn
  relMap_computablePredIn := by
    have hget : ∀ i : ℕ, Primrec fun l : List ℕ ↦ l[i]! := fun i ↦
      (Primrec.option_getD.comp
        (Primrec.list_getElem?.comp Primrec.id (Primrec.const i))
        (Primrec.const default)).of_eq fun _ ↦ List.getElem!_eq_getElem?_getD.symm
    have h0 : Primrec fun d : RelationApplicationData Language.graph ℕ ↦
        d.argsList[0]! := (hget 0).comp RelationApplicationData.primrec_argsList
    have h1 : Primrec fun d : RelationApplicationData Language.graph ℕ ↦
        d.argsList[1]! := (hget 1).comp RelationApplicationData.primrec_argsList
    have hp : PrimrecPred fun d : RelationApplicationData Language.graph ℕ ↦
        d.argsList[0]! + 1 = d.argsList[1]! ∨ d.argsList[1]! + 1 = d.argsList[0]! :=
      PrimrecPred.or (Primrec.eq.comp (Primrec.succ.comp h0) h1)
        (Primrec.eq.comp (Primrec.succ.comp h1) h0)
    refine ⟨inferInstance, hp.decide.to_comp.computableIn.of_eq fun d ↦ ?_⟩
    exact Bool.eq_iff_iff.2 (decide_eq_true_iff.trans
      ((pathGraph_relMap_iff d).trans decide_eq_true_iff.symm))

end

end FirstOrder.Language
