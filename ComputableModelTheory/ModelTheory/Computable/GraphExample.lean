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

/-- The path graph on `ℕ` is a computable structure in any oracle set: the roadmap's
finite-graph-language acceptance example. -/
instance pathGraph_isComputable {O : Set (ℕ →. ℕ)} :
    IsComputableStructureIn O Language.graph where
  funMap_computableIn _ := (Computable.of_isEmpty _).computableIn
  relMap_computablePredIn n :=
    match n with
    | 0 => ⟨fun p ↦ isEmptyElim p.1, (Computable.of_isEmpty _).computableIn⟩
    | 1 => ⟨fun p ↦ isEmptyElim p.1, (Computable.of_isEmpty _).computableIn⟩
    | 2 => by
      have happ : ∀ i : Fin 2, ComputableIn O
          fun p : Language.graph.Relations 2 × (Fin 2 → ℕ) ↦ p.2 i := fun i ↦
        (Computable.fin_app.comp Computable.id (Computable.const i)).computableIn.comp
          ComputableIn.snd
      have heq : ComputablePredIn O fun q : ℕ × ℕ ↦ q.1 = q.2 :=
        ComputablePred.computablePredIn (PrimrecPred.computablePred (Primrec.eq (α := ℕ)))
      have h₁ : ComputablePredIn O
          fun p : Language.graph.Relations 2 × (Fin 2 → ℕ) ↦ p.2 0 + 1 = p.2 1 :=
        heq.comp (((Primrec.succ.to_comp.computableIn).comp (happ 0)).pair (happ 1))
      have h₂ : ComputablePredIn O
          fun p : Language.graph.Relations 2 × (Fin 2 → ℕ) ↦ p.2 1 + 1 = p.2 0 :=
        heq.comp (((Primrec.succ.to_comp.computableIn).comp (happ 1)).pair (happ 0))
      exact (h₁.or h₂).of_eq fun p ↦ by rcases p with ⟨r, x⟩; cases r; rfl
    | (n + 3) => ⟨fun p ↦ isEmptyElim p.1, (Computable.of_isEmpty _).computableIn⟩

end

end FirstOrder.Language
