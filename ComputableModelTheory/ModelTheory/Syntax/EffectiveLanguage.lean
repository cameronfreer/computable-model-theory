/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.RecursiveIn
import Mathlib.ModelTheory.Basic

/-!
# Effective languages

Computability data on top of mathlib's `FirstOrder.Language`: a language is *effective*
when its arity-packaged function and relation symbols are primitively codable and the
arity maps are primitive recursive. Mathlib's languages are arity-indexed, so the natural
object to code is the sigma type of all symbols.

This is deliberately a *stronger* coding convention than the paper's, which asks only for
computable symbol sets with a computable arity map: the `Primcodable` instances for
first-order syntax discharge `Primcodable.prim` obligations, which live at the primitive
recursive level. A single strong class is used rather than a computable class with a
primitive recursive subclass; the eventual equivalence with the paper's presentation (up
to computable recoding of symbols) is a recorded proof obligation for the paper-wrapper
layer.

The `FunctionApplicationData`/`RelationApplicationData` structures package a symbol with
an arity-matched argument tuple, so that later files can quantify uniformly over all
symbols without destructing arities by hand.
-/

open Encodable

/-- Any function out of an empty `Primcodable` type is primitive recursive. Upstream
candidate for mathlib. -/
theorem Primrec.of_isEmpty {α σ : Type*} [Primcodable α] [Primcodable σ] [IsEmpty α]
    (f : α → σ) : Primrec f := by
  change Nat.Primrec fun n ↦ encode ((decode (α := α) n).map f)
  have h : (fun n ↦ encode ((decode (α := α) n).map f)) = fun _ ↦ 0 := by
    funext n
    rcases h : decode (α := α) n with - | a
    · simp
    · exact isEmptyElim a
  rw [h]
  exact Nat.Primrec.zero

/-- Any function out of an empty `Primcodable` type is computable. Upstream candidate for
mathlib. -/
theorem Computable.of_isEmpty {α σ : Type*} [Primcodable α] [Primcodable σ] [IsEmpty α]
    (f : α → σ) : Computable f :=
  Partrec.none.of_eq fun a ↦ isEmptyElim a

namespace FirstOrder.Language

universe u v

variable (L : Language.{u, v})

/-- The type of all function symbols of a language, packaged with their arities. This is
the left summand of mathlib's `Language.Symbols`. -/
def FunctionSymbol : Type u := Σ n, L.Functions n

/-- The type of all relation symbols of a language, packaged with their arities. This is
the right summand of mathlib's `Language.Symbols`. -/
def RelationSymbol : Type v := Σ n, L.Relations n

variable {L}

/-- The arity of a packaged function symbol. -/
def FunctionSymbol.arity : L.FunctionSymbol → ℕ := Sigma.fst

/-- The arity of a packaged relation symbol. -/
def RelationSymbol.arity : L.RelationSymbol → ℕ := Sigma.fst

variable (L)

/-- A first-order language is *effective* when its function and relation symbols are
primitively codable and the arity maps are primitive recursive. (Primitive recursion,
rather than mere computability, is what the `Primcodable` instances for syntax require.) -/
class EffectiveLanguage where
  [instFunctionSymbols : Primcodable L.FunctionSymbol]
  [instRelationSymbols : Primcodable L.RelationSymbol]
  primrec_functionArity : Primrec (FunctionSymbol.arity (L := L))
  primrec_relationArity : Primrec (RelationSymbol.arity (L := L))

attribute [reducible] EffectiveLanguage.instFunctionSymbols EffectiveLanguage.instRelationSymbols
attribute [instance] EffectiveLanguage.instFunctionSymbols EffectiveLanguage.instRelationSymbols

variable {L}

section

variable [L.EffectiveLanguage]

/-- The arity map on function symbols of an effective language is primitive recursive. -/
theorem primrec_functionSymbol_arity : Primrec (FunctionSymbol.arity (L := L)) :=
  EffectiveLanguage.primrec_functionArity

/-- The arity map on relation symbols of an effective language is primitive recursive. -/
theorem primrec_relationSymbol_arity : Primrec (RelationSymbol.arity (L := L)) :=
  EffectiveLanguage.primrec_relationArity

/-- The arity map on function symbols of an effective language is computable. -/
theorem computable_functionSymbol_arity : Computable (FunctionSymbol.arity (L := L)) :=
  primrec_functionSymbol_arity.to_comp

/-- The arity map on relation symbols of an effective language is computable. -/
theorem computable_relationSymbol_arity : Computable (RelationSymbol.arity (L := L)) :=
  primrec_relationSymbol_arity.to_comp

end

/-- A function symbol together with an arity-matched argument tuple in `M`. -/
structure FunctionApplicationData (L : Language) (M : Type*) where
  /-- The arity of the applied symbol. -/
  arity : ℕ
  /-- The applied function symbol. -/
  symbol : L.Functions arity
  /-- The argument tuple. -/
  args : Fin arity → M

/-- A relation symbol together with an arity-matched argument tuple in `M`. -/
structure RelationApplicationData (L : Language) (M : Type*) where
  /-- The arity of the applied symbol. -/
  arity : ℕ
  /-- The applied relation symbol. -/
  symbol : L.Relations arity
  /-- The argument tuple. -/
  args : Fin arity → M

/-- Function application data is a packaged symbol paired with an argument tuple of the
matching arity. -/
def FunctionApplicationData.equivSigma {M : Type*} :
    FunctionApplicationData L M ≃ Σ s : L.FunctionSymbol, Fin s.arity → M where
  toFun d := ⟨⟨d.arity, d.symbol⟩, d.args⟩
  invFun s := ⟨s.1.1, s.1.2, s.2⟩

/-- Relation application data is a packaged symbol paired with an argument tuple of the
matching arity. -/
def RelationApplicationData.equivSigma {M : Type*} :
    RelationApplicationData L M ≃ Σ s : L.RelationSymbol, Fin s.arity → M where
  toFun d := ⟨⟨d.arity, d.symbol⟩, d.args⟩
  invFun s := ⟨s.1.1, s.1.2, s.2⟩

instance : IsEmpty Language.empty.FunctionSymbol :=
  ⟨fun s ↦ s.2.elim⟩

instance : IsEmpty Language.empty.RelationSymbol :=
  ⟨fun s ↦ s.2.elim⟩

instance : Primcodable Language.empty.FunctionSymbol :=
  Primcodable.ofEquiv Empty (Equiv.equivEmpty _)

instance : Primcodable Language.empty.RelationSymbol :=
  Primcodable.ofEquiv Empty (Equiv.equivEmpty _)

/-- The empty language is effective. -/
instance : EffectiveLanguage Language.empty where
  primrec_functionArity := Primrec.of_isEmpty _
  primrec_relationArity := Primrec.of_isEmpty _

end FirstOrder.Language
