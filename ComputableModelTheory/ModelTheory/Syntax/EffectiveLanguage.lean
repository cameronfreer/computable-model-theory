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
symbols without destructing arities by hand. For an effective language over a
`Primcodable` carrier they are themselves `Primcodable` — coded through the equivalent
subtype of symbol/argument-list pairs of matching length — with primitive recursive
symbol and argument-list projections, and they carry the uniform structure evaluations
`FunctionApplicationData.funMap` and `RelationApplicationData.relMap`.
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

variable {M : Type*}

namespace FunctionApplicationData

/-- The packaged symbol of function application data. -/
def toSymbol (d : FunctionApplicationData L M) : L.FunctionSymbol := ⟨d.arity, d.symbol⟩

/-- The argument list of function application data. -/
def argsList (d : FunctionApplicationData L M) : List M := List.ofFn d.args

/-- Function application data is a packaged symbol paired with an argument list of the
matching length. -/
def equivSubtype : FunctionApplicationData L M ≃
    { p : L.FunctionSymbol × List M // p.2.length = p.1.arity } where
  toFun d := ⟨(⟨d.arity, d.symbol⟩, List.ofFn d.args), by simp [FunctionSymbol.arity]⟩
  invFun p := ⟨p.1.1.1, p.1.1.2, fun i ↦ p.1.2.get (Fin.cast p.2.symm i)⟩
  left_inv d := by
    rcases d with ⟨n, f, v⟩
    dsimp only
    congr 1
    funext i
    simp
  right_inv p := by
    rcases p with ⟨⟨⟨n, f⟩, l⟩, h⟩
    refine Subtype.ext (Prod.ext rfl ?_)
    exact List.ext_getElem (by simpa [FunctionSymbol.arity] using h.symm) fun i h₁ h₂ ↦ by
      simp

/-- The uniform evaluation of function application data in a structure. -/
def funMap [L.Structure M] (d : FunctionApplicationData L M) : M :=
  Structure.funMap d.symbol d.args

/-- Fixed-arity function application data. -/
def ofFixed {n : ℕ} (f : L.Functions n) (v : Fin n → M) : FunctionApplicationData L M :=
  ⟨n, f, v⟩

/-- Assemble function application data from a packaged symbol and an argument list,
succeeding exactly when the list length matches the symbol's arity. -/
def ofSymbolArgs? (p : L.FunctionSymbol × List M) :
    Option (FunctionApplicationData L M) :=
  if h : p.2.length = p.1.arity then some (equivSubtype.symm ⟨p, h⟩) else none

theorem ofSymbolArgs?_of_length_eq (p : L.FunctionSymbol × List M)
    (h : p.2.length = p.1.arity) :
    ofSymbolArgs? p = some (equivSubtype.symm ⟨p, h⟩) :=
  dif_pos h

theorem ofSymbolArgs?_of_length_ne (p : L.FunctionSymbol × List M)
    (h : ¬p.2.length = p.1.arity) : ofSymbolArgs? p = none :=
  dif_neg h

/-- Evaluating the data assembled from a symbol and its argument list. -/
theorem funMap_equivSubtype_symm [L.Structure M] (p : L.FunctionSymbol × List M)
    (h : p.2.length = p.1.arity) :
    (equivSubtype.symm ⟨p, h⟩ : FunctionApplicationData L M).funMap =
      Structure.funMap p.1.2 fun i ↦ p.2.get (Fin.cast h.symm i) :=
  rfl

section Primcodable

variable [Primcodable M] [L.EffectiveLanguage]

instance : Primcodable { p : L.FunctionSymbol × List M // p.2.length = p.1.arity } :=
  Primcodable.subtype
    (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
      (primrec_functionSymbol_arity.comp Primrec.fst))

instance : Primcodable (FunctionApplicationData L M) :=
  Primcodable.ofEquiv _ equivSubtype

/-- The symbol projection of function application data is primitive recursive. -/
theorem primrec_toSymbol : Primrec (toSymbol (L := L) (M := M)) :=
  ((Primrec.fst.comp Primrec.subtype_val).comp Primrec.of_equiv).of_eq fun _ ↦ rfl

/-- The argument-list projection of function application data is primitive recursive. -/
theorem primrec_argsList : Primrec (argsList (L := L) (M := M)) :=
  ((Primrec.snd.comp Primrec.subtype_val).comp Primrec.of_equiv).of_eq fun _ ↦ rfl

/-- Decoding the code of a symbol/argument-list pair is exactly the guarded assembly
`ofSymbolArgs?`. -/
theorem decode_encode (p : L.FunctionSymbol × List M) :
    decode (α := FunctionApplicationData L M) (encode p) = ofSymbolArgs? p := by
  rw [decode_ofEquiv equivSubtype (encode p),
    show decode (α := { q : L.FunctionSymbol × List M // q.2.length = q.1.arity })
        (encode p) = Encodable.decodeSubtype (encode p) from rfl,
    Encodable.decodeSubtype, encodek, ofSymbolArgs?]
  by_cases h : p.2.length = p.1.arity
  · simp [h]
  · simp [h]

/-- The guarded assembly of function application data is primitive recursive. -/
theorem primrec_ofSymbolArgs? : Primrec (ofSymbolArgs? (L := L) (M := M)) :=
  (Primrec.decode.comp Primrec.encode).of_eq decode_encode

end Primcodable

end FunctionApplicationData

namespace RelationApplicationData

/-- The packaged symbol of relation application data. -/
def toSymbol (d : RelationApplicationData L M) : L.RelationSymbol := ⟨d.arity, d.symbol⟩

/-- The argument list of relation application data. -/
def argsList (d : RelationApplicationData L M) : List M := List.ofFn d.args

/-- Relation application data is a packaged symbol paired with an argument list of the
matching length. -/
def equivSubtype : RelationApplicationData L M ≃
    { p : L.RelationSymbol × List M // p.2.length = p.1.arity } where
  toFun d := ⟨(⟨d.arity, d.symbol⟩, List.ofFn d.args), by simp [RelationSymbol.arity]⟩
  invFun p := ⟨p.1.1.1, p.1.1.2, fun i ↦ p.1.2.get (Fin.cast p.2.symm i)⟩
  left_inv d := by
    rcases d with ⟨n, r, v⟩
    dsimp only
    congr 1
    funext i
    simp
  right_inv p := by
    rcases p with ⟨⟨⟨n, r⟩, l⟩, h⟩
    refine Subtype.ext (Prod.ext rfl ?_)
    exact List.ext_getElem (by simpa [RelationSymbol.arity] using h.symm) fun i h₁ h₂ ↦ by
      simp

/-- The uniform evaluation of relation application data in a structure. -/
def relMap [L.Structure M] (d : RelationApplicationData L M) : Prop :=
  Structure.RelMap d.symbol d.args

/-- Fixed-arity relation application data. -/
def ofFixed {n : ℕ} (r : L.Relations n) (v : Fin n → M) : RelationApplicationData L M :=
  ⟨n, r, v⟩

/-- Assemble relation application data from a packaged symbol and an argument list,
succeeding exactly when the list length matches the symbol's arity. -/
def ofSymbolArgs? (p : L.RelationSymbol × List M) :
    Option (RelationApplicationData L M) :=
  if h : p.2.length = p.1.arity then some (equivSubtype.symm ⟨p, h⟩) else none

theorem ofSymbolArgs?_of_length_eq (p : L.RelationSymbol × List M)
    (h : p.2.length = p.1.arity) :
    ofSymbolArgs? p = some (equivSubtype.symm ⟨p, h⟩) :=
  dif_pos h

theorem ofSymbolArgs?_of_length_ne (p : L.RelationSymbol × List M)
    (h : ¬p.2.length = p.1.arity) : ofSymbolArgs? p = none :=
  dif_neg h

/-- Evaluating the data assembled from a symbol and its argument list. -/
theorem relMap_equivSubtype_symm [L.Structure M] (p : L.RelationSymbol × List M)
    (h : p.2.length = p.1.arity) :
    (equivSubtype.symm ⟨p, h⟩ : RelationApplicationData L M).relMap ↔
      Structure.RelMap p.1.2 fun i ↦ p.2.get (Fin.cast h.symm i) :=
  Iff.rfl

section Primcodable

variable [Primcodable M] [L.EffectiveLanguage]

instance : Primcodable { p : L.RelationSymbol × List M // p.2.length = p.1.arity } :=
  Primcodable.subtype
    (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
      (primrec_relationSymbol_arity.comp Primrec.fst))

instance : Primcodable (RelationApplicationData L M) :=
  Primcodable.ofEquiv _ equivSubtype

/-- The symbol projection of relation application data is primitive recursive. -/
theorem primrec_toSymbol : Primrec (toSymbol (L := L) (M := M)) :=
  ((Primrec.fst.comp Primrec.subtype_val).comp Primrec.of_equiv).of_eq fun _ ↦ rfl

/-- The argument-list projection of relation application data is primitive recursive. -/
theorem primrec_argsList : Primrec (argsList (L := L) (M := M)) :=
  ((Primrec.snd.comp Primrec.subtype_val).comp Primrec.of_equiv).of_eq fun _ ↦ rfl

/-- Decoding the code of a symbol/argument-list pair is exactly the guarded assembly
`ofSymbolArgs?`. -/
theorem decode_encode (p : L.RelationSymbol × List M) :
    decode (α := RelationApplicationData L M) (encode p) = ofSymbolArgs? p := by
  rw [decode_ofEquiv equivSubtype (encode p),
    show decode (α := { q : L.RelationSymbol × List M // q.2.length = q.1.arity })
        (encode p) = Encodable.decodeSubtype (encode p) from rfl,
    Encodable.decodeSubtype, encodek, ofSymbolArgs?]
  by_cases h : p.2.length = p.1.arity
  · simp [h]
  · simp [h]

/-- The guarded assembly of relation application data is primitive recursive. -/
theorem primrec_ofSymbolArgs? : Primrec (ofSymbolArgs? (L := L) (M := M)) :=
  (Primrec.decode.comp Primrec.encode).of_eq decode_encode


end Primcodable

end RelationApplicationData


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
