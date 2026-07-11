/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.TermEvaluation
import ComputableModelTheory.ModelTheory.TupleClosure

/-!
# A computable structure with a function symbol

The language of one unary function symbol, interpreted on `ℕ` as the successor: a
minimal computable structure exercising the function half of the uniform contracts and
the value-stack branch of term evaluation (the graph example has no function symbols).
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

/-- The functions of the successor language: a single unary symbol. -/
inductive SuccFunctions : ℕ → Type
  | succ : SuccFunctions 1

/-- The language with one unary function symbol and no relations. -/
def succLang : Language :=
  ⟨SuccFunctions, fun _ ↦ Empty⟩

instance : IsEmpty (succLang.Functions 0) := ⟨fun f ↦ nomatch f⟩

instance (n : ℕ) : IsEmpty (succLang.Functions (n + 2)) := ⟨fun f ↦ nomatch f⟩

instance (n : ℕ) : IsEmpty (succLang.Relations n) := ⟨fun r ↦ r.elim⟩

instance : IsEmpty succLang.RelationSymbol := ⟨fun s ↦ s.2.elim⟩

/-- The successor language has a single function symbol. -/
def succFunctionSymbolEquiv : succLang.FunctionSymbol ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨1, SuccFunctions.succ⟩
  left_inv s := by rcases s with ⟨n, f⟩; cases f; rfl
  right_inv _ := rfl

instance : Primcodable succLang.FunctionSymbol :=
  Primcodable.ofEquiv _ succFunctionSymbolEquiv

instance : Primcodable succLang.RelationSymbol :=
  Primcodable.ofEquiv Empty (Equiv.equivEmpty _)

/-- The successor language is effective. -/
instance : EffectiveLanguage succLang where
  primrec_functionArity :=
    (Primrec.const 1).of_eq fun s ↦ by rcases s with ⟨n, f⟩; cases f; rfl
  primrec_relationArity := Primrec.of_isEmpty _

/-- The successor structure on `ℕ`. -/
@[reducible] def succStructure : succLang.Structure ℕ where
  funMap | .succ => fun v ↦ v 0 + 1
  RelMap := fun r _ ↦ r.elim

section

attribute [local instance] succStructure

instance : IsEmpty (RelationApplicationData succLang ℕ) :=
  ⟨fun d ↦ isEmptyElim d.symbol⟩

/-- The successor structure is computable in any oracle set: the uniform function
interpretation is the successor of the head of the argument list. -/
instance succ_isComputable {O : Set (ℕ →. ℕ)} : IsComputableStructureIn O succLang where
  funMap_computableIn := by
    have h0 : Primrec fun l : List ℕ ↦ l[0]! :=
      (Primrec.option_getD.comp
        (Primrec.list_getElem?.comp Primrec.id (Primrec.const 0))
        (Primrec.const default)).of_eq fun _ ↦ List.getElem!_eq_getElem?_getD.symm
    have hb : Primrec fun d : FunctionApplicationData succLang ℕ ↦
        d.argsList[0]! + 1 :=
      Primrec.succ.comp (h0.comp FunctionApplicationData.primrec_argsList)
    refine hb.to_comp.computableIn.of_eq fun d ↦ ?_
    match d with
    | ⟨1, .succ, v⟩ => rfl
    | ⟨0, f, _⟩ => exact isEmptyElim f
    | ⟨n + 2, f, _⟩ => exact isEmptyElim f
  relMap_computablePredIn :=
    ⟨fun d ↦ isEmptyElim d, (Computable.of_isEmpty _).computableIn⟩

/-- The list tuple `[0]` generates the successor structure on `ℕ`: every natural
number is an iterated-successor term value. -/
theorem succ_tuple_generates : Tuple.Generates succLang ([0] : Tuple ℕ) := by
  rw [Tuple.generates_iff]
  intro x
  induction x with
  | zero => exact ⟨Term.var ⟨0, by simp⟩, rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨Term.func SuccFunctions.succ ![t], ?_⟩
    rw [Term.realize_func]
    show (![t] 0).realize (Tuple.view ([0] : Tuple ℕ)) + 1 = n + 1
    rw [Matrix.cons_val_zero, ht]

end

end FirstOrder.Language
