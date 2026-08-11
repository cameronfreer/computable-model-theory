/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.TermEvaluation
import ComputableModelTheory.ModelTheory.TupleClosure

/-!
# A computable structure with a constant symbol

The language of one constant, interpreted on `ℕ` as `7`. It occupies the third corner of the
example space alongside `GraphExample` (relations, no functions) and `SuccExample` (a unary
function): here the **empty tuple generates a nonempty substructure**, namely `{7}`.

That is the property nothing else in the example set has, and several boundaries need it — a
constant-free language cannot exhibit a nonempty member with no recorded generators, and the
all-ℕ fragment cannot exhibit a proper finite carrier at all.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

/-- The functions of the constant language: a single constant symbol. -/
inductive ConstFunctions : ℕ → Type
  | c : ConstFunctions 0

/-- The language with one constant symbol and no relations. -/
def constLang : Language :=
  ⟨ConstFunctions, fun _ ↦ Empty⟩

instance (n : ℕ) : IsEmpty (constLang.Functions (n + 1)) := ⟨fun f ↦ nomatch f⟩

instance (n : ℕ) : IsEmpty (constLang.Relations n) := ⟨fun r ↦ r.elim⟩

instance : IsEmpty constLang.RelationSymbol := ⟨fun s ↦ s.2.elim⟩

/-- The constant language has a single function symbol. -/
def constFunctionSymbolEquiv : constLang.FunctionSymbol ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨0, ConstFunctions.c⟩
  left_inv s := by rcases s with ⟨n, f⟩; cases f; rfl
  right_inv _ := rfl

instance : Primcodable constLang.FunctionSymbol :=
  Primcodable.ofEquiv _ constFunctionSymbolEquiv

instance : Primcodable constLang.RelationSymbol :=
  Primcodable.ofEquiv Empty (Equiv.equivEmpty _)

instance : EffectiveLanguage constLang where
  primrec_functionArity :=
    (Primrec.const 0).of_eq fun s ↦ by rcases s with ⟨n, f⟩; cases f; rfl
  primrec_relationArity := Primrec.of_isEmpty _

/-- The constant structure on `ℕ`: the constant is `7`. -/
@[reducible] def constStructure : constLang.Structure ℕ where
  funMap | .c => fun _ ↦ 7
  RelMap := fun r _ ↦ r.elim

instance : IsEmpty (RelationApplicationData constLang ℕ) :=
  ⟨fun d ↦ isEmptyElim d.symbol⟩

theorem constIsComputable {O : Set (ℕ →. ℕ)} :
    @IsComputableStructureIn O constLang _ constStructure :=
  @IsComputableStructureIn.mk O constLang _ constStructure
    ((ComputableIn.const 7).of_eq fun d ↦
      match d with
      | ⟨0, .c, _⟩ => rfl
      | ⟨_ + 1, f, _⟩ => isEmptyElim f)
    ⟨fun d ↦ isEmptyElim d, (Computable.of_isEmpty _).computableIn⟩

/-- **Every term realizes to `7`**, whatever the environment — there are no variables reachable
except through the environment, and the only symbol is the constant. This is what collapses every
member of a constant-language family to the singleton carrier. -/
theorem constStructure_realize_eq_seven {n : ℕ} (v : Fin n → ℕ) (hv : ∀ k, v k = 7)
    (T : constLang.Term (Fin n)) :
    @Term.realize constLang ℕ constStructure _ v T = 7 := by
  induction T with
  | var k => exact hv k
  | @func m f ts _ =>
    match m, f with
    | 0, .c => rfl

end FirstOrder.Language
