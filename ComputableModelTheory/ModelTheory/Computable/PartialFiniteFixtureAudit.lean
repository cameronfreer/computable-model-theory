/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialFiniteChecker
import ComputableModelTheory.Util.AssertAxioms

/-!
# Attribution fixture for the Observation 2.7 checker

A **mixed** fixture — one unary function and one binary relation — designed so that a rejected
candidate can be attributed to a specific scan rather than merely observed to fail.

The carrier is `{0, 1}`, the unary function is constantly `0`, and the binary relation is
equality. The candidate under test is the **swap** of `0` and `1`.

The swap preserves and reflects equality, so the relation scan genuinely *accepts* it. But it
does not preserve the constant-zero function: `f(swap 0) = f(1) = 0`, while `swap (f 0) =
swap 0 = 1`. So the function scan is exactly where rejection occurs, and the gates below prove
both memberships positively — `true ∈ relationScanPart` beside `false ∈ functionScanPart` —
before any use of the headline checker theorem. A single `false` from the complete checker would
not discriminate.

Everything here is audit-local. It is a discriminating fixture, not a reusable abstraction.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

/-! ### Layer 1: the mixed language -/

/-- One unary function symbol. -/
inductive MixedFunctions : ℕ → Type
  | zero : MixedFunctions 1

/-- One binary relation symbol. -/
inductive MixedRelations : ℕ → Type
  | eq : MixedRelations 2

/-- The fixture language: a unary function and a binary relation. Both halves are populated,
which is what makes the fixture discriminating — a functions-only or relations-only language
could not attribute a rejection. -/
def mixedLang : Language := ⟨MixedFunctions, MixedRelations⟩

instance : IsEmpty (mixedLang.Functions 0) := ⟨fun f ↦ nomatch f⟩
instance (n : ℕ) : IsEmpty (mixedLang.Functions (n + 2)) := ⟨fun f ↦ nomatch f⟩
instance : IsEmpty (mixedLang.Relations 0) := ⟨fun r ↦ nomatch r⟩
instance : IsEmpty (mixedLang.Relations 1) := ⟨fun r ↦ nomatch r⟩
instance (n : ℕ) : IsEmpty (mixedLang.Relations (n + 3)) := ⟨fun r ↦ nomatch r⟩

/-- The language has a single function symbol. -/
def mixedFunctionSymbolEquiv : mixedLang.FunctionSymbol ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨1, MixedFunctions.zero⟩
  left_inv s := by rcases s with ⟨n, f⟩; cases f; rfl
  right_inv _ := rfl

/-- The language has a single relation symbol. -/
def mixedRelationSymbolEquiv : mixedLang.RelationSymbol ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨2, MixedRelations.eq⟩
  left_inv s := by rcases s with ⟨n, r⟩; cases r; rfl
  right_inv _ := rfl

instance : Primcodable mixedLang.FunctionSymbol :=
  Primcodable.ofEquiv _ mixedFunctionSymbolEquiv

instance : Primcodable mixedLang.RelationSymbol :=
  Primcodable.ofEquiv _ mixedRelationSymbolEquiv

instance : EffectiveLanguage mixedLang where
  primrec_functionArity :=
    (Primrec.const 1).of_eq fun s ↦ by rcases s with ⟨n, f⟩; cases f; rfl
  primrec_relationArity :=
    (Primrec.const 2).of_eq fun s ↦ by rcases s with ⟨n, r⟩; cases r; rfl

instance : EffectivelyFiniteLanguage mixedLang where
  functionSymbols := [⟨1, MixedFunctions.zero⟩]
  relationSymbols := [⟨2, MixedRelations.eq⟩]
  mem_functionSymbols s := by
    rcases s with ⟨n, f⟩; cases f; exact List.mem_singleton_self _
  mem_relationSymbols r := by
    rcases r with ⟨n, s⟩; cases s; exact List.mem_singleton_self _

/-! ### Layer 2: the two-element partial age

Carrier `{0, 1}` at every index, generators `[0, 1]`, the unary function constantly `0`, and the
binary relation equality. -/

/-- The fixture structure on `ℕ`: the unary symbol is constantly `0`, the binary symbol is
equality. -/
@[reducible] def mixedStructure : mixedLang.Structure ℕ where
  funMap | .zero => fun _ ↦ 0
  RelMap | .eq => fun v ↦ v 0 = v 1

section

attribute [local instance] mixedStructure

/-- Every function application evaluates to `0`: the only symbol is the constant-zero one. -/
theorem mixedStructure_funMap (d : FunctionApplicationData mixedLang ℕ) :
    @FunctionApplicationData.funMap mixedLang ℕ mixedStructure d = 0 := by
  match d with
  | ⟨1, .zero, v⟩ => rfl
  | ⟨0, f, _⟩ => exact isEmptyElim f
  | ⟨n + 2, f, _⟩ => exact isEmptyElim f

/-- Every relation application is an equality test on its two arguments. -/
theorem mixedStructure_relMap (d : RelationApplicationData mixedLang ℕ) :
    (@RelationApplicationData.relMap mixedLang ℕ mixedStructure d ↔
      d.argsList[0]! = d.argsList[1]!) := by
  match d with
  | ⟨2, .eq, v⟩ => exact Iff.rfl
  | ⟨0, r, _⟩ => exact isEmptyElim r
  | ⟨1, r, _⟩ => exact isEmptyElim r
  | ⟨n + 3, r, _⟩ => exact isEmptyElim r

/-- Term values over the generators `[0, 1]` land in `{0, 1}`: variables are generators, and the
only function symbol returns `0`. No general closure machinery is needed. -/
theorem mixedStructure_realize_mem (v : Fin 2 → ℕ) (hv : ∀ k, v k = 0 ∨ v k = 1)
    (T : mixedLang.Term (Fin 2)) :
    @Term.realize mixedLang ℕ mixedStructure _ v T = 0 ∨
      @Term.realize mixedLang ℕ mixedStructure _ v T = 1 := by
  induction T with
  | var k => exact hv k
  | @func n f ts _ =>
    match n, f with
    | 1, .zero => exact Or.inl rfl
    | 0, f => exact isEmptyElim f
    | n + 2, f => exact isEmptyElim f

end

section

variable {O : Set (ℕ →. ℕ)}

private theorem primrec_getBang (i : ℕ) : Primrec fun l : List ℕ ↦ l[i]! :=
  (Primrec.option_getD.comp
    (Primrec.list_getElem?.comp Primrec.id (Primrec.const i))
    (Primrec.const default)).of_eq fun _ ↦ List.getElem!_eq_getElem?_getD.symm

/-- The fixture family: the same two-element member at every index. -/
def mixedAge : PartialAgeIn O mixedLang where
  structureAt _ := mixedStructure
  enum? _ m := Option.some (m % 2)
  enum?_computableIn :=
    (Primrec.option_some.comp
      (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))).to_comp.computableIn
  gens _ := [0, 1]
  gens_computableIn := ComputableIn.const _
  funEval _ _ := Part.some 0
  funEval_recursiveIn := (Primrec.const 0).to_comp.computableIn
  funEval_correct := fun _ d _ ↦ by
    rw [mixedStructure_funMap d]
    exact Part.mem_some 0
  relEval _ d := Part.some (d.argsList[0]! == d.argsList[1]!)
  relEval_recursiveIn :=
    (((Primrec.beq (α := ℕ)).comp
      ((primrec_getBang 0).comp
        (RelationApplicationData.primrec_argsList.comp Primrec.snd))
      ((primrec_getBang 1).comp
        (RelationApplicationData.primrec_argsList.comp Primrec.snd)))).to_comp.computableIn
  relEval_correct := fun _ d _ ↦
    ⟨_, Part.mem_some _, by rw [beq_iff_eq]; exact (mixedStructure_relMap d).symm⟩
  generates := fun _ x ↦ by
    constructor
    · rintro ⟨m, hm⟩
      have hx : x = m % 2 := (Option.some_inj.1 hm).symm
      have h2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
      rcases h2 with h | h
      · exact ⟨Term.var ⟨0, by simp⟩, by rw [hx, h]; rfl⟩
      · exact ⟨Term.var ⟨1, by simp⟩, by rw [hx, h]; rfl⟩
    · rintro ⟨T, rfl⟩
      have hv : ∀ k : Fin ([0, 1] : Tuple ℕ).length,
          (Tuple.view ([0, 1] : Tuple ℕ)) k = 0 ∨ (Tuple.view ([0, 1] : Tuple ℕ)) k = 1 := by
        rintro ⟨k, hk⟩
        simp only [List.length_cons, List.length_nil] at hk
        match k, hk with
        | 0, _ => exact Or.inl rfl
        | 1, _ => exact Or.inr rfl
      rcases mixedStructure_realize_mem _ hv T with h | h
      · exact ⟨0, by rw [h]⟩
      · exact ⟨1, by rw [h]⟩

/-- The exact carrier certificate: `[0, 1]` at every index. -/
def mixedCarriers : ExactFiniteCarriers (mixedAge (O := O)) where
  carrier _ := [0, 1]
  carrier_computableIn := ComputableIn.const _
  mem_carrier_iff := fun i x ↦ by
    constructor
    · intro hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨0, rfl⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨1, rfl⟩
        · exact absurd hx (by simp)
    · rintro ⟨m, hm⟩
      have hx : x = m % 2 := (Option.some_inj.1 hm).symm
      have h2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
      rcases h2 with h | h
      · rw [hx, h]; simp
      · rw [hx, h]; simp

@[simp]
theorem mixedCarriers_support (i : ℕ) : (mixedCarriers (O := O)).support i = [0, 1] := rfl

end

end FirstOrder.Language
