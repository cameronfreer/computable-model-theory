/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.TupleReindex
import ComputableModelTheory.ModelTheory.Computable.SuccExample
import ComputableModelTheory.ModelTheory.Computable.GraphExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for tuple re-indexing

Named acceptance tests for the Theorem 2.8 construction core, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it via
`scripts/run-audit-modules.sh`.

Abstract gates: the all-tuple enumeration hits every tuple including the empty one;
the possibly-empty embedding preserves domains; every original member reappears with
**no** hypothesis on its recorded generators; and the nonempty-layer specialization
agrees with the full construction.

The three concrete fixtures are chosen to expose exactly the boundaries a successor
test alone cannot:

* **infinite generated closure** — `⟨[5]⟩` in the successor structure is
  `{5, 6, 7, …}`: infinite, with `4` outside — no finite-carrier search can
  implement this;
* **empty generator, constant language** — over a language with one constant
  interpreted as `7`, the empty tuple generates the **nonempty** substructure `{7}`;
* **empty generator, constant-free relational language** — over the graph language,
  the empty tuple generates the **empty** substructure, representable only at the
  possibly-empty layer.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

section AbstractGates

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- Gate: the all-tuple enumeration is surjective — including the empty tuple — and
computable. -/
theorem test_allTupleFor (t : Tuple ℕ) :
    (∃ e, allTupleFor e = t) ∧ (∃ e, allTupleFor e = ([] : Tuple ℕ)) ∧
      ComputableIn O allTupleFor :=
  ⟨allTupleFor_surjective t, allTupleFor_surjective [], allTupleFor_computableIn⟩

/-- Gate: the possibly-empty embedding and recovery preserve domains. -/
theorem test_partial_layer (P : CePresentationIn O L)
    (Q : PartialCePresentationIn O L) {m₀ x₀ : ℕ} (h₀ : Q.enum? m₀ = Option.some x₀) :
    P.toPartial.domain = P.domain ∧ (Q.toCePresentation h₀).domain = Q.domain :=
  ⟨P.toPartial_domain, Q.toCePresentation_domain h₀⟩

/-- Gate: every original member reappears among the generated presentations, with no
hypothesis on its recorded generator tuple. -/
theorem test_generatedAt_gens (K : ComputableAgeIn O L) (i : ℕ) :
    (K.generatedAt i (K.gens i)).domain = Set.univ :=
  K.generatedAt_domain_of_gens i

/-- Gate: the nonempty-layer specialization agrees with the full construction. -/
theorem test_generated_agreement (K : ComputableAgeIn O L) (i : ℕ) (t : Tuple ℕ)
    (ht : t ≠ []) :
    (K.generatedPresentation i t ht).toPartial.domain = (K.generatedAt i t).domain :=
  K.generatedPresentation_toPartial_domain i t ht

end AbstractGates

section SuccessorFixture

variable (O : Set (ℕ →. ℕ))

/-- The successor structure, bundled. -/
noncomputable def succBundle : ComputableStructureIn O succLang :=
  { inst := succStructure, isComputable := succ_isComputable }

/-- The `n`-fold successor term over one variable. -/
def succIterTerm : ℕ → succLang.Term (Fin 1)
  | 0 => Term.var 0
  | n + 1 => Term.func SuccFunctions.succ fun _ ↦ succIterTerm n

private theorem succIterTerm_realize (n : ℕ) :
    @Term.realize succLang ℕ succStructure _ (Tuple.view [5]) (succIterTerm n)
      = 5 + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show @Term.realize succLang ℕ succStructure _ (Tuple.view [5])
      (succIterTerm n) + 1 = 5 + (n + 1)
    omega

private theorem succ_realize_ge (T : succLang.Term (Fin (List.length [5]))) :
    5 ≤ @Term.realize succLang ℕ succStructure _ (Tuple.view [5]) T := by
  induction T with
  | var v =>
    match v with
    | ⟨0, _⟩ => exact le_refl 5
  | func f ts ih =>
    cases f with
    | succ => exact le_trans (ih 0) (Nat.le_succ _)

/-- Concrete gate: the generated closure of `[5]` in the successor structure is
infinite — the fixture that rules out finite-carrier search. -/
theorem test_succ_generated_infinite :
    ((succBundle O).generatedPresentationOf [5]).domain.Infinite := by
  have hd := (succBundle O).generatedPresentationOf_domain ([5] : Tuple ℕ)
  rw [hd]
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ ↦ 5 + n) (fun a b h ↦ by simp only [] at h; omega) fun n ↦ ?_
  exact ⟨succIterTerm n, (succIterTerm_realize n).symm⟩

/-- Concrete gate: the generated closure of `[5]` omits `4` — the closure is a
proper c.e. subset. -/
theorem test_succ_generated_not_mem :
    (4 : ℕ) ∉ ((succBundle O).generatedPresentationOf [5]).domain := by
  have hd := (succBundle O).generatedPresentationOf_domain ([5] : Tuple ℕ)
  rw [hd]
  rintro ⟨T, hT⟩
  have hT' : (4 : ℕ) = @Term.realize succLang ℕ succStructure _ (Tuple.view [5]) T :=
    hT
  have h5 := succ_realize_ge T
  omega

end SuccessorFixture

/-! ### The constant language: one constant, interpreted as `7` -/

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

/-- The constant structure on ℕ: the constant is `7`. -/
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

section ConstantFixture

variable (O : Set (ℕ →. ℕ))

/-- The constant structure, bundled. -/
noncomputable def constBundle : ComputableStructureIn O constLang :=
  { inst := constStructure, isComputable := constIsComputable }

/-- Concrete gate: over a constant language, the **empty** tuple generates a
**nonempty** substructure — its domain is exactly `{7}`. The nonempty-tuple layer
cannot even state this. -/
theorem test_const_empty_tuple_domain :
    ((constBundle O).generatedPresentationOf ([] : Tuple ℕ)).domain = {7} := by
  rw [(constBundle O).generatedPresentationOf_domain ([] : Tuple ℕ)]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨T, rfl⟩
    induction T with
    | var v => exact v.elim0
    | func f ts ih =>
      cases f with
      | c => rfl
  · rintro rfl
    exact ⟨Term.func ConstFunctions.c fun k ↦ k.elim0, rfl⟩

end ConstantFixture

section RelationalFixture

variable (O : Set (ℕ →. ℕ))

/-- The path graph, bundled. -/
noncomputable def pathGraphBundle : ComputableStructureIn O Language.graph :=
  { inst := pathGraphStructure, isComputable := pathGraph_isComputable }

instance : IsEmpty (Language.graph.Term (Fin 0)) :=
  ⟨fun T ↦ by
    induction T with
    | var v => exact v.elim0
    | func f _ _ => exact isEmptyElim f⟩

/-- Concrete gate: over a constant-free relational language, the empty tuple
generates the **empty** substructure — representable only at the possibly-empty
layer. -/
theorem test_graph_empty_tuple_domain :
    ((pathGraphBundle O).generatedPresentationOf ([] : Tuple ℕ)).domain = ∅ := by
  rw [(pathGraphBundle O).generatedPresentationOf_domain ([] : Tuple ℕ)]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨T, -⟩
  exact isEmptyElim (show Language.graph.Term (Fin 0) from T)

end RelationalFixture

end FirstOrder.Language

open FirstOrder.Language

#assert_standard_axioms test_allTupleFor
#assert_standard_axioms test_partial_layer
#assert_standard_axioms test_generatedAt_gens
#assert_standard_axioms test_generated_agreement
#assert_standard_axioms test_succ_generated_infinite
#assert_standard_axioms test_succ_generated_not_mem
#assert_standard_axioms test_const_empty_tuple_domain
#assert_standard_axioms test_graph_empty_tuple_domain
