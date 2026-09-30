/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.CountablePrime
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: countable atomic structures are prime

Outside the root import spine; CI checks it through `scripts/run-audit-modules.sh`, and with
warnings as errors through `scripts/check-classical-layer.sh`.

* **Independent universes, no countability of the language or the target, function symbols
  allowed**: `test_exists_elementaryEmbedding` over `Language.{2, 3}`, source `Type 1`, target
  `Type 4`. No `Nonempty` premise on the target: it is derived from modelhood.
* **The one-sided extension** needs only that the target models the source's complete theory
  (`test_exists_extension`), no homogeneity.
* **The whole route, discharged, on a finite nonempty source with a function symbol**: `Bool` with
  negation as a unary function. Explicit orbit formulas (`negOrbit`, which separate orbits:
  `test_negOrbit_separates`) give atomicity (`test_bool_isAtomic`), the type-space singleton for
  every tuple, the empty tuple and repeated coordinates included (`test_bool_typesWith`,
  `test_bool_typesWith_repeated`, `test_bool_typesWith_empty`), and an elementary embedding into
  every model of the theory in another universe (`test_bool_prime`). The source is finite, so the
  enumeration the construction uses necessarily repeats.
* **Standard axioms** for every declaration of the production module
  (`#assert_module_standard_axioms`) and for the regression rows.
* **Import isolation**: the production module imports only `OrbitIsolation` and
  `Mathlib.Basic.Countable.Basic` besides `Init`, and its transitive closure contains no other
  module of this library and no module of `InfinitaryLogic`.
-/

universe u v w w'

open FirstOrder Language

namespace FirstOrder.Language

/-- The endpoint in independent universes, with function symbols and no countability of the
language or the target. -/
theorem test_exists_elementaryEmbedding {L : Language.{2, 3}} {M : Type 1} {N : Type 4}
    [L.Structure M] [L.Structure N] [Countable M] [Nonempty M]
    [N ⊨ L.completeTheory M] (h : IsAtomic (L.completeTheory M) M) :
    Nonempty (M ↪ₑ[L] N) :=
  exists_elementaryEmbedding_of_countable_atomic h

/-- The one-sided extension step: the target only models the source's complete theory. -/
theorem test_exists_extension {L : Language.{u, v}} {M : Type w} {N : Type w'}
    [L.Structure M] [L.Structure N] [Nonempty N] [N ⊨ L.completeTheory M]
    (hatomic : IsAtomic (L.completeTheory M) M) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : SameFormulaType (L := L) a b) (m : M) :
    ∃ z : N, SameFormulaType (L := L) (Fin.snoc a m) (Fin.snoc b z) :=
  h.exists_extension hatomic m

/-! ### The whole route on `Bool` with negation -/

/-- One unary function symbol. -/
inductive NegFun : ℕ → Type
  | neg : NegFun 1

/-- A language with one unary function symbol and no relation symbols. -/
def negLang : Language.{0, 0} :=
  ⟨NegFun, fun _ ↦ Empty⟩

/-- The symbol interpreted as Boolean negation. -/
def negMap : ∀ {n : ℕ}, NegFun n → (Fin n → Bool) → Bool
  | _, .neg, x => !(x 0)

instance : negLang.Structure Bool where
  funMap f x := negMap f x
  RelMap r := Empty.elim r

@[simp] theorem funMap_neg (x : Fin 1 → Bool) :
    Structure.funMap (L := negLang) (NegFun.neg : negLang.Functions 1) x = !(x 0) :=
  rfl

/-- Negation is an automorphism. -/
def negEquiv : Bool ≃[negLang] Bool where
  toEquiv := ⟨not, not, Bool.not_not, Bool.not_not⟩
  map_fun' := by
    rintro _ ⟨⟩ x
    rfl
  map_rel' := fun r ↦ Empty.elim r

/-- The orbit formula of `a`: coordinates equal where `a`'s are, and negations of each other
where `a`'s differ. -/
noncomputable def negOrbit {n : ℕ} (a : Fin n → Bool) : negLang.Formula (Fin n) :=
  Formula.iInf fun p : Fin n × Fin n ↦
    if a p.1 = a p.2 then (Term.var p.1).equal (Term.var p.2)
    else (Term.var p.1).equal (Functions.apply₁ (NegFun.neg : negLang.Functions 1) (Term.var p.2))

theorem realize_negOrbit {n : ℕ} (a b : Fin n → Bool) :
    (negOrbit a).Realize b ↔ ∀ i j, if a i = a j then b i = b j else b i = !(b j) := by
  simp only [negOrbit, Formula.realize_iInf, Prod.forall]
  refine forall₂_congr fun i j ↦ ?_
  split_ifs
  · simp [Formula.realize_equal]
  · exact Iff.rfl

/-- `negOrbit a` defines exactly the automorphism orbit of `a`. -/
theorem negOrbit_spec {n : ℕ} (a b : Fin n → Bool) :
    (negOrbit a).Realize b ↔ ∃ e : Bool ≃[negLang] Bool, ∀ i, e (a i) = b i := by
  constructor
  · intro h
    rw [realize_negOrbit] at h
    by_cases hall : ∀ i, a i = b i
    · exact ⟨Language.Equiv.refl _ _, hall⟩
    · obtain ⟨k, hk⟩ := not_forall.mp hall
      refine ⟨negEquiv, fun i ↦ ?_⟩
      have hik := h i k
      show (!a i) = b i
      generalize a i = x at hik ⊢
      generalize a k = y at hik hk
      generalize b i = z at hik ⊢
      generalize b k = t at hik hk
      cases x <;> cases y <;> cases z <;> cases t <;> simp_all
  · rintro ⟨e, he⟩
    have hb : ⇑e ∘ a = b := funext he
    rw [← hb, StrongHomClass.realize_formula, realize_negOrbit]
    intro i j
    split_ifs with h
    · exact h
    · generalize a i = x at h ⊢
      generalize a j = y at h ⊢
      cases x <;> cases y <;> simp_all

/-- The orbit formulas are not trivial: `negOrbit ![true, true]` rejects `![true, false]`. -/
theorem test_negOrbit_separates : ¬ (negOrbit ![true, true]).Realize ![true, false] := by
  rw [realize_negOrbit]
  intro h
  simpa using h 0 1

theorem test_bool_isAtomic : IsAtomic (negLang.completeTheory Bool) Bool :=
  isAtomic_of_orbit_formulas fun _ a ↦ ⟨negOrbit a, negOrbit_spec a⟩

/-- The type-space singleton for every tuple, derived from the orbit formula. -/
theorem test_bool_typesWith {n : ℕ} (a : Fin n → Bool) :
    (negLang.completeTheory Bool).typesWith (Formula.equivSentence (negOrbit a)) =
      {(negLang.completeTheory Bool).typeOf a} :=
  (isolatesTuple_of_orbit_formula a _ (negOrbit_spec a)).typesWith_eq_singleton

theorem test_bool_typesWith_repeated :
    (negLang.completeTheory Bool).typesWith (Formula.equivSentence (negOrbit ![true, true])) =
      {(negLang.completeTheory Bool).typeOf ![true, true]} :=
  test_bool_typesWith _

theorem test_bool_typesWith_empty :
    (negLang.completeTheory Bool).typesWith
        (Formula.equivSentence (negOrbit (Fin.elim0 : Fin 0 → Bool))) =
      {(negLang.completeTheory Bool).typeOf (Fin.elim0 : Fin 0 → Bool)} :=
  test_bool_typesWith _

/-- **The whole route**: the finite source embeds elementarily into every model of its complete
theory, here in `Type 4`. -/
theorem test_bool_prime (N : Type 4) [negLang.Structure N] [N ⊨ negLang.completeTheory Bool] :
    Nonempty (Bool ↪ₑ[negLang] N) :=
  exists_elementaryEmbedding_of_countable_atomic test_bool_isAtomic

end FirstOrder.Language

/-! ### Import isolation -/

-- The production module imports exactly `OrbitIsolation` and `Mathlib.Basic.Countable.Basic`, and
-- nothing else in its transitive import closure belongs to this library or to `InfinitaryLogic`.
open Lean in
run_cmd do
  let env ← getEnv
  let target := `ComputableModelTheory.ModelTheory.CountablePrime
  let sibling := `ComputableModelTheory.ModelTheory.OrbitIsolation
  let some idx := env.getModuleIdx? target | throwError "{target} is not imported"
  let direct := (env.header.moduleData[idx.toNat]!).imports.map (·.module)
  unless direct.filter (· != `Init) == #[sibling, `Mathlib.Basic.Countable.Basic] do
    throwError "unexpected direct imports of {target}: {direct}"
  let mut seen : NameSet := {}
  let mut todo : Array Name := direct
  while h : todo.size > 0 do
    let m := todo.back
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    if m != sibling &&
        ((`ComputableModelTheory).isPrefixOf m || (`InfinitaryLogic).isPrefixOf m) then
      throwError "{target} transitively imports {m}"
    if let some j := env.getModuleIdx? m then
      todo := todo ++ (env.header.moduleData[j.toNat]!).imports.map (·.module)

#assert_standard_axioms FirstOrder.Language.test_exists_elementaryEmbedding
#assert_standard_axioms FirstOrder.Language.test_exists_extension
#assert_standard_axioms FirstOrder.Language.negOrbit_spec
#assert_standard_axioms FirstOrder.Language.test_negOrbit_separates
#assert_standard_axioms FirstOrder.Language.test_bool_isAtomic
#assert_standard_axioms FirstOrder.Language.test_bool_typesWith
#assert_standard_axioms FirstOrder.Language.test_bool_typesWith_repeated
#assert_standard_axioms FirstOrder.Language.test_bool_typesWith_empty
#assert_standard_axioms FirstOrder.Language.test_bool_prime

#assert_module_standard_axioms ComputableModelTheory.ModelTheory.CountablePrime
