/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.OrbitIsolation
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: first-order isolation from automorphism orbits

Outside the root import spine; CI checks it through `scripts/run-audit-modules.sh`, and with
warnings as errors through `scripts/check-classical-layer.sh`.

* **Isolation is entailment over every model of the theory**, and transfers to a realizer in an
  independent universe with no cardinality bound (`test_realize_iff`).
* **The type-space singleton**: an isolating formula singles out the tuple's type among *all*
  complete types, not merely among types realized in the structure
  (`test_typesWith_eq_singleton`).
* **No countability, no relational restriction**: the orbit-formula theorems carry neither
  (`test_isolatesTuple_of_orbit_formula`, `test_isAtomic_of_orbit_formulas`).
* **A discharged fixture with a function symbol**: `Unit` with a unary function supplies orbit
  formulas, hence is atomic over its complete theory (`test_unit_isAtomic`), including the empty
  tuple (`test_unit_isolates_empty`) and a repeated coordinate, where the type-space singleton is
  derived, not assumed (`test_unit_typesWith_repeated`).
* **Standard axioms** for every declaration of the production module
  (`#assert_module_standard_axioms`) and for the regression rows.
* **Import isolation**: the production module's only import besides `Init` is
  `Mathlib.ModelTheory.Types`, and its transitive closure contains no module of this library or of
  `InfinitaryLogic`.
-/

universe u v w w'

open FirstOrder Language

namespace FirstOrder.Language

/-- A formula universally true in `M` is entailed by its complete theory; no countability. -/
theorem test_models_formula_of_forall_realize {L : Language.{u, v}} {M : Type w} [L.Structure M]
    {n : ℕ} (ψ : L.Formula (Fin n)) (h : ∀ a : Fin n → M, ψ.Realize a) :
    L.completeTheory M ⊨ᵇ ψ :=
  models_formula_of_forall_realize ψ h

/-- Isolation transfers to an independent target universe, for arbitrary first-order formulas. -/
theorem test_realize_iff {L : Language.{1, 2}} {T : L.Theory} {M : Type 1} {N : Type 3}
    [L.Structure M] [L.Structure N] [Nonempty N] [N ⊨ T]
    {φ : L.Formula (Fin 2)} {a : Fin 2 → M} {b : Fin 2 → N}
    (h : IsolatesTuple T φ a) (hb : φ.Realize b) (ψ : L.Formula (Fin 2)) :
    ψ.Realize b ↔ ψ.Realize a :=
  h.realize_iff hb ψ

/-- The type-space singleton, over all complete types of `T`. -/
theorem test_typesWith_eq_singleton {L : Language.{u, v}} {T : L.Theory} {M : Type w}
    [L.Structure M] [Nonempty M] [M ⊨ T] {n : ℕ} {φ : L.Formula (Fin n)} {a : Fin n → M}
    (h : IsolatesTuple T φ a) :
    T.typesWith (Formula.equivSentence φ) = {T.typeOf a} :=
  h.typesWith_eq_singleton

/-- An orbit formula isolates, with no countability of the language or the structure. -/
theorem test_isolatesTuple_of_orbit_formula {L : Language.{u, v}} {M : Type w} [L.Structure M]
    [Nonempty M] {n : ℕ} (a : Fin n → M) (φ : L.Formula (Fin n))
    (horbit : ∀ b : Fin n → M, φ.Realize b ↔ ∃ e : M ≃[L] M, ∀ i, e (a i) = b i) :
    IsolatesTuple (L.completeTheory M) φ a :=
  isolatesTuple_of_orbit_formula a φ horbit

/-- Orbit formulas for all finite tuples give atomicity over the structure's own theory. -/
theorem test_isAtomic_of_orbit_formulas {L : Language.{u, v}} {M : Type w} [L.Structure M]
    [Nonempty M]
    (horbit : ∀ (n : ℕ) (a : Fin n → M), ∃ φ : L.Formula (Fin n),
      ∀ b : Fin n → M, φ.Realize b ↔ ∃ e : M ≃[L] M, ∀ i, e (a i) = b i) :
    IsAtomic (L.completeTheory M) M :=
  isAtomic_of_orbit_formulas horbit

/-! ### A discharged fixture with a function symbol -/

/-- One unary function symbol. -/
inductive UnaryFun : ℕ → Type
  | op : UnaryFun 1

/-- A language with one unary function symbol and no relation symbols. -/
def unaryLang : Language.{0, 0} :=
  ⟨UnaryFun, fun _ ↦ Empty⟩

instance : unaryLang.Structure Unit where
  funMap _ _ := ()
  RelMap r := Empty.elim r

/-- `⊤` defines the orbit of every tuple of `Unit`. -/
theorem unit_orbit_formula (n : ℕ) (a : Fin n → Unit) :
    ∃ φ : unaryLang.Formula (Fin n),
      ∀ b : Fin n → Unit, φ.Realize b ↔ ∃ e : Unit ≃[unaryLang] Unit, ∀ i, e (a i) = b i :=
  ⟨⊤, fun _ ↦ iff_of_true (BoundedFormula.realize_top.2 trivial)
    ⟨Language.Equiv.refl unaryLang Unit, fun _ ↦ Subsingleton.elim _ _⟩⟩

theorem test_unit_isAtomic : IsAtomic (unaryLang.completeTheory Unit) Unit :=
  isAtomic_of_orbit_formulas unit_orbit_formula

/-- The empty tuple is isolated. -/
theorem test_unit_isolates_empty :
    ∃ φ : unaryLang.Formula (Fin 0),
      IsolatesTuple (unaryLang.completeTheory Unit) φ (Fin.elim0 : Fin 0 → Unit) :=
  test_unit_isAtomic 0 _

/-- A repeated coordinate: its isolating formula singles out its type among all complete types. -/
theorem test_unit_typesWith_repeated :
    ∃ φ : unaryLang.Formula (Fin 2),
      (unaryLang.completeTheory Unit).typesWith (Formula.equivSentence φ) =
        {(unaryLang.completeTheory Unit).typeOf ![(), ()]} := by
  obtain ⟨φ, hφ⟩ := test_unit_isAtomic 2 ![(), ()]
  exact ⟨φ, hφ.typesWith_eq_singleton⟩

end FirstOrder.Language

/-! ### Import isolation -/

-- The production module imports exactly `Mathlib.ModelTheory.Types`, and nothing in its transitive
-- import closure belongs to this library or to `InfinitaryLogic`.
open Lean in
run_cmd do
  let env ← getEnv
  let target := `ComputableModelTheory.ModelTheory.OrbitIsolation
  let some idx := env.getModuleIdx? target | throwError "{target} is not imported"
  let direct := (env.header.moduleData[idx.toNat]!).imports.map (·.module)
  unless direct.filter (· != `Init) == #[`Mathlib.ModelTheory.Types] do
    throwError "unexpected direct imports of {target}: {direct}"
  let mut seen : NameSet := {}
  let mut todo : Array Name := direct
  while h : todo.size > 0 do
    let m := todo.back
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    if (`ComputableModelTheory).isPrefixOf m || (`InfinitaryLogic).isPrefixOf m then
      throwError "{target} transitively imports {m}"
    if let some j := env.getModuleIdx? m then
      todo := todo ++ (env.header.moduleData[j.toNat]!).imports.map (·.module)

#assert_standard_axioms FirstOrder.Language.test_models_formula_of_forall_realize
#assert_standard_axioms FirstOrder.Language.test_realize_iff
#assert_standard_axioms FirstOrder.Language.test_typesWith_eq_singleton
#assert_standard_axioms FirstOrder.Language.test_isolatesTuple_of_orbit_formula
#assert_standard_axioms FirstOrder.Language.test_isAtomic_of_orbit_formulas
#assert_standard_axioms FirstOrder.Language.test_unit_isAtomic
#assert_standard_axioms FirstOrder.Language.test_unit_isolates_empty
#assert_standard_axioms FirstOrder.Language.test_unit_typesWith_repeated

#assert_module_standard_axioms ComputableModelTheory.ModelTheory.OrbitIsolation
