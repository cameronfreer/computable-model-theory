/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.ExtensionRichFamily
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: extension-rich families of substructures

Outside the root import spine; CI checks it through `scripts/run-audit-modules.sh`, and with
warnings as errors through `scripts/check-classical-layer.sh`.

1. **Independent universes, weak hypotheses.** `test_isExtensionPair` restates the core theorem
   over `Language.{u, v}`, `M : Type w`, `I : Type z`, with no countability, no `Nonempty M`, and
   nothing effective.
2. **The converse's boundary.** `test_extensionRich_of_isUltrahomogeneous` takes no countable
   generation.
3. **An empty index is not cofinal**: `test_empty_index_not_cofinal`, from the finitely generated
   bottom substructure.
4. **An empty carrier is supported**: `test_empty_carrier`, a stage family indexed by `Unit` on
   `Empty` in the empty language, cofinal and extension rich, hence an extension pair.
5. **Directed exhaustion needs an inhabited index**: `test_directed_needs_index` — on the empty
   carrier, the empty family is directed and covers every point, yet is not cofinal.
6. **The age-union theorem assumes only cofinality**: `test_age_eq_iUnion`.
7. **Standard axioms** for every declaration of the production module
   (`#assert_module_standard_axioms`, which scans by defining module), and for the regression rows.
8. **Import isolation**: the `run_cmd` at the end checks that the production module's only import
   besides the implicit `Init` is `Mathlib.ModelTheory.Fraisse`, and that its transitive import
   closure contains no module of this library or of `InfinitaryLogic`. This audit's own import of
   the axiom-check utility does not affect that check, which reads the production module's recorded
   imports.
-/

universe u v w z

open FirstOrder Language Substructure

namespace FirstOrder.Language

section General

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {I : Type z}
  {U : I → L.Substructure M}

/-- **The core theorem**, in independent universes, with no countability, nonemptiness, or
effectivity. -/
theorem test_isExtensionPair (hcof : FGCofinal U) (hrich : ExtensionRich U) :
    L.IsExtensionPair M M :=
  isExtensionPair_of_extensionRich hcof hrich

/-- **The converse, without countable generation.** -/
theorem test_extensionRich_of_isUltrahomogeneous (hcof : FGCofinal U)
    (hU : L.IsUltrahomogeneous M) : ExtensionRich U :=
  extensionRich_of_isUltrahomogeneous hcof hU

/-- The equivalence, where countable generation enters. -/
theorem test_extensionRich_iff (hcof : FGCofinal U) (hCG : Structure.CG L M) :
    ExtensionRich U ↔ L.IsUltrahomogeneous M :=
  extensionRich_iff_isUltrahomogeneous hcof hCG

/-- **The age is the union of the members' ages**, from cofinality alone: no homogeneity and no
extension hypothesis. -/
theorem test_age_eq_iUnion (hcof : FGCofinal U) : L.age M = ⋃ i, L.age (U i) :=
  age_eq_iUnion_of_fgCofinal hcof

/-- The age identified with a class, with coverage supplied and no joint embedding. -/
theorem test_age_eq (K : Set (CategoryTheory.Bundled.{w} L.Structure)) (hK : Hereditary K)
    (hstage : ∀ i, CategoryTheory.Bundled.of (c := L.Structure) (U i) ∈ K)
    (hcov : ∀ N ∈ K, ∃ i, Nonempty (N ↪[L] U i)) (hfg : ∀ N ∈ K, Structure.FG L N)
    (hcof : FGCofinal U) : L.age M = K :=
  age_eq_of_fgCofinal K hK hstage hcov hfg hcof

/-- Directed exhaustion over an inhabited index. -/
theorem test_fgCofinal_of_directed [Nonempty I] (hdir : Directed (· ≤ ·) U)
    (hcov : ∀ x : M, ∃ i, x ∈ U i) : FGCofinal U :=
  fgCofinal_of_directed hdir hcov

/-- The Fraïssé-limit package, where the countability of the interface enters. -/
theorem test_isFraisseLimit [Countable (Σ n, L.Functions n)] [Countable M]
    (K : Set (CategoryTheory.Bundled.{w} L.Structure)) (hcof : FGCofinal U)
    (hrich : ExtensionRich U) (hK : Hereditary K)
    (hstage : ∀ i, CategoryTheory.Bundled.of (c := L.Structure) (U i) ∈ K)
    (hcov : ∀ N ∈ K, ∃ i, Nonempty (N ↪[L] U i)) (hfg : ∀ N ∈ K, Structure.FG L N) :
    L.IsFraisseLimit K M :=
  isFraisseLimit_of_extensionRich K hcof hrich hK hstage hcov hfg

/-- **An empty index is never cofinal**: cofinality at the finitely generated bottom substructure
would produce an index. -/
theorem test_empty_index_not_cofinal (U : Empty → L.Substructure M) : ¬ FGCofinal U :=
  fun h ↦ (h ⊥ fg_bot).elim fun i _ ↦ i.elim

end General

section EmptyCarrier

local instance : Language.empty.Structure Empty := Language.emptyStructure

/-- The one-member family on the empty carrier: the whole (empty) structure. -/
def emptyFamily : Unit → Language.empty.Substructure Empty := fun _ ↦ ⊤

/-- **An empty carrier is supported**: the family indexed by `Unit` is cofinal and extension rich
on `Empty`, so the empty structure is its own extension pair through this file's theorem. -/
theorem test_empty_carrier :
    FGCofinal emptyFamily ∧ ExtensionRich emptyFamily ∧
      Language.empty.IsExtensionPair Empty Empty := by
  have hcof : FGCofinal emptyFamily := fun _ _ ↦ ⟨(), le_top⟩
  have hrich : ExtensionRich emptyFamily := fun _ _ T _ _ _ _ _ ↦
    ⟨(), Substructure.inclusion (le_top : T ≤ ⊤), fun a ↦ a.1.elim⟩
  exact ⟨hcof, hrich, isExtensionPair_of_extensionRich hcof hrich⟩

/-- **Directed exhaustion needs an inhabited index**: on the empty carrier the empty family is
directed and covers every point, but it is not cofinal. -/
theorem test_directed_needs_index :
    ∃ U : Empty → Language.empty.Substructure Empty,
      Directed (· ≤ ·) U ∧ (∀ x : Empty, ∃ i, x ∈ U i) ∧ ¬ FGCofinal U :=
  ⟨Empty.elim, fun i ↦ i.elim, fun x ↦ x.elim, test_empty_index_not_cofinal _⟩

end EmptyCarrier

end FirstOrder.Language

/-! ### Import isolation -/

-- The production module imports exactly `Mathlib.ModelTheory.Fraisse`, and nothing in its
-- transitive import closure belongs to this library or to `InfinitaryLogic`.
open Lean in
run_cmd do
  let env ← getEnv
  let target := `ComputableModelTheory.ModelTheory.ExtensionRichFamily
  let some idx := env.getModuleIdx? target | throwError "{target} is not imported"
  let direct := (env.header.moduleData[idx.toNat]!).imports.map (·.module)
  unless direct.filter (· != `Init) == #[`Mathlib.ModelTheory.Fraisse] do
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

#assert_standard_axioms FirstOrder.Language.isExtensionPair_of_extensionRich
#assert_standard_axioms FirstOrder.Language.isUltrahomogeneous_of_extensionRich
#assert_standard_axioms FirstOrder.Language.extensionRich_of_isUltrahomogeneous
#assert_standard_axioms FirstOrder.Language.extensionRich_iff_isUltrahomogeneous
#assert_standard_axioms FirstOrder.Language.fgCofinal_of_directed
#assert_standard_axioms FirstOrder.Language.age_eq_iUnion_of_fgCofinal
#assert_standard_axioms FirstOrder.Language.age_eq_of_fgCofinal
#assert_standard_axioms FirstOrder.Language.isFraisseLimit_of_extensionRich
#assert_standard_axioms FirstOrder.Language.test_empty_index_not_cofinal
#assert_standard_axioms FirstOrder.Language.test_empty_carrier
#assert_standard_axioms FirstOrder.Language.test_directed_needs_index
#assert_module_standard_axioms ComputableModelTheory.ModelTheory.ExtensionRichFamily
