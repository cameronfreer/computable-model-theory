/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.RepresentativeAge
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: Fraïssé classes from concrete representatives

Outside the root import spine; CI checks it through `scripts/run-audit-modules.sh`, and with
warnings as errors through `scripts/check-classical-layer.sh`.

* **Independent universes**: language, index and carrier universes are separate
  (`test_countable_quotient`); the class lives in the carrier universe.
* **Countability is of isomorphism classes**, not of the bundled class
  (`test_countable_quotient`).
* **An empty index gives the empty class** (`test_empty_index`); **an empty carrier can be a
  representative** (`test_empty_carrier`) — inhabited index and inhabited carriers are distinct.
* **Tuple factorization** (`test_factor_*`): independent universes with no countability,
  nonemptiness or finite-generation premise; discharged over the age-indexed family `ageFamily`
  for a repeated coordinate (the factor repeats it), an injective tuple (literal equation of
  embeddings), the empty tuple under a constant (the representative is nonempty), and the empty
  carrier.
* **Standard axioms** for every declaration of the production module
  (`#assert_module_standard_axioms`, which scans by defining module, whatever the namespace) and
  for the regression rows.
* **Import isolation**: the production module's only import besides `Init` is
  `Mathlib.ModelTheory.Fraisse`, and its transitive closure contains no module of this library or of
  `InfinitaryLogic`.
-/

universe u v w z

open CategoryTheory FirstOrder FirstOrder.Language

namespace FirstOrder.Language

/-- Essential countability, in independent language, index and carrier universes: countably many
isomorphism classes, not a countable set of bundled structures. -/
theorem test_countable_quotient {L : Language.{u, v}} {I : Type z} [Countable I]
    (F : I → Bundled.{w} L.Structure) :
    (Quotient.mk' '' representativeClass F).Countable :=
  representativeClass_countable_quotient F

/-- An empty carrier can be a representative. -/
theorem test_empty_carrier {L : Language} {M : Type*} [L.Structure M] [IsEmpty M] :
    (⟨M, inferInstance⟩ : Bundled L.Structure) ∈
      representativeClass (fun _ : Unit => (⟨M, inferInstance⟩ : Bundled L.Structure)) :=
  mem_representativeClass _ ()

/-- An empty index gives the empty class. -/
theorem test_empty_index {L : Language} (F : Empty → Bundled L.Structure) :
    representativeClass F = ∅ := by
  ext M
  constructor
  · rintro ⟨i, _⟩
    exact i.elim
  · intro h
    exact False.elim h

/-! ### Tuple factorization -/

/-- The factorization in independent language, index and carrier universes, with no
countability, nonemptiness or finite-generation premise. -/
theorem test_factor_tuple {L : Language.{u, v}} {I : Type z} {F : I → Bundled.{w} L.Structure}
    {M : Type w} [L.Structure M] (h : L.age M ⊆ representativeClass F) {n : ℕ} (a : Fin n → M) :
    ∃ (i : I) (e : F i ↪[L] M) (b : Fin n → F i), e ∘ b = a :=
  exists_factor_tuple_of_age_subset h a

/-- The members of the age, as their own representatives: a family that discharges the
age-containment premise outright. -/
def ageFamily (L : Language.{u, v}) (M : Type w) [L.Structure M] :
    L.age M → Bundled.{w} L.Structure :=
  fun N ↦ N.1

theorem age_subset_ageFamily (L : Language.{u, v}) (M : Type w) [L.Structure M] :
    L.age M ⊆ representativeClass (ageFamily L M) :=
  fun N hN ↦ ⟨⟨N, hN⟩, ⟨Language.Equiv.refl L N⟩⟩

/-- **Repeated coordinates**: a tuple with a repeated coordinate factors, and the factor repeats
it too. -/
theorem test_factor_repeated {L : Language.{u, v}} {M : Type w} [L.Structure M] (x : M) :
    ∃ (i : L.age M) (e : ageFamily L M i ↪[L] M) (b : Fin 2 → ageFamily L M i),
      e ∘ b = ![x, x] ∧ b 0 = b 1 := by
  obtain ⟨i, e, b, hb⟩ := exists_factor_tuple_of_age_subset (age_subset_ageFamily L M) ![x, x]
  refine ⟨i, e, b, hb, e.injective ?_⟩
  simpa using (congrFun hb 0).trans (congrFun hb 1).symm

/-- **Injective tuples**, with the literal equation of embeddings. -/
theorem test_factor_embedding {L : Language.{u, v}} {M : Type w} [L.Structure M] {n : ℕ}
    (a : Fin n ↪ M) :
    ∃ (i : L.age M) (e : ageFamily L M i ↪[L] M) (b : Fin n ↪ ageFamily L M i),
      b.trans e.toEmbedding = a :=
  exists_factor_embedding_of_age_subset (age_subset_ageFamily L M) a

/-- **The empty tuple under a constant**: the representative it factors through contains the
constant, so it is not the empty structure. -/
theorem test_factor_empty_tuple_constant {L : Language.{u, v}} (c : L.Functions 0) {M : Type w}
    [L.Structure M] :
    ∃ (i : L.age M) (e : ageFamily L M i ↪[L] M) (b : Fin 0 → ageFamily L M i),
      e ∘ b = Fin.elim0 ∧ Nonempty (ageFamily L M i) := by
  obtain ⟨i, e, b, hb⟩ := exists_factor_tuple_of_age_subset (age_subset_ageFamily L M) Fin.elim0
  exact ⟨i, e, b, hb, ⟨Structure.funMap c default⟩⟩

section EmptyCarrier

local instance : Language.empty.Structure Empty := Language.emptyStructure

/-- **An empty carrier**: the empty tuple of the empty structure factors. -/
theorem test_factor_empty_carrier :
    ∃ (i : Language.empty.age Empty) (e : ageFamily Language.empty Empty i ↪[Language.empty] Empty)
      (b : Fin 0 → ageFamily Language.empty Empty i), e ∘ b = Fin.elim0 :=
  exists_factor_tuple_of_age_subset (age_subset_ageFamily _ _) Fin.elim0

end EmptyCarrier

end FirstOrder.Language

-- The production module's imports stay below the computable layers.
open Lean in
run_cmd do
  let env ← getEnv
  let target := `ComputableModelTheory.ModelTheory.RepresentativeAge
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

#assert_standard_axioms FirstOrder.Language.test_countable_quotient
#assert_standard_axioms FirstOrder.Language.test_empty_carrier
#assert_standard_axioms FirstOrder.Language.test_empty_index
#assert_standard_axioms FirstOrder.Language.test_factor_tuple
#assert_standard_axioms FirstOrder.Language.test_factor_repeated
#assert_standard_axioms FirstOrder.Language.test_factor_embedding
#assert_standard_axioms FirstOrder.Language.test_factor_empty_tuple_constant
#assert_standard_axioms FirstOrder.Language.test_factor_empty_carrier

#assert_module_standard_axioms ComputableModelTheory.ModelTheory.RepresentativeAge
