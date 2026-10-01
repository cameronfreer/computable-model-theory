/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.FraisseExistence
import ComputableModelTheory.Util.AssertAxioms
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fintype

/-!
# Audit: classical Fraïssé existence

Outside the root import spine; CI checks it through `scripts/run-audit-modules.sh`, and with
warnings as errors through `scripts/check-classical-layer.sh`.

* **Signatures** in independent language, index and carrier universes
  (`test_exists_fraisseSequence`, `test_exists_isFraisseLimit`). The sequence needs no hereditary
  closure; countable representative carriers are explicit; countability of the function symbols
  appears only at the limit.
* **Existence for a Fraïssé class** (`test_exists_isFraisseLimit_of_isFraisse`): `IsFraisse K`
  and countably many function symbols give a countable limit; carrier countability is derived.
* **The two outputs are separate**: the scheduled square (`test_chain_square`, for an arbitrary
  stepper and schedule) and coverage (`test_chain_cover`).
* **The class of only the empty structure**, discharged through the completed theorem: its limit
  exists and is empty (`test_empty_only`). No infinitude is required.
* **Pure sets of size at most `b`**, discharged through the completed theorem
  (`test_bounded_pure_sets`): amalgamation identifies points, so the class is closed under it, and
  the limit exists for every `b`, including `b = 0`, and its carrier is equivalent to `Fin b`
  (`test_bounded_pure_sets_card`): the advertised finite cardinality is pinned, not just existence.
* **Standard axioms** for every declaration of the production module
  (`#assert_module_standard_axioms`) and for the regression rows.
* **Import isolation**: the production module imports only `ExtensionRichDirectLimit` and
  `RepresentativeAge` besides `Init`, and its transitive closure contains no other module of this
  library and no module of `InfinitaryLogic`.
-/

universe u v w z

open CategoryTheory FirstOrder Language Structure

namespace FirstOrder.Language

/-! ### Signatures -/

/-- The sequence: no hereditary closure, no signature countability. -/
theorem test_exists_fraisseSequence {L : Language.{u, v}} {I : Type z} [Countable I] [Nonempty I]
    (F : I → Bundled.{w} L.Structure) [∀ i, Countable (F i)] (hfg : ∀ i, Structure.FG L (F i))
    (hjep : ∀ i j, ∃ k, Nonempty (F i ↪[L] F k) ∧ Nonempty (F j ↪[L] F k))
    (hap : ∀ i j k (f : F i ↪[L] F j) (g : F i ↪[L] F k),
      ∃ (l : I) (a : F j ↪[L] F l) (b : F k ↪[L] F l), a.comp f = b.comp g) :
    ∃ (s : ℕ → I) (c : ∀ n, F (s n) ↪[L] F (s (n + 1))),
      (∀ r, ∃ n, Nonempty (F r ↪[L] F (s n))) ∧
      SequenceExtension (G := fun n ↦ F (s n)) (fun i j h ↦ DirectedSystem.natLERec c i j h)
        (representativeClass F) :=
  exists_fraisseSequence F hfg hjep hap

/-- The limit, in the representatives' universe. -/
theorem test_exists_isFraisseLimit {L : Language.{u, v}} [Countable (Σ n, L.Functions n)]
    {I : Type z} [Countable I] [Nonempty I] (F : I → Bundled.{w} L.Structure)
    [∀ i, Countable (F i)] (hfg : ∀ i, Structure.FG L (F i))
    (hsub : ∀ i (S : L.Substructure (F i)), S.FG → ∃ j, Nonempty (S ≃[L] F j))
    (hjep : ∀ i j, ∃ k, Nonempty (F i ↪[L] F k) ∧ Nonempty (F j ↪[L] F k))
    (hap : ∀ i j k (f : F i ↪[L] F j) (g : F i ↪[L] F k),
      ∃ (l : I) (a : F j ↪[L] F l) (b : F k ↪[L] F l), a.comp f = b.comp g) :
    ∃ (M : Bundled.{w} L.Structure) (_ : Countable M),
      IsFraisseLimit (representativeClass F) M :=
  exists_isFraisseLimit_representativeClass F hfg hsub hjep hap

/-- **Existence for a Fraïssé class**: only countability of the function symbols, which
`IsFraisseLimit` itself requires; countable carriers are derived. -/
theorem test_exists_isFraisseLimit_of_isFraisse {L : Language.{u, v}}
    [Countable (Σ n, L.Functions n)] (K : Set (Bundled.{w} L.Structure)) [IsFraisse K] :
    ∃ (M : Bundled.{w} L.Structure) (_ : Countable M), IsFraisseLimit K M :=
  exists_isFraisseLimit_of_isFraisse K

/-- The scheduled square, for an arbitrary stepper and schedule. -/
theorem test_chain_square {L : Language.{u, v}} {I : Type z} {F : I → Bundled.{w} L.Structure}
    (S : Stepper F) (σ : Schedule F) (m k : ℕ) {j : I} (e : F (chainIdx S σ m) ↪[L] F j)
    (he : σ.out (chainIdx S σ m) k = ⟨j, e⟩) :
    ∃ g : F j ↪[L] F (chainIdx S σ (Nat.pair m k + 1)),
      g.comp e = DirectedSystem.natLERec (chainMap S σ) m (Nat.pair m k + 1)
        ((Nat.left_le_pair m k).trans (Nat.le_succ _)) :=
  chain_square S σ m k e he

/-- Coverage, for an arbitrary stepper and schedule. -/
theorem test_chain_cover {L : Language.{u, v}} {I : Type z} {F : I → Bundled.{w} L.Structure}
    (S : Stepper F) (σ : Schedule F) (t : ℕ) :
    Nonempty (F (σ.rep t) ↪[L] F (chainIdx S σ (t + 1))) :=
  chain_cover S σ t

/-! ### Pure sets -/

instance : Countable (Σ n, Language.empty.Functions n) :=
  ⟨⟨fun _ ↦ 0, fun ⟨_, f⟩ ↦ Empty.elim f⟩⟩

/-- A type as a structure in the empty language. -/
def pureSet (X : Type) : Bundled.{0} Language.empty.Structure :=
  ⟨X, Language.emptyStructure⟩

instance (X : Type) [Countable X] : Countable (pureSet X) := inferInstanceAs (Countable X)

instance (X : Type) [Finite X] : Finite (pureSet X) := inferInstanceAs (Finite X)

instance (X : Type) [Fintype X] : Fintype (pureSet X) := inferInstanceAs (Fintype X)

/-- A plain embedding as an embedding of pure sets. -/
def pureEmb {X Y : Type} (f : X ↪ Y) : pureSet X ↪[Language.empty] pureSet Y where
  toFun := f
  inj' := f.injective
  map_fun' g := Empty.elim g
  map_rel' r := Empty.elim r

/-- A plain equivalence onto a pure set, from any empty-language structure. -/
def pureEquiv {X Y : Type} [Language.empty.Structure X] (e : X ≃ Y) :
    X ≃[Language.empty] pureSet Y where
  toEquiv := e
  map_fun' g := Empty.elim g
  map_rel' r := Empty.elim r

/-! ### The class of only the empty structure -/

/-- The family with the empty structure as its one representative. -/
abbrev emptyOnly : Unit → Bundled.{0} Language.empty.Structure :=
  fun _ ↦ pureSet Empty

/-- **Only the empty structure**: the completed theorem gives a limit, and that limit is empty. -/
theorem test_empty_only :
    ∃ (M : Bundled.{0} Language.empty.Structure) (_ : Countable M),
      IsFraisseLimit (representativeClass emptyOnly) M ∧ IsEmpty M := by
  obtain ⟨M, hM, hlim⟩ := exists_isFraisseLimit_representativeClass emptyOnly
    (fun _ ↦ Structure.fg_iff_finite.2 inferInstance)
    (fun _ S _ ↦ have : IsEmpty S := ⟨fun x ↦ Empty.elim (x.1 : Empty)⟩
      ⟨(), ⟨pureEquiv (Equiv.equivEmpty S)⟩⟩)
    (fun _ _ ↦ ⟨(), ⟨Embedding.refl _ _⟩, ⟨Embedding.refl _ _⟩⟩)
    (fun _ _ _ f _ ↦ ⟨(), Embedding.refl _ _, Embedding.refl _ _, Embedding.ext fun x ↦ x.elim⟩)
  refine ⟨M, hM, hlim, ⟨fun x ↦ ?_⟩⟩
  have hx : (⟨Substructure.closure Language.empty {x}, inferInstance⟩ :
      Bundled Language.empty.Structure) ∈ Language.empty.age M :=
    age.fg_substructure (Substructure.fg_closure_singleton x)
  rw [hlim.age] at hx
  obtain ⟨_, ⟨u⟩⟩ := hx
  exact (u ⟨x, Substructure.subset_closure rfl⟩).elim

/-! ### Pure sets of size at most `b` -/

/-- The family of pure sets of sizes `0, …, b`. -/
abbrev boundedSets (b : ℕ) : Fin (b + 1) → Bundled.{0} Language.empty.Structure :=
  fun i ↦ pureSet (Fin i)

/-- Two injections of `Fin i` into `Fin n` differ by a permutation of `Fin n`. -/
theorem exists_perm_comp {i n : ℕ} (p q : Fin i → Fin n) (hp : Function.Injective p)
    (hq : Function.Injective q) : ∃ π : Equiv.Perm (Fin n), ∀ x, π (p x) = q x := by
  classical
  let e : {y // y ∈ Set.range p} ≃ {y // y ∈ Set.range q} :=
    (Equiv.ofInjective p hp).symm.trans (Equiv.ofInjective q hq)
  refine ⟨e.extendSubtype, fun x ↦ ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (p x) ⟨x, rfl⟩]
  simp [e]

/-- Amalgamation of pure sets of size at most `b`, identifying points: the larger target receives
the smaller one along a permutation. -/
theorem boundedSets_amalgamation (b : ℕ) (i j k : Fin (b + 1))
    (f : boundedSets b i ↪[Language.empty] boundedSets b j)
    (g : boundedSets b i ↪[Language.empty] boundedSets b k) :
    ∃ (l : Fin (b + 1)) (a : boundedSets b j ↪[Language.empty] boundedSets b l)
      (c : boundedSets b k ↪[Language.empty] boundedSets b l), a.comp f = c.comp g := by
  rcases le_total (j : ℕ) k with hjk | hkj
  · obtain ⟨π, hπ⟩ := exists_perm_comp (fun x ↦ Fin.castLE hjk (f x)) (fun x ↦ g x)
      (fun _ _ h ↦ f.injective (Fin.castLE_injective hjk h)) g.injective
    refine ⟨k, pureEmb ((Fin.castLEEmb hjk).trans π.toEmbedding), Embedding.refl _ _, ?_⟩
    ext x
    exact hπ x
  · obtain ⟨π, hπ⟩ := exists_perm_comp (fun x ↦ Fin.castLE hkj (g x)) (fun x ↦ f x)
      (fun _ _ h ↦ g.injective (Fin.castLE_injective hkj h)) f.injective
    refine ⟨j, Embedding.refl _ _, pureEmb ((Fin.castLEEmb hkj).trans π.toEmbedding), ?_⟩
    ext x
    exact (hπ x).symm

/-- **Pure sets of size at most `b`**: the completed theorem gives a countable Fraïssé limit. -/
theorem test_bounded_pure_sets (b : ℕ) :
    ∃ (M : Bundled.{0} Language.empty.Structure) (_ : Countable M),
      IsFraisseLimit (representativeClass (boundedSets b)) M := by
  refine exists_isFraisseLimit_representativeClass (boundedSets b)
    (fun _ ↦ Structure.fg_iff_finite.2 inferInstance) (fun i S _ ↦ ?_)
    (fun i j ↦ ⟨max i j, ⟨pureEmb (Fin.castLEEmb (by simp))⟩, ⟨pureEmb (Fin.castLEEmb (by simp))⟩⟩)
    (boundedSets_amalgamation b)
  have : Finite S := Subtype.finite
  let := Fintype.ofFinite S
  have hS : Fintype.card S ≤ i := by
    simpa using Fintype.card_le_of_injective (β := Fin i) (fun x : S ↦ (x.1 : Fin i))
      fun _ _ h ↦ Subtype.ext h
  exact ⟨⟨Fintype.card S, by omega⟩, ⟨pureEquiv (Fintype.equivFin S)⟩⟩

/-- **The bounded limit has exactly `b` points**: the completed theorem's limit for pure sets of
size at most `b` has a carrier equivalent to `Fin b`. Every finite set of points spans a member of
the class, so has at most `b` points; and `Fin b` itself embeds. -/
theorem test_bounded_pure_sets_card (b : ℕ) :
    ∃ (M : Bundled.{0} Language.empty.Structure) (_ : Countable M),
      IsFraisseLimit (representativeClass (boundedSets b)) M ∧ Nonempty (M ≃ Fin b) := by
  obtain ⟨M, hM, hlim⟩ := test_bounded_pure_sets b
  refine ⟨M, hM, hlim, ?_⟩
  have hle : ∀ S : Finset M, S.card ≤ b := by
    intro S
    have h := age.fg_substructure (L := Language.empty) (Substructure.fg_closure S.finite_toSet)
    rw [hlim.age] at h
    obtain ⟨i, ⟨u⟩⟩ := h
    let := Fintype.ofEquiv _ u.toEquiv.symm
    have hcard : Fintype.card (Substructure.closure Language.empty (S : Set M)) = i :=
      (Fintype.card_congr u.toEquiv).trans (Fintype.card_fin _)
    have hinj := Fintype.card_le_of_injective
      (fun x : S ↦ (⟨x, Substructure.subset_closure x.2⟩ :
        Substructure.closure Language.empty (S : Set M)))
      (fun _ _ h ↦ Subtype.ext (by simpa using h))
    rw [hcard, Fintype.card_coe] at hinj
    omega
  have hfin : Finite M := by
    by_contra h
    have : Infinite M := not_finite_iff_infinite.mp h
    obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq M (b + 1)
    have := hle S
    omega
  let := Fintype.ofFinite M
  have hub : Fintype.card M ≤ b := by simpa using hle Finset.univ
  have hlb : b ≤ Fintype.card M := by
    have h : boundedSets b (Fin.last b) ∈ Language.empty.age M := by
      rw [hlim.age]
      exact mem_representativeClass _ _
    obtain ⟨_, ⟨g⟩⟩ := h
    simpa using Fintype.card_le_of_injective (α := Fin b) (fun x ↦ g x) g.injective
  exact ⟨Fintype.equivFinOfCardEq (le_antisymm hub hlb)⟩

end FirstOrder.Language

/-! ### Import isolation -/

-- The production module imports exactly `ExtensionRichDirectLimit` and `RepresentativeAge`, and
-- nothing else in its transitive import closure belongs to this library or to `InfinitaryLogic`.
open Lean in
run_cmd do
  let env ← getEnv
  let target := `ComputableModelTheory.ModelTheory.FraisseExistence
  let allowed : List Name := [`ComputableModelTheory.ModelTheory.ExtensionRichDirectLimit,
    `ComputableModelTheory.ModelTheory.ExtensionRichFamily,
    `ComputableModelTheory.ModelTheory.RepresentativeAge]
  let some idx := env.getModuleIdx? target | throwError "{target} is not imported"
  let direct := (env.header.moduleData[idx.toNat]!).imports.map (·.module)
  unless direct.filter (· != `Init) == #[allowed[0]!, allowed[2]!] do
    throwError "unexpected direct imports of {target}: {direct}"
  let mut seen : NameSet := {}
  let mut todo : Array Name := direct
  while h : todo.size > 0 do
    let m := todo.back
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    if !allowed.contains m &&
        ((`ComputableModelTheory).isPrefixOf m || (`InfinitaryLogic).isPrefixOf m) then
      throwError "{target} transitively imports {m}"
    if let some j := env.getModuleIdx? m then
      todo := todo ++ (env.header.moduleData[j.toNat]!).imports.map (·.module)

#assert_standard_axioms FirstOrder.Language.test_exists_fraisseSequence
#assert_standard_axioms FirstOrder.Language.test_exists_isFraisseLimit
#assert_standard_axioms FirstOrder.Language.test_exists_isFraisseLimit_of_isFraisse
#assert_standard_axioms FirstOrder.Language.test_chain_square
#assert_standard_axioms FirstOrder.Language.test_chain_cover
#assert_standard_axioms FirstOrder.Language.test_empty_only
#assert_standard_axioms FirstOrder.Language.test_bounded_pure_sets
#assert_standard_axioms FirstOrder.Language.test_bounded_pure_sets_card

#assert_module_standard_axioms ComputableModelTheory.ModelTheory.FraisseExistence
