/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.RootedExtension
import ComputableModelTheory.Util.AssertAxioms
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin

/-!
# Audit: rooted universality and uniqueness

Outside the root import spine; CI checks it through `scripts/run-audit-modules.sh`, and with
warnings as errors through `scripts/check-classical-layer.sh`.

* **Signatures**: independent universes for the language, source, target, root and index; no
  countability or age hypothesis on the universality target (`test_universality`); countable
  generation on both sides only for uniqueness (`test_uniqueness`).
* **A missing seed is a genuine obstruction** (`test_missing_seed`): with one nullary relation,
  true in the source and false in the target, the source is countable, its age lies in the class
  of its own age members, the target extends those representatives' embeddings, and the pair is an
  extension pair, all vacuously, yet there is no embedding at all. The root cannot be dropped.
* **Universality into a strictly larger age** (`test_universality_larger_age`): with one unary
  predicate, `ℕ` with the predicate empty embeds into `ℕ` with the predicate `{0}`, over a
  prescribed root, through the family of finite predicate-free structures `Fin n`; the target's
  age strictly contains the source's.
* **Rooted uniqueness over a nontrivial root** (`test_uniqueness_swap`): the predicate-free `ℕ`
  has an automorphism exchanging `0` and `1`, obtained from the same family on both sides.
* **Standard axioms** for every declaration of the production module
  (`#assert_module_standard_axioms`) and for the regression rows.
* **Import isolation**: the production module imports only `RepresentativeAge` besides `Init`, and
  its transitive closure contains no other module of this library and no module of
  `InfinitaryLogic`.
-/

universe u v w w' z x

open CategoryTheory FirstOrder Language Structure Substructure

namespace FirstOrder.Language

/-! ### Signatures -/

/-- Universality: no countability and no age hypothesis on the target. -/
theorem test_universality {L : Language.{u, v}} {I : Type z} {F : I → Bundled.{w} L.Structure}
    {M : Type w} {N : Type w'} {A : Type x} [L.Structure M] [L.Structure N] [L.Structure A]
    (hM : L.age M ⊆ representativeClass F) (hN : ExtendsRepresentatives F N)
    (hMcg : Structure.CG L M) (hA : Structure.FG L A) (aM : A ↪[L] M) (aN : A ↪[L] N) :
    ∃ e : M ↪[L] N, e.comp aM = aN :=
  exists_embedding_comp_eq_of_age_subset hM hN hMcg hA aM aN

/-- Uniqueness: the hypotheses on both sides, countable generation of both. -/
theorem test_uniqueness {L : Language.{u, v}} {I : Type z} {F : I → Bundled.{w} L.Structure}
    {M N : Type w} {A : Type x} [L.Structure M] [L.Structure N] [L.Structure A]
    (hM : L.age M ⊆ representativeClass F) (hN : L.age N ⊆ representativeClass F)
    (hMext : ExtendsRepresentatives F M) (hNext : ExtendsRepresentatives F N)
    (hMcg : Structure.CG L M) (hNcg : Structure.CG L N) (hA : Structure.FG L A)
    (aM : A ↪[L] M) (aN : A ↪[L] N) : ∃ e : M ≃[L] N, e.toEmbedding.comp aM = aN :=
  exists_equiv_comp_eq_of_age_subset hM hN hMext hNext hMcg hNcg hA aM aN

/-- The members of the age, as their own representatives. -/
def ageFamily (L : Language.{u, v}) (M : Type w) [L.Structure M] :
    L.age M → Bundled.{w} L.Structure :=
  fun N ↦ N.1

theorem age_subset_ageFamily (L : Language.{u, v}) (M : Type w) [L.Structure M] :
    L.age M ⊆ representativeClass (ageFamily L M) :=
  fun N hN ↦ ⟨⟨N, hN⟩, ⟨Language.Equiv.refl L N⟩⟩

/-! ### A missing seed: one nullary relation -/

/-- One nullary relation symbol. -/
inductive NullRel : ℕ → Type
  | r : NullRel 0

/-- A language with one nullary relation symbol and no function symbols. -/
def nullLang : Language.{0, 0} :=
  ⟨fun _ ↦ Empty, NullRel⟩

instance : IsRelational nullLang := fun _ ↦ (inferInstance : IsEmpty Empty)

/-- One point, where the nullary relation holds. -/
def RTrue : Type := Unit

/-- One point, where the nullary relation fails. -/
def RFalse : Type := Unit

instance : nullLang.Structure RTrue where
  funMap f := isEmptyElim f
  RelMap _ _ := True

instance : nullLang.Structure RFalse where
  funMap f := isEmptyElim f
  RelMap _ _ := False

instance : Countable RTrue := inferInstanceAs (Countable Unit)

/-- A structure where the nullary relation holds has no embedding into `RFalse`. -/
theorem isEmpty_embedding_rFalse (X : Type*) [nullLang.Structure X]
    (hX : RelMap (L := nullLang) NullRel.r (default : Fin 0 → X)) :
    IsEmpty (X ↪[nullLang] RFalse) :=
  ⟨fun e ↦ (e.map_rel NullRel.r default).2 hX⟩

/-- An embedding into `RTrue` forces the nullary relation. -/
theorem relMap_of_embedding_rTrue {X : Type*} [nullLang.Structure X] (e : X ↪[nullLang] RTrue) :
    RelMap (L := nullLang) NullRel.r (default : Fin 0 → X) :=
  (e.map_rel NullRel.r default).1 trivial

/-- **A missing seed is a genuine obstruction.** Every hypothesis of relative universality except
the root holds — countable source, age containment, the target extending the representatives'
embeddings, even the extension pair itself, vacuously — but there is no embedding. -/
theorem test_missing_seed :
    nullLang.age RTrue ⊆ representativeClass (ageFamily nullLang RTrue) ∧
      ExtendsRepresentatives (ageFamily nullLang RTrue) RFalse ∧
      nullLang.IsExtensionPair RTrue RFalse ∧ IsEmpty (RTrue ↪[nullLang] RFalse) := by
  refine ⟨age_subset_ageFamily _ _, fun i _ _ g ↦ ?_, fun f _ ↦ ?_,
    isEmpty_embedding_rFalse RTrue trivial⟩
  · obtain ⟨_, ⟨e⟩⟩ := i.2
    exact ((isEmpty_embedding_rFalse _ (relMap_of_embedding_rTrue e)).false g).elim
  · exact ((isEmpty_embedding_rFalse f.1.dom
      (relMap_of_embedding_rTrue f.1.dom.subtype)).false f.1.toEmbedding).elim

/-! ### One unary predicate: a strictly larger age, and a nontrivial root -/

/-- One unary relation symbol. -/
inductive PredRel : ℕ → Type
  | p : PredRel 1

/-- A language with one unary relation symbol and no function symbols. -/
def predLang : Language.{0, 0} :=
  ⟨fun _ ↦ Empty, PredRel⟩

instance : IsRelational predLang := fun _ ↦ (inferInstance : IsEmpty Empty)

/-- Interpreting the predicate by `S`. -/
def predRel {X : Type} (S : X → Prop) : ∀ {n : ℕ}, PredRel n → (Fin n → X) → Prop
  | _, .p, x => S (x 0)

/-- `ℕ` with the predicate interpreted by `S`. -/
def PredNat (_ : ℕ → Prop) : Type := ℕ

instance (S : ℕ → Prop) : predLang.Structure (PredNat S) where
  funMap f := isEmptyElim f
  RelMap r x := predRel S r x

instance (S : ℕ → Prop) : Countable (PredNat S) := inferInstanceAs (Countable ℕ)

/-- `ℕ` with the predicate empty. -/
abbrev Plain : Type := PredNat fun _ ↦ False

/-- `ℕ` with the predicate `{0}`. -/
abbrev Marked : Type := PredNat (· = 0)

/-- The finite predicate-free structures. -/
instance (n : ℕ) : predLang.Structure (Fin n) where
  funMap f := isEmptyElim f
  RelMap r x := predRel (fun _ ↦ False) r x

/-- The family of finite predicate-free structures. -/
def finFamily : ℕ → Bundled.{0} predLang.Structure :=
  fun n ↦ ⟨Fin n, inferInstance⟩

/-- An injective map preserving and reflecting the predicate on single points is an embedding. -/
def predEmb {X Y : Type} [predLang.Structure X] [predLang.Structure Y] (h : X → Y)
    (hinj : Function.Injective h)
    (hP : ∀ x : X,
      RelMap (L := predLang) PredRel.p ![h x] ↔ RelMap (L := predLang) PredRel.p ![x]) :
    X ↪[predLang] Y where
  toFun := h
  inj' := hinj
  map_fun' f := isEmptyElim f
  map_rel' := by
    rintro _ ⟨⟩ x
    have hx : x = ![x 0] := funext fun i ↦ by rw [Subsingleton.elim i 0]; rfl
    have hhx : h ∘ x = ![h (x 0)] := funext fun i ↦ by rw [Subsingleton.elim i 0]; rfl
    rw [hhx, hx]
    exact hP (x 0)

/-- Extending an injection of `Fin i` into `ℕ` along an injection `Fin i → Fin j`, sending the new
points above all old values. -/
theorem exists_extend_fin {i j : ℕ} (f : Fin i → Fin j) (hf : Function.Injective f)
    (g : Fin i → ℕ) (hg : Function.Injective g) :
    ∃ h : Fin j → ℕ, Function.Injective h ∧ h ∘ f = g ∧ ∀ y, h y = 0 → ∃ x, f x = y := by
  classical
  let K := Finset.univ.sup g
  have hK : ∀ x, g x ≤ K := fun x ↦ Finset.le_sup (f := g) (Finset.mem_univ x)
  refine ⟨fun y ↦ if hy : ∃ x, f x = y then g hy.choose else K + y + 1, ?_, ?_, ?_⟩
  · intro y y' hyy'
    simp only at hyy'
    split_ifs at hyy' with h1 h2 h2
    · rw [← h1.choose_spec, ← h2.choose_spec, hg hyy']
    · have := hK h1.choose
      omega
    · have := hK h2.choose
      omega
    · exact Fin.ext (by omega)
  · funext x
    simp only [Function.comp_apply]
    split_ifs with hx
    · exact congrArg g (hf hx.choose_spec)
    · exact absurd ⟨x, rfl⟩ hx
  · intro y hy
    by_contra hne
    simp only at hy
    split_ifs at hy

/-- `ℕ` with any predicate contained in `{0}` extends the embeddings of the finite predicate-free
structures: new points go above every old value, away from `0`. -/
theorem extendsRepresentatives_predNat (S : ℕ → Prop) (hS : ∀ n, S n → n = 0) :
    ExtendsRepresentatives finFamily (PredNat S) := by
  intro i j f g
  have hg : ∀ x, ¬ S (g x) := fun x hx ↦ (g.map_rel PredRel.p ![x]).1 (by
    change S (g (![x] 0))
    exact hx)
  obtain ⟨h, hinj, hcomp, hzero⟩ := exists_extend_fin (⇑f) f.injective (⇑g) g.injective
  refine ⟨predEmb (Y := PredNat S) h hinj fun y ↦ iff_of_false (fun hy ↦ ?_) not_false, ?_⟩
  · change S (h y) at hy
    obtain ⟨x, rfl⟩ := hzero y (hS _ hy)
    exact hg x (congrFun hcomp x ▸ hy)
  · ext x
    exact congrFun hcomp x

/-- A finite structure where the predicate is empty, reindexed by `Fin`. -/
noncomputable def equivFinOfPredFree (N : Type) [predLang.Structure N] [Fintype N]
    (hP : ∀ x : Fin 1 → N, ¬ RelMap (L := predLang) PredRel.p x) :
    N ≃[predLang] Fin (Fintype.card N) where
  toEquiv := Fintype.equivFin N
  map_fun' f := isEmptyElim f
  map_rel' := by
    rintro _ ⟨⟩ x
    exact iff_of_false not_false (hP x)

/-- The age of the predicate-free `ℕ` lies in the class of the finite predicate-free structures. -/
theorem age_plain_subset : predLang.age Plain ⊆ representativeClass finFamily := by
  rintro N ⟨hfg, ⟨e⟩⟩
  have : Finite N := hfg.finite
  let := Fintype.ofFinite N
  exact ⟨Fintype.card N, ⟨equivFinOfPredFree N fun x hx ↦ (e.map_rel PredRel.p x).2 hx⟩⟩

/-- The predicate-free embedding `Fin n → ℕ` given by an injective function. -/
def finEmb {n : ℕ} (S : ℕ → Prop) (h : Fin n → ℕ) (hinj : Function.Injective h)
    (hS : ∀ i, ¬ S (h i)) : Fin n ↪[predLang] PredNat S :=
  predEmb (Y := PredNat S) h hinj fun i ↦ iff_of_false (hS i) not_false

/-- **Universality into a strictly larger age.** The predicate-free `ℕ` embeds into `ℕ` with the
predicate `{0}` over the root `![0, 1] ↦ ![3, 4]`, though the target's age strictly contains the
source's. -/
theorem test_universality_larger_age :
    (∃ e : Plain ↪[predLang] Marked, e (0 : ℕ) = (3 : ℕ) ∧ e (1 : ℕ) = (4 : ℕ)) ∧
      predLang.age Plain ⊆ predLang.age Marked ∧ ¬ predLang.age Marked ⊆ predLang.age Plain := by
  obtain ⟨e, he⟩ := exists_embedding_comp_eq_of_age_subset_of_countable age_plain_subset
    (extendsRepresentatives_predNat (· = 0) fun _ h ↦ h)
    (Structure.fg_iff_finite.2 inferInstance)
    (finEmb (fun _ ↦ False) Fin.val Fin.val_injective fun _ ↦ not_false)
    (finEmb (· = 0) (fun i : Fin 2 ↦ i.val + 3) (fun _ _ h ↦ Fin.ext (by simpa using h))
      fun _ h ↦ by simp at h)
  refine ⟨⟨e, congrArg (· (0 : Fin 2)) he, congrArg (· (1 : Fin 2)) he⟩, ?_, fun h ↦ ?_⟩
  · rintro N ⟨hfg, ⟨g⟩⟩
    exact ⟨hfg, ⟨e.comp g⟩⟩
  · -- The point `0` of `Marked` satisfies the predicate; nothing in `Plain` does.
    let X : predLang.Substructure Marked := closure predLang {(0 : ℕ)}
    obtain ⟨_, ⟨g⟩⟩ := h (age.fg_substructure (fg_closure_singleton (M := Marked) (0 : ℕ)))
    have hX : RelMap (L := predLang) PredRel.p ![(⟨(0 : ℕ), subset_closure rfl⟩ : X)] := by
      change (0 : ℕ) = 0
      rfl
    exact (g.map_rel PredRel.p _).2 hX

/-- **Rooted uniqueness over a nontrivial root.** The predicate-free `ℕ` has an automorphism
exchanging `0` and `1`, from the same family on both sides. -/
theorem test_uniqueness_swap :
    ∃ e : Plain ≃[predLang] Plain, e (0 : ℕ) = (1 : ℕ) ∧ e (1 : ℕ) = (0 : ℕ) := by
  have hext := extendsRepresentatives_predNat (fun _ ↦ False) fun _ h ↦ h.elim
  obtain ⟨e, he⟩ := exists_equiv_comp_eq_of_age_subset_of_countable age_plain_subset
    age_plain_subset hext hext (Structure.fg_iff_finite.2 inferInstance)
    (finEmb (fun _ ↦ False) Fin.val Fin.val_injective fun _ ↦ not_false)
    (finEmb (fun _ ↦ False) (fun i : Fin 2 ↦ 1 - i.val)
      (fun a b h ↦ Fin.ext (by have := a.isLt; have := b.isLt; simp only at h; omega))
      fun _ ↦ not_false)
  exact ⟨e, congrArg (· (0 : Fin 2)) he, congrArg (· (1 : Fin 2)) he⟩

end FirstOrder.Language

/-! ### Import isolation -/

-- The production module imports exactly `RepresentativeAge`, and nothing else in its transitive
-- import closure belongs to this library or to `InfinitaryLogic`.
open Lean in
run_cmd do
  let env ← getEnv
  let target := `ComputableModelTheory.ModelTheory.RootedExtension
  let sibling := `ComputableModelTheory.ModelTheory.RepresentativeAge
  let some idx := env.getModuleIdx? target | throwError "{target} is not imported"
  let direct := (env.header.moduleData[idx.toNat]!).imports.map (·.module)
  unless direct.filter (· != `Init) == #[sibling] do
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

#assert_standard_axioms FirstOrder.Language.test_universality
#assert_standard_axioms FirstOrder.Language.test_uniqueness
#assert_standard_axioms FirstOrder.Language.test_missing_seed
#assert_standard_axioms FirstOrder.Language.test_universality_larger_age
#assert_standard_axioms FirstOrder.Language.test_uniqueness_swap

#assert_module_standard_axioms ComputableModelTheory.ModelTheory.RootedExtension
