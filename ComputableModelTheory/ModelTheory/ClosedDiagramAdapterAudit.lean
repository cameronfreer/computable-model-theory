/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.RootedExtension
import ComputableModelTheory.ModelTheory.Computable.AtomicEquiv
import Mathlib.ModelTheory.Order
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: finite-diagram presentations, adapted to rooted extension

This audit adds **no library declaration**. It checks that a presentation of finitely generated
substructures by diagrams reaches the existing rooted-extension interfaces through existing names,
and it tests only the conversion into those interfaces. The rooted conclusions themselves are
audited elsewhere.

"Finite diagram" here means a structure with a **generating tuple**, which is neither a finite
carrier nor a finite description. In a functional language a finitely generated diagram can be
infinite. Restricting to some coordinates means taking their generated closure, and a tuple may
repeat coordinates: it is tuple data, not an injective enumeration.

The receipts of such a presentation map onto the existing names as follows.

* **(A) Occurrences are actual embeddings.**
  - A tuple atomically equivalent to a generating tuple of a diagram is the image of those
    generators under an embedding of the whole diagram (`receiptA_exists_embedding`, from
    `atomicEquivalent_iff_exists_closure_equiv`).
  - Conversely, every embedding's image of the generators is atomically equivalent to them
    (`Embedding.atomicEquivalent_map`).
  - Equality, relation reflection, constants and functions all sit inside `AtomicEquivalent`.
    Repeated coordinates are neither invented nor lost (`test_repeated_*`).
  - Positive preservation is not enough (`test_positive_not_embedding_*`, nullary and unary).
* **(B) Morphisms are all `L`-embeddings.** `ExtendsRepresentatives` quantifies over **every**
  embedding between representatives and **every** occurrence, so an extension property restricted
  to a closed-image class does not supply it.
  - In the order language, extension along initial-segment morphisms holds for `ℕ`
    (`test_initialSegment_extends`).
  - `ExtendsRepresentatives` fails (`test_not_extendsRepresentatives`), at an ordinary embedding the
    restriction excludes (`lift_not_initialSegment`).
* **(C) Coverage gives age containment.** Suppose every finitely generated substructure lies in the
  range of some occurrence, and the representatives are closed under finitely generated
  substructures. Then the age lies in the representative class (`receiptC_age_subset`, by
  `representativeClass_hereditary`).
* **(D) Exact extension** is `ExtendsRepresentatives`, with the root equation literal. Then
  `isExtensionPair_of_age_subset` applies. Its proof consumes `ExtendsRepresentatives` only at
  one-generator steps (`S ≤ closure {m} ⊔ S`). A presentation that supplies extension only along
  one-generator morphisms would still need a factorization or a restricted variant of the adapter;
  neither is added here.

**Conclusions.**
- Universality quotes `exists_embedding_comp_eq_of_isExtensionPair`.
- Uniqueness applies the adapter in **both** directions and quotes
  `exists_equiv_comp_eq_of_isExtensionPair`, with independent source and target universes and one
  family per side (`test_uniqueness_two_families`).
- The single-family `exists_equiv_comp_eq_of_age_subset` keeps one carrier universe.

**The concrete application** is pure sets.
- `ℕ` is presented by the diagrams `Fin n`, with occurrences converted from the tuples
  `0, …, n - 1` through receipt (A).
- Coverage goes through receipt (C), and extension through (D).
- It derives universality over the root `0 ↦ 5, 1 ↦ 3`, and uniqueness over the swap root
  `0 ↦ 1, 1 ↦ 0`.

**Guards already audited, not repeated here.**
- In `RootedExtensionAudit`: the missing-seed negative control (`test_missing_seed`), a target of
  strictly larger age (`test_universality_larger_age`), and exact commutation over a nontrivial
  root (`test_uniqueness_swap`).
- In `RepresentativeAgeAudit` and `ExtensionRichFamilyAudit`: empty carriers, the empty tuple
  under a constant, repeated coordinates in factorization, and the inhabited index needed for
  directed coverage.

`AtomicEquiv` lives outside the classical entry point (it imports the syntax-coding layer), but it
carries no effective hypotheses. Nothing here is effective.
-/

universe u v w w' z z'

open CategoryTheory FirstOrder Language Structure Substructure

namespace ClosedDiagramAdapterAudit

/-! ### The receipts, in general -/

section Receipts

variable {L : Language.{u, v}}

/-- **Receipt (A).** A tuple atomically equivalent to a generating tuple of a diagram is the image
of the generators under an actual embedding of the whole diagram. -/
theorem receiptA_exists_embedding {D : Type w} {M : Type w'} [L.Structure D] [L.Structure M]
    {k : ℕ} (a : Fin k → D) (ha : closure L (Set.range a) = ⊤) (b : Fin k → M)
    (hab : AtomicEquivalent L a b) : ∃ o : D ↪[L] M, ∀ i, o (a i) = b i := by
  obtain ⟨e, he⟩ := (atomicEquivalent_iff_exists_closure_equiv a b).1 hab
  refine ⟨(closure L (Set.range b)).subtype.comp (e.toEmbedding.comp
    ((Substructure.inclusion ha.ge).comp (Substructure.topEquiv (L := L)).symm.toEmbedding)),
    fun i ↦ ?_⟩
  have hi : Substructure.inclusion ha.ge ((Substructure.topEquiv (L := L)).symm (a i)) =
      ⟨a i, subset_closure ⟨i, rfl⟩⟩ := rfl
  change ((e (Substructure.inclusion ha.ge ((Substructure.topEquiv (L := L)).symm (a i))) :
    closure L (Set.range b)) : M) = b i
  rw [hi, he i]

/-- **Receipt (C).** Coverage by occurrences, with the representatives closed under finitely
generated substructures, gives age containment. -/
theorem receiptC_age_subset {M : Type w} [L.Structure M] {I : Type z}
    {F : I → Bundled.{w} L.Structure}
    (hsub : ∀ i (S : L.Substructure (F i)), S.FG → ∃ j, Nonempty (S ≃[L] F j))
    (hcover : ∀ S : L.Substructure M, S.FG → ∃ (i : I) (o : F i ↪[L] M), S ≤ o.toHom.range) :
    L.age M ⊆ representativeClass F := by
  rintro N ⟨hN, ⟨e⟩⟩
  obtain ⟨i, o, hS⟩ := hcover _ (hN.range e.toHom)
  have hmem : ∀ x, e x ∈ o.toHom.range := fun x ↦ hS ⟨x, rfl⟩
  exact representativeClass_hereditary F hsub _ (mem_representativeClass F i)
    ⟨hN, ⟨o.equivRange.symm.toEmbedding.comp (Embedding.codRestrict _ e hmem)⟩⟩

/-- **Universality from receipts (C) and (D).** Exactly `exists_embedding_comp_eq_of_age_subset`.
Nothing is assumed of the target's age or size. -/
theorem test_universality {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N] {I : Type z}
    {F : I → Bundled.{w} L.Structure} {A : Type*} [L.Structure A]
    (hM : L.age M ⊆ representativeClass F) (hN : ExtendsRepresentatives F N)
    (hMcg : Structure.CG L M) (hA : Structure.FG L A) (aM : A ↪[L] M) (aN : A ↪[L] N) :
    ∃ e : M ↪[L] N, e.comp aM = aN :=
  exists_embedding_comp_eq_of_isExtensionPair hA aM aN hMcg (isExtensionPair_of_age_subset hM hN)

/-- **Uniqueness, by the adapter in both directions**, across carrier universes: one family
presents `M`, another presents `N`, and each structure extends the other family's
representatives. -/
theorem test_uniqueness_two_families {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
    {I : Type z} {J : Type z'} {F : I → Bundled.{w} L.Structure}
    {G : J → Bundled.{w'} L.Structure} {A : Type*} [L.Structure A]
    (hM : L.age M ⊆ representativeClass F) (hN : L.age N ⊆ representativeClass G)
    (hNext : ExtendsRepresentatives F N) (hMext : ExtendsRepresentatives G M)
    (hMcg : Structure.CG L M) (hNcg : Structure.CG L N) (hA : Structure.FG L A)
    (aM : A ↪[L] M) (aN : A ↪[L] N) : ∃ e : M ≃[L] N, e.toEmbedding.comp aM = aN :=
  exists_equiv_comp_eq_of_isExtensionPair hA aM aN hMcg hNcg
    (isExtensionPair_of_age_subset hM hNext) (isExtensionPair_of_age_subset hN hMext)

end Receipts

/-! ### Pure sets: the empty language -/

section Pure

instance : Language.empty.Structure ℕ := Language.emptyStructure

instance (n : ℕ) : Language.empty.Structure (Fin n) := Language.emptyStructure

instance : Language.empty.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

/-- An injection, as an embedding of pure sets. -/
def pureEmb {X Y : Type*} [Language.empty.Structure X] [Language.empty.Structure Y] (f : X → Y)
    (hf : Function.Injective f) : X ↪[Language.empty] Y where
  toFun := f
  inj' := hf
  map_fun' := fun g ↦ isEmptyElim g
  map_rel' := fun r ↦ isEmptyElim r

@[simp] theorem pureEmb_apply {X Y : Type*} [Language.empty.Structure X]
    [Language.empty.Structure Y] (f : X → Y) (hf : Function.Injective f) (x : X) :
    pureEmb f hf x = f x :=
  rfl

/-- Every pure-set term is a variable. -/
theorem pure_term_eq_var {k : ℕ} (t : Language.empty.Term (Fin k)) : ∃ i, t = Term.var i := by
  cases t with
  | var i => exact ⟨i, rfl⟩
  | func f _ => exact isEmptyElim f

/-- **Pure-set atomic equivalence is agreement on coordinate equalities**: repeated coordinates
are exactly what it sees. -/
theorem pure_atomicEquivalent_iff {X Y : Type*} [Language.empty.Structure X]
    [Language.empty.Structure Y] {k : ℕ} (a : Fin k → X) (b : Fin k → Y) :
    AtomicEquivalent Language.empty a b ↔ ∀ i j, a i = a j ↔ b i = b j := by
  constructor
  · intro h i j
    exact h.1 (Term.var i) (Term.var j)
  · intro h
    refine ⟨fun t₁ t₂ ↦ ?_, fun R _ ↦ isEmptyElim R⟩
    obtain ⟨i, rfl⟩ := pure_term_eq_var t₁
    obtain ⟨j, rfl⟩ := pure_term_eq_var t₂
    exact h i j

/-- The representatives: `Fin n`, generated by the identity tuple. -/
abbrev F (n : ℕ) : Bundled.{0} Language.empty.Structure :=
  ⟨Fin n, inferInstance⟩

theorem closure_range_id (n : ℕ) :
    closure Language.empty (Set.range (id : Fin n → Fin n)) = ⊤ := by
  rw [Set.range_id, closure_univ]

/-- **Occurrences from tuples, through receipt (A).** The tuple `0, …, n - 1` of `ℕ` is atomically
equivalent to the generators of `Fin n`, so it is the image of an actual occurrence. -/
theorem exists_occurrence (n : ℕ) :
    ∃ o : Fin n ↪[Language.empty] ℕ, ∀ k : Fin n, o k = k :=
  receiptA_exists_embedding id (closure_range_id n) (fun k : Fin n ↦ (k : ℕ))
    ((pure_atomicEquivalent_iff _ _).2 fun _ _ ↦ ⟨fun h ↦ congrArg _ h, fun h ↦ Fin.ext h⟩)

/-- The occurrence of `Fin n` in `ℕ`. -/
noncomputable def occ (n : ℕ) : Fin n ↪[Language.empty] ℕ :=
  (exists_occurrence n).choose

theorem occ_apply (n : ℕ) (k : Fin n) : occ n k = k :=
  (exists_occurrence n).choose_spec k

/-- **Coverage.** A finitely generated substructure of `ℕ` is finite, so it lies in an initial
segment, which is the range of an occurrence. -/
theorem cover (S : Language.empty.Substructure ℕ) (hS : S.FG) :
    ∃ (n : ℕ) (o : F n ↪[Language.empty] ℕ), S ≤ o.toHom.range := by
  have hfin : (S : Set ℕ).Finite := Set.finite_coe_iff.1 (fg_iff_finite.1 hS)
  obtain ⟨m, hm⟩ := hfin.bddAbove
  refine ⟨m + 1, occ (m + 1), fun x hx ↦ ⟨⟨x, Nat.lt_succ_of_le (hm hx)⟩, occ_apply _ _⟩⟩

/-- **Restriction closure.** A finitely generated substructure of a representative is isomorphic to
a representative. -/
theorem hsub (n : ℕ) (S : Language.empty.Substructure (F n)) (_ : S.FG) :
    ∃ j, Nonempty (S ≃[Language.empty] F j) := by
  have : Fintype S := Fintype.ofFinite S
  exact ⟨Fintype.card S, ⟨{ toEquiv := Fintype.equivFin S }⟩⟩

theorem age_nat_subset : Language.empty.age ℕ ⊆ representativeClass F :=
  receiptC_age_subset hsub cover

/-- Extend an injection of `Fin i` into `ℕ` along an injection `Fin i → Fin j`, sending the new
points above everything already used. -/
theorem exists_extend {i j : ℕ} (f : Fin i → Fin j) (hf : Function.Injective f)
    (g : Fin i → ℕ) (hg : Function.Injective g) :
    ∃ h : Fin j → ℕ, Function.Injective h ∧ h ∘ f = g := by
  classical
  let K := Finset.univ.sup g
  have hK : ∀ x, g x ≤ K := fun x ↦ Finset.le_sup (f := g) (Finset.mem_univ x)
  refine ⟨fun y ↦ if hy : ∃ x, f x = y then g hy.choose else K + y + 1, ?_, ?_⟩
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

/-- **Receipt (D).** `ℕ` extends the representatives' embeddings, with the root equation literal. -/
theorem extends_nat : ExtendsRepresentatives F ℕ := by
  intro i j f g
  obtain ⟨h, hinj, hcomp⟩ := exists_extend (⇑f) f.injective (⇑g) g.injective
  exact ⟨pureEmb h hinj, DFunLike.ext _ _ (congrFun hcomp)⟩

/-- The root `Fin 2`, sent to the two given distinct points. -/
def root (p q : ℕ) (hpq : p ≠ q) : Fin 2 ↪[Language.empty] ℕ :=
  pureEmb ![p, q] <| by
    intro x y
    revert x y
    simp [Fin.forall_fin_two, hpq, hpq.symm]

theorem fg_fin2 : Structure.FG Language.empty (Fin 2) :=
  Structure.fg_iff_finite.2 inferInstance

/-- **Universality over a root.** An embedding `ℕ ↪ ℕ` with `0 ↦ 5` and `1 ↦ 3`, literally. -/
theorem test_pure_universality :
    ∃ e : ℕ ↪[Language.empty] ℕ, e 0 = 5 ∧ e 1 = 3 := by
  obtain ⟨e, he⟩ := test_universality age_nat_subset extends_nat Structure.cg_of_countable fg_fin2
    (root 0 1 (by decide)) (root 5 3 (by decide))
  have h0 := DFunLike.congr_fun he 0
  have h1 := DFunLike.congr_fun he 1
  exact ⟨e, h0, h1⟩

/-- **Uniqueness over the swap root**, by the adapter in both directions: an automorphism of `ℕ`
exchanging `0` and `1`, so certainly not the identity. -/
theorem test_pure_uniqueness_swap :
    ∃ e : ℕ ≃[Language.empty] ℕ, e 0 = 1 ∧ e 1 = 0 := by
  obtain ⟨e, he⟩ := test_uniqueness_two_families age_nat_subset age_nat_subset extends_nat
    extends_nat Structure.cg_of_countable Structure.cg_of_countable fg_fin2
    (root 0 1 (by decide)) (root 1 0 (by decide))
  have h0 := DFunLike.congr_fun he 0
  have h1 := DFunLike.congr_fun he 1
  exact ⟨e, h0, h1⟩

/-! #### Repeated tuple coordinates -/

/-- **A repeated tuple converts when the diagram repeats too.** The one-point diagram, generated by
`(0, 0)`, occurs at `(7, 7)`. -/
theorem test_repeated_converts :
    ∃ o : Fin 1 ↪[Language.empty] ℕ, ∀ i, o (![0, 0] i) = ![7, 7] i := by
  refine receiptA_exists_embedding ![0, 0] ?_ ![7, 7] ((pure_atomicEquivalent_iff _ _).2 ?_)
  · refine eq_top_iff.2 fun x _ ↦ subset_closure ⟨0, ?_⟩
    exact Subsingleton.elim _ _
  · simp [Fin.forall_fin_two]

/-- **Repetition is not invented.** The distinct generators of `Fin 2` do not occur at the repeated
tuple `(7, 7)`: the atomic equivalence fails, and so does every embedding. -/
theorem test_repeated_rejected :
    ¬ AtomicEquivalent Language.empty (id : Fin 2 → Fin 2) ![7, 7] ∧
      ¬ ∃ o : Fin 2 ↪[Language.empty] ℕ, ∀ i, o i = ![7, 7] i := by
  refine ⟨fun h ↦ ?_, fun ⟨o, ho⟩ ↦ ?_⟩
  · have := ((pure_atomicEquivalent_iff _ _).1 h 0 1).2 rfl
    exact absurd this (by decide)
  · exact absurd (o.injective ((ho 0).trans (ho 1).symm)) (by decide)

/-- **Repetition is not lost.** A repeated generator cannot occur at a non-repeated tuple. -/
theorem test_repeated_not_split :
    ¬ ∃ o : Fin 1 ↪[Language.empty] ℕ, ∀ i, o (![0, 0] i) = ![7, 8] i := by
  rintro ⟨o, ho⟩
  have h0 := ho 0
  have h1 := ho 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  omega

end Pure

/-! ### Relation reflection, nullary and unary -/

/-- One nullary symbol (`0`) and one unary symbol (`1`). -/
def RelSym : ℕ → Type
  | 0 => Unit
  | 1 => Unit
  | _ + 2 => Empty

/-- A relational language with a nullary and a unary relation symbol. -/
def relLang : Language.{0, 0} :=
  ⟨fun _ ↦ Empty, RelSym⟩

/-- The one-point structure with the nullary relation interpreted by `r` and the unary one by
`p`. -/
def RelPt (_r _p : Prop) : Type :=
  Unit

instance (r p : Prop) : relLang.Structure (RelPt r p) where
  funMap := fun f ↦ Empty.elim f
  RelMap := fun {n} R _ ↦
    match n, R with
    | 0, _ => r
    | 1, _ => p
    | _ + 2, R => Empty.elim R

/-- A map preserves the **positive** relation atoms. -/
def PreservesPositive {X Y : Type} [relLang.Structure X] [relLang.Structure Y] (f : X → Y) :
    Prop :=
  ∀ {n} (R : relLang.Relations n) (x : Fin n → X), RelMap R x → RelMap R (f ∘ x)

/-- **Positive preservation is not an embedding: nullary.** The identity preserves every positive
atom of the point where the nullary relation fails, but no embedding reaches the point where it
holds, because an embedding also reflects it. -/
theorem test_positive_not_embedding_nullary :
    PreservesPositive (X := RelPt False False) (Y := RelPt True False) id ∧
      IsEmpty (RelPt False False ↪[relLang] RelPt True False) := by
  refine ⟨fun {n} R x hx ↦ ?_, ⟨fun e ↦ ?_⟩⟩
  · match n, R with
    | 0, _ => exact hx.elim
    | 1, _ => exact hx.elim
    | _ + 2, R => exact R.elim
  · have h := e.map_rel (n := 0) (show relLang.Relations 0 from ()) Fin.elim0
    exact (h.1 trivial).elim

/-- **Positive preservation is not an embedding: unary.** The same, for the unary relation. -/
theorem test_positive_not_embedding_unary :
    PreservesPositive (X := RelPt False False) (Y := RelPt False True) id ∧
      IsEmpty (RelPt False False ↪[relLang] RelPt False True) := by
  refine ⟨fun {n} R x hx ↦ ?_, ⟨fun e ↦ ?_⟩⟩
  · match n, R with
    | 0, _ => exact hx.elim
    | 1, _ => exact hx.elim
    | _ + 2, R => exact R.elim
  · have h := e.map_rel (n := 1) (show relLang.Relations 1 from ()) ![()]
    exact (h.1 trivial).elim

/-! ### A closed-image restriction does not give `ExtendsRepresentatives`

`ExtendsRepresentatives` quantifies over **every** embedding between representatives. Here the
morphisms are restricted by an external closed-image condition (an initial-segment image), and the
restricted extension property holds while the full one fails. So the bridge from such a
presentation needs its own theorem: the restricted property does not supply it. -/

section Order

instance : Language.order.Structure ℕ := Language.orderStructure ℕ

instance (n : ℕ) : Language.order.Structure (Fin n) := Language.orderStructure (Fin n)

instance : Language.order.OrderedStructure ℕ :=
  ⟨fun _ ↦ Iff.rfl⟩

instance (n : ℕ) : Language.order.OrderedStructure (Fin n) :=
  ⟨fun _ ↦ Iff.rfl⟩

/-- The representatives: `Fin n` with its order. -/
abbrev G (n : ℕ) : Bundled.{0} Language.order.Structure :=
  ⟨Fin n, inferInstance⟩

/-- A strictly monotone map, as an embedding in the order language. -/
def ordEmb {X Y : Type} [LinearOrder X] [LinearOrder Y] [Language.order.Structure X]
    [Language.order.OrderedStructure X] [Language.order.Structure Y]
    [Language.order.OrderedStructure Y] (f : X → Y) (hf : StrictMono f) :
    X ↪[Language.order] Y :=
  StrongHomClass.toEmbedding (OrderEmbedding.ofStrictMono f hf)

@[simp] theorem ordEmb_apply {X Y : Type} [LinearOrder X] [LinearOrder Y]
    [Language.order.Structure X] [Language.order.OrderedStructure X] [Language.order.Structure Y]
    [Language.order.OrderedStructure Y] (f : X → Y)
    (hf : StrictMono f) (x : X) : ordEmb f hf x = f x :=
  rfl

/-- **The restricted extension property holds for `ℕ`**: along an initial-segment morphism, the
new points go above everything already used. -/
theorem test_initialSegment_extends (i j : ℕ) (f : G i ↪[Language.order] G j)
    (hf : ∀ k : Fin i, Fin.val (f k) = k) (g : G i ↪[Language.order] ℕ) :
    ∃ h : G j ↪[Language.order] ℕ, h.comp f = g := by
  classical
  let K := Finset.univ.sup (fun k : Fin i ↦ g k) + 1
  have hK : ∀ k : Fin i, g k < K := fun k ↦
    Nat.lt_succ_of_le (Finset.le_sup (f := fun k : Fin i ↦ g k) (Finset.mem_univ k))
  have hg : StrictMono (fun k : Fin i ↦ g k) := HomClass.strictMono g
  let h : Fin j → ℕ := fun y ↦ if hy : (y : ℕ) < i then g ⟨y, hy⟩ else K + y
  have hmono : StrictMono h := by
    intro y y' hyy'
    have hlt : (y : ℕ) < y' := hyy'
    simp only [h]
    split_ifs with h1 h2 h2
    · exact hg (show (⟨y, h1⟩ : Fin i) < ⟨y', h2⟩ from hlt)
    · have := hK ⟨y, h1⟩
      omega
    · omega
    · omega
  refine ⟨ordEmb h hmono, DFunLike.ext _ _ fun k ↦ ?_⟩
  have hk : Fin.val (f k) < i := (hf k).symm ▸ k.2
  change h (f k) = g k
  simp only [h, hk, dite_true]
  congr 1
  exact Fin.ext (hf k)

/-- The excluded ordinary embedding: `Fin 1 → Fin 2`, `0 ↦ 1`. Its image is not an initial
segment. -/
def lift : G 1 ↪[Language.order] G 2 :=
  ordEmb (fun _ : Fin 1 ↦ (1 : Fin 2)) fun a b hab ↦ absurd hab (by
    rw [Subsingleton.elim a b]
    exact lt_irrefl b)

theorem lift_not_initialSegment : ¬ ∀ k : Fin 1, Fin.val (lift k) = k := fun h ↦
  absurd (h 0) (by change Fin.val (1 : Fin 2) ≠ Fin.val (0 : Fin 1); decide)

/-- **The full extension property fails for `ℕ`**: extending `0 ↦ 0` along `lift` would need a
point below `0`. -/
theorem test_not_extendsRepresentatives : ¬ ExtendsRepresentatives G ℕ := by
  intro hext
  let g : G 1 ↪[Language.order] ℕ := ordEmb (fun _ : Fin 1 ↦ (0 : ℕ)) fun a b hab ↦ absurd hab (by
    rw [Subsingleton.elim a b]
    exact lt_irrefl b)
  obtain ⟨h, hh⟩ := hext 1 2 lift g
  have h1 : h (1 : Fin 2) = 0 := DFunLike.congr_fun hh (0 : Fin 1)
  have hlt : h (0 : Fin 2) < h (1 : Fin 2) :=
    HomClass.strictMono h (show (0 : Fin 2) < 1 by decide)
  omega

end Order

end ClosedDiagramAdapterAudit

#assert_standard_axioms ClosedDiagramAdapterAudit.receiptA_exists_embedding
#assert_standard_axioms ClosedDiagramAdapterAudit.receiptC_age_subset
#assert_standard_axioms ClosedDiagramAdapterAudit.test_universality
#assert_standard_axioms ClosedDiagramAdapterAudit.test_uniqueness_two_families
#assert_standard_axioms ClosedDiagramAdapterAudit.age_nat_subset
#assert_standard_axioms ClosedDiagramAdapterAudit.extends_nat
#assert_standard_axioms ClosedDiagramAdapterAudit.test_pure_universality
#assert_standard_axioms ClosedDiagramAdapterAudit.test_pure_uniqueness_swap
#assert_standard_axioms ClosedDiagramAdapterAudit.test_repeated_converts
#assert_standard_axioms ClosedDiagramAdapterAudit.test_repeated_rejected
#assert_standard_axioms ClosedDiagramAdapterAudit.test_repeated_not_split
#assert_standard_axioms ClosedDiagramAdapterAudit.test_positive_not_embedding_nullary
#assert_standard_axioms ClosedDiagramAdapterAudit.test_positive_not_embedding_unary
#assert_standard_axioms ClosedDiagramAdapterAudit.test_initialSegment_extends
#assert_standard_axioms ClosedDiagramAdapterAudit.lift_not_initialSegment
#assert_standard_axioms ClosedDiagramAdapterAudit.test_not_extendsRepresentatives
