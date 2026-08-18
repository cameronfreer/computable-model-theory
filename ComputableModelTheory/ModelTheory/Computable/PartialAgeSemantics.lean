/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialAge
import ComputableModelTheory.ModelTheory.TupleClosure

/-!
# The semantic layer of empty-capable representations

The isomorphism-class semantics of a `PartialAgeIn`, over which CHMM Theorem 2.8's
same-class conclusion and its hereditary hypothesis are stated. Each possibly-empty
member induces a first-order structure on its carrier subtype (`subtypeStr`), so a
member is a genuine structure — even the empty one — and members of different families
are compared by first-order equivalence of these induced structures (`IsoTo`).

* `SameClass A A'` — the two families represent the same isomorphism classes: every
  member of each is `IsoTo` some member of the other.
* `HasHP A` — the **semantic** hereditary property: every finitely generated
  substructure of every member (a `Substructure.closure` of a finite tuple in the
  induced structure) is `IsoTo` some member. This is the general hypothesis of
  Theorem 2.8; the coded `ComputableAgeIn.IndexedHP` is only an all-ℕ adapter for it,
  not its definition — it cannot even name an empty source member.

`IsoTo` is reflexive and symmetric; `SameClass` is reflexive and symmetric. For the
all-ℕ bridge, `toPartialAge`'s members carry their full ℕ carrier, so their induced
structure is `topEquiv`-equivalent to the ambient structure.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- The structure a possibly-empty presentation induces on its (possibly empty)
carrier subtype — the semantic reading of the member. -/
@[reducible]
def _root_.FirstOrder.Language.PartialCePresentationIn.subtypeStr
    (P : PartialCePresentationIn O L) : L.Structure P.domain where
  funMap {_} f v :=
    ⟨@Structure.funMap L ℕ P.str _ f fun k ↦ (v k).1,
      P.domain_closed _ f _ fun k ↦ (v k).2⟩
  RelMap {_} R v := @Structure.RelMap L ℕ P.str _ R fun k ↦ (v k).1

instance (P : PartialCePresentationIn O L) : L.Structure P.domain :=
  P.subtypeStr

/-- The carrier subtype sits inside `ℕ` as a substructure of the ambient stored structure, by the
very definition of `subtypeStr`. All four laws are `rfl`. The empty-capable twin of
`CePresentationIn.domainInclusion`; stated with `P.str` supplied explicitly, since no
`L.Structure ℕ` instance exists. -/
def _root_.FirstOrder.Language.PartialCePresentationIn.domainInclusion
    (P : PartialCePresentationIn O L) : @Language.Embedding L P.domain ℕ _ P.str :=
  letI : L.Structure ℕ := P.str
  { toFun := Subtype.val
    inj' := Subtype.val_injective
    map_fun' := fun _ _ ↦ rfl
    map_rel' := fun _ _ ↦ Iff.rfl }

@[simp]
theorem _root_.FirstOrder.Language.PartialCePresentationIn.domainInclusion_apply
    (P : PartialCePresentationIn O L) (x : P.domain) : P.domainInclusion x = (x : ℕ) :=
  rfl

namespace PartialCePresentationIn

/-- Member isomorphism: first-order equivalence of the induced subtype structures. -/
def IsoTo (P Q : PartialCePresentationIn O L) : Prop :=
  Nonempty (P.domain ≃[L] Q.domain)

@[refl]
theorem IsoTo.refl (P : PartialCePresentationIn O L) : P.IsoTo P :=
  ⟨Language.Equiv.refl L _⟩

theorem IsoTo.symm {P Q : PartialCePresentationIn O L} (h : P.IsoTo Q) : Q.IsoTo P :=
  h.elim fun e ↦ ⟨e.symm⟩

theorem IsoTo.trans {P Q W : PartialCePresentationIn O L}
    (h₁ : P.IsoTo Q) (h₂ : Q.IsoTo W) : P.IsoTo W :=
  h₁.elim fun e₁ ↦ h₂.elim fun e₂ ↦ ⟨e₂.comp e₁⟩

/-- Realizing a term inside a member's carrier is realizing it in the ambient structure, on
the underlying values — the inclusion is a homomorphism, by construction of
`subtypeStr`. -/
theorem realize_domain_val (P : PartialCePresentationIn O L) {n : ℕ} (v : Fin n → P.domain)
    (T : L.Term (Fin n)) :
    ((T.realize v : P.domain) : ℕ) =
      @Term.realize L ℕ P.str _ (fun k ↦ ((v k : ℕ))) T := by
  induction T with
  | var k => rfl
  | @func m f ts ih =>
    show @Structure.funMap L ℕ P.str m f (fun k ↦ (((ts k).realize v : P.domain) : ℕ)) =
      @Structure.funMap L ℕ P.str m f
        fun k ↦ @Term.realize L ℕ P.str _ (fun k ↦ ((v k : ℕ))) (ts k)
    exact congrArg _ (funext fun k ↦ ih k)

/-! ### Identity-on-underlying bridges

Two semantic bridges between members, both the identity on the underlying naturals. They
are what lets a construction stated on **raw** carriers be compared with one stated inside
a member's carrier **subtype**; nothing about enumerations or evaluators enters, and
neither needs a nonemptiness hypothesis. -/

/-- Members with the same ambient structure data and the same carrier are first-order
equivalent, by the identity. No nonemptiness is required: an empty carrier closes through
the domain equality alone. -/
def eqDomainEquiv {P Q : PartialCePresentationIn O L} (hstr : Q.str = P.str)
    (hdom : Q.domain = P.domain) : Q.domain ≃[L] P.domain where
  toFun q := ⟨q.1, by rw [← hdom]; exact q.2⟩
  invFun p := ⟨p.1, by rw [hdom]; exact p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_fun' {m} f v := Subtype.ext (by
    show @Structure.funMap L ℕ Q.str m f (fun k ↦ (v k).1) =
      @Structure.funMap L ℕ P.str m f (fun k ↦ (v k).1)
    rw [hstr])
  map_rel' {m} r v := by
    show @Structure.RelMap L ℕ P.str m r (fun k ↦ (v k).1) ↔
      @Structure.RelMap L ℕ Q.str m r (fun k ↦ (v k).1)
    rw [hstr]

/-- A member whose carrier is contained in another's, with the same ambient structure data,
embeds in it by the identity. The `⊆` companion of `eqDomainEquiv`; again no nonemptiness
is required. -/
def subsetDomainEmbedding {P Q : PartialCePresentationIn O L} (hstr : Q.str = P.str)
    (hdom : Q.domain ⊆ P.domain) : Q.domain ↪[L] P.domain where
  toFun q := ⟨q.1, hdom q.2⟩
  inj' _ _ h := Subtype.ext (congrArg Subtype.val h : (_ : ℕ) = _)
  map_fun' {m} f v := Subtype.ext (by
    show @Structure.funMap L ℕ Q.str m f (fun k ↦ (v k).1) =
      @Structure.funMap L ℕ P.str m f (fun k ↦ (v k).1)
    rw [hstr])
  map_rel' {m} r v := by
    show @Structure.RelMap L ℕ P.str m r (fun k ↦ (v k).1) ↔
      @Structure.RelMap L ℕ Q.str m r (fun k ↦ (v k).1)
    rw [hstr]

/-- **The generated-carrier bridge.** A member whose carrier consists exactly of the
underlying values of the terms over a tuple `t` drawn from another member's carrier is
first-order equivalent to the closure of `t` computed **inside** that other member's
carrier subtype.

Both sides are the identity on the underlying naturals; the content is that a raw-domain
subtype and a closure inside a subtype agree, functions and relations included. The
hypothesis is stated by term values rather than by an ambient substructure, so no
substructure of `ℕ` at the unnamed instance `P.str` ever has to be formed. Reusable
wherever a generated substructure is presented on raw carriers. -/
def closureDomainEquiv {P Q : PartialCePresentationIn O L} {n : ℕ} (t : Fin n → P.domain)
    (hstr : Q.str = P.str)
    (hdom : ∀ x : ℕ, x ∈ Q.domain ↔ ∃ T : L.Term (Fin n), ((T.realize t : P.domain) : ℕ) = x) :
    Q.domain ≃[L] Substructure.closure L (Set.range t) := by
  have hmem : ∀ q : Q.domain, (q.1 : ℕ) ∈ P.domain := by
    rintro ⟨x, hx⟩
    obtain ⟨T, hT⟩ := (hdom x).1 hx
    exact hT ▸ (T.realize t).2
  have hclo : ∀ q : Q.domain,
      (⟨q.1, hmem q⟩ : P.domain) ∈ Substructure.closure L (Set.range t) := by
    intro q
    obtain ⟨T, hT⟩ := (hdom q.1).1 q.2
    exact (mem_closure_range_iff_exists_term t).2 ⟨T, Subtype.ext hT⟩
  have hback : ∀ s : Substructure.closure L (Set.range t), ((s : P.domain) : ℕ) ∈ Q.domain := by
    intro s
    obtain ⟨T, hT⟩ := (mem_closure_range_iff_exists_term t).1 s.2
    exact (hdom _).2 ⟨T, congrArg Subtype.val hT⟩
  exact
    { toFun := fun q ↦ ⟨⟨q.1, hmem q⟩, hclo q⟩
      invFun := fun s ↦ ⟨((s : P.domain) : ℕ), hback s⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_fun' := fun {m} f v ↦ Subtype.ext (Subtype.ext (by
        show @Structure.funMap L ℕ Q.str m f (fun k ↦ (v k).1) =
          @Structure.funMap L ℕ P.str m f (fun k ↦ (v k).1)
        rw [hstr]))
      map_rel' := fun {m} r v ↦ by
        show @Structure.RelMap L ℕ P.str m r (fun k ↦ (v k).1) ↔
          @Structure.RelMap L ℕ Q.str m r (fun k ↦ (v k).1)
        rw [hstr] }

end PartialCePresentationIn

namespace PartialAgeIn

variable (A A' : PartialAgeIn O L)

/-- The induced structure on member `i`'s carrier. -/
@[reducible]
noncomputable def memberSubtypeStr (i : ℕ) : L.Structure (A.domainAt i) :=
  (A.memberAt i).subtypeStr

/-- The two families represent the same isomorphism classes. -/
def SameClass : Prop :=
  (∀ i, ∃ j, (A.memberAt i).IsoTo (A'.memberAt j)) ∧
    (∀ j, ∃ i, (A'.memberAt j).IsoTo (A.memberAt i))

@[refl]
theorem SameClass.refl : A.SameClass A :=
  ⟨fun i ↦ ⟨i, .refl _⟩, fun j ↦ ⟨j, .refl _⟩⟩

theorem SameClass.symm {A A' : PartialAgeIn O L} (h : A.SameClass A') : A'.SameClass A :=
  ⟨h.2, h.1⟩

/-- The **semantic** hereditary property: every finitely generated substructure of
every member is `IsoTo` some member. Stated over the induced structure via
`Substructure.closure`; no all-ℕ carrier and no coding assumption. -/
def HasHP : Prop :=
  ∀ (i n : ℕ) (t : Fin n → (A.memberAt i).domain),
    ∃ j : ℕ, Nonempty
      ((Substructure.closure L (Set.range t)) ≃[L] (A.memberAt j).domain)

end PartialAgeIn

namespace ComputableAgeIn

variable (K : ComputableAgeIn O L)

/-- The all-ℕ bridge at the representation level: `toPartialAge`'s member `i` induces
exactly the ambient structure on its full ℕ carrier — the induced subtype structure is
first-order equivalent to `structureAt i`. -/
noncomputable def toPartialAge_memberEquiv (i : ℕ) :
    @Language.Equiv L (K.toPartialAge.memberAt i).domain ℕ _ (K.structureAt i) :=
  letI : L.Structure ℕ := K.structureAt i
  { toFun := fun x ↦ x.1
    invFun := fun x ↦ ⟨x, ⟨x, rfl⟩⟩
    left_inv := fun _ ↦ Subtype.ext rfl
    right_inv := fun _ ↦ rfl
    map_fun' := fun {_} _ _ ↦ rfl
    map_rel' := fun {_} _ _ ↦ Iff.rfl }

/-! ### Carrier change between the stored structure and the member subtype

An all-ℕ member's carrier subtype and the ambient structure are the same thing, but they are
*different types*, and the ambient `K.structureAt i` is not an instance — so an embedding
between two ambient structures at different indices needs **two distinct `L.Structure ℕ`
instances at once**, which ordinary synthesis cannot supply and `letI` cannot fix.

The mechanism the library already provides is `GeneratedPresentationIn.toBundled`, whose
structure instance is *registered* (`instStructureToBundled`) precisely so it is found
"without an ambient structure on the raw carrier". Conjugating through it therefore removes
the verbosity rather than centralizing it: the two operations below are ordinary
compositions, and downstream bridges consume only them and their application lemmas. -/

/-- The bundled form of the all-ℕ member equivalence: member `i`'s carrier subtype is the
presentation at `i`, on a carrier whose structure instance is registered. -/
noncomputable def toPartialAge_memberEquivBundled (i : ℕ) :
    (K.toPartialAge.memberAt i).domain ≃[L] (K.presentationAt i).toBundled where
  toFun x := x.1
  invFun x := ⟨x, ⟨x, rfl⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_fun' _ _ := rfl
  map_rel' _ _ := Iff.rfl

/-- Carrier change, presentation → member: an embedding of the stored structures at two
indices, conjugated to the corresponding all-ℕ members' carrier subtypes. -/
noncomputable def embeddingToPartial {c e : ℕ}
    (g : (K.presentationAt c).toBundled ↪[L] (K.presentationAt e).toBundled) :
    (K.toPartialAge.memberAt c).domain ↪[L] (K.toPartialAge.memberAt e).domain :=
  (K.toPartialAge_memberEquivBundled e).symm.toEmbedding.comp
    (g.comp (K.toPartialAge_memberEquivBundled c).toEmbedding)

/-- Carrier change, member → presentation: the inverse conjugation. -/
noncomputable def embeddingOfPartial {c e : ℕ}
    (F : (K.toPartialAge.memberAt c).domain ↪[L] (K.toPartialAge.memberAt e).domain) :
    (K.presentationAt c).toBundled ↪[L] (K.presentationAt e).toBundled :=
  (K.toPartialAge_memberEquivBundled e).toEmbedding.comp
    (F.comp (K.toPartialAge_memberEquivBundled c).symm.toEmbedding)

/-- Every natural lies in an all-ℕ member's carrier. -/
theorem mem_toPartialAge_memberAt_domain (i x : ℕ) :
    x ∈ (K.toPartialAge.memberAt i).domain :=
  ⟨x, rfl⟩

@[simp]
theorem embeddingToPartial_coe {c e : ℕ}
    (g : (K.presentationAt c).toBundled ↪[L] (K.presentationAt e).toBundled)
    (x : (K.toPartialAge.memberAt c).domain) :
    ((K.embeddingToPartial g x : (K.toPartialAge.memberAt e).domain) : ℕ) = g x.1 :=
  rfl

/-- **Carrier conjugation respects composite equality.** Two composites of conjugated
embeddings are equal exactly when the underlying embeddings agree pointwise on `ℕ`. The
bundled-versus-pointwise crossing every commuting-square argument needs, proved without
rewriting through any structure instance: outward by applying both sides at the carrier
element over `x`, inward by `DFunLike.ext` and `Subtype.ext`. -/
theorem embeddingToPartial_comp_eq_iff_pointwise {d m₁ m₂ a : ℕ}
    (fl : (K.presentationAt d).toBundled ↪[L] (K.presentationAt m₁).toBundled)
    (gl : (K.presentationAt m₁).toBundled ↪[L] (K.presentationAt a).toBundled)
    (fr : (K.presentationAt d).toBundled ↪[L] (K.presentationAt m₂).toBundled)
    (gr : (K.presentationAt m₂).toBundled ↪[L] (K.presentationAt a).toBundled) :
    (K.embeddingToPartial gl).comp (K.embeddingToPartial fl) =
        (K.embeddingToPartial gr).comp (K.embeddingToPartial fr) ↔
      ∀ x : ℕ, gl (fl x) = gr (fr x) := by
  constructor
  · intro h x
    have hx := DFunLike.congr_fun h
      (⟨x, K.mem_toPartialAge_memberAt_domain d x⟩ : (K.toPartialAge.memberAt d).domain)
    exact congrArg Subtype.val hx
  · intro h
    refine DFunLike.ext _ _ fun y ↦ Subtype.ext ?_
    exact h (y : ℕ)

@[simp]
theorem embeddingOfPartial_apply {c e : ℕ}
    (F : (K.toPartialAge.memberAt c).domain ↪[L] (K.toPartialAge.memberAt e).domain)
    (x : (K.presentationAt c).toBundled) :
    K.embeddingOfPartial F x =
      ((F ⟨x, K.mem_toPartialAge_memberAt_domain c x⟩ :
        (K.toPartialAge.memberAt e).domain) : ℕ) :=
  rfl

end ComputableAgeIn

end FirstOrder.Language
