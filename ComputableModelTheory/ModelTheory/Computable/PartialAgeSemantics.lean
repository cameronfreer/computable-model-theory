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

end ComputableAgeIn

end FirstOrder.Language
