/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PureSetExample
import ComputableModelTheory.ModelTheory.Computable.ListAgeExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the semantic Fraïssé criterion

**The generic theorem, in its four steps.** `test_classSet` (isomorphism closure, membership,
invariance, finite generation), `test_coverage_derived` (coverage from JEP and extension — it is not
a hypothesis), `test_age_eq`, `test_extension_pair`, `test_isFraisseLimit`. The hypotheses are
exactly semantic HP, semantic JEP, and the chain data; no base witness, no selector, no certificate,
no oracle inclusion appears in any signature.

**Through the classical criterion.** The stage images form a family of substructures of the limit
(`test_stageRange_coherent`, `test_stageRange_cofinal`), the chain data and HP make it extension
rich (`test_extensionRich`), and the class is hereditary with every stage image in it
(`test_classSet_inputs`); coverage is the upper-layer JEP argument (`test_stageRange_coverage`). In
every row the family lives at `O` and the chain at `E`, with no inclusion between them.

**Discharged on an actual fixture.** `test_tiny_isFraisseLimit` is `IsFraisseLimit` for the
two-member age's limit, obtained by discharging every hypothesis on `tinyAge` — not by restating the
generic theorem under assumed hypotheses. The surrounding rows exhibit the discharged inputs: HP
and JEP hold, every stage is the point, the extension property holds, and the limit's age is the
represented class, which contains both the empty member and the point.
-/

open FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

section General

variable (K : PartialAgeIn O L) {E : Set (ℕ →. ℕ)} {D : CeStructureChainIn E L} {Z : D.LimitIn}

theorem test_classSet (i : ℕ) {A B : CategoryTheory.Bundled L.Structure} (hA : A ∈ K.classSet)
    (e : A ≃[L] B) :
    K.memberBundled i ∈ K.classSet ∧ B ∈ K.classSet ∧ Structure.FG L A :=
  ⟨K.memberBundled_mem_classSet i, K.classSet_equiv_invariant hA e, K.classSet_fg hA⟩

/-- **Coverage is derived**, from JEP and the extension property. -/
theorem test_coverage_derived (C : CeStructureChainIn.LimitIn.FraisseChainData K Z)
    (hJ : K.HasJEP) (i : ℕ) :
    ∃ s, Nonempty ((K.memberAt i).domain ↪[L] (D.stageAt s).domain) :=
  C.coverage hJ i

theorem test_age_eq (C : CeStructureChainIn.LimitIn.FraisseChainData K Z) (hHP : K.HasHP)
    (hJ : K.HasJEP) : L.age Z.presentation.domain = K.classSet :=
  C.age_eq hHP hJ

theorem test_extension_pair (C : CeStructureChainIn.LimitIn.FraisseChainData K Z)
    (hHP : K.HasHP) : L.IsExtensionPair Z.presentation.domain Z.presentation.domain :=
  C.isExtensionPair hHP

theorem test_isFraisseLimit (C : CeStructureChainIn.LimitIn.FraisseChainData K Z) (hHP : K.HasHP)
    (hJ : K.HasJEP) : L.IsFraisseLimit K.classSet Z.presentation.domain :=
  C.isFraisseLimit hHP hJ

/-- **Coherence**: earlier stage images lie in later ones, and every limit element is in one. -/
theorem test_stageRange_coherent {r s : ℕ} (hrs : r ≤ s) (x : Z.presentation.domain) :
    Z.stageRange r ≤ Z.stageRange s ∧ ∃ t, x ∈ Z.stageRange t :=
  ⟨CeStructureChainIn.LimitIn.stageRange_mono hrs,
    CeStructureChainIn.LimitIn.exists_mem_stageRange x⟩

/-- **The stage images are finitely cofinal.** -/
theorem test_stageRange_cofinal : FGCofinal Z.stageRange :=
  CeStructureChainIn.LimitIn.fgCofinal_stageRange Z

/-- **Extension richness from the chain data and HP** — the family oracle `O` and the chain oracle
`E` independent, with no inclusion. -/
theorem test_extensionRich (C : CeStructureChainIn.LimitIn.FraisseChainData K Z)
    (hHP : K.HasHP) : ExtensionRich Z.stageRange :=
  C.extensionRich hHP

/-- The class inputs of the age theorem: heredity from HP, and every stage image in the class. -/
theorem test_classSet_inputs (C : CeStructureChainIn.LimitIn.FraisseChainData K Z)
    (hHP : K.HasHP) (r : ℕ) :
    Hereditary K.classSet ∧
      CategoryTheory.Bundled.of (c := L.Structure) (Z.stageRange r) ∈ K.classSet :=
  ⟨hHP.classSet_hereditary, C.stageRange_mem_classSet r⟩

/-- Coverage of the class by the stage images: the upper-layer JEP argument. -/
theorem test_stageRange_coverage (C : CeStructureChainIn.LimitIn.FraisseChainData K Z)
    (hJ : K.HasJEP) {A : CategoryTheory.Bundled L.Structure} (hA : A ∈ K.classSet) :
    ∃ r, Nonempty (A ↪[L] Z.stageRange r) :=
  C.exists_embedding_stageRange hJ hA

end General

/-! ### The fixture -/

section Fixture

variable (O : Set (ℕ →. ℕ))

theorem test_tiny_inputs :
    (tinyAge O).HasHP ∧ (tinyAge O).HasJEP ∧
      CeStructureChainIn.LimitIn.FraisseChainData (tinyAge O) (tinyAge.limit O) :=
  ⟨tinyAge.hasHP O, tinyAge.hasJEP O, tinyAge.fraisseChainData O⟩

/-- **`IsFraisseLimit` on an actual limit**, every hypothesis discharged. -/
theorem test_tiny_isFraisseLimit :
    Language.empty.IsFraisseLimit (tinyAge O).classSet (tinyAge.limit O).presentation.domain :=
  tinyAge.limit_isFraisseLimit O

/-- The limit's age is the represented class, which contains the empty member and the point. -/
theorem test_tiny_age :
    Language.empty.age (tinyAge.limit O).presentation.domain = (tinyAge O).classSet ∧
      (tinyAge O).memberBundled 0 ∈ (tinyAge O).classSet ∧
        (tinyAge O).memberBundled 1 ∈ (tinyAge O).classSet :=
  ⟨(tinyAge.fraisseChainData O).age_eq (tinyAge.hasHP O) (tinyAge.hasJEP O),
    (tinyAge O).memberBundled_mem_classSet 0, (tinyAge O).memberBundled_mem_classSet 1⟩

/-- The two members really are distinct: the empty member is empty, the point is inhabited. -/
theorem test_tiny_members :
    IsEmpty ((tinyAge O).memberAt 0).domain ∧ Nonempty ((tinyAge O).memberAt 1).domain :=
  ⟨⟨fun a ↦ Nat.lt_irrefl 0 ((tinyAge.mem_domainAt_iff O).1 a.2).1⟩,
    ⟨tinyAge.point O Nat.one_pos⟩⟩

/-- **The new route on a nontrivial fixture**: the list age's initial-segment chain makes its
stage images extension rich, and ultrahomogeneity follows from the classical criterion. -/
theorem test_listAge_extensionRich :
    ExtensionRich (listAge.limit O).stageRange ∧
      Language.empty.IsUltrahomogeneous (listAge.limit O).presentation.domain :=
  ⟨(listAge.fraisseChainData O).extensionRich (listAge.hasMappedHP O).hasHP,
    isUltrahomogeneous_of_extensionRich Structure.cg_of_countable
      (CeStructureChainIn.LimitIn.fgCofinal_stageRange _)
      ((listAge.fraisseChainData O).extensionRich (listAge.hasMappedHP O).hasHP)⟩

/-- And on the two-member age. -/
theorem test_tiny_extensionRich : ExtensionRich (tinyAge.limit O).stageRange :=
  (tinyAge.fraisseChainData O).extensionRich (tinyAge.hasHP O)

end Fixture

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_classSet
#assert_standard_axioms FirstOrder.Language.test_coverage_derived
#assert_standard_axioms FirstOrder.Language.test_age_eq
#assert_standard_axioms FirstOrder.Language.test_extension_pair
#assert_standard_axioms FirstOrder.Language.test_isFraisseLimit
#assert_standard_axioms FirstOrder.Language.test_tiny_inputs
#assert_standard_axioms FirstOrder.Language.test_tiny_isFraisseLimit
#assert_standard_axioms FirstOrder.Language.test_tiny_age
#assert_standard_axioms FirstOrder.Language.test_tiny_members
#assert_standard_axioms FirstOrder.Language.test_stageRange_coherent
#assert_standard_axioms FirstOrder.Language.test_stageRange_cofinal
#assert_standard_axioms FirstOrder.Language.test_extensionRich
#assert_standard_axioms FirstOrder.Language.test_classSet_inputs
#assert_standard_axioms FirstOrder.Language.test_stageRange_coverage
#assert_standard_axioms FirstOrder.Language.test_listAge_extensionRich
#assert_standard_axioms FirstOrder.Language.test_tiny_extensionRich
