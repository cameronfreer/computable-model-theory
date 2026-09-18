/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PureSetExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the semantic Fraïssé criterion

**The generic theorem, in its four steps.** `test_classSet` (isomorphism closure, membership,
invariance, finite generation), `test_coverage_derived` (coverage from JEP and extension — it is not
a hypothesis), `test_age_eq`, `test_extension_pair`, `test_isFraisseLimit`. The hypotheses are
exactly semantic HP, semantic JEP, and the chain data; no base witness, no selector, no certificate,
no oracle inclusion appears in any signature.

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
