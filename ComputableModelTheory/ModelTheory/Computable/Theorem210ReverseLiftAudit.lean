/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.Theorem210ReverseLift
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the selector-oracle rebase

**The rebase preserves data, not just meaning.** `test_mono_preserves_data` and
`test_mono_preserves_member` are `rfl` across every field a consumer can observe — structures,
enumeration, generators, both evaluators, the carriers, and taking a member. Nothing is
reconstructed, so nothing can be reconstructed *differently*; only the computability proofs are
lifted. An implementation that rebuilt any of this would fail these rows even if it happened to be
extensionally right.

**The effective properties are unchanged on the nose.** `test_mono_cjep`, `test_mono_chp`,
`test_mono_jointSpec` and `test_mono_chpSpec` are `Iff.rfl`: CJEP, CHP and their selector-facing
forms quantify only over data `mono` preserves definitionally. So this is not a transport theorem —
there is nothing to transport. `K`'s effective properties at `E` *are* `K.mono hOE`'s.

**The crossing is in the statement.** `test_lifted_theorem`'s conclusion is about `K.mono hOE`, not
`K`, because `RepresentationCoverIn` relates two representations at one family oracle and the limit
of `E`-computable selectors is `E`-computable. `test_crossing_is_visible` says the same thing by
shape: the isomorphism's second argument is the rebased family.

**The certificate still is not free.** `test_lifted_cjep_gives_no_certificate` produces only the
scheduled package, exactly as at the base oracle — infinitude belongs to the particular limit the
particular selector builds, and no amount of oracle strength supplies it.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-! ### The member level -/

/-- **A rebased member is the same presentation.** -/
theorem test_mono_member_data (P : PartialCePresentationIn O L) (hOE : O ⊆ E) :
    (P.mono hOE).str = P.str ∧ (P.mono hOE).enum? = P.enum? ∧
      (P.mono hOE).funEval = P.funEval ∧ (P.mono hOE).relEval = P.relEval ∧
        (P.mono hOE).domain = P.domain :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

namespace PartialAgeIn

variable {K : PartialAgeIn O L}

/-! ### The family level -/

/-- **Every observable field is carried over definitionally**, so a rebased family cannot differ
from the original in anything a consumer can see. -/
theorem test_mono_preserves_data (hOE : O ⊆ E) :
    (K.mono hOE).structureAt = K.structureAt ∧ (K.mono hOE).enum? = K.enum? ∧
      (K.mono hOE).gens = K.gens ∧ (K.mono hOE).funEval = K.funEval ∧
        (K.mono hOE).relEval = K.relEval ∧ ∀ i, (K.mono hOE).domainAt i = K.domainAt i :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ ↦ rfl⟩

/-- **And rebasing commutes with taking a member**, so member-level facts cross the boundary with
no transport at all. -/
theorem test_mono_preserves_member (hOE : O ⊆ E) (i : ℕ) :
    (K.mono hOE).memberAt i = (K.memberAt i).mono hOE :=
  rfl

/-! ### The effective properties are unchanged -/

/-- **CJEP is unchanged** — `Iff.rfl`, since it quantifies only over preserved data. -/
theorem test_mono_cjep (hOE : O ⊆ E) {E' : Set (ℕ →. ℕ)} :
    (K.mono hOE).PartialCJEPIn E' ↔ K.PartialCJEPIn E' :=
  mono_partialCJEPIn hOE

/-- **And so is CHP.** Together these say the rebase changes effectivity evidence, not the
represented family. -/
theorem test_mono_chp (hOE : O ⊆ E) {E' : Set (ℕ →. ℕ)} :
    MappedPartialCHPIn E' (K.mono hOE) ↔ MappedPartialCHPIn E' K :=
  mono_mappedPartialCHPIn hOE

/-- The selector-facing forms too, which is what the producers actually consume. -/
theorem test_mono_specs (hOE : O ⊆ E) {sel : ℕ → ℕ → PartialJointEmbeddingData}
    {chpSel : ℕ → List ℕ →. ℕ} :
    ((K.mono hOE).JointSpec sel ↔ K.JointSpec sel) ∧
      ((K.mono hOE).MappedCHPSpec chpSel ↔ K.MappedCHPSpec chpSel) :=
  ⟨mono_jointSpec hOE, mono_mappedCHPSpec hOE⟩

/-! ### The lifted construction -/

/-- **`E`-CJEP plus a base witness gives the rebased scheduled package — and no certificate.**
Oracle strength does not supply infinitude, which is a property of one limit. -/
theorem test_lifted_cjep_gives_no_certificate (hOE : O ⊆ E) (h : K.PartialCJEPIn E) {baseIdx : ℕ}
    (hbase : (K.domainAt baseIdx).Nonempty) : Nonempty (ScheduledCJEPDataIn (K.mono hOE)) :=
  exists_scheduledCJEPData_of_subset hOE h hbase

/-- **Theorem 2.10(⇐) with selectors at a stronger oracle**, compatible in both directions. -/
theorem test_lifted_theorem (hOE : O ⊆ E) (W : OmegaCJEPDataIn (K.mono hOE))
    (hCHP : K.MappedPartialCHPIn E) :
    ∃ (S : ComputableStructureIn E L) (r : RepresentationIsoIn E S.canonicalAge (K.mono hOE)),
      r.forward.GeneratorCompatible ∧ r.backward.GeneratorCompatible :=
  exists_compatibleCanonicalAge_omega_of_subset hOE W hCHP

/-- **The crossing is visible in the statement.** The conclusion is about `K.mono hOE`: the limit of
`E`-computable selectors is `E`-computable, and `RepresentationCoverIn` relates representations at
one family oracle, so the rebased family is the only thing the isomorphism can be about. Hiding this
inside the proof would misreport what was proved. -/
theorem test_crossing_is_visible (hOE : O ⊆ E) (W : OmegaCJEPDataIn (K.mono hOE))
    (hCHP : K.MappedPartialCHPIn E) :
    ∃ S : ComputableStructureIn E L, (K.mono hOE).IsCanonicalAgeOfIn E S :=
  exists_isCanonicalAgeOfIn_of_subset hOE W hCHP

/-- The base-oracle theorem is the `O = E` case, and needs no rebase at all. -/
theorem test_base_oracle_is_the_identity_case (W : OmegaCJEPDataIn K)
    (hCHP : K.MappedPartialCHPIn O) :
    ∃ S : ComputableStructureIn O L, K.IsCanonicalAgeOfIn O S :=
  exists_isCanonicalAgeOfIn W hCHP

end PartialAgeIn

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_mono_member_data
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_mono_preserves_data
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_mono_preserves_member
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_mono_cjep
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_mono_chp
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_mono_specs
#assert_standard_axioms
  FirstOrder.Language.PartialAgeIn.test_lifted_cjep_gives_no_certificate
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_lifted_theorem
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_crossing_is_visible
#assert_standard_axioms
  FirstOrder.Language.PartialAgeIn.test_base_oracle_is_the_identity_case
