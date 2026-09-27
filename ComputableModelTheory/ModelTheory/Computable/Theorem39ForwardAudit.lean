/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.Theorem39Forward
import ComputableModelTheory.ModelTheory.Computable.ListAgeCAP
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: CHMM Theorem 3.9, forward direction

`test_named_structure` pins the structure of the headline: it is the ω structure of the canonical
limit of the run the named CAP witness builds over the named base member, under a certificate for
*that* limit. `test_headline` is the three conclusions for it; `test_existential` forgets the
structure but keeps the certificate's dependence on the witness. `test_listAge_headline` discharges
every hypothesis on the list age.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

section General

open PartialAgeIn

variable {K : PartialAgeIn O L} (W : PartialCAPWitness O K) (i : ℕ) (h0 : (K.domainAt i).Nonempty)

/-- **The structure is the named run's**: its limit is the canonical limit of the chain `W` builds
over `i`, and the certificate is about that limit. -/
theorem test_named_structure (cert : (runLimit K W i h0).presentation.InfinitudeCertificate) :
    runStructure K W i h0 cert =
      ((runChain K W i (Set.Subset.refl O) h0).toLimit
        (runChain_uniformEvaluators K W i (Set.Subset.refl O) h0)).omegaStructure cert :=
  rfl

/-- **The headline**: computable homogeneity, the canonical age with compatibility both ways, and
`IsFraisseLimit`, for one structure. -/
theorem test_headline (hCHP : MappedPartialCHPIn O K) (hCJEP : K.PartialCJEPIn O)
    (cert : (runLimit K W i h0).presentation.InfinitudeCertificate) :
    Nonempty (ComputablyHomogeneousIn O (runStructure K W i h0 cert)) ∧
      (∃ r : RepresentationIsoIn O (runStructure K W i h0 cert).canonicalAge K,
        r.forward.GeneratorCompatible ∧ r.backward.GeneratorCompatible) ∧
      (letI : L.Structure ℕ := (runStructure K W i h0 cert).inst;
        L.IsFraisseLimit K.classSet ℕ) :=
  runStructure_fraisseLimit W i h0 hCHP hCJEP cert

/-- **The existential form**, with the certificate still about the named witness's run. -/
theorem test_existential (hCHP : MappedPartialCHPIn O K) (hCJEP : K.PartialCJEPIn O)
    (cert : (runLimit K W i h0).presentation.InfinitudeCertificate) :
    ∃ F : ComputableStructureIn O L,
      Nonempty (ComputablyHomogeneousIn O F) ∧
        (∃ r : RepresentationIsoIn O F.canonicalAge K,
          r.forward.GeneratorCompatible ∧ r.backward.GeneratorCompatible) ∧
        (letI : L.Structure ℕ := F.inst; L.IsFraisseLimit K.classSet ℕ) :=
  exists_computablyHomogeneous_fraisseLimit W i h0 hCHP hCJEP cert

end General

section Fixture

variable (O : Set (ℕ →. ℕ))

/-- **On the list age**, every hypothesis discharged: the pushout CAP witness over `{0}`, the
selectors, and the certificate of that run's limit. -/
theorem test_listAge_headline :
    Nonempty (ComputablyHomogeneousIn O (PartialAgeIn.runStructure (listAge O)
        (listAge.capWitness O) (encode [0]) listAge.base_nonempty (listAge.runLimit_cert O))) ∧
      (∃ r : RepresentationIsoIn O (PartialAgeIn.runStructure (listAge O) (listAge.capWitness O)
          (encode [0]) listAge.base_nonempty (listAge.runLimit_cert O)).canonicalAge (listAge O),
        r.forward.GeneratorCompatible ∧ r.backward.GeneratorCompatible) ∧
      (letI : Language.empty.Structure ℕ := (PartialAgeIn.runStructure (listAge O)
          (listAge.capWitness O) (encode [0]) listAge.base_nonempty (listAge.runLimit_cert O)).inst;
        Language.empty.IsFraisseLimit (listAge O).classSet ℕ) :=
  PartialAgeIn.runStructure_fraisseLimit (listAge.capWitness O) (encode [0]) listAge.base_nonempty
    listAge.mappedPartialCHPIn listAge.partialCJEPIn (listAge.runLimit_cert O)

end Fixture

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_named_structure
#assert_standard_axioms FirstOrder.Language.test_headline
#assert_standard_axioms FirstOrder.Language.test_existential
#assert_standard_axioms FirstOrder.Language.test_listAge_headline
