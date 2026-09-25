/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.RunCanonicalAge
import ComputableModelTheory.ModelTheory.Computable.ListAgeCAP
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the run's limit represents its own age

**One oracle.** Every row is at the family's oracle `O`: the CAP witness, both selectors, the run's
chain and its limit. `RepresentationCoverIn` admits no cover between families at different oracles.

**The forward cover** is the tuple pullback followed by CHP at the stage's member index:
`test_forward_generatorCompatible`.

**The backward cover is computed, not chosen.** `test_prefixPart_recursiveIn` is the prefix
iteration as a partial recursive program, with no certificate and no semantic extension property;
`test_prefixStep_spec` is one step's halting and invariant — CHP represents the next prefix, the
positional one-point requirement is admissible and fires, and the recomputed payload's right leg is
actual; `test_finalData` is the apex's embedding at the last prefix, read off positions `n + k` with
no inverse computed; `test_backward_generatorCompatible` is the cover.

**Both directions**: `test_runCanonicalIso`, `test_exists_from_selectors`,
`test_toLimit_exists`. **On the list age**, every hypothesis discharged:
`test_listAge_canonicalIso`.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

section General

open PartialAgeIn

variable {K : PartialAgeIn O L} {W : PartialCAPWitness O K} {i : ℕ}
  {h0 : (K.domainAt i).Nonempty} (Z : (runChain K W i (Set.Subset.refl O) h0).LimitIn)
  (cert : Z.presentation.InfinitudeCertificate)
  {chpSel : ℕ → List ℕ →. ℕ} {sel : ℕ → ℕ → PartialJointEmbeddingData}
  (hchpSpec : K.MappedCHPSpec chpSel) (hjoint : K.JointSpec sel)
  (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2)
  (hsel : ComputableIn O fun p : ℕ × ℕ ↦ sel p.1 p.2)

/-- **The forward cover**, generator-compatible. -/
theorem test_forward_generatorCompatible (hrep : Z.RepresentedByRawRep) :
    (runForwardCover Z chpSel cert hchpSpec hchp hrep).GeneratorCompatible :=
  runForwardCover_generatorCompatible Z chpSel cert hchpSpec hchp hrep

include hchp hsel in
/-- **The prefix iteration is a program**: partial recursive in the member and the prefix, with no
certificate. -/
theorem test_prefixPart_recursiveIn :
    RecursiveIn O fun p : ℕ × ℕ ↦ prefixPart K W i chpSel sel p.1 p.2 :=
  prefixPart_recursiveIn hchp hsel

include hchpSpec hjoint in
/-- **One prefix step** halts and preserves the invariant. -/
theorem test_prefixStep_spec {j t : ℕ} {st : ℕ × ℕ × List ℕ} (hinv : PrefixInv K W i sel j t st)
    (ht : t < (K.gens (sel i j).apexIdx).length) :
    (prefixStep K W i chpSel sel j t st).Dom ∧
      ∀ st' ∈ prefixStep K W i chpSel sel j t st, PrefixInv K W i sel j (t + 1) st' :=
  prefixStep_spec hchpSpec hjoint hinv ht

/-- **The step's requirement**: its coded maps are actual and it is admissible. -/
theorem test_prefixRequirement {j t : ℕ} {st : ℕ × ℕ × List ℕ}
    (hinv : PrefixInv K W i sel j t st) (ht : t < (K.gens (sel i j).apexIdx).length) {c' : ℕ}
    (hA : K.PartialIsEmbedding
      (PotentialEmbeddingData.ofTriple (c', (sel i j).apexIdx, prefixList K i sel j (t + 1)))) :
    K.Admissible (memberIdx K W i) (prefixRequirement K st c') :=
  (prefixRequirement_spec hinv ht hA).2.2

include hjoint in
/-- **The apex at the last prefix**: its generators go to `H_T.drop n`, no inverse computed. -/
theorem test_finalData {j : ℕ} {st : ℕ × ℕ × List ℕ}
    (hinv : PrefixInv K W i sel j (K.gens (sel i j).apexIdx).length st) :
    K.PartialIsEmbedding (PotentialEmbeddingData.ofTriple
      ((sel i j).apexIdx, memberIdx K W i st.2.1, st.2.2.drop (K.gens i).length)) :=
  finalData_partialIsEmbedding hjoint hinv

/-- **The backward cover**, generator-compatible. -/
theorem test_backward_generatorCompatible :
    (runBackwardCover Z cert hchpSpec hjoint hchp hsel).GeneratorCompatible :=
  runBackwardCover_generatorCompatible Z cert hchpSpec hjoint hchp hsel

/-- **Both directions.** -/
theorem test_runCanonicalIso (hrep : Z.RepresentedByRawRep) :
    (runCanonicalIso Z cert hchpSpec hjoint hchp hsel hrep).forward.GeneratorCompatible ∧
      (runCanonicalIso Z cert hchpSpec hjoint hchp hsel hrep).backward.GeneratorCompatible :=
  runCanonicalIso_generatorCompatible Z cert hchpSpec hjoint hchp hsel hrep

omit cert in
/-- From the paper's selector properties. -/
theorem test_exists_from_selectors (hCHP : MappedPartialCHPIn O K) (hCJEP : K.PartialCJEPIn O)
    (hrep : Z.RepresentedByRawRep) (cert : Z.presentation.InfinitudeCertificate) :
    ∃ r : RepresentationIsoIn O (Z.omegaStructure cert).canonicalAge K,
      r.forward.GeneratorCompatible ∧ r.backward.GeneratorCompatible :=
  exists_runCanonicalIso Z hCHP hCJEP hrep cert

/-- At the run's canonical limit. -/
theorem test_toLimit_exists (hCHP : MappedPartialCHPIn O K) (hCJEP : K.PartialCJEPIn O)
    (cert : CePresentationIn.InfinitudeCertificate ((runChain K W i (Set.Subset.refl O) h0).toLimit
      (runChain_uniformEvaluators K W i (Set.Subset.refl O) h0)).presentation) :
    ∃ r : RepresentationIsoIn O
        (((runChain K W i (Set.Subset.refl O) h0).toLimit
          (runChain_uniformEvaluators K W i (Set.Subset.refl O) h0)).omegaStructure
            cert).canonicalAge K,
      r.forward.GeneratorCompatible ∧ r.backward.GeneratorCompatible :=
  toLimit_exists_runCanonicalIso hCHP hCJEP cert

end General

section Fixture

variable (O : Set (ℕ →. ℕ))

/-- **The list age is a canonical representation of the age of its run's ω structure**, compatibly
in both directions, with every hypothesis discharged. -/
theorem test_listAge_canonicalIso :
    ∃ r : RepresentationIsoIn O
        ((listAge.runLimit O).omegaStructure (listAge.runLimit_cert O)).canonicalAge (listAge O),
      r.forward.GeneratorCompatible ∧ r.backward.GeneratorCompatible :=
  ⟨_, PartialAgeIn.runCanonicalIso_generatorCompatible (listAge.runLimit O)
    (listAge.runLimit_cert O) listAge.mappedCHPSpec listAge.jointSpec listAge.chpSel_recursiveIn
    listAge.jointSel_computableIn (CeStructureChainIn.toLimit_representedByRawRep _ _)⟩

end Fixture

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_forward_generatorCompatible
#assert_standard_axioms FirstOrder.Language.test_prefixPart_recursiveIn
#assert_standard_axioms FirstOrder.Language.test_prefixStep_spec
#assert_standard_axioms FirstOrder.Language.test_prefixRequirement
#assert_standard_axioms FirstOrder.Language.test_finalData
#assert_standard_axioms FirstOrder.Language.test_backward_generatorCompatible
#assert_standard_axioms FirstOrder.Language.test_runCanonicalIso
#assert_standard_axioms FirstOrder.Language.test_exists_from_selectors
#assert_standard_axioms FirstOrder.Language.test_toLimit_exists
#assert_standard_axioms FirstOrder.Language.test_listAge_canonicalIso
