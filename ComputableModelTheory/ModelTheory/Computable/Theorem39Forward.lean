/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.RunCanonicalAge

/-!
# CHMM Theorem 3.9, forward direction

> If `K` has CHP, CJEP and CAP, then the Fraïssé limit of `K` has a computable presentation that is
> computably homogeneous and whose canonical age is `K`.

Packaging only: the three conclusions are the results of Lemma 3.8 applied to the run
(`omegaStructure_isFraisseLimit`), of the homogeneity selector (`toLimit_computablyHomogeneousIn`),
and of the two covers (`toLimit_exists_runCanonicalIso`), stated for **one** named structure.

**The construction is named.** The structure is `runStructure K W i h0 cert`: the ω structure of the
canonical limit of the run built from the CAP witness `W` over the base member `i`. The infinitude
certificate is attached to *that* limit. It is this library's all-ℕ restriction, not a hypothesis of
the paper, and it is not a property of `K`: a different witness or base member gives a different
run, and a different limit to certify. So no statement below quantifies it away. The existential
corollary forgets the structure, not the witness its certificate is about.

**What is not here.** No `iff`: the converse is a separate result. No oracle rebase: everything is
at the family oracle `O`, and a separate witness oracle would need the rebased family `K.mono hOE`.
No converse deriving CAP for a general `K` from the conclusion.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (K : PartialAgeIn O L) (W : PartialCAPWitness O K) (i : ℕ)
  (h0 : (K.domainAt i).Nonempty)

/-- **The run's canonical limit**: the Lemma 2.9 limit of the chain the CAP witness `W` builds over
the base member `i`. -/
noncomputable abbrev runLimit : (runChain K W i (Set.Subset.refl O) h0).LimitIn :=
  (runChain K W i (Set.Subset.refl O) h0).toLimit
    (runChain_uniformEvaluators K W i (Set.Subset.refl O) h0)

/-- **The structure of Theorem 3.9**: the ω structure of the run's canonical limit, under an
infinitude certificate for that limit. -/
noncomputable abbrev runStructure
    (cert : (runLimit K W i h0).presentation.InfinitudeCertificate) : ComputableStructureIn O L :=
  (runLimit K W i h0).omegaStructure cert

variable {K}

/-- **CHMM Theorem 3.9, forward direction**, for the named structure: from CHP, CJEP, a CAP witness,
a nonempty base member and a certificate for that witness's run limit, the run's ω structure `F`

* is computably homogeneous,
* has `K` as its canonical age, by a representation isomorphism generator-compatible in both
  directions, and
* is a Fraïssé limit of the class `K` represents.

No `iff`, one oracle. -/
theorem runStructure_fraisseLimit (hCHP : MappedPartialCHPIn O K) (hCJEP : K.PartialCJEPIn O)
    (cert : (runLimit K W i h0).presentation.InfinitudeCertificate) :
    Nonempty (ComputablyHomogeneousIn O (runStructure K W i h0 cert)) ∧
      (∃ r : RepresentationIsoIn O (runStructure K W i h0 cert).canonicalAge K,
        r.forward.GeneratorCompatible ∧ r.backward.GeneratorCompatible) ∧
      (letI : L.Structure ℕ := (runStructure K W i h0 cert).inst;
        L.IsFraisseLimit K.classSet ℕ) :=
  ⟨toLimit_computablyHomogeneousIn hCHP cert, toLimit_exists_runCanonicalIso hCHP hCJEP cert,
    omegaStructure_isFraisseLimit (Set.Subset.refl O) h0 _ hCHP.hasMappedHP hCJEP.hasJEP cert⟩

/-- **The existential form.** The structure is forgotten; the certificate is still a hypothesis
about the run limit of the named witness `W` over the base member `i`. -/
theorem exists_computablyHomogeneous_fraisseLimit (hCHP : MappedPartialCHPIn O K)
    (hCJEP : K.PartialCJEPIn O)
    (cert : (runLimit K W i h0).presentation.InfinitudeCertificate) :
    ∃ F : ComputableStructureIn O L,
      Nonempty (ComputablyHomogeneousIn O F) ∧
        (∃ r : RepresentationIsoIn O F.canonicalAge K,
          r.forward.GeneratorCompatible ∧ r.backward.GeneratorCompatible) ∧
        (letI : L.Structure ℕ := F.inst; L.IsFraisseLimit K.classSet ℕ) :=
  ⟨runStructure K W i h0 cert, runStructure_fraisseLimit W i h0 hCHP hCJEP cert⟩

end PartialAgeIn

end FirstOrder.Language
