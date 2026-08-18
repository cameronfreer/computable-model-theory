/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CanonicalAgeForwardCover

/-!
# CHMM Theorem 2.10, reverse direction (ω-specialized)

> If `K` has CHP and CJEP then `K` is the canonical representation of the age of some computable
> structure.

**The inputs are named, not hidden.** The obvious statement — `MappedPartialCHPIn O K →
PartialCJEPIn O K → ∃ S, …` — would be dishonest, because the infinitude certificate is not a
property of `K`: it is a property of *the limit of one particular extracted CJEP selector*, and a
different selector gives a different limit with a different certificate. So the joint-embedding data
is packaged first (`ScheduledCJEPDataIn`), the certificate is attached to *its* limit
(`OmegaCJEPDataIn`), and the theorem takes that package. `PartialCJEPIn` plus a named base witness
produces the scheduled package; attaching infinitude stays explicit and supplied, exactly as every
other certificate in this development does.

**The conclusion is stronger than canonicality**, and deliberately so. Definition 2.4 asks only for a
representation isomorphism; `CanonicalAgeSeparationAudit` shows that such an isomorphism need not
carry recorded generators to recorded generators, which is why the published *forward* implication
needs `r.forward.GeneratorCompatible` as an explicit hypothesis. The reverse implication constructs
a witness that has it — in **both** directions — so the two theorems compose. The paper-facing
corollary forgets that extra information.

**No `iff` is stated.** The unqualified published equivalence is not available: the forward direction
is the separately corrected theorem `mappedPartialCHPIn_of_canonicalAge`, which requires
compatibility on the cover running `𝕂_𝒟 → K`, and the two separations in
`CanonicalAgeSeparationAudit` show the gaps in the two directions are independent.

**Base oracle only.** Everything is at one `O`: `RepresentationCoverIn` admits no cover between
representations at different family oracles, so the selectors must live where `K`'s data does. An
oracle-lifting version is a separate result.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage] {K : PartialAgeIn O L}

/-! ### The joint-embedding witness package

Everything the chain construction consumes, in one record: the named base witness and a computable
joint-embedding selector whose legs are actual. -/

/-- A CJEP selector together with the named base witness its schedule needs. -/
structure ScheduledCJEPDataIn (K : PartialAgeIn O L) where
  /-- The base index of the schedule. -/
  baseIdx : ℕ
  /-- Its member is nonempty — the one witness the whole construction is bought with. -/
  base_nonempty : (K.domainAt baseIdx).Nonempty
  /-- The joint-embedding selector. -/
  sel : ℕ → ℕ → PartialJointEmbeddingData
  sel_computableIn : ComputableIn O fun p : ℕ × ℕ ↦ sel p.1 p.2
  /-- Both legs are actual at every pair of indices. -/
  spec : K.JointSpec sel

namespace ScheduledCJEPDataIn

variable (W : ScheduledCJEPDataIn K)

/-- Nonemptiness propagates along the left legs from the base witness alone. -/
theorem nonempty (n : ℕ) : (K.domainAt (cjepSchedule W.sel W.baseIdx n)).Nonempty :=
  cjepSchedule_domainAt_nonempty W.spec W.base_nonempty n

/-- The c.e. structure chain of the schedule, at the base oracle. -/
noncomputable def selfChain : CeStructureChainIn O L :=
  PartialAgeIn.selfChain K W.sel W.baseIdx W.nonempty W.spec W.sel_computableIn

theorem uniformEvaluators : W.selfChain.UniformEvaluatorsIn :=
  PartialAgeIn.selfChain_uniformEvaluators K W.sel W.baseIdx W.nonempty W.spec W.sel_computableIn

/-- **The Lemma 2.9 limit of the chain** — the canonical one, so `RepresentedByRawRep` is available
rather than assumed. -/
noncomputable def limit : W.selfChain.LimitIn :=
  W.selfChain.toLimit W.uniformEvaluators

/-- The limit names its codes by their own raw representatives, since it is `toLimit`. -/
theorem limit_representedByRawRep : W.limit.RepresentedByRawRep :=
  CeStructureChainIn.toLimit_representedByRawRep _ W.uniformEvaluators

end ScheduledCJEPDataIn

/-- **CJEP plus a named base witness produces the package.** The base witness is genuinely extra:
`PartialCJEPIn` says nothing about any member being nonempty, and at the empty-capable layer an
infinite age may have an empty member at index `0`. -/
theorem exists_scheduledCJEPData (h : K.PartialCJEPIn O) {baseIdx : ℕ}
    (hbase : (K.domainAt baseIdx).Nonempty) : Nonempty (ScheduledCJEPDataIn K) := by
  obtain ⟨sel, hsel, hspec⟩ := h.exists_jointSpec
  exact ⟨⟨baseIdx, hbase, sel, hsel, hspec⟩⟩

/-! ### Attaching the certificate

Deliberately a second record. The certificate is a property of *this* package's limit; it is not
recoverable from `K`, and a different selector would need a different one. -/

/-- A scheduled package whose limit is certified infinite. -/
structure OmegaCJEPDataIn (K : PartialAgeIn O L) where
  /-- The joint-embedding data. -/
  scheduled : ScheduledCJEPDataIn K
  /-- Its limit is infinite. Supplied input; nothing recovers it from the c.e. data. -/
  infinitude : scheduled.limit.presentation.InfinitudeCertificate

namespace OmegaCJEPDataIn

variable (W : OmegaCJEPDataIn K)

/-- **The computable structure the age is realized in**: the rank-recoded ω-limit. -/
noncomputable def omegaStructure : ComputableStructureIn O L :=
  limitStructure W.scheduled.limit W.infinitude

end OmegaCJEPDataIn

/-! ### The isomorphism, named

Named rather than left inside the existential so that the two covers can be read back out by `rfl`.
An accidental forward/backward swap typechecks in the existential — both are covers — but not
against these projections. -/

variable (W : OmegaCJEPDataIn K) (chpSel : ℕ → List ℕ →. ℕ)

/-- **The representation isomorphism** `𝕂_𝒟 ↔ K`: the two covers, built independently. -/
noncomputable def canonicalIso (hchpSpec : K.MappedCHPSpec chpSel)
    (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2) :
    RepresentationIsoIn O W.omegaStructure.canonicalAge K where
  forward := forwardCover W.scheduled.limit chpSel W.infinitude hchpSpec
    W.scheduled.limit_representedByRawRep hchp
  backward := backwardCover W.scheduled.limit W.infinitude

@[simp] theorem canonicalIso_forward (hchpSpec : K.MappedCHPSpec chpSel)
    (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2) :
    (canonicalIso W chpSel hchpSpec hchp).forward
      = forwardCover W.scheduled.limit chpSel W.infinitude hchpSpec
        W.scheduled.limit_representedByRawRep hchp :=
  rfl

@[simp] theorem canonicalIso_backward (hchpSpec : K.MappedCHPSpec chpSel)
    (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2) :
    (canonicalIso W chpSel hchpSpec hchp).backward = backwardCover W.scheduled.limit W.infinitude :=
  rfl

/-- Both covers of the named isomorphism are generator-compatible. -/
theorem canonicalIso_generatorCompatible (hchpSpec : K.MappedCHPSpec chpSel)
    (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2) :
    (canonicalIso W chpSel hchpSpec hchp).forward.GeneratorCompatible ∧
      (canonicalIso W chpSel hchpSpec hchp).backward.GeneratorCompatible :=
  ⟨forwardCover_generatorCompatible W.scheduled.limit chpSel W.infinitude hchpSpec
      W.scheduled.limit_representedByRawRep hchp,
    backwardCover_generatorCompatible W.scheduled.limit W.infinitude⟩

variable {W chpSel}

/-! ### The theorem -/

/-- **CHMM Theorem 2.10(⇐), ω-specialized and strengthened.** From a certified ω joint-embedding
package and the hereditary property, `K` is computably isomorphic to the canonical age of a
computable structure — by an isomorphism that is generator-compatible in **both** directions.

The compatibility is the part Definition 2.3 does not supply and `CanonicalAgeSeparationAudit`
shows cannot be had for free; carrying it here is what lets this compose with the corrected forward
implication, which assumes it. -/
theorem exists_compatibleCanonicalAge_omega (W : OmegaCJEPDataIn K)
    (hCHP : K.MappedPartialCHPIn O) :
    ∃ (S : ComputableStructureIn O L) (r : RepresentationIsoIn O S.canonicalAge K),
      r.forward.GeneratorCompatible ∧ r.backward.GeneratorCompatible := by
  obtain ⟨chpSel, hchp, hchpSpec⟩ := MappedPartialCHPIn.exists_chpSpec hCHP
  exact ⟨W.omegaStructure, canonicalIso W chpSel hchpSpec hchp,
    canonicalIso_generatorCompatible W chpSel hchpSpec hchp⟩

/-- **The paper-facing corollary**: `K` is a canonical representation of the age of a computable
structure, in the literal sense of Definition 2.4. Obtained by forgetting the compatibility the
construction actually delivers. -/
theorem exists_isCanonicalAgeOfIn (W : OmegaCJEPDataIn K) (hCHP : K.MappedPartialCHPIn O) :
    ∃ S : ComputableStructureIn O L, K.IsCanonicalAgeOfIn O S := by
  obtain ⟨S, r, -, -⟩ := exists_compatibleCanonicalAge_omega W hCHP
  exact ⟨S, ⟨r⟩⟩

end PartialAgeIn

end FirstOrder.Language
