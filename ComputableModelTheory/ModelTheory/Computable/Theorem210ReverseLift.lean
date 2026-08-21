/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.Theorem210Reverse

/-!
# Theorem 2.10(⇐) with selectors at a stronger oracle

The base-oracle theorem needs the CJEP and CHP selectors to be computable in the presentation
oracle `O`. The genuinely remaining case is the one where they are not: they exist only relative to
a stronger oracle `E`. This is the **selector-oracle rebase**, and it is not monotonicity of an
already-built witness — no such witness exists yet.

**The crossing is explicit, and load-bearing.** `RepresentationCoverIn` takes both representations at
one family oracle. The limit built from `E`-computable selectors is an `E`-computable structure, so
its `𝕂_𝒟` is a `PartialAgeIn E L`, while `K` is a `PartialAgeIn O L`. There is no cover between them.
`K.mono hOE` is what puts `K` on the same side, and it appears in the statement rather than inside
the proof, so a reader can see exactly which object the conclusion is about.

**Rebasing changes evidence, not the family.** `mono` copies every piece of computational data
definitionally and lifts only the computability proofs, and the four bridges in
`PartialSelectorSpecs` are the sharp form of that claim: `mono_partialCJEPIn`,
`mono_mappedPartialCHPIn` and their selector-facing companions are all `Iff.rfl`, because these
properties are stated entirely in terms of data `mono` preserves on the nose. So there is no
"transport" step here at all — the effective properties of `K` at `E` *are* those of `K.mono hOE`,
and this file only has to put the rebased family into the statement.

**The certificate stays supplied.** The lifted scheduled package is produced from `E`-CJEP plus the
named base witness and stops there, exactly as at the base oracle: infinitude is a property of the
particular limit that particular selector builds.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage] {K : PartialAgeIn O L}

/-! ### The lifted scheduled package -/

/-- **`E`-CJEP plus a named base witness produces the rebased scheduled package.** The base witness
is about `K`, the selector about `E`, and the package about `K.mono hOE` — the object every later
step lives over. As at the base oracle, no certificate comes out of this. -/
theorem exists_scheduledCJEPData_of_subset (hOE : O ⊆ E) (h : K.PartialCJEPIn E) {baseIdx : ℕ}
    (hbase : (K.domainAt baseIdx).Nonempty) : Nonempty (ScheduledCJEPDataIn (K.mono hOE)) :=
  exists_scheduledCJEPData ((mono_partialCJEPIn hOE).2 h) hbase

/-! ### The lifted theorem -/

/-- **CHMM Theorem 2.10(⇐), ω-specialized, with selectors at a stronger oracle.** The conclusion is
about `K.mono hOE` — the same family, presented at the oracle where its selectors live — because a
representation isomorphism relates two representations at one family oracle and the limit is
`E`-computable. Compatibility in both directions, as at the base oracle. -/
theorem exists_compatibleCanonicalAge_omega_of_subset (hOE : O ⊆ E)
    (W : OmegaCJEPDataIn (K.mono hOE)) (hCHP : K.MappedPartialCHPIn E) :
    ∃ (S : ComputableStructureIn E L) (r : RepresentationIsoIn E S.canonicalAge (K.mono hOE)),
      r.forward.GeneratorCompatible ∧ r.backward.GeneratorCompatible :=
  exists_compatibleCanonicalAge_omega W ((mono_mappedPartialCHPIn hOE).2 hCHP)

/-- The paper-facing corollary at the stronger oracle. -/
theorem exists_isCanonicalAgeOfIn_of_subset (hOE : O ⊆ E) (W : OmegaCJEPDataIn (K.mono hOE))
    (hCHP : K.MappedPartialCHPIn E) :
    ∃ S : ComputableStructureIn E L, (K.mono hOE).IsCanonicalAgeOfIn E S :=
  exists_isCanonicalAgeOfIn W ((mono_mappedPartialCHPIn hOE).2 hCHP)

end PartialAgeIn

end FirstOrder.Language
