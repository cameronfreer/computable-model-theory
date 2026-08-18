/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.Theorem210Reverse
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: CHMM Theorem 2.10, reverse direction

**The projection rows come first**, because they are what catches an orientation error that the
headline cannot. In the theorem's existential both components are covers, so a forward/backward swap
typechecks and would silently prove a different statement; `test_forward_is_forwardCover` and
`test_backward_is_backwardCover` are `rfl` against the named isomorphism, and pin

* `r.forward : 𝕂_𝒟 → K` — the cover CHP builds, and the one the corrected published forward
  implication demands compatibility on;
* `r.backward : K → 𝕂_𝒟` — the cofinal cover, whose compatibility is `allTupleFor_encode`.

**The inputs are named.** `test_inputs_are_named` reads the base witness and the certificate back
out of the package, and `test_cjep_gives_no_certificate` shows what `PartialCJEPIn` plus a base
witness actually produces — the *scheduled* package, not the ω one. The certificate is a property of
one selector's limit, not of `K`, so a statement quantifying it away would be dishonest about its
own inputs.

**The conclusion is stronger than Definition 2.4**, and `test_round_trip` is the reason that matters:
the compatibility this theorem produces is exactly what the corrected forward implication consumes,
so the two compose. Its *conclusion* is not news — CHP was a hypothesis — but its *elaboration* is:
if the two covers were swapped, or if compatibility landed on the wrong one,
`mappedPartialCHPIn_of_canonicalAge` would not accept it.

**No `iff`.** None is stated here and none should be: the published forward direction is the
separately corrected theorem, and `CanonicalAgeSeparationAudit` shows the two directions' gaps are
independent. `test_paper_facing` is the literal Definition 2.4 conclusion, obtained by forgetting.

Everything is at a single oracle `O`, on both sides of every cover.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage] {K : PartialAgeIn O L}

/-! ### The named inputs -/

/-- **The two supplied witnesses, read back out**: a nonempty base member and an infinitude
certificate for *this* package's limit. Neither is a property of `K` alone. -/
theorem test_inputs_are_named (W : OmegaCJEPDataIn K) :
    (K.domainAt W.scheduled.baseIdx).Nonempty ∧
      W.scheduled.limit.presentation.InfinitudeCertificate :=
  ⟨W.scheduled.base_nonempty, W.infinitude⟩

/-- **CJEP plus a base witness produces the scheduled package — and stops there.** The certificate
is not among its outputs, which is exactly why it is attached separately. -/
theorem test_cjep_gives_no_certificate (h : K.PartialCJEPIn O) {baseIdx : ℕ}
    (hbase : (K.domainAt baseIdx).Nonempty) : Nonempty (ScheduledCJEPDataIn K) :=
  exists_scheduledCJEPData h hbase

/-- The limit the certificate is about is the canonical Lemma 2.9 one, so `RepresentedByRawRep` is a
theorem here rather than a further hypothesis. -/
theorem test_limit_is_canonical (W : ScheduledCJEPDataIn K) : W.limit.RepresentedByRawRep :=
  W.limit_representedByRawRep

/-! ### The two covers, by `rfl` -/

section Iso

variable (W : OmegaCJEPDataIn K) (chpSel : ℕ → List ℕ →. ℕ)
variable (hchpSpec : K.MappedCHPSpec chpSel)
variable (hchp : RecursiveIn O fun q : ℕ × List ℕ ↦ chpSel q.1 q.2)

/-- **`r.forward` is the CHP-built cover `𝕂_𝒟 → K`.** Definitional, so a swap cannot survive. -/
theorem test_forward_is_forwardCover :
    (canonicalIso W chpSel hchpSpec hchp).forward
      = forwardCover W.scheduled.limit chpSel W.infinitude hchpSpec
        W.scheduled.limit_representedByRawRep hchp :=
  rfl

/-- **`r.backward` is the cofinal cover `K → 𝕂_𝒟`.** -/
theorem test_backward_is_backwardCover :
    (canonicalIso W chpSel hchpSpec hchp).backward
      = backwardCover W.scheduled.limit W.infinitude :=
  rfl

/-- Both are generator-compatible — CHP's contract on one side, `allTupleFor_encode` on the
other. -/
theorem test_iso_generatorCompatible :
    (canonicalIso W chpSel hchpSpec hchp).forward.GeneratorCompatible ∧
      (canonicalIso W chpSel hchpSpec hchp).backward.GeneratorCompatible :=
  canonicalIso_generatorCompatible W chpSel hchpSpec hchp

end Iso

/-! ### The theorem -/

/-- **CHMM Theorem 2.10(⇐), ω-specialized and strengthened**, at the base oracle: one `O` on both
sides of both covers. -/
theorem test_exists_compatibleCanonicalAge (W : OmegaCJEPDataIn K)
    (hCHP : K.MappedPartialCHPIn O) :
    ∃ (S : ComputableStructureIn O L) (r : RepresentationIsoIn O S.canonicalAge K),
      r.forward.GeneratorCompatible ∧ r.backward.GeneratorCompatible :=
  exists_compatibleCanonicalAge_omega W hCHP

/-- **The paper-facing corollary**, literal Definition 2.4 — obtained by forgetting compatibility,
which is the honest direction of the implication. -/
theorem test_paper_facing (W : OmegaCJEPDataIn K) (hCHP : K.MappedPartialCHPIn O) :
    ∃ S : ComputableStructureIn O L, K.IsCanonicalAgeOfIn O S :=
  exists_isCanonicalAgeOfIn W hCHP

/-- **The two theorems compose.** The compatibility this construction produces is exactly what the
corrected forward implication requires, on exactly the cover it requires it on. The conclusion is
not news — CHP was assumed — but the elaboration is: with the covers swapped, or with compatibility
on the wrong one, `mappedPartialCHPIn_of_canonicalAge` would not accept this witness. -/
theorem test_round_trip (W : OmegaCJEPDataIn K) (hCHP : K.MappedPartialCHPIn O) :
    K.MappedPartialCHPIn O := by
  obtain ⟨S, r, hforward, -⟩ := exists_compatibleCanonicalAge_omega W hCHP
  exact PartialAgeIn.mappedPartialCHPIn_of_canonicalAge r (Set.Subset.refl O) hforward

/-- And CJEP transports back unconditionally, so the witness carries both effective properties. -/
theorem test_round_trip_cjep (W : OmegaCJEPDataIn K) (hCHP : K.MappedPartialCHPIn O) :
    K.PartialCJEPIn O := by
  obtain ⟨S, r, -, -⟩ := exists_compatibleCanonicalAge_omega W hCHP
  exact PartialAgeIn.partialCJEPIn_of_canonicalAge r (Set.Subset.refl O)

end PartialAgeIn

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_inputs_are_named
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_cjep_gives_no_certificate
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_limit_is_canonical
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_forward_is_forwardCover
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_backward_is_backwardCover
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_iso_generatorCompatible
#assert_standard_axioms
  FirstOrder.Language.PartialAgeIn.test_exists_compatibleCanonicalAge
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_paper_facing
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_round_trip
#assert_standard_axioms FirstOrder.Language.PartialAgeIn.test_round_trip_cjep
