/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureOmegaTuple
import ComputableModelTheory.ModelTheory.Computable.ChainShiftExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the ω-limit adapter

The four adapter laws, gated twice: generically, and then on the successor shift chain — whose
limit is genuinely infinite, so the certificate is discharged rather than assumed. The concrete
pass is what makes `test_omega_coverage` mean something: over an arbitrary chain the certificate
is a hypothesis, and a hypothesis that happens to be unsatisfiable would gate a vacuous law.

Two rows record boundaries rather than results.

`test_embedding_needs_no_certificate` states the four laws' certificate dependency by *shape*: the
embedding rows take no `cert` argument at all, and only coverage does. That is not an accident of
proof order — the rank structure lives on all of ℕ whatever the rank domain is, and only the claim
that the stage images exhaust ℕ can fail without infinitude.

`test_omegaStructure_inst` pins the recoded interpretation as the ω structure's, definitionally.
Every other row here names `rankStr` as the structure on ℕ; without this row a reader could not
tell that naming from a weaker one that merely happens to agree.

The fixture's infinitude is proved through the classes of the stage-`0` representatives: distinct
naturals at stage `0` are never `limEquiv`, because transport to their own stage is the identity.
No property of the successor function is used — the fixture is infinite for carrier reasons, which
is the honest reason and the reusable one.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace CeStructureChainIn

namespace LimitIn

section Abstract

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {D : CeStructureChainIn O L} (Z : D.LimitIn)

/-! ### The ω structure -/

/-- **Adapter law 4.** The recoded interpretation *is* the ω structure's — definitionally, so the
rows below may name `rankStr` with no loss. -/
theorem test_omegaStructure_inst (cert : Z.presentation.InfinitudeCertificate) :
    (Z.omegaStructure cert).inst = Z.presentation.rankStr :=
  Z.omegaStructure_inst cert

/-- The upgrade really is on shape `omega`, so the carrier is all of ℕ — the reason a separate
adapter is needed at all, since Lemma 2.9's carrier is only the accepted codes. -/
theorem test_omegaPresentation_omega (cert : Z.presentation.InfinitudeCertificate) :
    (Z.omegaPresentation cert).shape = .omega ∧
      (Z.omegaPresentation cert).domain = Set.univ :=
  ⟨rfl, rfl⟩

/-! ### The effective side -/

/-- The rank-lifted stage map is partial recursive **uniformly in the stage** — one computability
proof per stage would not give this. -/
theorem test_rankStageMap_recursiveIn :
    RecursiveIn O fun p : ℕ × ℕ ↦ Z.rankStageMap p.1 p.2 :=
  Z.rankStageMap_recursiveIn

/-! ### The four laws -/

/-- **Adapter law 1.** The bundled recoded embedding's value is a value of the recoded program.
Without this row the adapter would carry a semantic map and a computable map with nothing relating
them — exactly the gap `stageEmbedding_apply_mem` closes one level down. -/
theorem test_omega_apply_mem (i : ℕ) (x : (D.stageAt i).domain) :
    Z.omegaStageEmbedding i x ∈ Z.rankStageMap i x.1 :=
  Z.omegaStageEmbedding_apply_mem i x

/-- **Adapter law 2.** Coherence at **any** realized step, not a chosen one — matching the Lemma 2.9
contract, so no consumer repeats the single-valuedness argument. -/
theorem test_omega_step {i x y : ℕ} (hx : x ∈ (D.stageAt i).domain)
    (hy : y ∈ D.toDomainChain.step i x) :
    ∃ hy' : y ∈ (D.stageAt (i + 1)).domain,
      Z.omegaStageEmbedding i ⟨x, hx⟩ = Z.omegaStageEmbedding (i + 1) ⟨y, hy'⟩ :=
  Z.omegaStageEmbedding_step hx hy

/-- **Adapter law 3.** Coverage of **all of ω**, not merely of the limit carrier: every natural
number is a stage image. This is the strengthening the recoding buys, and the only law that
consumes the certificate. -/
theorem test_omega_coverage (cert : Z.presentation.InfinitudeCertificate) (n : ℕ) :
    ∃ (i x : ℕ) (hx : x ∈ (D.stageAt i).domain), Z.omegaStageEmbedding i ⟨x, hx⟩ = n :=
  Z.exists_omegaStageEmbedding_eq cert n

/-- **The certificate boundary, stated by shape.** The embedding and its first two laws are
certificate-free: this row typechecks precisely because `omegaStageEmbedding`,
`omegaStageEmbedding_apply_mem`, and `omegaStageEmbedding_step` take no certificate. If a later
refactor threaded `cert` through the embedding, this row would stop elaborating. -/
theorem test_embedding_needs_no_certificate (i : ℕ) (x : (D.stageAt i).domain) :
    Z.omegaStageEmbedding i x ∈ Z.rankStageMap i x.1 ∧
      ∀ {j y z : ℕ} (hy : y ∈ (D.stageAt j).domain), z ∈ D.toDomainChain.step j y →
        ∃ hz : z ∈ (D.stageAt (j + 1)).domain,
          Z.omegaStageEmbedding j ⟨y, hy⟩ = Z.omegaStageEmbedding (j + 1) ⟨z, hz⟩ :=
  ⟨Z.omegaStageEmbedding_apply_mem i x, fun hy hz ↦ Z.omegaStageEmbedding_step hy hz⟩

end Abstract

/-! ### The concrete fixture: the successor shift chain

Everything above is gated over an arbitrary chain with a *hypothetical* certificate. Here the
certificate is produced, so the coverage row is not vacuous. -/

section Fixture

variable (O : Set (ℕ →. ℕ))

/-- Constant-stage uniform evaluators. Restated rather than imported: an audit module's `.olean` is
never built, so audit modules cannot import one another. -/
theorem succShiftUniform' : (succShiftChain O).UniformEvaluatorsIn where
  funEval_uniform :=
    ((succShiftChain O).stageAt 0).funEval_recursiveIn.comp ComputableIn.snd
  relEval_uniform :=
    ((succShiftChain O).stageAt 0).relEval_recursiveIn.comp ComputableIn.snd

/-- The Lemma 2.9 limit of the successor shift chain. -/
noncomputable def succShiftLimit : (succShiftChain O).LimitIn :=
  (succShiftChain O).toLimit (succShiftUniform' O)

/-- The stage-`0` representatives are exactly the naturals: the stage enumerations are `id`. -/
private theorem succShift_rawRep_pair (d : ℕ) :
    (succShiftChain O).toDomainChain.rawRep (Nat.pair 0 d) = (0, d) := by
  rw [CeDomainChainIn.rawRep, Nat.unpair_pair]
  rfl

/-- Distinct stage-`0` representatives are never equivalent: transport to their own stage is the
identity, so the two witnesses collapse. -/
private theorem succShift_limEquiv_zero {d d' : ℕ}
    (h : (succShiftChain O).toDomainChain.limEquiv (0, d) (0, d')) : d = d' := by
  obtain ⟨z, h₁, h₂⟩ := h
  rw [show max 0 0 = 0 from rfl, CeDomainChainIn.transportTo_self] at h₁ h₂
  exact (Part.mem_some_iff.1 h₁).symm.trans (Part.mem_some_iff.1 h₂)

/-- **The fixture's limit carrier is infinite** — the semantic fact the certificate needs, and the
only route to one, since nothing recovers infinitude from the c.e. data. -/
theorem succShift_domain_infinite :
    ((succShiftLimit O).presentation).domain.Infinite := by
  have hmem : ∀ d : ℕ,
      (succShiftChain O).toDomainChain.canonicalRaw (Nat.pair 0 d) ∈
        ((succShiftLimit O).presentation).domain := by
    intro d
    show _ ∈ ((succShiftChain O).limitPresentation (succShiftUniform' O)).domain
    rw [CeStructureChainIn.limitPresentation_domain]
    exact (succShiftChain O).toDomainChain.accepted_canonicalRaw _
  refine Set.infinite_of_injective_forall_mem
    (f := fun d ↦ (succShiftChain O).toDomainChain.canonicalRaw (Nat.pair 0 d)) ?_ hmem
  intro d d' hdd
  have h₁ := (succShiftChain O).toDomainChain.limEquiv_canonicalRaw (Nat.pair 0 d)
  have h₂ := (succShiftChain O).toDomainChain.limEquiv_canonicalRaw (Nat.pair 0 d')
  rw [show (succShiftChain O).toDomainChain.canonicalRaw (Nat.pair 0 d)
      = (succShiftChain O).toDomainChain.canonicalRaw (Nat.pair 0 d') from hdd] at h₁
  have hchain := (succShiftChain O).toDomainChain.limEquiv_trans
    ((succShiftChain O).toDomainChain.rawRep_limMem _)
    ((succShiftChain O).toDomainChain.rawRep_limMem _)
    ((succShiftChain O).toDomainChain.rawRep_limMem _)
    h₁ ((succShiftChain O).toDomainChain.limEquiv_symm h₂)
  rw [succShift_rawRep_pair, succShift_rawRep_pair] at hchain
  exact succShift_limEquiv_zero O hchain

/-- **The fixture's infinitude certificate**, discharged. -/
theorem succShiftInfinitude : ((succShiftLimit O).presentation).InfinitudeCertificate :=
  CePresentationIn.infinitudeCertificate_of_infinite _ (succShift_domain_infinite O)

/-! ### The four laws on the fixture -/

/-- **Law 4, concretely.** -/
theorem test_succShift_omegaStructure_inst :
    ((succShiftLimit O).omegaStructure (succShiftInfinitude O)).inst
      = ((succShiftLimit O).presentation).rankStr :=
  (succShiftLimit O).omegaStructure_inst _

/-- **Law 1, concretely.** -/
theorem test_succShift_apply_mem (i : ℕ)
    (x : ((succShiftChain O).stageAt i).domain) :
    (succShiftLimit O).omegaStageEmbedding i x ∈ (succShiftLimit O).rankStageMap i x.1 :=
  (succShiftLimit O).omegaStageEmbedding_apply_mem i x

/-- **Law 2, concretely**, at the fixture's genuine non-inclusion step `x ↦ x + 1`. -/
theorem test_succShift_step (i x : ℕ) :
    ∃ hy : (x + 1) ∈ ((succShiftChain O).stageAt (i + 1)).domain,
      (succShiftLimit O).omegaStageEmbedding i ⟨x, ⟨x, rfl⟩⟩
        = (succShiftLimit O).omegaStageEmbedding (i + 1) ⟨x + 1, hy⟩ :=
  (succShiftLimit O).omegaStageEmbedding_step ⟨x, rfl⟩ (Part.mem_some _)

/-- **Law 3, concretely, with the certificate discharged.** Every natural number is a stage image
of the fixture's limit — the row the abstract gate cannot make non-vacuous on its own. -/
theorem test_succShift_coverage (n : ℕ) :
    ∃ (i x : ℕ) (hx : x ∈ ((succShiftChain O).stageAt i).domain),
      (succShiftLimit O).omegaStageEmbedding i ⟨x, hx⟩ = n :=
  (succShiftLimit O).exists_omegaStageEmbedding_eq (succShiftInfinitude O) n

/-! ### The tuple pullback on the fixture

The generic tuple rows live in `CeStructureOmegaTupleAudit`; the fixture stays here, since it is the
only place both of the coordinate theorem's hypotheses are discharged at once. -/

/-- The fixture's limit names its codes by their own raw representatives. -/
theorem succShiftRepresented : (succShiftLimit O).RepresentedByRawRep :=
  CeStructureChainIn.toLimit_representedByRawRep _ (succShiftUniform' O)

/-- **The pullback halts on every query**, with the certificate discharged rather than assumed. -/
theorem test_succShift_tuple_dom (s : List ℕ) :
    ((succShiftLimit O).rankTupleAtStagePart s).Dom :=
  (succShiftLimit O).rankTupleAtStagePart_dom (succShiftInfinitude O) s

/-- **The coordinate theorem on the fixture, with both hypotheses discharged.** Every answer's
ω-image is the query, entry by entry — the row the abstract gate cannot make non-vacuous on its
own. -/
theorem test_succShift_tuple_coordinates {s : List ℕ} {p : ℕ × List ℕ}
    (h : p ∈ (succShiftLimit O).rankTupleAtStagePart s) :
    List.Forall₂ (fun n y ↦ ∃ hy : y ∈ ((succShiftChain O).stageAt p.1).domain,
      (succShiftLimit O).omegaStageEmbedding p.1 ⟨y, hy⟩ = n) s p.2 :=
  (succShiftLimit O).forall₂_omegaStageEmbedding (succShiftRepresented O) h

end Fixture

end LimitIn

end CeStructureChainIn

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.test_omegaStructure_inst
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.test_omegaPresentation_omega
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.test_rankStageMap_recursiveIn
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.test_omega_apply_mem
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.test_omega_step
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.test_omega_coverage
#assert_standard_axioms
  FirstOrder.Language.CeStructureChainIn.LimitIn.test_embedding_needs_no_certificate
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.succShift_domain_infinite
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.succShiftInfinitude
#assert_standard_axioms
  FirstOrder.Language.CeStructureChainIn.LimitIn.test_succShift_omegaStructure_inst
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.test_succShift_apply_mem
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.test_succShift_step
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.test_succShift_coverage
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.succShiftRepresented
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.test_succShift_tuple_dom
#assert_standard_axioms
  FirstOrder.Language.CeStructureChainIn.LimitIn.test_succShift_tuple_coordinates
