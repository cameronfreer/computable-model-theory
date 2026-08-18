/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureOmegaTuple
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the finite-tuple pullback to a common stage

The headline row is `test_tuple_coordinates`: the pulled-back tuple's ω-image **is** the query,
coordinatewise. Everything else in this file exists so that row can be stated and so a consumer can
use it without unfolding either traversal.

Three rows record where the hypotheses sit, since that is the part a refactor can quietly break.

* `test_tuple_recursiveIn_no_certificate` and `test_tuple_nil_no_certificate` take **no**
  `InfinitudeCertificate`. The definition and its computability are certificate-free by
  construction; only halting is not, because `rankEnum` is the sole source of divergence
  (`transportRawArgsPart` halts on every list). If a later refactor moved the certificate onto the
  definition, these rows would stop elaborating.
* `test_represented_by_rawRep` discharges `RepresentedByRawRep` for the canonical limit, so
  `test_tuple_coordinates` is gated on a satisfiable hypothesis rather than a decorative one. It is
  a hypothesis rather than a record field because it is genuinely extra: `coverage` says *some*
  stage carries a code, `RepresentedByRawRep` says the totally computable `rawRep` finds one.

`test_stageEmbedding_transport` is gated separately from the one-step law it comes from. The step
law is what the limit record carries; the transport law is what a tuple consumer needs, because a
tuple's entries reach the common stage from different depths and nothing records how far.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace CeStructureChainIn

namespace LimitIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {D : CeStructureChainIn O L} (Z : D.LimitIn)

/-! ### Transport coherence -/

/-- **Coherence along an arbitrary transport**, at the Lemma 2.9 level. Derived from the record's
universal one-step law — the record is not extended. -/
theorem test_stageEmbedding_transport {i j : ℕ} (hij : i ≤ j) {x y : ℕ}
    (hx : x ∈ (D.stageAt i).domain) (hy : y ∈ D.toDomainChain.transportTo i j x) :
    ∃ hy' : y ∈ (D.stageAt j).domain,
      Z.stageEmbedding i ⟨x, hx⟩ = Z.stageEmbedding j ⟨y, hy'⟩ :=
  Z.stageEmbedding_transport hij hx hy

/-- And its recoded form, which is what the tuple unit consumes. -/
theorem test_omegaStageEmbedding_transport {i j : ℕ} (hij : i ≤ j) {x y : ℕ}
    (hx : x ∈ (D.stageAt i).domain) (hy : y ∈ D.toDomainChain.transportTo i j x) :
    ∃ hy' : y ∈ (D.stageAt j).domain,
      Z.omegaStageEmbedding i ⟨x, hx⟩ = Z.omegaStageEmbedding j ⟨y, hy'⟩ :=
  Z.omegaStageEmbedding_transport hij hx hy

/-! ### The pullback, certificate-free -/

/-- **Uniformly partial recursive, with no certificate.** -/
theorem test_tuple_recursiveIn_no_certificate : RecursiveIn O Z.rankTupleAtStagePart :=
  Z.rankTupleAtStagePart_recursiveIn

/-- **The empty query is answered at stage `0`, with no certificate** — nullary data is evaluated
once, at the bottom of the chain. -/
theorem test_tuple_nil_no_certificate : Z.rankTupleAtStagePart [] = Part.some (0, []) :=
  Z.rankTupleAtStagePart_nil

/-- **Membership exposes the intermediate raw tuple**, so consumers name `raw` and never reopen
either traversal. -/
theorem test_tuple_mem_iff {s : List ℕ} {p : ℕ × List ℕ} :
    p ∈ Z.rankTupleAtStagePart s ↔
      ∃ raw : List ℕ,
        List.Forall₂ (fun n a ↦ a ∈ Z.presentation.rankEnum n) s raw ∧
          p.1 = D.toDomainChain.rawStageBound raw ∧
          p.2 ∈ D.toDomainChain.transportRawArgsPart raw :=
  Z.mem_rankTupleAtStagePart_iff

/-! ### What the certificate buys -/

/-- **Halting — the one place infinitude enters.** -/
theorem test_tuple_dom (cert : Z.presentation.InfinitudeCertificate) (s : List ℕ) :
    (Z.rankTupleAtStagePart s).Dom :=
  Z.rankTupleAtStagePart_dom cert s

/-! ### Shape and validity -/

/-- The answer has the query's length. -/
theorem test_tuple_length {s : List ℕ} {p : ℕ × List ℕ}
    (h : p ∈ Z.rankTupleAtStagePart s) : p.2.length = s.length :=
  Z.rankTupleAtStagePart_length h

/-- **Every entry lives at the returned stage** — the reason the stage is returned at all, rather
than left for a consumer to re-derive. -/
theorem test_tuple_mem_stage {s : List ℕ} {p : ℕ × List ℕ}
    (h : p ∈ Z.rankTupleAtStagePart s) : ∀ y ∈ p.2, y ∈ (D.stageAt p.1).domain :=
  Z.mem_domainAt_of_mem_rankTupleAtStagePart h

/-! ### The coordinate theorem -/

/-- **The load-bearing row.** Not merely a tuple valid at one stage: its ω-image is the original
query, entry by entry. This is what the CHP cover consumes. -/
theorem test_tuple_coordinates (hrep : Z.RepresentedByRawRep) {s : List ℕ} {p : ℕ × List ℕ}
    (h : p ∈ Z.rankTupleAtStagePart s) :
    List.Forall₂ (fun n y ↦ ∃ hy : y ∈ (D.stageAt p.1).domain,
      Z.omegaStageEmbedding p.1 ⟨y, hy⟩ = n) s p.2 :=
  Z.forall₂_omegaStageEmbedding hrep h

end LimitIn

/-- **The coordinate theorem's hypothesis is satisfiable**: the canonical limit names its codes by
their own raw representatives. Without this row `test_tuple_coordinates` would be gated on a
hypothesis nothing supplies. -/
theorem test_represented_by_rawRep {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
    {D : CeStructureChainIn O L} (U : D.UniformEvaluatorsIn) :
    (D.toLimit U).RepresentedByRawRep :=
  D.toLimit_representedByRawRep U

end CeStructureChainIn

end FirstOrder.Language

#assert_standard_axioms
  FirstOrder.Language.CeStructureChainIn.LimitIn.test_stageEmbedding_transport
#assert_standard_axioms
  FirstOrder.Language.CeStructureChainIn.LimitIn.test_omegaStageEmbedding_transport
#assert_standard_axioms
  FirstOrder.Language.CeStructureChainIn.LimitIn.test_tuple_recursiveIn_no_certificate
#assert_standard_axioms
  FirstOrder.Language.CeStructureChainIn.LimitIn.test_tuple_nil_no_certificate
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.test_tuple_mem_iff
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.test_tuple_dom
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.test_tuple_length
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.test_tuple_mem_stage
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.LimitIn.test_tuple_coordinates
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_represented_by_rawRep
