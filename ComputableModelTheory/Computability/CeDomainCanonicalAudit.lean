/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.CeDomainCanonical
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: canonical representatives of a c.e. domain chain

The carrier package, gated over an **arbitrary** chain. These are statements about the construction
rather than about any one fixture, and for structural facts that is the stronger claim: a fixture
would only witness that the package holds somewhere.

The rows are chosen so that the two things that could silently go wrong are both pinned:

* that canonicalization stays inside the class (`limEquiv_canonicalRaw`) — a search that returned
  some unrelated least code would still be idempotent and still be bounded by `n`;
* that accepted codes do not repeat (`accepted_limEquiv_iff`) — the property that makes them names
  for the limit's elements rather than merely a subset of the raw codes.

`accepted_zero` is gated separately because of what it costs: **nothing**. The base witness was
spent upstream making the scheduled stages totalizable, and `rawRep 0` is valid outright, so the
extensional limit needs no base witness of its own. It is a nonemptiness boundary gate, not an
operational fallback — `range_canonicalRaw` means the carrier is enumerated by `canonicalRaw`
directly, with no membership test and nothing to fall back to.
-/

open Encodable Part

namespace CeDomainChainIn

variable {O : Set (ℕ →. ℕ)} (C : CeDomainChainIn O)

/-! ### What the search rests on -/

/-- Every raw representative is a valid pair, by construction. -/
theorem test_rawRep_valid (n : ℕ) : C.limMem (C.rawRep n) :=
  C.rawRep_limMem n

/-- And every valid pair is a raw representative — without this the search could fail to
terminate. -/
theorem test_rawRep_surjective {p : ℕ × ℕ} (hp : C.limMem p) : ∃ n, C.rawRep n = p :=
  C.exists_rawRep_eq hp

/-- The search halts on valid input. No exact domain is claimed: off valid pairs the comparison is
undefined, which is why this is `rfind` rather than a total search. -/
theorem test_canonicalPart_dom {p : ℕ × ℕ} (hp : C.limMem p) : (C.canonicalPart p).Dom :=
  C.canonicalPart_dom_of_limMem hp

/-! ### The carrier package -/

/-- Canonicalization never increases the code. -/
theorem test_canonicalRaw_le (n : ℕ) : C.canonicalRaw n ≤ n :=
  C.canonicalRaw_le n

/-- **And stays inside the class.** Boundedness and idempotence alone would not catch a search that
returned an unrelated least code; this row does. -/
theorem test_canonicalRaw_limEquiv (n : ℕ) :
    C.limEquiv (C.rawRep n) (C.rawRep (C.canonicalRaw n)) :=
  C.limEquiv_canonicalRaw n

/-- Canonicalization is idempotent, so accepted codes are exactly its image. -/
theorem test_canonicalRaw_idem (n : ℕ) :
    C.canonicalRaw (C.canonicalRaw n) = C.canonicalRaw n ∧ C.Accepted (C.canonicalRaw n) :=
  ⟨C.canonicalRaw_idem n, C.accepted_canonicalRaw n⟩

/-- **Accepted codes name limit elements without repetition**: equivalent exactly when equal. -/
theorem test_accepted_limEquiv_iff {n m : ℕ} (hn : C.Accepted n) (hm : C.Accepted m) :
    C.limEquiv (C.rawRep n) (C.rawRep m) ↔ n = m :=
  C.accepted_limEquiv_iff hn hm

/-- **`0` is accepted, at no cost** — nonemptiness of the carrier with no base witness of this
layer's own. Not needed as a fallback: see `range_canonicalRaw`. -/
theorem test_accepted_zero : C.Accepted 0 :=
  C.accepted_zero

/-- The effectivity the layer supplies — including that canonicalization itself is **computable**,
so acceptedness is oracle-computable the moment a consumer needs it. Unbounded search is no barrier
when the search is total on raw codes. -/
theorem test_canonical_recursiveIn :
    ComputableIn O C.rawRep ∧ RecursiveIn O C.canonicalPart ∧ ComputableIn O C.canonicalRaw :=
  ⟨C.rawRep_computableIn, C.canonicalPart_recursiveIn, C.canonicalRaw_computableIn⟩

/-- **The carrier needs no membership test and no fallback**: the accepted codes are exactly the
range of canonicalization, so `canonicalRaw` enumerates them outright. -/
theorem test_range_canonicalRaw : Set.range C.canonicalRaw = {n | C.Accepted n} :=
  C.range_canonicalRaw

/-! ### The stage maps -/

/-- On its own stage the map halts, returns an **accepted** code, and names the element's class. -/
theorem test_stageIntoPart_spec {i x : ℕ} (hx : x ∈ C.domainAt i) :
    (C.stageIntoPart i x).Dom ∧
      ∀ k ∈ C.stageIntoPart i x, C.Accepted k ∧ C.limEquiv (i, x) (C.rawRep k) :=
  ⟨C.stageIntoPart_dom hx, fun _ hk ↦
    ⟨C.accepted_of_mem_stageIntoPart hx hk, C.limEquiv_of_mem_stageIntoPart hx hk⟩⟩

/-- **And it is injective on its stage** — two elements of one stage never share a canonical code.
This is what makes the stage maps embeddings rather than merely well-defined. -/
theorem test_stageIntoPart_injOn {i x y k : ℕ} (hx : x ∈ C.domainAt i) (hy : y ∈ C.domainAt i)
    (hkx : k ∈ C.stageIntoPart i x) (hky : k ∈ C.stageIntoPart i y) : x = y :=
  C.stageIntoPart_injOn hx hy hkx hky

/-- The stage maps are partial recursive uniformly in the stage. -/
theorem test_stageIntoPart_recursiveIn :
    RecursiveIn O fun p : ℕ × ℕ ↦ C.stageIntoPart p.1 p.2 :=
  C.stageIntoPart_recursiveIn

/-! ### The shared transport boundary -/

/-- **Transport halts on every coded tuple, with no `Accepted` guard.** Every natural number has a
valid raw representative, not only the accepted ones — which is why both evaluator pipelines can be
unconditional and acceptedness enters only when the carrier is identified. -/
theorem test_transportRawArgsPart_dom_unconditional (args : List ℕ) :
    (C.transportRawArgsPart args).Dom :=
  C.transportRawArgsPart_dom args

/-- The transported values share one stage — the common stage the evaluators then run at. -/
theorem test_transportRawArgsPart_common_stage {args out : List ℕ}
    (h : out ∈ C.transportRawArgsPart args) :
    ∀ y ∈ out, y ∈ C.domainAt (C.rawStageBound args) :=
  C.mem_domainAt_of_mem_transportRawArgsPart h

/-- And the bound really does dominate every argument's own stage. -/
theorem test_le_rawStageBound {args : List ℕ} {a : ℕ} (ha : a ∈ args) :
    (C.rawRep a).1 ≤ C.rawStageBound args :=
  C.le_rawStageBound ha

/-- The traversal is partial recursive, and specified by `Forall₂` rather than by a fold. -/
theorem test_transportRawArgsPart_recursiveIn :
    RecursiveIn O C.transportRawArgsPart ∧
      ∀ {args out : List ℕ}, out ∈ C.transportRawArgsPart args ↔
        List.Forall₂ (fun a y ↦ y ∈ C.transportRawArg args a) args out :=
  ⟨C.transportRawArgsPart_recursiveIn, C.mem_transportRawArgsPart_iff⟩

end CeDomainChainIn

#assert_standard_axioms CeDomainChainIn.test_rawRep_valid
#assert_standard_axioms CeDomainChainIn.test_rawRep_surjective
#assert_standard_axioms CeDomainChainIn.test_canonicalPart_dom
#assert_standard_axioms CeDomainChainIn.test_canonicalRaw_le
#assert_standard_axioms CeDomainChainIn.test_canonicalRaw_limEquiv
#assert_standard_axioms CeDomainChainIn.test_canonicalRaw_idem
#assert_standard_axioms CeDomainChainIn.test_accepted_limEquiv_iff
#assert_standard_axioms CeDomainChainIn.test_accepted_zero
#assert_standard_axioms CeDomainChainIn.test_canonical_recursiveIn
#assert_standard_axioms CeDomainChainIn.test_range_canonicalRaw
#assert_standard_axioms CeDomainChainIn.test_stageIntoPart_spec
#assert_standard_axioms CeDomainChainIn.test_stageIntoPart_injOn
#assert_standard_axioms CeDomainChainIn.test_stageIntoPart_recursiveIn
#assert_standard_axioms CeDomainChainIn.test_transportRawArgsPart_dom_unconditional
#assert_standard_axioms CeDomainChainIn.test_transportRawArgsPart_common_stage
#assert_standard_axioms CeDomainChainIn.test_le_rawStageBound
#assert_standard_axioms CeDomainChainIn.test_transportRawArgsPart_recursiveIn
