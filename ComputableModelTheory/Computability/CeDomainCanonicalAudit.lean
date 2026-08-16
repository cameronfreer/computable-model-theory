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
extensional limit needs no base witness of its own.
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

/-- **`0` is accepted, at no cost.** The fallback a total enumeration of the limit will need, with
no base witness of this layer's own. -/
theorem test_accepted_zero : C.Accepted 0 :=
  C.accepted_zero

/-- The two effectivity facts the layer supplies. -/
theorem test_canonical_recursiveIn :
    ComputableIn O C.rawRep ∧ RecursiveIn O C.canonicalPart :=
  ⟨C.rawRep_computableIn, C.canonicalPart_recursiveIn⟩

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
