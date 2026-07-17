/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CePresentation
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for c.e.-domain presentations (Level 1)

Named acceptance tests for `CePresentationIn`, the all-ℕ adapter, and the
enumeration-rank machinery, checked by `#assert_standard_axioms`. Outside the root
import spine; CI checks it via `scripts/run-audit-modules.sh`.

Coverage: r.e. domain membership; the all-ℕ adapter with its full-domain preservation
theorem (exercised on the empty-language computable structure); computability of the
rank machinery; the downward-closed (initial-segment) rank domain; freshness and strict
monotonicity of rank positions; and the exact halting domain of the rank search. No
gate here claims a decidable domain or total-code computability — that is the point of
the Level-1 type.
-/

open Encodable FirstOrder Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (P : CePresentationIn O L)

/-- Domain membership is r.e. in the oracle. -/
theorem test_mem_domain_rePredIn : REPredIn O fun x ↦ x ∈ P.domain :=
  P.mem_domain_rePredIn

/-- The all-ℕ adapter preserves the landed layer: full domain. -/
theorem test_toCePresentation_domain (S : ComputableStructureIn O L) :
    S.toCePresentation.domain = Set.univ :=
  S.toCePresentation_domain

/-- The rank machinery is computable/partial recursive in the oracle. -/
theorem test_rank_machinery_recursiveIn :
    ComputableIn O P.freshAt ∧ RecursiveIn O P.rankIdx ∧
      RecursiveIn O P.rankEnum ∧ RecursiveIn O P.firstIdxOf :=
  ⟨P.freshAt_computableIn, P.rankIdx_recursiveIn, P.rankEnum_recursiveIn,
    P.firstIdxOf_recursiveIn⟩

/-- The rank domain is downward closed: the c.e. initial segment of the Level-1
Pullback. -/
theorem test_rankIdx_dom_mono {r s : ℕ} (hrs : r ≤ s) (h : (P.rankIdx s).Dom) :
    (P.rankIdx r).Dom :=
  P.rankIdx_dom_mono hrs h

/-- Defined rank positions are fresh and strictly increasing. -/
theorem test_rankIdx_spec {r i j : ℕ} (hi : i ∈ P.rankIdx r)
    (hj : j ∈ P.rankIdx (r + 1)) : P.freshAt i = true ∧ i < j :=
  ⟨P.freshAt_of_mem_rankIdx hi, P.rankIdx_lt_of_mem hi hj⟩

/-- Rank-enumerated values lie in the domain, and the rank search halts exactly on the
domain. -/
theorem test_rank_domain_correspondence {r x : ℕ} (h : x ∈ P.rankEnum r) (y : ℕ) :
    x ∈ P.domain ∧ ((P.firstIdxOf y).Dom ↔ y ∈ P.domain) :=
  ⟨P.mem_domain_of_mem_rankEnum h, P.firstIdxOf_dom_iff y⟩

/-- Gate: the rank domain is c.e. — the range of the total computable `posRank` (and
downward closed, by the gate above). -/
theorem test_rank_domain_ce (r : ℕ) :
    ComputableIn O P.posRank ∧ ((P.rankIdx r).Dom ↔ r ∈ Set.range P.posRank) :=
  ⟨P.posRank_computableIn, P.rankIdx_dom_iff_mem_range_posRank r⟩

/-- Gate: `rankEnum` and `rankOf` are inverse on their respective domains, and the rank
search halts exactly on the domain. -/
theorem test_rank_inverse_laws {r x y : ℕ} (h : x ∈ P.rankEnum r) (hy : y ∈ P.domain)
    (z : ℕ) :
    r ∈ P.rankOf x ∧ (∃ s ∈ P.rankOf y, y ∈ P.rankEnum s) ∧
      ((P.rankOf z).Dom ↔ z ∈ P.domain) :=
  ⟨P.rankOf_rankEnum h, P.rankEnum_rankOf hy, P.rankOf_dom_iff z⟩

end

section ConcreteCe

variable (O : Set (ℕ →. ℕ))

/-- The empty-language computable structure on ℕ, adapted: a concrete all-ℕ c.e.
presentation with full domain. -/
theorem test_empty_adapter_domain :
    (ComputableStructureIn.toCePresentation
      (⟨inferInstance⟩ : ComputableStructureIn O Language.empty)).domain = Set.univ :=
  ComputableStructureIn.toCePresentation_domain _

end ConcreteCe

#assert_standard_axioms test_mem_domain_rePredIn
#assert_standard_axioms test_toCePresentation_domain
#assert_standard_axioms test_rank_machinery_recursiveIn
#assert_standard_axioms test_rankIdx_dom_mono
#assert_standard_axioms test_rankIdx_spec
#assert_standard_axioms test_rank_domain_correspondence
#assert_standard_axioms test_rank_domain_ce
#assert_standard_axioms test_rank_inverse_laws
#assert_standard_axioms test_empty_adapter_domain
