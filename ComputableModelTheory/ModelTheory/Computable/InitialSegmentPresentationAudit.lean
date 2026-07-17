/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.InitialSegmentPresentation
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for initial-segment presentations and certified upgrades

Named acceptance tests for the Level-2 layer, checked by `#assert_standard_axioms`.
Outside the root import spine; CI checks it via `scripts/run-audit-modules.sh`.

Coverage: the derived domain machinery with the named correctness theorems for the
derived total evaluators; both certified upgrades — whose signatures are themselves the
structural API gate that no upgrade happens without an explicit certificate argument —
with their domain identities; the `omega`-to-all-ℕ conversion; and the nonuniform
existence corollary with its single existential target.
-/

open Encodable FirstOrder Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (Q : ComputableInitialSegmentPresentationIn O L) (P : CePresentationIn O L)

/-- The domain and its decider are derived from the shape. -/
theorem test_derived_domain :
    Q.domain = Q.shape.toSet ∧
      (DomainShape.finite 3).toSet = {m | m < 3} ∧ DomainShape.omega.toSet = Set.univ :=
  ⟨rfl, rfl, rfl⟩

/-- Named correctness of the derived total function evaluator. -/
theorem test_totalFunMap_correct (d : FunctionApplicationData L ℕ)
    (hd : ∀ k, d.args k ∈ Q.domain) :
    Q.totalFunMap d = @FunctionApplicationData.funMap L ℕ Q.str d :=
  Q.totalFunMap_correct d hd

/-- Named correctness of the derived total relation predicate. -/
theorem test_totalRelMap_iff (d : RelationApplicationData L ℕ)
    (hd : ∀ k, d.args k ∈ Q.domain) :
    Q.totalRelMap d ↔ @RelationApplicationData.relMap L ℕ Q.str d :=
  Q.totalRelMap_iff d hd

/-- Gate (structural, certificates): the infinite upgrade exists only through an
explicit `InfinitudeCertificate`, lands on shape `omega`, and its domain is the rank
domain. -/
theorem test_upgradeOmega (cert : P.InfinitudeCertificate) :
    (P.upgradeOmega cert).shape = .omega ∧
      (P.upgradeOmega cert).domain = Set.range P.posRank :=
  ⟨rfl, P.upgradeOmega_domain cert⟩

/-- Gate (structural, certificates): the exact-finite upgrade exists only through an
explicit `ExactFiniteCertificate`, lands on shape `finite card`, and its domain is the
rank domain. -/
theorem test_upgradeFinite (cert : P.ExactFiniteCertificate) :
    (P.upgradeFinite cert).shape = .finite cert.card ∧
      (P.upgradeFinite cert).domain = Set.range P.posRank :=
  ⟨rfl, P.upgradeFinite_domain cert⟩

/-- The `omega` case converts to the all-ℕ computable structure, preserving the
structure data. -/
theorem test_toComputableStructure (h : Q.shape = .omega) :
    (Q.toComputableStructure h).inst = Q.str :=
  rfl

/-- The nonuniform corollary: one clean existential target. -/
theorem test_exists_initialSegment :
    ∃ Q' : ComputableInitialSegmentPresentationIn O L,
      Q'.str = P.rankStr ∧ Q'.domain = Set.range P.posRank :=
  P.exists_initialSegment

end

#assert_standard_axioms test_derived_domain
#assert_standard_axioms test_totalFunMap_correct
#assert_standard_axioms test_totalRelMap_iff
#assert_standard_axioms test_upgradeOmega
#assert_standard_axioms test_upgradeFinite
#assert_standard_axioms test_toComputableStructure
#assert_standard_axioms test_exists_initialSegment
