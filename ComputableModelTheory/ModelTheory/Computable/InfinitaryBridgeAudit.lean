/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.InfinitaryBridge
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for the infinitary-logic bridge

Named acceptance tests for the B1a import surface and boundary wrappers, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it via
`scripts/run-audit-modules.sh`.

Coverage: the boundary wrappers elaborate at indexed presentations and the level-zero
re-export holds; and the upstream import surface — `BFEquiv.zero`, the atomic-diagram
characterization, `model_existence`, and `karp_completeness` at `6614ec7` — is
standard-axioms-only, auditing the imported trust base itself.
-/

open Encodable FirstOrder Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {K : ComputableAgeIn O L}

/-- The boundary wrappers elaborate and level zero re-exports through them. -/
theorem test_bfEquivAt_zero (i j : ℕ) {n : ℕ} (a b : Fin n → ℕ) :
    K.bfEquivAt i j 0 a b ↔ K.sameAtomicTypeAt i j a b :=
  K.bfEquivAt_zero i j a b

/-- Same atomic type at equal indices is reflexive, through the boundary — a minimal
semantic sanity check that the wrapper really is upstream's notion. -/
theorem test_sameAtomicTypeAt_refl (i : ℕ) {n : ℕ} (a : Fin n → ℕ) :
    K.sameAtomicTypeAt i i a a :=
  fun _ ↦ Iff.rfl

end

section UpstreamSurface

-- These are deliberate `def`s, not `theorem`s: each re-exports an upstream constant
-- verbatim (no statement restated, no proof re-run) so that `#assert_standard_axioms`
-- audits the upstream proof's own axiom trust base at the pinned commit.
set_option linter.defProp false

/-- Upstream surface: the level-zero characterization of back-and-forth equivalence. -/
def test_upstream_bfEquiv_zero :=
  @FirstOrder.Language.BFEquiv.zero

/-- Upstream surface: same atomic type is realizing the atomic diagram. -/
def test_upstream_atomicDiagram :=
  @FirstOrder.Language.sameAtomicType_iff_realize_atomicDiagram

/-- Upstream surface: classical model existence from a supplied consistency property. -/
def test_upstream_model_existence :=
  @FirstOrder.Language.model_existence

/-- Upstream surface: classical Karp completeness. -/
def test_upstream_karp_completeness :=
  @FirstOrder.Language.karp_completeness

end UpstreamSurface

#assert_standard_axioms test_bfEquivAt_zero
#assert_standard_axioms test_sameAtomicTypeAt_refl
#assert_standard_axioms test_upstream_bfEquiv_zero
#assert_standard_axioms test_upstream_atomicDiagram
#assert_standard_axioms test_upstream_model_existence
#assert_standard_axioms test_upstream_karp_completeness
