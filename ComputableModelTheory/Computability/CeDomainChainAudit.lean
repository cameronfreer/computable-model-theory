/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.CeDomainChain
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for c.e. domain chains

Named acceptance tests for the carrier-level direct limit, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it via
`scripts/run-audit-modules.sh`.

Coverage: transport coherence, domain preservation, and on-domain injectivity; the
limit equivalence laws on the (c.e.) limit domain; the partial comparison decider with
its uniform recursiveness and on-domain specification; stage compatibility — and all of
it exercised concretely on the **shift chain**, whose steps `x ↦ x + 1` are genuinely
not inclusions, so tag/coherence/transport errors cannot hide behind identity maps.
-/

open Encodable

section

variable {O : Set (ℕ →. ℕ)} (C : CeDomainChainIn O)

/-- Gate: transport coherence, domain preservation, and injectivity on domains. -/
theorem test_transport_laws {i j k x y z : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hx : x ∈ C.domainAt i) (hy : y ∈ C.transportTo i j x)
    (hz : z ∈ C.transportTo j k y) :
    z ∈ C.transportTo i k x ∧ ∃ w ∈ C.transportTo i j x, w ∈ C.domainAt j :=
  ⟨C.transportTo_trans hij hjk hy hz, C.transportTo_dom j hij hx⟩

/-- Gate: transport injectivity on domains. -/
theorem test_transport_injOn {i j x₁ x₂ y : ℕ} (hx₁ : x₁ ∈ C.domainAt i)
    (hx₂ : x₂ ∈ C.domainAt i) (h₁ : y ∈ C.transportTo i j x₁)
    (h₂ : y ∈ C.transportTo i j x₂) : x₁ = x₂ :=
  C.transportTo_injOn hx₁ hx₂ h₁ h₂

/-- Gate: the limit equivalence is an equivalence on the limit domain, which is r.e. -/
theorem test_limEquiv_equivalence {p q r : ℕ × ℕ} (hp : C.limMem p) (hq : C.limMem q)
    (hr : C.limMem r) (hpq : C.limEquiv p q) (hqr : C.limEquiv q r) :
    C.limEquiv p p ∧ C.limEquiv q p ∧ C.limEquiv p r ∧
      REPredIn O fun s : ℕ × ℕ ↦ C.limMem s :=
  ⟨C.limEquiv_refl p, C.limEquiv_symm hpq, C.limEquiv_trans hp hq hr hpq hqr,
    C.limMem_rePredIn⟩

/-- Gate: the comparison is uniformly partial recursive and, on domain pairs, halts
with the equivalence verdict — a partial decider, never claimed total. -/
theorem test_limEquivTest {p q : ℕ × ℕ} (hp : C.limMem p) (hq : C.limMem q) :
    RecursiveIn O (fun r : (ℕ × ℕ) × (ℕ × ℕ) ↦ C.limEquivTest r.1 r.2) ∧
      ∃ b ∈ C.limEquivTest p q, (b = true ↔ C.limEquiv p q) :=
  ⟨C.limEquivTest_recursiveIn, C.limEquivTest_spec hp hq⟩

/-- Gate: stage compatibility through the tagging maps. -/
theorem test_stageInto_compat {i x : ℕ} (hx : x ∈ C.domainAt i) :
    ∃ y ∈ C.step i x,
      C.limEquiv (CeDomainChainIn.stageInto i x)
        (CeDomainChainIn.stageInto (i + 1) y) :=
  C.stageInto_compat hx

end

section ShiftChain

variable (O : Set (ℕ →. ℕ))

/-- The shift chain: every stage is all of ℕ, and each step is `x ↦ x + 1` — an
embedding that is **not** an inclusion, so coherence and tag errors cannot hide. -/
def shiftChain : CeDomainChainIn O where
  enum _ := id
  enum_computableIn := ComputableIn.snd
  step _ x := Part.some (x + 1)
  step_recursiveIn :=
    ((Primrec.succ.to_comp.computableIn (O := O)).comp ComputableIn.snd :
      ComputableIn O fun p : ℕ × ℕ ↦ p.2 + 1)
  step_mem := fun _ x _ ↦ ⟨x + 1, Part.mem_some _, ⟨x + 1, rfl⟩⟩
  step_injOn := fun _ x₁ x₂ y _ _ h₁ h₂ ↦ by
    have e₁ := Part.mem_some_iff.1 h₁
    have e₂ := Part.mem_some_iff.1 h₂
    omega

/-- Concrete transport along the shift chain: two stages shift by two. -/
theorem test_shift_transport : (7 : ℕ) ∈ (shiftChain O).transportTo 0 2 5 :=
  (shiftChain O).transportTo_trans (by omega) (by omega)
    ((shiftChain O).step_mem_transportTo_succ (Part.mem_some _))
    ((shiftChain O).step_mem_transportTo_succ (Part.mem_some _))

/-- Concrete positive identification: `(0, 1)` and `(2, 3)` denote the same limit
element. -/
theorem test_shift_limEquiv : (shiftChain O).limEquiv (0, 1) (2, 3) := by
  refine ⟨3, ?_, ?_⟩
  · show (3 : ℕ) ∈ (shiftChain O).transportTo 0 (max 0 2) 1
    exact (shiftChain O).transportTo_trans (by omega) (by omega)
      ((shiftChain O).step_mem_transportTo_succ (Part.mem_some _))
      ((shiftChain O).step_mem_transportTo_succ (Part.mem_some _))
  · show (3 : ℕ) ∈ (shiftChain O).transportTo 2 (max 0 2) 3
    rw [show max 0 2 = 2 from rfl, CeDomainChainIn.transportTo_self]
    exact Part.mem_some _

/-- Concrete negative identification: `(0, 5)` and `(2, 3)` are distinct limit
elements. -/
theorem test_shift_not_limEquiv : ¬(shiftChain O).limEquiv (0, 5) (2, 3) := by
  rintro ⟨z, h₁, h₂⟩
  have hz3 : z = 3 := by
    have : z ∈ Part.some 3 := by
      have h2' : z ∈ (shiftChain O).transportTo 2 2 3 := h₂
      rwa [CeDomainChainIn.transportTo_self] at h2'
    exact Part.mem_some_iff.1 this
  have h7 : (7 : ℕ) ∈ (shiftChain O).transportTo 0 2 5 := test_shift_transport O
  have : z = 7 := Part.mem_unique h₁ h7
  omega

end ShiftChain

#assert_standard_axioms test_transport_laws
#assert_standard_axioms test_transport_injOn
#assert_standard_axioms test_limEquiv_equivalence
#assert_standard_axioms test_limEquivTest
#assert_standard_axioms test_stageInto_compat
#assert_standard_axioms test_shift_transport
#assert_standard_axioms test_shift_limEquiv
#assert_standard_axioms test_shift_not_limEquiv
