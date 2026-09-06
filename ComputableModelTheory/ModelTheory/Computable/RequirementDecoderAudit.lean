/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.RequirementDecoder
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the staged requirement decoder

**The three availability facts are gated separately**, because they are consumed at different
places: `avail_mono` by the scheduler's structure field, `avail_sound` by the firing stage, and
`admissible_eventually_available` by the fairness theorem. `test_avail_sound` recovers the
**payload** — `DovetailAvail.pick` returns only a code — and `test_avail_carrier_valid` recovers the
landing facts from the same availability, which is what the firing stage will hand to
`PartialCAPIn`'s halting clause.

**Coverage is canonical.** `test_coverage_canonical` exhibits the actual decoded equality
`decodeAt d s (encode q) = some q`, not merely "some payload at some code". That is what makes
persistence carry *the same* `q` forward after `max s₀ q.chainStage`.

**The `r ≤ s` gate, isolated.** In the fixture, landing of the requirement `q₀` is certified at
stage `7`, but its chain stage is `9`: `test_certified_before_chainStage_unavailable` shows it stays
unavailable at stage `8` even though the decoder has certified it, and
`test_available_at_chainStage` shows it becomes available at `9` — with the same decoded datum.

**Landing has genuine delay in the fixture.** The lifted successor family enumerates `m` at step
`m`, so the tuple `[7]` is certified only from stage `7`: `test_landing_delay` pins `decodeAt` at
stage `6` to `none` and at stage `7` to `some q₀`.

**The static guard rejects.** `q₁` differs from `q₀` only in its target member, whose generator
tuple is not one longer than the source's — so it is never available at any stage, regardless of
landing (`test_static_guard_rejects`). `succAgeMixed` exists for exactly this contrast: in the
constant families every member has the same generator width, so the `(n+1)`-clause could never hold
and the positive rows would be vacuous.

**Locality and effectivity.** `test_local` pins that availability at stage `s` reads `d` only at
chain stages `≤ s`; `test_effective` records uniform computability of the decoder and of
availability at any oracle reading the family, with `O ⊆ E` appearing only there.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-! ### The general gates -/

section General

variable (K : PartialAgeIn O L) (d : ℕ → ℕ)

/-- **`avail_mono`**, as the scheduler's structure field. -/
theorem test_avail_mono {s t e : ℕ} (hst : s ≤ t)
    (h : (K.requirementDovetail d).avail s e = true) :
    (K.requirementDovetail d).avail t e = true :=
  (K.requirementDovetail d).avail_mono hst h

/-- **`avail_sound`**: the payload behind an available code — decoded at *this* stage, chain stage
reached, static guards satisfied. -/
theorem test_avail_sound {s e : ℕ} (h : K.requirementAvail d s e = true) :
    ∃ q, K.decodeAt d s e = some q ∧ q.chainStage ≤ s ∧ K.StaticAdmissible q :=
  K.requirementAvail_sound d h

/-- The landing half: both coded maps of an available datum are carrier-valid. -/
theorem test_avail_carrier_valid {s e : ℕ} (h : K.requirementAvail d s e = true) :
    ∃ q, K.decodeAt d s e = some q ∧
      K.CarrierValid (q.chainMap d) ∧ K.CarrierValid q.targetMap :=
  K.requirementAvail_carrierValid d h

/-- **Canonical coverage**: the actual decoded equality at the datum's own encoding. -/
theorem test_coverage_canonical {q : RequirementData} (h₁ : K.CarrierValid (q.chainMap d))
    (h₂ : K.CarrierValid q.targetMap) : ∃ s, K.decodeAt d s (encode q) = some q :=
  K.decodeAt_encode_of_carrierValid d h₁ h₂

/-- **`admissible_eventually_available`**, and stays available. -/
theorem test_admissible_eventually_available {q : RequirementData} (h : K.Admissible d q) :
    ∃ s₀, ∀ s, s₀ ≤ s → K.requirementAvail d s (encode q) = true :=
  K.admissible_eventually_available d h

/-- **Coverage meets fairness**: at least one code of every admissible requirement fires. -/
theorem test_admissible_eventually_fires {q : RequirementData} (h : K.Admissible d q) :
    ∃ s, (K.requirementDovetail d).FiresAt (encode q) s :=
  K.admissible_eventually_fires d h

/-- **At most once per code** — the scheduler's negative half, unchanged by the instantiation. -/
theorem test_fires_at_most_once {e s t : ℕ} (hs : (K.requirementDovetail d).FiresAt e s)
    (ht : (K.requirementDovetail d).FiresAt e t) : s = t :=
  (K.requirementDovetail d).fires_at_most_once hs ht

/-- **A firing code fires with its own decoded data**, and that data is admissible. -/
theorem test_fires_with_decoded_data {e s : ℕ} (h : (K.requirementDovetail d).FiresAt e s) :
    ∃ q, (decode e : Option RequirementData) = some q ∧ q.chainStage ≤ s ∧ K.Admissible d q := by
  obtain ⟨q, hq, -, hr, hstat, h₁, h₂⟩ := K.decode_eq_of_firesAt d h
  exact ⟨q, hq, hr, hstat, h₁, h₂⟩

/-- **Locality**: availability at stage `s` reads `d` only at chain stages `≤ s`. -/
theorem test_local {d' : ℕ → ℕ} {s : ℕ} (hdd : ∀ r ≤ s, d r = d' r) (e : ℕ) :
    K.requirementAvail d s e = K.requirementAvail d' s e :=
  K.requirementAvail_local d hdd e

/-- **Effectivity**, at any oracle reading the family: the decoder, availability, and the staged
packaging. `O ⊆ E` appears here and nowhere else in this audit. -/
theorem test_effective (hOE : O ⊆ E) (hd : ComputableIn E d) :
    ComputableIn E (fun p : ℕ × ℕ ↦ K.decodeAt d p.1 p.2) ∧
      ComputableIn E (fun p : ℕ × ℕ ↦ K.requirementAvail d p.1 p.2) ∧
        (K.stagedDecoder d hOE hd).approx = K.decodeAt d :=
  ⟨K.decodeAt_computableIn d hOE hd, K.requirementAvail_computableIn d hOE hd, rfl⟩

end General

/-! ### The fixture: a family with two generator widths -/

section Fixture

attribute [local instance] succStructure

/-- The successor structure at every index, generated by `[0]` at index `0` and by `[0, 1]`
elsewhere. Two generator widths are needed for the `(n+1)`-clause to be satisfiable at all. -/
def succAgeMixed (O : Set (ℕ →. ℕ)) : ComputableAgeIn O succLang :=
  { succAge O with
    gens := fun i ↦ if i = 0 then [0] else [0, 1]
    gens_computableIn :=
      ComputableIn.ite (c := fun i : ℕ ↦ i = 0)
        (((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp
          ComputableIn.id (ComputableIn.const 0))
        (ComputableIn.const [0]) (ComputableIn.const [0, 1])
    generates := fun i ↦ by
      by_cases hi : i = 0
      · simp only [hi, if_true]; exact succ_tuple_generates
      · simp only [hi, if_false]; exact succ_pair_generates }

/-- The fixture family in the general setting: full carriers, with `m` enumerated at step `m`. -/
noncomputable abbrev mixedFamily (O : Set (ℕ →. ℕ)) : PartialAgeIn O succLang :=
  (succAgeMixed O).toPartialAge

/-- The positive fixture requirement: source member `0` (one generator), target member `1` (two
generators), chain stage `9`, images `[5]` and `[7]`. -/
def q₀ : RequirementData := ⟨0, 9, 1, [5], [7]⟩

/-- The negative fixture requirement: as `q₀`, but the target member is `0`, whose generator tuple
is not one longer than the source's. -/
def q₁ : RequirementData := ⟨0, 9, 0, [5], [7]⟩

variable (O : Set (ℕ →. ℕ))

theorem test_q₀_static : (mixedFamily O).StaticAdmissible q₀ := by
  simp [PartialAgeIn.StaticAdmissible, q₀, mixedFamily, ComputableAgeIn.toPartialAge, succAgeMixed]

theorem test_q₁_not_static : ¬ (mixedFamily O).StaticAdmissible q₁ := by
  simp [PartialAgeIn.StaticAdmissible, q₁, mixedFamily, ComputableAgeIn.toPartialAge, succAgeMixed]

/-- Landing certificates in the fixture: `[7]` is certified in member `1` exactly from stage `7`. -/
theorem test_landsBy_seven :
    (mixedFamily O).landsBy 1 6 [7] = false ∧ (mixedFamily O).landsBy 1 7 [7] = true := by
  constructor
  · rw [Bool.eq_false_iff]
    intro h
    obtain ⟨m, hm, hx⟩ := (mixedFamily O).seenBy_eq_true_iff.1
      ((mixedFamily O).landsBy_eq_true_iff.1 h 7 (List.mem_singleton_self _))
    have : m = 7 := Option.some.inj hx
    omega
  · exact (mixedFamily O).landsBy_eq_true_iff.2 fun x hx ↦
      (mixedFamily O).seenBy_eq_true_iff.2 ⟨x, by simp at hx; omega, rfl⟩

/-- **Landing delay**: `q₀` is not certified at stage `6`, and is at stage `7`. -/
theorem test_landing_delay :
    (mixedFamily O).decodeAt id 6 (encode q₀) = none ∧
      (mixedFamily O).decodeAt id 7 (encode q₀) = some q₀ := by
  constructor
  · rw [Option.eq_none_iff_forall_ne_some]
    intro q h
    obtain ⟨hq, -, h₂⟩ := ((mixedFamily O).decodeAt_eq_some_iff id).1 h
    rw [RequirementData.decode_encode] at hq
    obtain rfl := Option.some.inj hq
    exact absurd h₂ (by
      change ¬ (mixedFamily O).landsBy 1 6 [7] = true
      rw [(test_landsBy_seven O).1]; decide)
  · refine ((mixedFamily O).decodeAt_eq_some_iff id).2
      ⟨RequirementData.decode_encode q₀, ?_, (test_landsBy_seven O).2⟩
    exact (mixedFamily O).landsBy_eq_true_iff.2 fun x hx ↦
      (mixedFamily O).seenBy_eq_true_iff.2 ⟨x, by simp [q₀] at hx; omega, rfl⟩

/-- **Certified before its chain stage, and still unavailable.** At stage `8` the decoder has
certified `q₀`, but its chain stage is `9`. -/
theorem test_certified_before_chainStage_unavailable :
    (mixedFamily O).decodeAt id 8 (encode q₀) = some q₀ ∧
      (mixedFamily O).requirementAvail id 8 (encode q₀) = false :=
  ⟨(mixedFamily O).decodeAt_mono id (by decide : 7 ≤ 8) (test_landing_delay O).2,
    (mixedFamily O).requirementAvail_eq_false_of_lt_chainStage id
      (RequirementData.decode_encode q₀) (by decide)⟩

/-- **Available at its chain stage**, with the same decoded datum. -/
theorem test_available_at_chainStage :
    (mixedFamily O).requirementAvail id 9 (encode q₀) = true ∧
      (mixedFamily O).decodeAt id 9 (encode q₀) = some q₀ := by
  have h := (mixedFamily O).decodeAt_mono id (by decide : 7 ≤ 9) (test_landing_delay O).2
  exact ⟨((mixedFamily O).requirementAvail_eq_true_iff id).2 ⟨q₀, h, le_rfl, test_q₀_static O⟩, h⟩

/-- **The static guard rejects**: `q₁` is never available, at any stage, for any `d`. -/
theorem test_static_guard_rejects (d : ℕ → ℕ) (s : ℕ) :
    (mixedFamily O).requirementAvail d s (encode q₁) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨q, hq, -, hstat⟩ := (mixedFamily O).requirementAvail_sound d h
  have := (mixedFamily O).decode_eq_of_decodeAt d hq
  rw [RequirementData.decode_encode] at this
  obtain rfl := Option.some.inj this
  exact test_q₁_not_static O hstat

/-- `q₀` is admissible, so — by the general theorems — some code of it fires. -/
theorem test_q₀_fires : ∃ s, ((mixedFamily O).requirementDovetail id).FiresAt (encode q₀) s :=
  (mixedFamily O).admissible_eventually_fires id
    ⟨test_q₀_static O, fun _ _ ↦ by simp [mixedFamily], fun _ _ ↦ by simp [mixedFamily]⟩

end Fixture

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_avail_mono
#assert_standard_axioms FirstOrder.Language.test_avail_sound
#assert_standard_axioms FirstOrder.Language.test_avail_carrier_valid
#assert_standard_axioms FirstOrder.Language.test_coverage_canonical
#assert_standard_axioms FirstOrder.Language.test_admissible_eventually_available
#assert_standard_axioms FirstOrder.Language.test_admissible_eventually_fires
#assert_standard_axioms FirstOrder.Language.test_fires_at_most_once
#assert_standard_axioms FirstOrder.Language.test_fires_with_decoded_data
#assert_standard_axioms FirstOrder.Language.test_local
#assert_standard_axioms FirstOrder.Language.test_effective
#assert_standard_axioms FirstOrder.Language.test_q₀_static
#assert_standard_axioms FirstOrder.Language.test_q₁_not_static
#assert_standard_axioms FirstOrder.Language.test_landsBy_seven
#assert_standard_axioms FirstOrder.Language.test_landing_delay
#assert_standard_axioms FirstOrder.Language.test_certified_before_chainStage_unavailable
#assert_standard_axioms FirstOrder.Language.test_available_at_chainStage
#assert_standard_axioms FirstOrder.Language.test_static_guard_rejects
#assert_standard_axioms FirstOrder.Language.test_q₀_fires
