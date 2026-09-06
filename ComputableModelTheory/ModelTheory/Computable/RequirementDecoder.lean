/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.Dovetail
import ComputableModelTheory.Computability.ListPredicates
import ComputableModelTheory.Computability.StagedPartial
import ComputableModelTheory.ModelTheory.Computable.PartialMemberEmbedding

/-!
# The staged requirement decoder for Lemma 3.8

CHMM's Lemma 3.8 construction meets one requirement `R⟨i, r, k, f, g⟩` per stage, "from some
uniform enumeration of all such maps". This module is that enumeration, made precise, together with
the **availability** predicate the dovetailing scheduler (`DovetailAvail`) consumes. Nothing here
calls a CAP selector: availability is about whether a requirement's coded data has been *seen to be
legitimate*, never about whether its amalgamation has been computed.

## Three indices

* the **requirement code** `e : ℕ`, decoding to `RequirementData` — `(i, r, k, f, g)`;
* the **computation stage** `s`, at which the decoder has enumerated enough of the members'
  carriers to certify that `f` lands in `A_{d r}` and `g` in `A_k`;
* the **chain stage** `r`, fixed with the code, at which `f`'s target `A_{d r}` sits.

The chain's member-index function `d : ℕ → ℕ` is a *parameter* here. Availability at stage `s`
reads it only at chain stages `≤ s` (`requirementAvail_local`), which is what lets the later
clock-stage recursion define `d (s + 1)` from availability at stage `s`.

## What is fixed with the code, and what is not

`requirementAvail d s e` depends on the decoded `(i, r, k, f, g)`, on the *static* guards
(`StaticAdmissible`: the width equations and the `(n+1)`-generator clause), on `r ≤ s`, and on the
staged **landing** certificate `decodeAt`: every entry of `f` has appeared in the enumeration of
`A_{d r}` and every entry of `g` in that of `A_k` by step `s`. All of that is a predicate on data
fixed with `e`, so it is monotone in `s` (`decodeAt_mono`), and `StagedPartialIn.monotone` applies
to it. The span actually amalgamated at the firing stage — `δ_{r,s} ∘ f` into the *current* member —
is stage-dependent and does **not** enter availability.

## The three facts, and coverage

* `requirementDovetail` packages `avail_mono`;
* `requirementAvail_sound` recovers the payload: an available code decodes to a `q` with
  `q.chainStage ≤ s` and `StaticAdmissible q`, and `requirementAvail_carrierValid` adds that its two
  coded maps are `CarrierValid` — exactly what the firing stage needs to build the current span and
  discharge `PartialCAPIn`'s halting clause;
* `admissible_eventually_available`: every admissible `q` is available at `encode q` from stage
  `max (discovery stage) q.chainStage` on, and stays so.

Coverage is canonical: `decodeAt_encode_of_carrierValid` exhibits the *actual* decoded equality
`decodeAt d s₀ (encode q) = some q`, so persistence guarantees the same `q` — not merely some
payload — remains available. Quantifiers, precisely: each **code** fires at most once
(`DovetailAvail.fires_at_most_once`); every admissible **semantic requirement** has at least one
code that eventually fires (`admissible_eventually_fires`); uniqueness of a code for a requirement
is neither needed nor claimed.

## Proof-free data

`RequirementData` carries `(i, r, k, f, g)` and nothing else. It must be `Primcodable`, to be the
value of a staged approximation and the argument of the guards; computational data and semantic
certification belong in separate layers; and decoder soundness (`decodeAt_carrierValid`) stays
inspectable as a theorem rather than buried in a structure field.

## Placement of `r ≤ s`

The clause "we may assume `r ≤ s`" enters **availability**, not the enumeration: a code whose
landing is certified before stage `r` stays unavailable until `r`
(`requirementAvail_eq_false_of_lt_chainStage`) and then fires with the same decoded data
(`decode_eq_of_firesAt`). Decoding is a function of `e` alone.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

/-! ### The requirement datum -/

/-- The proof-free datum of one Lemma 3.8 requirement `R⟨i, r, k, f, g⟩`: `f : ~a_i → A_{d r}` is
coded by its image tuple `chainImage`, `g : ~a_i → A_k` by `targetImage`. No proof fields, so
that it is `Primcodable`. -/
structure RequirementData where
  /-- `i`: the index of the common domain member `A_i`. -/
  memberIdx : ℕ
  /-- `r`: the chain stage whose member `A_{d r}` receives `f`. -/
  chainStage : ℕ
  /-- `k`: the index of the extension member `A_k`. -/
  targetIdx : ℕ
  /-- `f`, as the intended images in `A_{d r}` of the recorded generators of `A_i`. -/
  chainImage : Tuple ℕ
  /-- `g`, as the intended images in `A_k` of the recorded generators of `A_i`. -/
  targetImage : Tuple ℕ

/-- The code-level packaging of requirement data. -/
private def rdEquiv : RequirementData ≃ ℕ × ℕ × ℕ × Tuple ℕ × Tuple ℕ where
  toFun q := (q.memberIdx, q.chainStage, q.targetIdx, q.chainImage, q.targetImage)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable RequirementData :=
  Primcodable.ofEquiv _ rdEquiv

namespace RequirementData

theorem primrec_memberIdx : Primrec memberIdx :=
  (Primrec.fst.comp (Primrec.of_equiv (e := rdEquiv))).of_eq fun _ ↦ rfl

theorem primrec_chainStage : Primrec chainStage :=
  ((Primrec.fst.comp Primrec.snd).comp (Primrec.of_equiv (e := rdEquiv))).of_eq fun _ ↦ rfl

theorem primrec_targetIdx : Primrec targetIdx :=
  ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp
    (Primrec.of_equiv (e := rdEquiv))).of_eq fun _ ↦ rfl

theorem primrec_chainImage : Primrec chainImage :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).comp
    (Primrec.of_equiv (e := rdEquiv))).of_eq fun _ ↦ rfl

theorem primrec_targetImage : Primrec targetImage :=
  ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).comp
    (Primrec.of_equiv (e := rdEquiv))).of_eq fun _ ↦ rfl

/-- **Canonical coverage of the code space.** Every datum has a code decoding to it, namely its own
encoding; nothing here says the code is unique, and nothing needs it to be. -/
theorem decode_encode (q : RequirementData) :
    (decode (encode q) : Option RequirementData) = some q :=
  encodek q

/-- The coded chain map `f : A_i → A_{d r}`, relative to a member-index function `d`. -/
def chainMap (d : ℕ → ℕ) (q : RequirementData) : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple (q.memberIdx, d q.chainStage, q.chainImage)

/-- The coded extension map `g : A_i → A_k`. -/
def targetMap (q : RequirementData) : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple (q.memberIdx, q.targetIdx, q.targetImage)

@[simp] theorem chainMap_domIdx (d : ℕ → ℕ) (q : RequirementData) :
    (q.chainMap d).domIdx = q.memberIdx := rfl

@[simp] theorem chainMap_codIdx (d : ℕ → ℕ) (q : RequirementData) :
    (q.chainMap d).codIdx = d q.chainStage := rfl

@[simp] theorem chainMap_rangeTuple (d : ℕ → ℕ) (q : RequirementData) :
    (q.chainMap d).rangeTuple = q.chainImage := rfl

@[simp] theorem targetMap_domIdx (q : RequirementData) : q.targetMap.domIdx = q.memberIdx := rfl

@[simp] theorem targetMap_codIdx (q : RequirementData) : q.targetMap.codIdx = q.targetIdx := rfl

@[simp] theorem targetMap_rangeTuple (q : RequirementData) :
    q.targetMap.rangeTuple = q.targetImage := rfl

end RequirementData

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace PartialAgeIn

variable (K : PartialAgeIn O L)

/-! ### The static guards -/

/-- The static fireability guards of a requirement, decidable from the recorded generators alone:
both image tuples have the width of `A_i`'s generators, and `A_k` is generated by one more
generator than `A_i` — CHMM's "`A_k` is generated by an `(n+1)`-tuple". -/
def StaticAdmissible (q : RequirementData) : Prop :=
  q.chainImage.length = (K.gens q.memberIdx).length ∧
    q.targetImage.length = (K.gens q.memberIdx).length ∧
      (K.gens q.targetIdx).length = (K.gens q.memberIdx).length + 1

instance (q : RequirementData) : Decidable (K.StaticAdmissible q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The static guards are uniformly computable in any oracle that reads the generators. -/
theorem staticAdmissible_computableIn (hOE : O ⊆ E) :
    ComputableIn E fun q : RequirementData ↦ decide (K.StaticAdmissible q) := by
  have hgens : ComputableIn E K.gens := RecursiveIn.mono hOE K.gens_computableIn
  have hlen : ComputableIn E fun q : RequirementData ↦ (K.gens q.memberIdx).length :=
    (Primrec.list_length.to_comp.computableIn (O := E)).comp
      (hgens.comp (RequirementData.primrec_memberIdx.to_comp.computableIn))
  have h₁ : ComputableIn E fun q : RequirementData ↦
      decide (q.chainImage.length = (K.gens q.memberIdx).length) :=
    ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := E)).comp
      ((Primrec.list_length.to_comp.computableIn (O := E)).comp
        (RequirementData.primrec_chainImage.to_comp.computableIn)) hlen
  have h₂ : ComputableIn E fun q : RequirementData ↦
      decide (q.targetImage.length = (K.gens q.memberIdx).length) :=
    ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := E)).comp
      ((Primrec.list_length.to_comp.computableIn (O := E)).comp
        (RequirementData.primrec_targetImage.to_comp.computableIn)) hlen
  have h₃ : ComputableIn E fun q : RequirementData ↦
      decide ((K.gens q.targetIdx).length = (K.gens q.memberIdx).length + 1) :=
    ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := E)).comp
      ((Primrec.list_length.to_comp.computableIn (O := E)).comp
        (hgens.comp (RequirementData.primrec_targetIdx.to_comp.computableIn)))
      ((Primrec.succ.to_comp.computableIn (O := E)).comp hlen)
  refine ((Primrec.and.to_comp.computableIn₂ (O := E)).comp h₁
    ((Primrec.and.to_comp.computableIn₂ (O := E)).comp h₂ h₃)).of_eq fun q ↦ ?_
  simp only [StaticAdmissible, Bool.decide_and]

/-! ### The staged landing certificate -/

/-- `x` has been enumerated into member `j` by step `s`. -/
def seenBy (j s x : ℕ) : Bool :=
  (List.range (s + 1)).any fun m ↦ decide (K.enum? j m = some x)

theorem seenBy_eq_true_iff {j s x : ℕ} :
    K.seenBy j s x = true ↔ ∃ m ≤ s, K.enum? j m = some x := by
  simp only [seenBy, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  exact ⟨fun ⟨m, hm, h⟩ ↦ ⟨m, Nat.lt_succ_iff.1 hm, h⟩,
    fun ⟨m, hm, h⟩ ↦ ⟨m, Nat.lt_succ_iff.2 hm, h⟩⟩

theorem seenBy_mono {j s t x : ℕ} (hst : s ≤ t) (h : K.seenBy j s x = true) :
    K.seenBy j t x = true := by
  obtain ⟨m, hm, hx⟩ := K.seenBy_eq_true_iff.1 h
  exact K.seenBy_eq_true_iff.2 ⟨m, le_trans hm hst, hx⟩

theorem mem_domainAt_of_seenBy {j s x : ℕ} (h : K.seenBy j s x = true) : x ∈ K.domainAt j :=
  let ⟨m, _, hx⟩ := K.seenBy_eq_true_iff.1 h
  ⟨m, hx⟩

theorem exists_seenBy {j x : ℕ} (h : x ∈ K.domainAt j) : ∃ s, K.seenBy j s x = true :=
  let ⟨m, hm⟩ := h
  ⟨m, K.seenBy_eq_true_iff.2 ⟨m, le_rfl, hm⟩⟩

/-- Every entry of `t` has been enumerated into member `j` by step `s`. -/
def landsBy (j s : ℕ) (t : Tuple ℕ) : Bool :=
  t.all (K.seenBy j s)

theorem landsBy_eq_true_iff {j s : ℕ} {t : Tuple ℕ} :
    K.landsBy j s t = true ↔ ∀ x ∈ t, K.seenBy j s x = true :=
  List.all_eq_true

theorem landsBy_mono {j s t : ℕ} {l : Tuple ℕ} (hst : s ≤ t) (h : K.landsBy j s l = true) :
    K.landsBy j t l = true :=
  K.landsBy_eq_true_iff.2 fun x hx ↦ K.seenBy_mono hst (K.landsBy_eq_true_iff.1 h x hx)

/-- **Landing soundness**: a certified tuple lies in the member's carrier. -/
theorem mem_domainAt_of_landsBy {j s : ℕ} {l : Tuple ℕ} (h : K.landsBy j s l = true) :
    ∀ x ∈ l, x ∈ K.domainAt j :=
  fun x hx ↦ K.mem_domainAt_of_seenBy (K.landsBy_eq_true_iff.1 h x hx)

/-- **Landing completeness**: a tuple in the carrier is eventually certified — a finite tuple, so
a maximum of finitely many discovery steps. -/
theorem exists_landsBy {j : ℕ} {l : Tuple ℕ} (h : ∀ x ∈ l, x ∈ K.domainAt j) :
    ∃ s, K.landsBy j s l = true := by
  induction l with
  | nil => exact ⟨0, rfl⟩
  | cons x l ih =>
    obtain ⟨s₁, hs₁⟩ := K.exists_seenBy (h x (List.mem_cons_self ..))
    obtain ⟨s₂, hs₂⟩ := ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    refine ⟨max s₁ s₂, K.landsBy_eq_true_iff.2 fun y hy ↦ ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact K.seenBy_mono (le_max_left _ _) hs₁
    · exact K.seenBy_mono (le_max_right _ _) (K.landsBy_eq_true_iff.1 hs₂ y hy)

/-- The step-bounded enumeration test is uniformly computable in any oracle reading the family. -/
theorem seenBy_computableIn (hOE : O ⊆ E) :
    ComputableIn E fun p : (ℕ × ℕ) × ℕ ↦ K.seenBy p.1.1 p.1.2 p.2 := by
  have henum : ComputableIn E fun p : ℕ × ℕ ↦ K.enum? p.1 p.2 :=
    RecursiveIn.mono hOE K.enum?_computableIn
  have hj : ComputableIn E fun r : ((ℕ × ℕ) × ℕ) × ℕ ↦ r.1.1.1 :=
    ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst)
  have hm : ComputableIn E fun r : ((ℕ × ℕ) × ℕ) × ℕ ↦ r.2 := ComputableIn.snd
  have hx : ComputableIn E fun r : ((ℕ × ℕ) × ℕ) × ℕ ↦ r.1.2 :=
    ComputableIn.snd.comp ComputableIn.fst
  have hjm : ComputableIn E fun r : ((ℕ × ℕ) × ℕ) × ℕ ↦ (r.1.1.1, r.2) :=
    ComputableIn.pair (α := ((ℕ × ℕ) × ℕ) × ℕ) (β := ℕ) (γ := ℕ)
      (f := fun r ↦ r.1.1.1) (g := fun r ↦ r.2) hj hm
  have he : ComputableIn E fun r : ((ℕ × ℕ) × ℕ) × ℕ ↦ K.enum? r.1.1.1 r.2 :=
    ComputableIn.comp (α := ((ℕ × ℕ) × ℕ) × ℕ) (β := ℕ × ℕ) (σ := Option ℕ)
      (f := fun p ↦ K.enum? p.1 p.2) (g := fun r ↦ (r.1.1.1, r.2)) henum hjm
  have hsx : ComputableIn E fun r : ((ℕ × ℕ) × ℕ) × ℕ ↦ (Option.some r.1.2 : Option ℕ) :=
    ComputableIn.comp (α := ((ℕ × ℕ) × ℕ) × ℕ) (β := ℕ) (σ := Option ℕ)
      (f := Option.some) (g := fun r ↦ r.1.2) ComputableIn.option_some hx
  have hp : ComputableIn E fun r : ((ℕ × ℕ) × ℕ) × ℕ ↦
      decide (K.enum? r.1.1.1 r.2 = Option.some r.1.2) :=
    ((Primrec.eq (α := Option ℕ)).decide.to_comp.computableIn₂ (O := E)).comp he hsx
  have hrange : ComputableIn E fun p : (ℕ × ℕ) × ℕ ↦ List.range (p.1.2 + 1) :=
    ComputableIn.comp (α := (ℕ × ℕ) × ℕ) (β := ℕ) (σ := List ℕ) (f := List.range)
      (g := fun p ↦ p.1.2 + 1) (Primrec.list_range.to_comp.computableIn (O := E))
      (ComputableIn.comp (α := (ℕ × ℕ) × ℕ) (β := ℕ) (σ := ℕ) (f := Nat.succ)
        (g := fun p ↦ p.1.2) (Primrec.succ.to_comp.computableIn (O := E))
        (ComputableIn.snd.comp ComputableIn.fst))
  exact ComputableIn.list_any (α := (ℕ × ℕ) × ℕ) (β := ℕ)
    (f := fun p ↦ List.range (p.1.2 + 1))
    (p := fun p m ↦ decide (K.enum? p.1.1 m = Option.some p.2)) hrange hp.to₂

/-- The landing certificate is uniformly computable in any oracle that reads the family. -/
theorem landsBy_computableIn (hOE : O ⊆ E) :
    ComputableIn E fun p : (ℕ × ℕ) × Tuple ℕ ↦ K.landsBy p.1.1 p.1.2 p.2 := by
  have hseen := K.seenBy_computableIn (E := E) hOE
  have hrepack : ComputableIn E fun r : ((ℕ × ℕ) × Tuple ℕ) × ℕ ↦ (r.1.1, r.2) :=
    ComputableIn.pair (α := ((ℕ × ℕ) × Tuple ℕ) × ℕ) (β := ℕ × ℕ) (γ := ℕ)
      (f := fun r ↦ r.1.1) (g := fun r ↦ r.2) (ComputableIn.fst.comp ComputableIn.fst)
      ComputableIn.snd
  have hp : ComputableIn E fun r : ((ℕ × ℕ) × Tuple ℕ) × ℕ ↦ K.seenBy r.1.1.1 r.1.1.2 r.2 :=
    ComputableIn.comp (α := ((ℕ × ℕ) × Tuple ℕ) × ℕ) (β := (ℕ × ℕ) × ℕ) (σ := Bool)
      (f := fun p ↦ K.seenBy p.1.1 p.1.2 p.2) (g := fun r ↦ (r.1.1, r.2)) hseen hrepack
  exact ComputableIn.list_all (α := (ℕ × ℕ) × Tuple ℕ) (β := ℕ) (f := fun p ↦ p.2)
    (p := fun p x ↦ K.seenBy p.1.1 p.1.2 x) ComputableIn.snd hp.to₂

variable (d : ℕ → ℕ)

/-- **The staged decoder.** At stage `s`, code `e` yields its decoded requirement exactly when both
coded maps have been certified to land: `f`'s entries in `A_{d r}`, `g`'s in `A_k`. Decoding is a
function of `e` alone; the stage only governs *whether* the datum has been certified yet. -/
def decodeAt (s e : ℕ) : Option RequirementData :=
  (decode e : Option RequirementData).bind fun q ↦
    cond (K.landsBy (d q.chainStage) s q.chainImage && K.landsBy q.targetIdx s q.targetImage)
      (some q) none

theorem decodeAt_eq_some_iff {s e : ℕ} {q : RequirementData} :
    K.decodeAt d s e = some q ↔
      (decode e : Option RequirementData) = some q ∧
        K.landsBy (d q.chainStage) s q.chainImage = true ∧
          K.landsBy q.targetIdx s q.targetImage = true := by
  unfold decodeAt
  constructor
  · intro h
    obtain ⟨q', hq', hc⟩ := Option.bind_eq_some_iff.1 h
    rcases hb : (K.landsBy (d q'.chainStage) s q'.chainImage &&
      K.landsBy q'.targetIdx s q'.targetImage) with _ | _
    · rw [hb] at hc; exact absurd hc (by simp)
    · rw [hb] at hc
      obtain rfl := Option.some.inj hc
      exact ⟨hq', Bool.and_eq_true_iff.1 hb⟩
  · rintro ⟨hq, h₁, h₂⟩
    rw [hq, Option.bind_some, h₁, h₂]
    rfl

/-- A code that does not decode is never certified. -/
theorem decodeAt_eq_none_of_decode {s e : ℕ} (h : (decode e : Option RequirementData) = none) :
    K.decodeAt d s e = none := by
  rw [decodeAt, h]; rfl

/-- The decoder reads `d` only at the decoded datum's own chain stage. -/
theorem decodeAt_congr {d' : ℕ → ℕ} {s e : ℕ} {q : RequirementData}
    (hq : (decode e : Option RequirementData) = some q) (hd : d q.chainStage = d' q.chainStage) :
    K.decodeAt d s e = K.decodeAt d' s e := by
  rw [decodeAt, decodeAt, hq, Option.bind_some, Option.bind_some, hd]

theorem decodeAt_computableIn (hOE : O ⊆ E) (hd : ComputableIn E d) :
    ComputableIn E fun p : ℕ × ℕ ↦ K.decodeAt d p.1 p.2 := by
  have hlands := K.landsBy_computableIn (E := E) hOE
  have hq : ComputableIn E fun r : ℕ × RequirementData ↦ r.2 := ComputableIn.snd
  have hs : ComputableIn E fun r : ℕ × RequirementData ↦ r.1 := ComputableIn.fst
  have hr : ComputableIn E fun r : ℕ × RequirementData ↦ r.2.chainStage :=
    ComputableIn.comp (α := ℕ × RequirementData) (β := RequirementData) (σ := ℕ)
      (f := RequirementData.chainStage) (g := fun r ↦ r.2)
      (RequirementData.primrec_chainStage.to_comp.computableIn (O := E)) hq
  have hdr : ComputableIn E fun r : ℕ × RequirementData ↦ d r.2.chainStage :=
    ComputableIn.comp (α := ℕ × RequirementData) (β := ℕ) (σ := ℕ) (f := d)
      (g := fun r ↦ r.2.chainStage) hd hr
  have hk : ComputableIn E fun r : ℕ × RequirementData ↦ r.2.targetIdx :=
    ComputableIn.comp (α := ℕ × RequirementData) (β := RequirementData) (σ := ℕ)
      (f := RequirementData.targetIdx) (g := fun r ↦ r.2)
      (RequirementData.primrec_targetIdx.to_comp.computableIn (O := E)) hq
  have hf : ComputableIn E fun r : ℕ × RequirementData ↦ r.2.chainImage :=
    ComputableIn.comp (α := ℕ × RequirementData) (β := RequirementData) (σ := Tuple ℕ)
      (f := RequirementData.chainImage) (g := fun r ↦ r.2)
      (RequirementData.primrec_chainImage.to_comp.computableIn (O := E)) hq
  have hg : ComputableIn E fun r : ℕ × RequirementData ↦ r.2.targetImage :=
    ComputableIn.comp (α := ℕ × RequirementData) (β := RequirementData) (σ := Tuple ℕ)
      (f := RequirementData.targetImage) (g := fun r ↦ r.2)
      (RequirementData.primrec_targetImage.to_comp.computableIn (O := E)) hq
  have hpack₁ : ComputableIn E fun r : ℕ × RequirementData ↦
      ((d r.2.chainStage, r.1), r.2.chainImage) :=
    ComputableIn.pair (α := ℕ × RequirementData) (β := ℕ × ℕ) (γ := Tuple ℕ)
      (f := fun r ↦ (d r.2.chainStage, r.1)) (g := fun r ↦ r.2.chainImage)
      (ComputableIn.pair (α := ℕ × RequirementData) (β := ℕ) (γ := ℕ)
        (f := fun r ↦ d r.2.chainStage) (g := fun r ↦ r.1) hdr hs) hf
  have hpack₂ : ComputableIn E fun r : ℕ × RequirementData ↦
      ((r.2.targetIdx, r.1), r.2.targetImage) :=
    ComputableIn.pair (α := ℕ × RequirementData) (β := ℕ × ℕ) (γ := Tuple ℕ)
      (f := fun r ↦ (r.2.targetIdx, r.1)) (g := fun r ↦ r.2.targetImage)
      (ComputableIn.pair (α := ℕ × RequirementData) (β := ℕ) (γ := ℕ)
        (f := fun r ↦ r.2.targetIdx) (g := fun r ↦ r.1) hk hs) hg
  have h₁ : ComputableIn E fun r : ℕ × RequirementData ↦
      K.landsBy (d r.2.chainStage) r.1 r.2.chainImage :=
    ComputableIn.comp (α := ℕ × RequirementData) (β := (ℕ × ℕ) × Tuple ℕ) (σ := Bool)
      (f := fun p ↦ K.landsBy p.1.1 p.1.2 p.2)
      (g := fun r ↦ ((d r.2.chainStage, r.1), r.2.chainImage)) hlands hpack₁
  have h₂ : ComputableIn E fun r : ℕ × RequirementData ↦
      K.landsBy r.2.targetIdx r.1 r.2.targetImage :=
    ComputableIn.comp (α := ℕ × RequirementData) (β := (ℕ × ℕ) × Tuple ℕ) (σ := Bool)
      (f := fun p ↦ K.landsBy p.1.1 p.1.2 p.2)
      (g := fun r ↦ ((r.2.targetIdx, r.1), r.2.targetImage)) hlands hpack₂
  have hguard : ComputableIn E fun r : ℕ × RequirementData ↦
      (K.landsBy (d r.2.chainStage) r.1 r.2.chainImage &&
        K.landsBy r.2.targetIdx r.1 r.2.targetImage) :=
    (Primrec.and.to_comp.computableIn₂ (O := E)).comp h₁ h₂
  have hsome : ComputableIn E fun r : ℕ × RequirementData ↦
      (Option.some r.2 : Option RequirementData) :=
    ComputableIn.comp (α := ℕ × RequirementData) (β := RequirementData)
      (σ := Option RequirementData) (f := Option.some) (g := fun r ↦ r.2)
      ComputableIn.option_some hq
  have hbody : ComputableIn E fun r : ℕ × RequirementData ↦
      cond (K.landsBy (d r.2.chainStage) r.1 r.2.chainImage &&
          K.landsBy r.2.targetIdx r.1 r.2.targetImage)
        (Option.some r.2) (Option.none : Option RequirementData) :=
    ComputableIn.cond (α := ℕ × RequirementData) (σ := Option RequirementData)
      (c := fun r ↦ K.landsBy (d r.2.chainStage) r.1 r.2.chainImage &&
        K.landsBy r.2.targetIdx r.1 r.2.targetImage)
      (f := fun r ↦ Option.some r.2) (g := fun _ ↦ Option.none) hguard hsome
      (ComputableIn.const (Option.none : Option RequirementData))
  have h := ComputableIn.bind_decode (α := ℕ) (β := RequirementData) (σ := RequirementData)
    (O := E) (f := fun s q ↦ cond (K.landsBy (d q.chainStage) s q.chainImage &&
      K.landsBy q.targetIdx s q.targetImage) (Option.some q) Option.none) hbody.to₂
  unfold decodeAt
  exact h

/-! `decodeAt` is sealed here. Unfolding it exposes `decode e` on a free code, and `whnf` then runs
away inside the numeral decoding (a heartbeat timeout even on `rfl` goals) — so every later use goes
through `decodeAt_eq_some_iff`, `decodeAt_eq_none_of_decode` and `decodeAt_congr`. -/
attribute [irreducible] decodeAt

/-- **Decoding is a function of the code alone.** -/
theorem decode_eq_of_decodeAt {s e : ℕ} {q : RequirementData} (h : K.decodeAt d s e = some q) :
    (decode e : Option RequirementData) = some q :=
  ((K.decodeAt_eq_some_iff d).1 h).1

/-- **Persistence**: a certified datum stays certified. This is the fact `StagedPartialIn.monotone`
records, and it holds because everything the decoder inspects is fixed with the code. -/
theorem decodeAt_mono {s t e : ℕ} {q : RequirementData} (hst : s ≤ t)
    (h : K.decodeAt d s e = some q) : K.decodeAt d t e = some q := by
  obtain ⟨hq, h₁, h₂⟩ := (K.decodeAt_eq_some_iff d).1 h
  exact (K.decodeAt_eq_some_iff d).2 ⟨hq, K.landsBy_mono hst h₁, K.landsBy_mono hst h₂⟩

/-- **Decoder soundness**: a decoded datum's coded maps land in their intended members — `f` in
`A_{d r}`, `g` in `A_k`. Exposed as a theorem, not stored in the datum. -/
theorem decodeAt_carrierValid {s e : ℕ} {q : RequirementData} (h : K.decodeAt d s e = some q) :
    K.CarrierValid (q.chainMap d) ∧ K.CarrierValid q.targetMap := by
  obtain ⟨-, h₁, h₂⟩ := (K.decodeAt_eq_some_iff d).1 h
  exact ⟨K.mem_domainAt_of_landsBy h₁, K.mem_domainAt_of_landsBy h₂⟩

/-- **Decoder completeness**: a code whose decoded maps land is eventually certified, to the same
datum. -/
theorem exists_decodeAt_eq_some {e : ℕ} {q : RequirementData}
    (hq : (decode e : Option RequirementData) = some q) (h₁ : K.CarrierValid (q.chainMap d))
    (h₂ : K.CarrierValid q.targetMap) : ∃ s, K.decodeAt d s e = some q := by
  obtain ⟨s₁, hs₁⟩ := K.exists_landsBy (j := d q.chainStage) (l := q.chainImage) h₁
  obtain ⟨s₂, hs₂⟩ := K.exists_landsBy (j := q.targetIdx) (l := q.targetImage) h₂
  exact ⟨max s₁ s₂, (K.decodeAt_eq_some_iff d).2 ⟨hq, K.landsBy_mono (le_max_left _ _) hs₁,
    K.landsBy_mono (le_max_right _ _) hs₂⟩⟩

/-- **Canonical coverage.** Every datum whose maps land is certified at its own encoding, with the
actual decoded equality — not merely some payload at some code. -/
theorem decodeAt_encode_of_carrierValid {q : RequirementData} (h₁ : K.CarrierValid (q.chainMap d))
    (h₂ : K.CarrierValid q.targetMap) : ∃ s, K.decodeAt d s (encode q) = some q :=
  K.exists_decodeAt_eq_some d (RequirementData.decode_encode q) h₁ h₂

/-! ### The semantic landing function, and the staged packaging -/

/-- The partial function the decoder approximates: a code's decoded requirement, defined exactly
when both coded maps land in their intended members. -/
def landingFun : ℕ →. RequirementData := fun e ↦
  (Part.ofOption (decode e : Option RequirementData)).bind fun q ↦
    Part.assert (K.CarrierValid (q.chainMap d) ∧ K.CarrierValid q.targetMap) fun _ ↦ Part.some q

theorem mem_landingFun_iff {e : ℕ} {q : RequirementData} :
    q ∈ K.landingFun d e ↔
      (decode e : Option RequirementData) = some q ∧
        K.CarrierValid (q.chainMap d) ∧ K.CarrierValid q.targetMap := by
  simp only [landingFun, Part.mem_bind_iff, Part.mem_ofOption, Part.mem_assert_iff,
    Part.mem_some_iff]
  constructor
  · rintro ⟨q', hq', h, rfl⟩
    exact ⟨hq', h⟩
  · rintro ⟨hq, h⟩
    exact ⟨q, hq, h, rfl⟩

/-- **The decoder as a staged approximation** of `landingFun`, at any oracle that reads the family
and computes `d`. The four laws are `decodeAt_computableIn`, `decodeAt_carrierValid`,
`decodeAt_mono` and `exists_decodeAt_eq_some`. -/
def stagedDecoder (hOE : O ⊆ E) (hd : ComputableIn E d) : StagedPartialIn E (K.landingFun d) where
  approx := K.decodeAt d
  approx_computableIn := K.decodeAt_computableIn d hOE hd
  sound h := (K.mem_landingFun_iff d).2 ⟨K.decode_eq_of_decodeAt d h, K.decodeAt_carrierValid d h⟩
  monotone hst h := K.decodeAt_mono d hst h
  complete h :=
    let ⟨hq, h₁, h₂⟩ := (K.mem_landingFun_iff d).1 h
    K.exists_decodeAt_eq_some d hq h₁ h₂

@[simp] theorem stagedDecoder_approx (hOE : O ⊆ E) (hd : ComputableIn E d) :
    (K.stagedDecoder d hOE hd).approx = K.decodeAt d := rfl

/-! ### Availability -/

/-- **Availability of a code at a stage**: the decoder has certified it, its chain stage has been
reached (`r ≤ s`), and the static guards hold. No CAP call appears here, and nothing here depends
on the chain beyond `d` at the code's own chain stage. -/
def requirementAvail (s e : ℕ) : Bool :=
  match K.decodeAt d s e with
  | some q => decide (q.chainStage ≤ s ∧ K.StaticAdmissible q)
  | none => false

theorem requirementAvail_eq_true_iff {s e : ℕ} :
    K.requirementAvail d s e = true ↔
      ∃ q, K.decodeAt d s e = some q ∧ q.chainStage ≤ s ∧ K.StaticAdmissible q := by
  unfold requirementAvail
  rcases h : K.decodeAt d s e with _ | q
  · simp
  · simp only [decide_eq_true_eq, Option.some.injEq]
    exact ⟨fun hq ↦ ⟨q, rfl, hq⟩, fun ⟨q', hq', h'⟩ ↦ hq' ▸ h'⟩

/-- **`avail_sound`**: an available code decodes — at this very stage — to a datum whose chain stage
has been reached and whose static guards hold. -/
theorem requirementAvail_sound {s e : ℕ} (h : K.requirementAvail d s e = true) :
    ∃ q, K.decodeAt d s e = some q ∧ q.chainStage ≤ s ∧ K.StaticAdmissible q :=
  (K.requirementAvail_eq_true_iff d).1 h

/-- The landing half of soundness: the available datum's coded maps are carrier-valid, which is
what the firing stage needs to build the current span and discharge the CAP halting clause. -/
theorem requirementAvail_carrierValid {s e : ℕ} (h : K.requirementAvail d s e = true) :
    ∃ q, K.decodeAt d s e = some q ∧ K.CarrierValid (q.chainMap d) ∧ K.CarrierValid q.targetMap :=
  let ⟨q, hq, _, _⟩ := K.requirementAvail_sound d h
  ⟨q, hq, K.decodeAt_carrierValid d hq⟩

/-- **Persistence of availability**: the static guards are monotone in the stage and the decoder
persists. This is `DovetailAvail.avail_mono`. -/
theorem requirementAvail_mono {s t e : ℕ} (hst : s ≤ t) (h : K.requirementAvail d s e = true) :
    K.requirementAvail d t e = true := by
  obtain ⟨q, hq, hr, hs⟩ := K.requirementAvail_sound d h
  exact (K.requirementAvail_eq_true_iff d).2 ⟨q, K.decodeAt_mono d hst hq, le_trans hr hst, hs⟩

/-- **The `r ≤ s` gate.** A code whose datum names a chain stage not yet reached is unavailable, no
matter how early its landing was certified. -/
theorem requirementAvail_eq_false_of_lt_chainStage {s e : ℕ} {q : RequirementData}
    (hq : (decode e : Option RequirementData) = some q) (hlt : s < q.chainStage) :
    K.requirementAvail d s e = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨q', hq', hr, -⟩ := K.requirementAvail_sound d h
  have := K.decode_eq_of_decodeAt d hq'
  rw [hq] at this
  obtain rfl := Option.some.inj this
  exact absurd hr (not_le.2 hlt)

/-- **Locality in the chain.** Availability at stage `s` reads `d` only at chain stages `≤ s` — the
fact that lets a clock-stage recursion define `d (s + 1)` from availability at `s`. -/
theorem requirementAvail_local {d' : ℕ → ℕ} {s : ℕ} (hdd : ∀ r ≤ s, d r = d' r) (e : ℕ) :
    K.requirementAvail d s e = K.requirementAvail d' s e := by
  rcases hq : (decode e : Option RequirementData) with _ | q
  · rw [Bool.eq_iff_iff, K.requirementAvail_eq_true_iff, K.requirementAvail_eq_true_iff,
      K.decodeAt_eq_none_of_decode d hq, K.decodeAt_eq_none_of_decode d' hq]
  by_cases hr : q.chainStage ≤ s
  · rw [Bool.eq_iff_iff, K.requirementAvail_eq_true_iff, K.requirementAvail_eq_true_iff,
      K.decodeAt_congr d hq (hdd _ hr)]
  · rw [K.requirementAvail_eq_false_of_lt_chainStage d hq (not_le.1 hr),
      K.requirementAvail_eq_false_of_lt_chainStage d' hq (not_le.1 hr)]

theorem requirementAvail_computableIn (hOE : O ⊆ E) (hd : ComputableIn E d) :
    ComputableIn E fun p : ℕ × ℕ ↦ K.requirementAvail d p.1 p.2 := by
  have hdec := K.decodeAt_computableIn d hOE hd
  have hq : ComputableIn E fun r : (ℕ × ℕ) × RequirementData ↦ r.2 := ComputableIn.snd
  have hs : ComputableIn E fun r : (ℕ × ℕ) × RequirementData ↦ r.1.1 :=
    ComputableIn.fst.comp ComputableIn.fst
  have hr : ComputableIn E fun r : (ℕ × ℕ) × RequirementData ↦ r.2.chainStage :=
    ComputableIn.comp (α := (ℕ × ℕ) × RequirementData) (β := RequirementData) (σ := ℕ)
      (f := RequirementData.chainStage) (g := fun r ↦ r.2)
      (RequirementData.primrec_chainStage.to_comp.computableIn (O := E)) hq
  have hle : ComputableIn E fun r : (ℕ × ℕ) × RequirementData ↦
      decide (r.2.chainStage ≤ r.1.1) :=
    (Primrec.nat_le.decide.to_comp.computableIn₂ (O := E)).comp hr hs
  have hstat : ComputableIn E fun r : (ℕ × ℕ) × RequirementData ↦
      decide (K.StaticAdmissible r.2) :=
    ComputableIn.comp (α := (ℕ × ℕ) × RequirementData) (β := RequirementData) (σ := Bool)
      (f := fun q ↦ decide (K.StaticAdmissible q)) (g := fun r ↦ r.2)
      (K.staticAdmissible_computableIn hOE) hq
  have hguard : ComputableIn E fun r : (ℕ × ℕ) × RequirementData ↦
      decide (r.2.chainStage ≤ r.1.1 ∧ K.StaticAdmissible r.2) :=
    ((Primrec.and.to_comp.computableIn₂ (O := E)).comp hle hstat).of_eq fun r ↦ by
      rw [Bool.decide_and]
  refine (ComputableIn.option_casesOn (α := ℕ × ℕ) (β := RequirementData) (σ := Bool)
    (o := fun p ↦ K.decodeAt d p.1 p.2) (f := fun _ ↦ false)
    (g := fun p q ↦ decide (q.chainStage ≤ p.1 ∧ K.StaticAdmissible q)) hdec
    (ComputableIn.const false) hguard.to₂).of_eq fun p ↦ ?_
  unfold requirementAvail
  cases K.decodeAt d p.1 p.2 <;> rfl

/-! Sealed for the same reason as `decodeAt`; use `requirementAvail_eq_true_iff`. -/
attribute [irreducible] requirementAvail

/-- **The dovetailing availability datum** for the Lemma 3.8 requirements. -/
def requirementDovetail : DovetailAvail where
  avail := K.requirementAvail d
  avail_mono hst h := K.requirementAvail_mono d hst h

theorem requirementDovetail_avail :
    (K.requirementDovetail d).avail = K.requirementAvail d := rfl

/-! ### Admissibility and coverage -/

/-- **Admissibility** of a semantic requirement: the static guards, and both coded maps landing in
their intended members. This is what Lemma 3.8 must meet for *every* `q`. -/
def Admissible (q : RequirementData) : Prop :=
  K.StaticAdmissible q ∧ K.CarrierValid (q.chainMap d) ∧ K.CarrierValid q.targetMap

/-- **`admissible_eventually_available`**: an admissible requirement is available at its own
encoding from some stage on — the later of its certification stage and its chain stage — and stays
so. -/
theorem admissible_eventually_available {q : RequirementData} (h : K.Admissible d q) :
    ∃ s₀, ∀ s, s₀ ≤ s → K.requirementAvail d s (encode q) = true := by
  obtain ⟨hstat, h₁, h₂⟩ := h
  obtain ⟨s₁, hs₁⟩ := K.decodeAt_encode_of_carrierValid d h₁ h₂
  refine ⟨max s₁ q.chainStage, fun s hs ↦ (K.requirementAvail_eq_true_iff d).2
    ⟨q, K.decodeAt_mono d (le_trans (le_max_left _ _) hs) hs₁,
      le_trans (le_max_right _ _) hs, hstat⟩⟩

/-- **Coverage meets fairness**: every admissible semantic requirement has a code — its encoding —
that eventually fires. At most once per code is `DovetailAvail.fires_at_most_once`; nothing says
this is the only code decoding to `q`, and nothing needs it. -/
theorem admissible_eventually_fires {q : RequirementData} (h : K.Admissible d q) :
    ∃ s, (K.requirementDovetail d).FiresAt (encode q) s := by
  obtain ⟨s₀, hs₀⟩ := K.admissible_eventually_available d h
  have h₀ : (K.requirementDovetail d).avail s₀ (encode q) = true := hs₀ s₀ le_rfl
  exact (K.requirementDovetail d).valid_eventually_fires h₀

/-- **A firing code fires with its own decoded data**: at the firing stage the code decodes to a
datum, that datum is what the decoder certified, its chain stage has been reached, its static
guards hold, and both coded maps are carrier-valid. -/
theorem decode_eq_of_firesAt {e s : ℕ} (h : (K.requirementDovetail d).FiresAt e s) :
    ∃ q, (decode e : Option RequirementData) = some q ∧ K.decodeAt d s e = some q ∧
      q.chainStage ≤ s ∧ K.StaticAdmissible q ∧
        K.CarrierValid (q.chainMap d) ∧ K.CarrierValid q.targetMap := by
  have havail : (K.requirementDovetail d).avail s e = true :=
    (K.requirementDovetail d).avail_of_pick h
  obtain ⟨q, hq, hr, hs⟩ := K.requirementAvail_sound d havail
  exact ⟨q, K.decode_eq_of_decodeAt d hq, hq, hr, hs, K.decodeAt_carrierValid d hq⟩

end PartialAgeIn

end FirstOrder.Language
