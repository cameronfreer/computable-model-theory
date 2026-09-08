/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialPotentialTransport
import ComputableModelTheory.ModelTheory.Computable.RequirementDecoder

/-!
# The recorded finite chain: stage records, invariant, transport, and selection from history

The clock-stage recursion behind Theorem 3.9's construction carries its own history. This module
is that history's data and the three things the transition needs from it, none of which may consume
the assembled chain — the chain does not exist yet while it is being built.

## Stage records

A `StageRecord` is a member index `d s` together with the potential embedding data of the connecting
map **into** it: `δ_{s-1} : A_{d(s-1)} → A_{d s}`, and the identity data on `A_{d 0}` at stage `0`.
Records are proof-free and `Primcodable`; every semantic condition lives in `ChainInvariant`:

* the head's step is the identity data on its own member;
* each step lands in its own record's member (`step.codIdx = memberIdx`);
* each step departs from the previous record's member;
* each step is an actual embedding (`PartialIsEmbedding`).

`ChainInvariant.snoc` is the one extension lemma the transition will use.

## Partial composition and finite transport

`compPart G F` composes potential data by pushing `F`'s range tuple through `applyPotentialPart G`.
It is `Part`-valued because application is. Two contracts, for two consumers:

* **the firing step** needs only `compPart_carrierValid`: if the middle indices match, `F` is
  carrier-valid and `G` is an actual embedding, then composition halts on carrier-valid data with
  the outer endpoints. Availability supplies exactly carrier validity of the scheduled candidate,
  and the chain invariant supplies actualness of the transport — nothing stronger is available at
  that point, and asking for actualness of `F` would silently restrict which requirements the
  construction processes;
* **the commuting square** needs `compPart_realizes`, which names the composite's realizer as
  `g.comp f` when both maps are actual; `compPart_partialIsEmbedding` is its existential shadow.

`transportPart stages r s` is the fold of `compPart` over the recorded steps `r+1, …, s`, starting
from the identity data on `A_{d r}` — the finite `δ_{r,s}` read off the recorded prefix. Under the
invariant it halts with an actual embedding between the right members
(`transportPart_partialIsEmbedding`), and it satisfies the two laws the transition uses:
`transportPart_self` and `transportPart_succ`. **Nothing here mentions `CeStructureChainIn`**;
identifying this transport with the assembled chain's is a later theorem, after assembly.

## Bounded selection from history

`pickFromHistory hist fired s` is the scheduler's `DovetailAvail.pick` with availability read
through the recorded history, and `pickFromHistory_eq` says it agrees with
`(K.requirementDovetail d).pick` whenever the history represents `d` on `0, …, s`. This is the
selection step of the transition, and the bridge through which scheduler agreement will later be
proved.

Everything is uniformly computable or partial recursive at any oracle reading the family, with no
hypothesis on any member-index function.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-! ### Stage records -/

/-- One recorded stage of the chain: the member index, and the potential embedding data of the
connecting map into it from the previous stage (the identity data at stage `0`). Proof-free. -/
structure StageRecord where
  /-- `d s`, the member at this stage. -/
  memberIdx : ℕ
  /-- The connecting map into this stage's member. -/
  step : PotentialEmbeddingData

/-- The code-level packaging of stage records. -/
private def srEquiv : StageRecord ≃ ℕ × PotentialEmbeddingData where
  toFun r := (r.memberIdx, r.step)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable StageRecord :=
  Primcodable.ofEquiv _ srEquiv

namespace StageRecord

theorem primrec_memberIdx : Primrec memberIdx :=
  (Primrec.fst.comp (Primrec.of_equiv (e := srEquiv))).of_eq fun _ ↦ rfl

theorem primrec_step : Primrec step :=
  (Primrec.snd.comp (Primrec.of_equiv (e := srEquiv))).of_eq fun _ ↦ rfl

/-- The named pair → record factory, the analogue of `PotentialEmbeddingData.ofTriple`. -/
def ofPair (p : ℕ × PotentialEmbeddingData) : StageRecord :=
  srEquiv.symm p

@[simp] theorem ofPair_memberIdx (p : ℕ × PotentialEmbeddingData) :
    (ofPair p).memberIdx = p.1 := rfl

@[simp] theorem ofPair_step (p : ℕ × PotentialEmbeddingData) : (ofPair p).step = p.2 := rfl

theorem primrec_ofPair : Primrec ofPair :=
  Primrec.of_equiv_symm

end StageRecord

/-- The member-index history `[d 0, …, d s]` recorded by a list of stage records. -/
def stageHistory (stages : List StageRecord) : List ℕ :=
  stages.map StageRecord.memberIdx

theorem stageHistory_getElem? (stages : List StageRecord) (s : ℕ) :
    (stageHistory stages)[s]? = (stages[s]?).map StageRecord.memberIdx :=
  List.getElem?_map ..

theorem stageHistory_computableIn : ComputableIn O stageHistory :=
  (Computable.list_map StageRecord.primrec_memberIdx.to_comp).computableIn

namespace PartialAgeIn

variable (K : PartialAgeIn O L)

/-! ### Identity data -/

/-- The identity potential embedding data on member `i`: its recorded generators to themselves. -/
def idData (i : ℕ) : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple (i, i, K.gens i)

@[simp] theorem idData_domIdx (i : ℕ) : (K.idData i).domIdx = i := rfl

@[simp] theorem idData_codIdx (i : ℕ) : (K.idData i).codIdx = i := rfl

@[simp] theorem idData_rangeTuple (i : ℕ) : (K.idData i).rangeTuple = K.gens i := rfl

/-- The identity embedding realizes the identity data. -/
theorem idData_realizes (i : ℕ) :
    K.PartialRealizes (K.idData i) (Embedding.refl L (K.memberAt i).domain) :=
  ⟨rfl, fun _ ↦ rfl⟩

theorem idData_partialIsEmbedding (i : ℕ) : K.PartialIsEmbedding (K.idData i) :=
  ⟨_, K.idData_realizes i⟩

theorem idData_computableIn (hOE : O ⊆ E) : ComputableIn E K.idData :=
  ComputableIn.encode_iff.1
    ((ComputableIn.encode.comp (ComputableIn.id.pair (ComputableIn.id.pair
      (RecursiveIn.mono hOE K.gens_computableIn)))).of_eq fun _ ↦ rfl)

/-! ### Partial composition of potential data -/

/-- **Partial composition**: push `F`'s range tuple through the application of `G`. `Part`-valued
because application is. The guarantee the construction uses is `compPart_carrierValid`: when the
middle indices match, `F` is carrier-valid and `G` is an actual embedding, composition halts on
carrier-valid data with the outer endpoints — no actualness of `F`, and no generator-width equation
for `F`, is needed. No exact-domain claim is made. -/
noncomputable def compPart (G F : PotentialEmbeddingData) : Part PotentialEmbeddingData :=
  (listMapPart (K.applyPotentialPart G) F.rangeTuple).map fun v ↦
    PotentialEmbeddingData.ofTriple (F.domIdx, G.codIdx, v)

theorem compPart_recursiveIn :
    RecursiveIn O fun p : PotentialEmbeddingData × PotentialEmbeddingData ↦
      K.compPart p.1 p.2 := by
  have hmap : RecursiveIn O fun p : PotentialEmbeddingData × PotentialEmbeddingData ↦
      listMapPart (K.applyPotentialPart p.1) p.2.rangeTuple :=
    RecursiveIn₂.comp (α := PotentialEmbeddingData × PotentialEmbeddingData)
      (β := PotentialEmbeddingData) (γ := Tuple ℕ) (σ := Tuple ℕ)
      (f := fun G l ↦ listMapPart (K.applyPotentialPart G) l) (g := fun p ↦ p.1)
      (h := fun p ↦ p.2.rangeTuple)
      (RecursiveIn.listMapPart₂ (g := K.applyPotentialPart) K.applyPotentialPart_recursiveIn)
      ComputableIn.fst
      (ComputableIn.comp (α := PotentialEmbeddingData × PotentialEmbeddingData)
        (β := PotentialEmbeddingData) (σ := Tuple ℕ) (f := PotentialEmbeddingData.rangeTuple)
        (g := fun p ↦ p.2) PotentialEmbeddingData.rangeTuple_computable ComputableIn.snd)
  have hdom : ComputableIn O fun q : (PotentialEmbeddingData × PotentialEmbeddingData) × Tuple ℕ ↦
      q.1.2.domIdx :=
    ComputableIn.comp (α := (PotentialEmbeddingData × PotentialEmbeddingData) × Tuple ℕ)
      (β := PotentialEmbeddingData) (σ := ℕ) (f := PotentialEmbeddingData.domIdx)
      (g := fun q ↦ q.1.2) PotentialEmbeddingData.domIdx_computable
      (ComputableIn.snd.comp ComputableIn.fst)
  have hcod : ComputableIn O fun q : (PotentialEmbeddingData × PotentialEmbeddingData) × Tuple ℕ ↦
      q.1.1.codIdx :=
    ComputableIn.comp (α := (PotentialEmbeddingData × PotentialEmbeddingData) × Tuple ℕ)
      (β := PotentialEmbeddingData) (σ := ℕ) (f := PotentialEmbeddingData.codIdx)
      (g := fun q ↦ q.1.1) PotentialEmbeddingData.codIdx_computable
      (ComputableIn.fst.comp ComputableIn.fst)
  have htriple : ComputableIn O
      fun q : (PotentialEmbeddingData × PotentialEmbeddingData) × Tuple ℕ ↦
        ((q.1.2.domIdx, q.1.1.codIdx, q.2) : ℕ × ℕ × Tuple ℕ) :=
    ComputableIn.pair (α := (PotentialEmbeddingData × PotentialEmbeddingData) × Tuple ℕ) (β := ℕ)
      (γ := ℕ × Tuple ℕ) (f := fun q ↦ q.1.2.domIdx) (g := fun q ↦ (q.1.1.codIdx, q.2)) hdom
      (ComputableIn.pair (α := (PotentialEmbeddingData × PotentialEmbeddingData) × Tuple ℕ)
        (β := ℕ) (γ := Tuple ℕ) (f := fun q ↦ q.1.1.codIdx) (g := fun q ↦ q.2) hcod
        ComputableIn.snd)
  have hpack : ComputableIn O
      fun q : (PotentialEmbeddingData × PotentialEmbeddingData) × Tuple ℕ ↦
        PotentialEmbeddingData.ofTriple (q.1.2.domIdx, q.1.1.codIdx, q.2) :=
    ComputableIn.encode_iff.1 ((ComputableIn.encode.comp htriple).of_eq fun _ ↦ rfl)
  exact RecursiveIn.map hmap hpack.to₂

/-- **The composite's realizer is the composite of the realizers.** Stated on `ofTriple` data so
the middle member is shared syntactically; the composite's range tuple is exhibited. -/
theorem compPart_realizes {c d e : ℕ} {w v : Tuple ℕ}
    {f : (K.memberAt c).domain ↪[L] (K.memberAt d).domain}
    {g : (K.memberAt d).domain ↪[L] (K.memberAt e).domain}
    (hf : K.PartialRealizes (PotentialEmbeddingData.ofTriple (c, d, w)) f)
    (hg : K.PartialRealizes (PotentialEmbeddingData.ofTriple (d, e, v)) g) :
    ∃ v' : Tuple ℕ,
      K.compPart (PotentialEmbeddingData.ofTriple (d, e, v))
          (PotentialEmbeddingData.ofTriple (c, d, w)) =
        Part.some (PotentialEmbeddingData.ofTriple (c, e, v')) ∧
      K.PartialRealizes (PotentialEmbeddingData.ofTriple (c, e, v')) (g.comp f) := by
  obtain ⟨hlen, hcoord⟩ : ∃ hlen : (K.gens c).length = w.length,
      ∀ k : Fin (K.gens c).length,
        ((f (K.gensView c k) : (K.memberAt d).domain) : ℕ) = w.get (Fin.cast hlen k) := hf
  -- the composite tuple, read off the composite realizer
  let v' : Tuple ℕ := List.ofFn fun k : Fin (K.gens c).length ↦
    ((g (f (K.gensView c k)) : (K.memberAt e).domain) : ℕ)
  have hlen' : (K.gens c).length = v'.length := (List.length_ofFn).symm
  refine ⟨v', ?_, ?_⟩
  · refine Part.eq_some_iff.2 ((Part.mem_map_iff _).2 ⟨v', ?_, rfl⟩)
    change v' ∈ listMapPart (K.applyPotentialPart (PotentialEmbeddingData.ofTriple (d, e, v))) w
    refine (mem_listMapPart_iff).2 ((List.forall₂_iff_get).2
      ⟨by rw [← hlen, hlen'], fun i h₁ h₂ ↦ ?_⟩)
    have hi : i < (K.gens c).length := by omega
    have hw : w.get ⟨i, h₁⟩ = ((f (K.gensView c ⟨i, hi⟩) : (K.memberAt d).domain) : ℕ) :=
      (hcoord ⟨i, hi⟩).symm
    have hv' : v'.get ⟨i, h₂⟩ = ((g (f (K.gensView c ⟨i, hi⟩)) : (K.memberAt e).domain) : ℕ) := by
      simp [v']
    rw [hw, hv']
    exact K.applyPotentialPart_mem_realizer hg (f (K.gensView c ⟨i, hi⟩)).2
  · change ∃ hlen : (K.gens c).length = v'.length, ∀ k : Fin (K.gens c).length,
      (((g.comp f) (K.gensView c k) : (K.memberAt e).domain) : ℕ) = v'.get (Fin.cast hlen k)
    exact ⟨hlen', fun k ↦ by rw [List.get_ofFn]; rfl⟩

/-- The existential shadow, on arbitrary data: composing two actual embeddings whose middle member
agrees halts on an actual embedding between the outer members. -/
theorem compPart_partialIsEmbedding {G F : PotentialEmbeddingData} (hFG : F.codIdx = G.domIdx)
    (hF : K.PartialIsEmbedding F) (hG : K.PartialIsEmbedding G) :
    ∃ H ∈ K.compPart G F, H.domIdx = F.domIdx ∧ H.codIdx = G.codIdx ∧ K.PartialIsEmbedding H := by
  obtain ⟨c, d, w⟩ := F
  obtain ⟨d', e, v⟩ := G
  cases hFG
  obtain ⟨f, hf⟩ := hF
  obtain ⟨g, hg⟩ := hG
  have hf' : K.PartialRealizes (PotentialEmbeddingData.ofTriple (c, d, w)) f := hf
  have hg' : K.PartialRealizes (PotentialEmbeddingData.ofTriple (d, e, v)) g := hg
  obtain ⟨v', hcomp, hreal⟩ := K.compPart_realizes hf' hg'
  refine ⟨PotentialEmbeddingData.ofTriple (c, e, v'), ?_, rfl, rfl, _, hreal⟩
  change _ ∈ K.compPart (PotentialEmbeddingData.ofTriple (d, e, v))
    (PotentialEmbeddingData.ofTriple (c, d, w))
  rw [hcomp]
  exact Part.mem_some _

/-- **Halting from carrier validity alone.** With matching middle indices and an actual `G`, the
composite is defined as soon as `F`'s range lies in the middle member — actualness of `F` and its
generator width play no part. -/
theorem compPart_dom_of_carrierValid {G F : PotentialEmbeddingData} (hFG : F.codIdx = G.domIdx)
    (hF : K.CarrierValid F) (hG : K.PartialIsEmbedding G) : (K.compPart G F).Dom := by
  refine Part.dom_iff_mem.2 ?_
  have hdom : (listMapPart (K.applyPotentialPart G) F.rangeTuple).Dom :=
    listMapPart_dom_iff.2 fun x hx ↦
      K.applyPotentialPart_dom_of_partialIsEmbedding hG
        (by rw [memberAt_domain, ← hFG]; exact hF x hx)
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 hdom
  exact ⟨_, (Part.mem_map_iff _).2 ⟨v, hv, rfl⟩⟩

/-- **Membership**: every value of the composite is `ofTriple (F.domIdx, G.codIdx, v)` for a tuple
`v` obtained by applying `G` entrywise to `F`'s range. -/
theorem mem_compPart_iff {G F H : PotentialEmbeddingData} :
    H ∈ K.compPart G F ↔
      ∃ v : Tuple ℕ, List.Forall₂ (fun a b ↦ b ∈ K.applyPotentialPart G a) F.rangeTuple v ∧
        H = PotentialEmbeddingData.ofTriple (F.domIdx, G.codIdx, v) := by
  unfold compPart
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, mem_listMapPart_iff.1 hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, mem_listMapPart_iff.2 hv, rfl⟩

/-- **Landing**: with matching middle indices, a carrier-valid `F` and an actual `G`, every value of
the composite is carrier-valid. -/
theorem carrierValid_of_mem_compPart {G F H : PotentialEmbeddingData} (hFG : F.codIdx = G.domIdx)
    (hF : K.CarrierValid F) (hG : K.PartialIsEmbedding G) (hH : H ∈ K.compPart G F) :
    K.CarrierValid H := by
  obtain ⟨v, hv, rfl⟩ := (K.mem_compPart_iff).1 hH
  intro y hy
  change y ∈ K.domainAt G.codIdx
  have hy' : y ∈ v := hy
  obtain ⟨⟨i, hi⟩, rfl⟩ := List.mem_iff_get.1 hy'
  obtain ⟨hlen, hget⟩ := (List.forall₂_iff_get).1 hv
  have hmem := hget i (by omega) hi
  have hx : F.rangeTuple.get ⟨i, by omega⟩ ∈ (K.memberAt G.domIdx).domain := by
    rw [memberAt_domain, ← hFG]; exact hF _ (List.get_mem _ _)
  exact K.applyPotentialPart_mem_domainAt_of_partialIsEmbedding hG hx hmem

/-- **The composition contract the firing step uses.** Matching middle indices, a carrier-valid
candidate `F`, an actual transport `G`: the composite halts, has the outer endpoints, and is
carrier-valid. Neither actualness of `F` nor a generator-width equation for `F` enters. -/
theorem compPart_carrierValid {G F : PotentialEmbeddingData} (hFG : F.codIdx = G.domIdx)
    (hF : K.CarrierValid F) (hG : K.PartialIsEmbedding G) :
    ∃ H ∈ K.compPart G F, H.domIdx = F.domIdx ∧ H.codIdx = G.codIdx ∧ K.CarrierValid H := by
  obtain ⟨H, hH⟩ := Part.dom_iff_mem.1 (K.compPart_dom_of_carrierValid hFG hF hG)
  obtain ⟨v, -, rfl⟩ := (K.mem_compPart_iff).1 hH
  exact ⟨_, hH, rfl, rfl, K.carrierValid_of_mem_compPart hFG hF hG hH⟩

/-! ### The invariant -/

/-- **The chain invariant** on a recorded prefix: the head carries the identity data on its own
member, every step lands in its own record's member and departs from the previous record's member,
and every step is an actual embedding. -/
structure ChainInvariant (stages : List StageRecord) : Prop where
  /-- The chain has a base stage. -/
  nonempty : stages ≠ []
  /-- The base stage's step is the identity data on its member. -/
  head_step : ∀ r ∈ stages.head?, r.step = K.idData r.memberIdx
  /-- Each step lands in its own record's member. -/
  step_codIdx : ∀ r ∈ stages, r.step.codIdx = r.memberIdx
  /-- Each step departs from the previous record's member. -/
  step_domIdx : ∀ (s : ℕ) (r r' : StageRecord), stages[s]? = some r → stages[s + 1]? = some r' →
    r'.step.domIdx = r.memberIdx
  /-- Each step is an actual embedding. -/
  step_isEmbedding : ∀ r ∈ stages, K.PartialIsEmbedding r.step

/-- The base prefix: one stage, with the identity data on its member. -/
theorem chainInvariant_base (i : ℕ) : K.ChainInvariant [⟨i, K.idData i⟩] where
  nonempty := List.cons_ne_nil _ _
  head_step r hr := by
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hr
    subst hr; rfl
  step_codIdx r hr := by
    rw [List.mem_singleton] at hr; subst hr; rfl
  step_domIdx s r r' hr hr' := by
    rcases s with _ | s
    · simp at hr'
    · simp at hr
  step_isEmbedding r hr := by
    rw [List.mem_singleton] at hr; subst hr; exact K.idData_partialIsEmbedding i

variable {K} in
/-- **Extension**: appending a stage whose step is an actual embedding from the last recorded member
into the new member preserves the invariant. -/
theorem ChainInvariant.snoc {stages : List StageRecord} (h : K.ChainInvariant stages)
    {j : ℕ} {F : PotentialEmbeddingData} (hdom : ∀ r ∈ stages.getLast?, F.domIdx = r.memberIdx)
    (hcod : F.codIdx = j) (hF : K.PartialIsEmbedding F) :
    K.ChainInvariant (stages ++ [⟨j, F⟩]) where
  nonempty := List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  head_step r hr := by
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h.nonempty
    exact h.head_step r (by simpa using hr)
  step_codIdx r hr := by
    rcases List.mem_append.1 hr with hr | hr
    · exact h.step_codIdx r hr
    · rw [List.mem_singleton] at hr; subst hr; exact hcod
  step_domIdx s r r' hr hr' := by
    by_cases hs : s + 1 < stages.length
    · rw [List.getElem?_append_left hs] at hr'
      rw [List.getElem?_append_left (by omega)] at hr
      exact h.step_domIdx s r r' hr hr'
    · have hs1 : s + 1 = stages.length := by
        by_contra hne
        have : stages.length < s + 1 := by omega
        rw [List.getElem?_eq_none (by simp; omega)] at hr'
        exact absurd hr' (by simp)
      rw [List.getElem?_append_right (by omega), hs1, Nat.sub_self] at hr'
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr'
      subst hr'
      rw [List.getElem?_append_left (by omega)] at hr
      refine hdom r ?_
      rw [List.getLast?_eq_getElem?, Option.mem_def, ← hr]
      congr 1; omega
  step_isEmbedding r hr := by
    rcases List.mem_append.1 hr with hr | hr
    · exact h.step_isEmbedding r hr
    · rw [List.mem_singleton] at hr; subst hr; exact hF

/-! ### Finite transport from the recorded prefix -/

/-- The recorded steps strictly after stage `r` up to stage `s`. -/
def stepsBetween (stages : List StageRecord) (r s : ℕ) : List StageRecord :=
  (stages.drop (r + 1)).take (s - r)

theorem stepsBetween_self (stages : List StageRecord) (r : ℕ) : stepsBetween stages r r = [] := by
  simp [stepsBetween]

theorem stepsBetween_succ (stages : List StageRecord) {r s : ℕ} (hrs : r ≤ s)
    {rec : StageRecord} (hrec : stages[s + 1]? = some rec) :
    stepsBetween stages r (s + 1) = stepsBetween stages r s ++ [rec] := by
  unfold stepsBetween
  rw [show s + 1 - r = (s - r) + 1 by omega, List.take_add_one, List.getElem?_drop,
    show r + 1 + (s - r) = s + 1 by omega, hrec]
  rfl

/-- **Finite transport** `δ_{r,s}` read off the recorded prefix: the fold of `compPart` over the
steps `r+1, …, s`, from the identity data on the member recorded at `r`. -/
noncomputable def transportPart (stages : List StageRecord) (r s : ℕ) :
    Part PotentialEmbeddingData :=
  foldlPart (fun acc rec ↦ K.compPart rec.step acc)
    (K.idData ((stageHistory stages).getD r 0)) (stepsBetween stages r s)

/-- **Transport law, base**: from a stage to itself is the identity data. -/
theorem transportPart_self (stages : List StageRecord) (r : ℕ) :
    K.transportPart stages r r = Part.some (K.idData ((stageHistory stages).getD r 0)) := by
  rw [transportPart, stepsBetween_self]; rfl

/-- **Transport law, step**: one more recorded stage is one more composition. -/
theorem transportPart_succ (stages : List StageRecord) {r s : ℕ} (hrs : r ≤ s)
    {rec : StageRecord} (hrec : stages[s + 1]? = some rec) :
    K.transportPart stages r (s + 1) =
      (K.transportPart stages r s).bind fun H ↦ K.compPart rec.step H := by
  rw [transportPart, transportPart, stepsBetween_succ stages hrs hrec, foldlPart_concat]

/-- **Transport halts on an actual embedding between the right members**, under the invariant. -/
theorem transportPart_partialIsEmbedding {stages : List StageRecord}
    (h : K.ChainInvariant stages) {r s : ℕ} (hrs : r ≤ s) {rr rs : StageRecord}
    (hr : stages[r]? = some rr) (hs : stages[s]? = some rs) :
    ∃ H ∈ K.transportPart stages r s,
      H.domIdx = rr.memberIdx ∧ H.codIdx = rs.memberIdx ∧ K.PartialIsEmbedding H := by
  have hhist : (stageHistory stages).getD r 0 = rr.memberIdx := by
    rw [List.getD_eq_getElem?_getD, stageHistory_getElem?, hr]; rfl
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hrs
  clear hrs
  induction k generalizing rs with
  | zero =>
    rw [Nat.add_zero] at hs ⊢
    obtain rfl := Option.some.inj (hr.symm.trans hs)
    refine ⟨_, by rw [K.transportPart_self, hhist]; exact Part.mem_some _, rfl, rfl,
      K.idData_partialIsEmbedding _⟩
  | succ k ih =>
    have hk : (stages[r + k]?).isSome = true := by
      rw [Option.isSome_iff_ne_none]
      intro hnone
      rw [List.getElem?_eq_none_iff] at hnone
      rw [← Nat.add_assoc, List.getElem?_eq_none (by omega)] at hs
      exact absurd hs (by simp)
    obtain ⟨rk, hrk⟩ := Option.isSome_iff_exists.1 hk
    obtain ⟨H, hH, hdom, hcod, hemb⟩ := ih hrk
    rw [← Nat.add_assoc] at hs
    rw [← Nat.add_assoc, K.transportPart_succ stages (Nat.le_add_right _ _) hs]
    have hFG : H.codIdx = rs.step.domIdx := by
      rw [hcod, h.step_domIdx (r + k) rk rs hrk hs]
    obtain ⟨H', hH', hdom', hcod', hemb'⟩ :=
      K.compPart_partialIsEmbedding hFG hemb (h.step_isEmbedding rs (List.mem_of_getElem? hs))
    exact ⟨H', Part.mem_bind_iff.2 ⟨H, hH, hH'⟩, hdom'.trans hdom,
      hcod'.trans (h.step_codIdx rs (List.mem_of_getElem? hs)), hemb'⟩

theorem stepsBetween_computableIn :
    ComputableIn O fun p : (List StageRecord × ℕ) × ℕ ↦ stepsBetween p.1.1 p.1.2 p.2 := by
  have hl : ComputableIn O fun p : (List StageRecord × ℕ) × ℕ ↦ p.1.1 :=
    ComputableIn.fst.comp ComputableIn.fst
  have hr : ComputableIn O fun p : (List StageRecord × ℕ) × ℕ ↦ p.1.2 :=
    ComputableIn.snd.comp ComputableIn.fst
  have hs : ComputableIn O fun p : (List StageRecord × ℕ) × ℕ ↦ p.2 := ComputableIn.snd
  have hr1 : ComputableIn O fun p : (List StageRecord × ℕ) × ℕ ↦ p.1.2 + 1 :=
    ComputableIn.comp (α := (List StageRecord × ℕ) × ℕ) (β := ℕ) (σ := ℕ) (f := Nat.succ)
      (g := fun p ↦ p.1.2) (Primrec.succ.to_comp.computableIn (O := O)) hr
  have hsub : ComputableIn O fun p : (List StageRecord × ℕ) × ℕ ↦ p.2 - p.1.2 :=
    ComputableIn₂.comp (α := (List StageRecord × ℕ) × ℕ) (β := ℕ) (γ := ℕ) (σ := ℕ)
      (f := fun a b ↦ a - b) (g := fun p ↦ p.2) (h := fun p ↦ p.1.2)
      (Primrec.nat_sub.to_comp.computableIn₂ (O := O)) hs hr
  have hdrop : ComputableIn O fun p : (List StageRecord × ℕ) × ℕ ↦ p.1.1.drop (p.1.2 + 1) :=
    ComputableIn₂.comp (α := (List StageRecord × ℕ) × ℕ) (β := ℕ) (γ := List StageRecord)
      (σ := List StageRecord) (f := fun n l ↦ l.drop n) (g := fun p ↦ p.1.2 + 1)
      (h := fun p ↦ p.1.1) (Primrec.list_drop.to_comp.computableIn₂ (O := O)) hr1 hl
  exact ComputableIn₂.comp (α := (List StageRecord × ℕ) × ℕ) (β := ℕ) (γ := List StageRecord)
    (σ := List StageRecord) (f := fun n l ↦ l.take n) (g := fun p ↦ p.2 - p.1.2)
    (h := fun p ↦ p.1.1.drop (p.1.2 + 1)) (Primrec.list_take.to_comp.computableIn₂ (O := O)) hsub
    hdrop

/-- Finite transport is partial recursive in the recorded prefix and both stages. -/
theorem transportPart_recursiveIn (hOE : O ⊆ E) :
    RecursiveIn E fun p : (List StageRecord × ℕ) × ℕ ↦ K.transportPart p.1.1 p.1.2 p.2 := by
  have hstepF : ComputableIn E
      fun q : (((List StageRecord × ℕ) × ℕ) × PotentialEmbeddingData) × StageRecord ↦
        q.2.step :=
    ComputableIn.comp (α := (((List StageRecord × ℕ) × ℕ) × PotentialEmbeddingData) × StageRecord)
      (β := StageRecord) (σ := PotentialEmbeddingData) (f := StageRecord.step) (g := fun q ↦ q.2)
      (StageRecord.primrec_step.to_comp.computableIn (O := E)) ComputableIn.snd
  have hacc : ComputableIn E
      fun q : (((List StageRecord × ℕ) × ℕ) × PotentialEmbeddingData) × StageRecord ↦
        q.1.2 :=
    ComputableIn.snd.comp ComputableIn.fst
  have hstep : RecursiveIn₂ E fun (ds : ((List StageRecord × ℕ) × ℕ) × PotentialEmbeddingData)
      (rec : StageRecord) ↦ K.compPart rec.step ds.2 :=
    RecursiveIn.comp (α := (((List StageRecord × ℕ) × ℕ) × PotentialEmbeddingData) × StageRecord)
      (β := PotentialEmbeddingData × PotentialEmbeddingData) (σ := PotentialEmbeddingData)
      (f := fun p ↦ K.compPart p.1 p.2) (g := fun q ↦ (q.2.step, q.1.2))
      (RecursiveIn.mono hOE K.compPart_recursiveIn)
      (ComputableIn.pair
        (α := (((List StageRecord × ℕ) × ℕ) × PotentialEmbeddingData) × StageRecord)
        (β := PotentialEmbeddingData) (γ := PotentialEmbeddingData) (f := fun q ↦ q.2.step)
        (g := fun q ↦ q.1.2) hstepF hacc)
  have hhist : ComputableIn E fun p : (List StageRecord × ℕ) × ℕ ↦ stageHistory p.1.1 :=
    ComputableIn.comp (α := (List StageRecord × ℕ) × ℕ) (β := List StageRecord) (σ := List ℕ)
      (f := stageHistory) (g := fun p ↦ p.1.1) stageHistory_computableIn
      (ComputableIn.fst.comp ComputableIn.fst)
  have hgetD : ComputableIn E fun p : (List StageRecord × ℕ) × ℕ ↦
      (stageHistory p.1.1).getD p.1.2 0 :=
    ComputableIn₂.comp (α := (List StageRecord × ℕ) × ℕ) (β := List ℕ) (γ := ℕ) (σ := ℕ)
      (f := fun l n ↦ l.getD n 0) (g := fun p ↦ stageHistory p.1.1) (h := fun p ↦ p.1.2)
      ((Primrec.list_getD (0 : ℕ)).to_comp.computableIn₂ (O := E)) hhist
      (ComputableIn.snd.comp ComputableIn.fst)
  have hinit : ComputableIn E fun p : (List StageRecord × ℕ) × ℕ ↦
      K.idData ((stageHistory p.1.1).getD p.1.2 0) :=
    ComputableIn.comp (α := (List StageRecord × ℕ) × ℕ) (β := ℕ) (σ := PotentialEmbeddingData)
      (f := K.idData) (g := fun p ↦ (stageHistory p.1.1).getD p.1.2 0) (K.idData_computableIn hOE)
      hgetD
  have hfold := RecursiveIn.foldlPart₂ (O := E) (δ := (List StageRecord × ℕ) × ℕ)
    (σ := PotentialEmbeddingData) (β := StageRecord)
    (g := fun _ acc rec ↦ K.compPart rec.step acc)
    (init := fun p ↦ K.idData ((stageHistory p.1.1).getD p.1.2 0)) hstep hinit
  have hpair : ComputableIn E fun p : (List StageRecord × ℕ) × ℕ ↦
      (p, stepsBetween p.1.1 p.1.2 p.2) :=
    ComputableIn.pair (α := (List StageRecord × ℕ) × ℕ) (β := (List StageRecord × ℕ) × ℕ)
      (γ := List StageRecord) (f := fun p ↦ p) (g := fun p ↦ stepsBetween p.1.1 p.1.2 p.2)
      ComputableIn.id stepsBetween_computableIn
  have hcomp : RecursiveIn E fun p : (List StageRecord × ℕ) × ℕ ↦
      foldlPart (fun acc rec ↦ K.compPart rec.step acc)
        (K.idData ((stageHistory p.1.1).getD p.1.2 0)) (stepsBetween p.1.1 p.1.2 p.2) :=
    -- `exact hfold.comp hpair` swamps `whnf` on the unreduced pair projections; the pointwise
    -- equation closes by `rfl` instead.
    (hfold.comp hpair).of_eq fun _ ↦ rfl
  unfold transportPart
  exact hcomp

/-! ### Bounded selection from history -/

/-- **Bounded least selection from the recorded history**: the least code `≤ s` that is available
through the history and not yet fired. This is `DovetailAvail.pick` with availability read off the
history. -/
def pickFromHistory (hist fired : List ℕ) (s : ℕ) : Option ℕ :=
  (List.range (s + 1)).find? fun e ↦ K.requirementAvailFromHistory hist s e && !fired.contains e

/-- **Agreement with the scheduler**: on a history representing `d` on `0, …, s`, selection from
history is the scheduler's selection at `d`. -/
theorem pickFromHistory_eq {d : ℕ → ℕ} {hist : List ℕ} {s : ℕ}
    (hh : ∀ r ≤ s, hist[r]? = some (d r)) (fired : List ℕ) :
    K.pickFromHistory hist fired s = (K.requirementDovetail d).pick fired s := by
  unfold pickFromHistory DovetailAvail.pick
  rw [requirementDovetail_avail]
  congr 1
  funext e
  rw [K.requirementAvailFromHistory_eq d hh e]

/-- **What a successful selection certifies**: the selected code is available through the history at
this stage, has not fired, and is at most the stage. -/
theorem avail_of_pickFromHistory {hist fired : List ℕ} {s e : ℕ}
    (h : K.pickFromHistory hist fired s = some e) :
    K.requirementAvailFromHistory hist s e = true ∧ e ∉ fired ∧ e ≤ s := by
  have hmem := List.mem_range.1 (List.mem_of_find?_eq_some h)
  have hp := List.find?_some h
  rw [Bool.and_eq_true] at hp
  refine ⟨hp.1, fun hmem' ↦ ?_, Nat.lt_succ_iff.1 hmem⟩
  have : fired.contains e = true := List.contains_iff_mem.2 hmem'
  rw [this] at hp
  exact absurd hp.2 (by simp)

/-- Selection from history is uniformly computable, with no hypothesis on any member-index
function. -/
theorem pickFromHistory_computableIn (hOE : O ⊆ E) :
    ComputableIn E fun p : (List ℕ × List ℕ) × ℕ ↦ K.pickFromHistory p.1.1 p.1.2 p.2 := by
  have hrange : ComputableIn E fun p : (List ℕ × List ℕ) × ℕ ↦ List.range (p.2 + 1) :=
    ComputableIn.comp (α := (List ℕ × List ℕ) × ℕ) (β := ℕ) (σ := List ℕ) (f := List.range)
      (g := fun p ↦ p.2 + 1) (Primrec.list_range.to_comp.computableIn (O := E))
      (ComputableIn.comp (α := (List ℕ × List ℕ) × ℕ) (β := ℕ) (σ := ℕ) (f := Nat.succ)
        (g := fun p ↦ p.2) (Primrec.succ.to_comp.computableIn (O := E)) ComputableIn.snd)
  have hhist : ComputableIn E fun q : ((List ℕ × List ℕ) × ℕ) × ℕ ↦ q.1.1.1 :=
    ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst)
  have hfired : ComputableIn E fun q : ((List ℕ × List ℕ) × ℕ) × ℕ ↦ q.1.1.2 :=
    ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)
  have hs : ComputableIn E fun q : ((List ℕ × List ℕ) × ℕ) × ℕ ↦ q.1.2 :=
    ComputableIn.snd.comp ComputableIn.fst
  have he : ComputableIn E fun q : ((List ℕ × List ℕ) × ℕ) × ℕ ↦ q.2 := ComputableIn.snd
  have hpack : ComputableIn E fun q : ((List ℕ × List ℕ) × ℕ) × ℕ ↦ ((q.1.1.1, q.1.2), q.2) :=
    ComputableIn.pair (α := ((List ℕ × List ℕ) × ℕ) × ℕ) (β := List ℕ × ℕ) (γ := ℕ)
      (f := fun q ↦ (q.1.1.1, q.1.2)) (g := fun q ↦ q.2)
      (ComputableIn.pair (α := ((List ℕ × List ℕ) × ℕ) × ℕ) (β := List ℕ) (γ := ℕ)
        (f := fun q ↦ q.1.1.1) (g := fun q ↦ q.1.2) hhist hs) he
  have havail : ComputableIn E fun q : ((List ℕ × List ℕ) × ℕ) × ℕ ↦
      K.requirementAvailFromHistory q.1.1.1 q.1.2 q.2 :=
    ComputableIn.comp (α := ((List ℕ × List ℕ) × ℕ) × ℕ) (β := (List ℕ × ℕ) × ℕ) (σ := Bool)
      (f := fun p ↦ K.requirementAvailFromHistory p.1.1 p.1.2 p.2)
      (g := fun q ↦ ((q.1.1.1, q.1.2), q.2)) (K.requirementAvailFromHistory_computableIn hOE) hpack
  have hmem : ComputableIn E fun q : ((List ℕ × List ℕ) × ℕ) × ℕ ↦ decide (q.2 ∈ q.1.1.2) :=
    ComputableIn.list_mem (α := ((List ℕ × List ℕ) × ℕ) × ℕ) (β := ℕ) (f := fun q ↦ q.1.1.2)
      (g := fun q ↦ q.2) hfired he
  have hnot : ComputableIn E fun q : ((List ℕ × List ℕ) × ℕ) × ℕ ↦ !q.1.1.2.contains q.2 :=
    (ComputableIn.comp (α := ((List ℕ × List ℕ) × ℕ) × ℕ) (β := Bool) (σ := Bool) (f := not)
      (g := fun q ↦ decide (q.2 ∈ q.1.1.2)) (Primrec.not.to_comp.computableIn (O := E))
      hmem).of_eq fun q ↦ by
        congr 1
        exact (Bool.eq_iff_iff.2 (by rw [decide_eq_true_iff, List.contains_iff_mem])).symm
  have hp : ComputableIn E fun q : ((List ℕ × List ℕ) × ℕ) × ℕ ↦
      (K.requirementAvailFromHistory q.1.1.1 q.1.2 q.2 && !q.1.1.2.contains q.2) :=
    ComputableIn₂.comp (α := ((List ℕ × List ℕ) × ℕ) × ℕ) (β := Bool) (γ := Bool) (σ := Bool)
      (f := fun a b ↦ a && b) (g := fun q ↦ K.requirementAvailFromHistory q.1.1.1 q.1.2 q.2)
      (h := fun q ↦ !q.1.1.2.contains q.2) (Primrec.and.to_comp.computableIn₂ (O := E)) havail hnot
  exact ComputableIn.list_find? (α := (List ℕ × List ℕ) × ℕ) (β := ℕ)
    (f := fun p ↦ List.range (p.2 + 1))
    (p := fun p e ↦ K.requirementAvailFromHistory p.1.1 p.2 e && !p.1.2.contains e) hrange hp.to₂

end PartialAgeIn

end FirstOrder.Language
