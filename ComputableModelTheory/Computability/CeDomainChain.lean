/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.OraclePred

/-!
# C.e. domain chains and the carrier-level direct limit (Level 1)

The carrier half of effective direct limits, language-free: a **c.e. domain chain**
is a uniformly computable sequence of enumerated domains with uniformly partial
recursive, injective, domain-preserving step maps between consecutive stages — the
steps are *arbitrary carrier embeddings, not inclusions*. `climbAux` iterates steps
as a stage-tagged partial computation; `transportTo i j` is the induced transport
from stage `i` to stage `j`, with the coherence (`transportTo_trans`), domain
preservation, and on-domain injectivity laws.

**Terminology guard:** the raw pair type `ℕ × ℕ` (stage, code) is the
**representative space**, not the extensional direct-limit carrier — its meaningful
equality is `limEquiv`, *never* Lean equality of codes. The actual carrier exists only
as a semantic quotient or, at the certified decidable level, as canonical
representatives (`normalize`); downstream structure lifting must respect `limEquiv`
invariance and may not compare codes with `=`. The equivalence `limEquiv` holds when
both elements transport to the maximum of their stages and agree there; on the (c.e.,
never claimed decidable) limit domain it is a genuine equivalence relation, with
transitivity by pushing to a common later stage and descending along transport
injectivity. The comparison is
also available as a computation: `limEquivTest` is partial recursive and halts with
the verdict on domain pairs — a *partial* decider, which is all Level 1 can offer.
Canonical (least-representative) normalization requires deciding stage-domain
membership and therefore belongs at the certified decidable level, not here.

The stage inclusions into the limit are the tagging maps `θᵢ = (i, ·)`, trivially
computable, with `θᵢ x ≈ θᵢ₊₁ (step i x)` on-domain.
-/

open Encodable Part

/-- A c.e. domain chain: uniformly enumerated stage domains with uniformly partial
recursive step maps, injective and domain-preserving on-domain. The steps are
arbitrary carrier embeddings — nothing assumes they are inclusions. -/
structure CeDomainChainIn (O : Set (ℕ →. ℕ)) where
  /-- The stage-`i` domain enumeration; stage `i`'s domain is its range. -/
  enum : ℕ → ℕ → ℕ
  /-- The enumerations are computable uniformly in the stage. -/
  enum_computableIn : ComputableIn O fun p : ℕ × ℕ ↦ enum p.1 p.2
  /-- The step map from stage `i` into stage `i + 1`. -/
  step : ℕ → ℕ →. ℕ
  /-- The steps are partial recursive uniformly in the stage. -/
  step_recursiveIn : RecursiveIn O fun p : ℕ × ℕ ↦ step p.1 p.2
  /-- On-domain, a step halts and lands in the next stage's domain. -/
  step_mem : ∀ i x, x ∈ Set.range (enum i) →
    ∃ y ∈ step i x, y ∈ Set.range (enum (i + 1))
  /-- Steps are injective on domains. -/
  step_injOn : ∀ i x₁ x₂ y, x₁ ∈ Set.range (enum i) → x₂ ∈ Set.range (enum i) →
    y ∈ step i x₁ → y ∈ step i x₂ → x₁ = x₂

namespace CeDomainChainIn

variable {O : Set (ℕ →. ℕ)} (C : CeDomainChainIn O)

/-- The stage-`i` domain. -/
def domainAt (i : ℕ) : Set ℕ :=
  Set.range (C.enum i)

/-- Iterate `n` steps from a stage-tagged element. The stage tag travels with the
computation. -/
def climbAux (n : ℕ) (s : ℕ × ℕ) : Part (ℕ × ℕ) :=
  Nat.rec (Part.some s)
    (fun _ IH ↦ IH.bind fun t ↦ (C.step t.1 t.2).map fun y ↦ (t.1 + 1, y)) n

@[simp]
theorem climbAux_zero (s : ℕ × ℕ) : C.climbAux 0 s = Part.some s :=
  rfl

theorem climbAux_succ (n : ℕ) (s : ℕ × ℕ) :
    C.climbAux (n + 1) s = (C.climbAux n s).bind fun t ↦
      (C.step t.1 t.2).map fun y ↦ (t.1 + 1, y) :=
  rfl

/-- Stage tracking: after `n` steps the stage tag has advanced by exactly `n`. -/
theorem stage_of_mem_climbAux {n : ℕ} {s t : ℕ × ℕ} (h : t ∈ C.climbAux n s) :
    t.1 = s.1 + n := by
  induction n generalizing t with
  | zero =>
    rw [Part.mem_some_iff.1 h]
    rfl
  | succ m ih =>
    rw [climbAux_succ] at h
    obtain ⟨u, hu, hstep⟩ := Part.mem_bind_iff.1 h
    obtain ⟨y, -, rfl⟩ := (Part.mem_map_iff _).1 hstep
    rw [ih hu]
    rfl

/-- Additivity of climbing: `m + n` steps is `m` steps then `n` more. The coherence
engine. -/
theorem climbAux_add (m n : ℕ) (s : ℕ × ℕ) :
    C.climbAux (m + n) s = (C.climbAux m s).bind (C.climbAux n) := by
  induction n with
  | zero =>
    ext v
    simp [climbAux_zero]
  | succ k ih =>
    rw [show m + (k + 1) = (m + k) + 1 from rfl, climbAux_succ, ih, Part.bind_assoc]
    exact rfl

/-- On-domain, climbing halts, lands in the target stage's domain, and carries the
right tag. -/
theorem climbAux_dom {i x : ℕ} (n : ℕ) (hx : x ∈ C.domainAt i) :
    ∃ t ∈ C.climbAux n (i, x), t.1 = i + n ∧ t.2 ∈ C.domainAt (i + n) := by
  induction n with
  | zero => exact ⟨(i, x), Part.mem_some _, rfl, hx⟩
  | succ m ih =>
    obtain ⟨t, ht, htag, hdom⟩ := ih
    obtain ⟨y, hy, hydom⟩ := C.step_mem t.1 t.2 (htag ▸ hdom)
    refine ⟨(t.1 + 1, y), ?_, ?_, ?_⟩
    · rw [climbAux_succ]
      exact Part.mem_bind_iff.2 ⟨t, ht, (Part.mem_map_iff _).2 ⟨y, hy, rfl⟩⟩
    · show t.1 + 1 = i + (m + 1)
      omega
    · have heq : t.1 + 1 = i + (m + 1) := by omega
      rw [← heq]
      exact hydom

/-- Climbing is injective on domains: same landing value, same start. -/
theorem climbAux_injOn {i x₁ x₂ : ℕ} {n : ℕ} {t₁ t₂ : ℕ × ℕ}
    (hx₁ : x₁ ∈ C.domainAt i) (hx₂ : x₂ ∈ C.domainAt i)
    (h₁ : t₁ ∈ C.climbAux n (i, x₁)) (h₂ : t₂ ∈ C.climbAux n (i, x₂))
    (hval : t₁.2 = t₂.2) : x₁ = x₂ := by
  induction n generalizing t₁ t₂ with
  | zero =>
    rw [Part.mem_some_iff.1 h₁, Part.mem_some_iff.1 h₂] at hval
    exact hval
  | succ m ih =>
    rw [climbAux_succ] at h₁ h₂
    obtain ⟨u₁, hu₁, hs₁⟩ := Part.mem_bind_iff.1 h₁
    obtain ⟨y₁, hy₁, rfl⟩ := (Part.mem_map_iff _).1 hs₁
    obtain ⟨u₂, hu₂, hs₂⟩ := Part.mem_bind_iff.1 h₂
    obtain ⟨y₂, hy₂, rfl⟩ := (Part.mem_map_iff _).1 hs₂
    obtain ⟨t₁', ht₁', htag₁, hdom₁⟩ := C.climbAux_dom m hx₁
    obtain ⟨t₂', ht₂', htag₂, hdom₂⟩ := C.climbAux_dom m hx₂
    obtain rfl : u₁ = t₁' := Part.mem_unique hu₁ ht₁'
    obtain rfl : u₂ = t₂' := Part.mem_unique hu₂ ht₂'
    have hyval : y₁ = y₂ := hval
    have hd₁ : u₁.2 ∈ Set.range (C.enum u₁.1) := by rw [htag₁]; exact hdom₁
    have hd₂ : u₂.2 ∈ Set.range (C.enum u₁.1) := by rw [htag₁]; exact hdom₂
    have hy₂' : y₁ ∈ C.step u₁.1 u₂.2 := by
      rw [hyval, show u₁.1 = u₂.1 from by omega]
      exact hy₂
    exact ih hu₁ hu₂ (C.step_injOn u₁.1 u₁.2 u₂.2 y₁ hd₁ hd₂ hy₁ hy₂')

/-! ### Transport between stages -/

/-- Transport from stage `i` to stage `j ≥ i`: climb `j - i` steps and read the
value. -/
def transportTo (i j x : ℕ) : Part ℕ :=
  (C.climbAux (j - i) (i, x)).map Prod.snd

@[simp]
theorem transportTo_self (i x : ℕ) : C.transportTo i i x = Part.some x := by
  simp [transportTo]

/-- On-domain, transport halts and lands in the target domain. -/
theorem transportTo_dom {i x : ℕ} (j : ℕ) (hij : i ≤ j) (hx : x ∈ C.domainAt i) :
    ∃ y ∈ C.transportTo i j x, y ∈ C.domainAt j := by
  obtain ⟨t, ht, htag, hdom⟩ := C.climbAux_dom (j - i) hx
  refine ⟨t.2, (Part.mem_map_iff _).2 ⟨t, ht, rfl⟩, ?_⟩
  rwa [show i + (j - i) = j from by omega] at hdom

/-- Coherence: transporting `i → j → k` is transporting `i → k`, membership-wise. -/
theorem transportTo_trans {i j k x y z : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hy : y ∈ C.transportTo i j x) (hz : z ∈ C.transportTo j k y) :
    z ∈ C.transportTo i k x := by
  obtain ⟨t, ht, rfl⟩ := (Part.mem_map_iff _).1 hy
  obtain ⟨u, hu, rfl⟩ := (Part.mem_map_iff _).1 hz
  have htag : t.1 = j := by
    have := C.stage_of_mem_climbAux ht
    omega
  have hsplit : k - i = (j - i) + (k - j) := by omega
  refine (Part.mem_map_iff _).2 ⟨u, ?_, rfl⟩
  rw [transportTo] at *
  rw [hsplit, C.climbAux_add]
  refine Part.mem_bind_iff.2 ⟨t, ht, ?_⟩
  rw [show t = (j, t.2) from Prod.ext htag rfl]
  exact hu

/-- Transport is injective on domains. -/
theorem transportTo_injOn {i j x₁ x₂ y : ℕ} (hx₁ : x₁ ∈ C.domainAt i)
    (hx₂ : x₂ ∈ C.domainAt i) (h₁ : y ∈ C.transportTo i j x₁)
    (h₂ : y ∈ C.transportTo i j x₂) : x₁ = x₂ := by
  obtain ⟨t₁, ht₁, hv₁⟩ := (Part.mem_map_iff _).1 h₁
  obtain ⟨t₂, ht₂, hv₂⟩ := (Part.mem_map_iff _).1 h₂
  exact C.climbAux_injOn hx₁ hx₂ ht₁ ht₂ (hv₁.trans hv₂.symm)

/-- Transport is partial recursive uniformly in both stages and the value. -/
theorem transportTo_recursiveIn :
    RecursiveIn O fun q : (ℕ × ℕ) × ℕ ↦ C.transportTo q.1.1 q.1.2 q.2 := by
  have hstep : RecursiveIn₂ O fun (_ : (ℕ × ℕ) × ℕ) (t : ℕ × (ℕ × ℕ)) ↦
      (C.step t.2.1 t.2.2).map fun y ↦ (t.2.1 + 1, y) :=
    (RecursiveIn.map
      (C.step_recursiveIn.comp
        ((ComputableIn.fst.comp (ComputableIn.snd.comp ComputableIn.snd)).pair
          (ComputableIn.snd.comp (ComputableIn.snd.comp ComputableIn.snd))))
      ((((Primrec.succ.to_comp.computableIn (O := O)).comp
        (ComputableIn.fst.comp
          (ComputableIn.snd.comp (ComputableIn.snd.comp ComputableIn.fst)))).pair
        ComputableIn.snd).to₂)).to₂
  have hF : RecursiveIn O fun q : (ℕ × ℕ) × ℕ ↦
      Nat.rec (motive := fun _ ↦ Part (ℕ × ℕ)) (Part.some (q.1.1, q.2))
        (fun _ IH ↦ IH.bind fun t ↦ (C.step t.1 t.2).map fun y ↦ (t.1 + 1, y))
        (q.1.2 - q.1.1) :=
    RecursiveIn.nat_rec
      ((Primrec.nat_sub.to_comp.computableIn₂ (O := O)).comp
        (ComputableIn.snd.comp ComputableIn.fst)
        (ComputableIn.fst.comp ComputableIn.fst))
      (RecursiveIn.comp RecursiveIn.some
        ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd))
      hstep
  exact (RecursiveIn.map hF
    ((ComputableIn.snd.comp ComputableIn.snd).to₂)).of_eq fun q ↦ rfl

/-! ### The Level-1 limit carrier: raw pairs, no quotient -/

/-- Limit-domain membership for a raw (stage, code) pair. C.e., never claimed
decidable. -/
def limMem (p : ℕ × ℕ) : Prop :=
  p.2 ∈ C.domainAt p.1

/-- Limit-domain membership is r.e. in the oracle. -/
theorem limMem_rePredIn : REPredIn O fun p : ℕ × ℕ ↦ C.limMem p :=
  (REPredIn.exists_nat_of_computablePredIn
    (p := fun p n ↦ C.enum p.1 n = p.2)
    ⟨fun _ ↦ instDecidableEqNat _ _,
      ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp
        (C.enum_computableIn.comp
          ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd))
        (ComputableIn.snd.comp ComputableIn.fst)⟩).of_eq
    fun _ ↦ ⟨fun ⟨n, h⟩ ↦ ⟨n, h⟩, fun ⟨n, h⟩ ↦ ⟨n, h⟩⟩

/-- The limit equivalence on raw pairs: both transport to the maximum of their stages
and agree there. -/
def limEquiv (p q : ℕ × ℕ) : Prop :=
  ∃ z, z ∈ C.transportTo p.1 (max p.1 q.1) p.2 ∧
    z ∈ C.transportTo q.1 (max p.1 q.1) q.2

theorem limEquiv_refl (p : ℕ × ℕ) : C.limEquiv p p := by
  refine ⟨p.2, ?_, ?_⟩ <;>
    · rw [show max p.1 p.1 = p.1 from Nat.max_self p.1, transportTo_self]
      exact Part.mem_some _

theorem limEquiv_symm {p q : ℕ × ℕ} (h : C.limEquiv p q) : C.limEquiv q p := by
  obtain ⟨z, h₁, h₂⟩ := h
  exact ⟨z, by rwa [Nat.max_comm], by rwa [Nat.max_comm]⟩

/-- The common value of an equivalent pair at any later stage. -/
theorem limEquiv_push {p q : ℕ × ℕ} (hp : C.limMem p)
    (h : C.limEquiv p q) {M : ℕ} (hM : max p.1 q.1 ≤ M) :
    ∃ w, w ∈ C.transportTo p.1 M p.2 ∧ w ∈ C.transportTo q.1 M q.2 := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  have hzdom : z ∈ C.domainAt (max p.1 q.1) := by
    obtain ⟨y, hy, hydom⟩ :=
      C.transportTo_dom (max p.1 q.1) (Nat.le_max_left _ _) hp
    rwa [Part.mem_unique hz₁ hy]
  obtain ⟨w, hw, -⟩ := C.transportTo_dom M hM hzdom
  exact ⟨w, C.transportTo_trans (Nat.le_max_left _ _) hM hz₁ hw,
    C.transportTo_trans (Nat.le_max_right _ _) hM hz₂ hw⟩

/-- Transports of equivalent representatives agree at any common later stage — the
engine of every invariance statement over the chain. -/
theorem transportTo_eq_of_limEquiv {p q : ℕ × ℕ} (hp : C.limMem p)
    (h : C.limEquiv p q) {M s t : ℕ} (hpM : p.1 ≤ M) (hqM : q.1 ≤ M)
    (hs : s ∈ C.transportTo p.1 M p.2) (ht : t ∈ C.transportTo q.1 M q.2) :
    s = t := by
  obtain ⟨w, hw₁, hw₂⟩ := C.limEquiv_push hp h (Nat.max_le.2 ⟨hpM, hqM⟩)
  exact (Part.mem_unique hs hw₁).trans (Part.mem_unique hw₂ ht)

/-- Transitivity on the limit domain: push to a common later stage, then descend along
transport injectivity. -/
theorem limEquiv_trans {p q r : ℕ × ℕ} (hp : C.limMem p) (hq : C.limMem q)
    (hr : C.limMem r) (hpq : C.limEquiv p q) (hqr : C.limEquiv q r) :
    C.limEquiv p r := by
  set M := max (max p.1 q.1) (max q.1 r.1) with hM
  obtain ⟨w₁, hw₁p, hw₁q⟩ :=
    C.limEquiv_push hp hpq (Nat.le_max_left _ _)
  obtain ⟨w₂, hw₂q, hw₂r⟩ :=
    C.limEquiv_push hq hqr (Nat.le_max_right _ _)
  obtain rfl : w₁ = w₂ := Part.mem_unique hw₁q hw₂q
  -- Descend from `M` to `max p.1 r.1` along transport injectivity.
  have hm₃M : max p.1 r.1 ≤ M := by
    simp only [hM, Nat.max_le]
    omega
  obtain ⟨yp, hyp, hypdom⟩ :=
    C.transportTo_dom (max p.1 r.1) (Nat.le_max_left _ _) hp
  obtain ⟨yr, hyr, hyrdom⟩ :=
    C.transportTo_dom (max p.1 r.1) (Nat.le_max_right _ _) hr
  obtain ⟨vp, hvp, -⟩ := C.transportTo_dom M hm₃M hypdom
  obtain ⟨vr, hvr, -⟩ := C.transportTo_dom M hm₃M hyrdom
  have hvpw : vp = w₁ := Part.mem_unique
    (C.transportTo_trans (Nat.le_max_left _ _) hm₃M hyp hvp) hw₁p
  have hvrw : vr = w₁ := Part.mem_unique
    (C.transportTo_trans (Nat.le_max_right _ _) hm₃M hyr hvr) hw₂r
  have : yp = yr := C.transportTo_injOn hypdom hyrdom
    (hvpw ▸ hvp) (by rw [← hvrw] at hvpw ⊢; exact hvrw ▸ hvr)
  exact ⟨yp, hyp, this ▸ hyr⟩

/-- The comparison computation: transport both to the maximum stage and compare. A
*partial* decider — Level 1 offers nothing total. -/
def limEquivTest (p q : ℕ × ℕ) : Part Bool :=
  (C.transportTo p.1 (max p.1 q.1) p.2).bind fun z₁ ↦
    (C.transportTo q.1 (max p.1 q.1) q.2).map fun z₂ ↦ decide (z₁ = z₂)

-- `transportTo` is consumed only through its computability contract here; opacity
-- keeps the compositions comparing by congruence instead of unfolding the climb.
attribute [local irreducible] CeDomainChainIn.transportTo in
/-- The comparison is partial recursive uniformly in both pairs. -/
theorem limEquivTest_recursiveIn :
    RecursiveIn O fun r : (ℕ × ℕ) × (ℕ × ℕ) ↦ C.limEquivTest r.1 r.2 := by
  have hmax : ComputableIn O fun r : (ℕ × ℕ) × (ℕ × ℕ) ↦ max r.1.1 r.2.1 :=
    (Primrec.nat_max.to_comp.computableIn₂ (O := O)).comp
      (ComputableIn.fst.comp ComputableIn.fst)
      (ComputableIn.fst.comp ComputableIn.snd)
  have h₁ : RecursiveIn O fun r : (ℕ × ℕ) × (ℕ × ℕ) ↦
      C.transportTo r.1.1 (max r.1.1 r.2.1) r.1.2 :=
    C.transportTo_recursiveIn.comp
      (((ComputableIn.fst.comp ComputableIn.fst).pair hmax).pair
        (ComputableIn.snd.comp ComputableIn.fst))
  have h₂ : RecursiveIn O fun r : (ℕ × ℕ) × (ℕ × ℕ) ↦
      C.transportTo r.2.1 (max r.1.1 r.2.1) r.2.2 :=
    C.transportTo_recursiveIn.comp
      (((ComputableIn.fst.comp ComputableIn.snd).pair hmax).pair
        (ComputableIn.snd.comp ComputableIn.snd))
  exact RecursiveIn.bind h₁
    ((RecursiveIn.map (h₂.comp ComputableIn.fst)
      (((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp
        (ComputableIn.snd.comp ComputableIn.fst) ComputableIn.snd).to₂).to₂)

/-- On domain pairs the comparison halts with the equivalence verdict. -/
theorem limEquivTest_spec {p q : ℕ × ℕ} (hp : C.limMem p) (hq : C.limMem q) :
    ∃ b ∈ C.limEquivTest p q, (b = true ↔ C.limEquiv p q) := by
  obtain ⟨z₁, hz₁, -⟩ :=
    C.transportTo_dom (max p.1 q.1) (Nat.le_max_left _ _) hp
  obtain ⟨z₂, hz₂, -⟩ :=
    C.transportTo_dom (max p.1 q.1) (Nat.le_max_right _ _) hq
  refine ⟨decide (z₁ = z₂),
    Part.mem_bind_iff.2 ⟨z₁, hz₁, (Part.mem_map_iff _).2 ⟨z₂, hz₂, rfl⟩⟩, ?_⟩
  constructor
  · intro hb
    exact ⟨z₁, hz₁, of_decide_eq_true hb ▸ hz₂⟩
  · rintro ⟨z, hzp, hzq⟩
    rw [Part.mem_unique hz₁ hzp, Part.mem_unique hz₂ hzq]
    exact decide_eq_true rfl

/-! ### Stage maps into the limit -/

/-- The stage-`i` tagging map into the limit carrier. Data-free: pure tagging. -/
def stageInto (i x : ℕ) : ℕ × ℕ :=
  (i, x)

/-- One-step transport realizes the step value. -/
theorem step_mem_transportTo_succ {i x y : ℕ} (hy : y ∈ C.step i x) :
    y ∈ C.transportTo i (i + 1) x := by
  refine (Part.mem_map_iff _).2 ⟨(i + 1, y), ?_, rfl⟩
  rw [show i + 1 - i = 1 from by omega, climbAux_succ]
  exact Part.mem_bind_iff.2
    ⟨(i, x), by simp, (Part.mem_map_iff _).2 ⟨y, hy, rfl⟩⟩

/-- Stage compatibility: a stage element and its step image are identified in the
limit. -/
theorem stageInto_compat {i x : ℕ} (hx : x ∈ C.domainAt i) :
    ∃ y ∈ C.step i x, C.limEquiv (stageInto i x) (stageInto (i + 1) y) := by
  obtain ⟨y, hy, -⟩ := C.step_mem i x hx
  refine ⟨y, hy, y, ?_, ?_⟩
  · simp only [stageInto]
    rw [show max i (i + 1) = i + 1 from by omega]
    exact C.step_mem_transportTo_succ hy
  · simp only [stageInto]
    rw [show max i (i + 1) = i + 1 from by omega, transportTo_self]
    exact Part.mem_some _


/-! ### Certified canonical representatives

Everything below is gated on an explicit `DecidableStagesCertificate` — no
normalization exists for bare Level-1 c.e. stages, by construction. Candidates are
enumerated through `Nat.unpair`, which decodes every code totally. -/

/-- A decidable-stages certificate: a computable Boolean membership decider for every
stage domain. Supplied input; nothing recovers this from the c.e. data. -/
structure DecidableStagesCertificate (C : CeDomainChainIn O) where
  /-- The stage-domain membership decider. -/
  memB : ℕ → ℕ → Bool
  /-- The decider is computable uniformly in the stage. -/
  memB_computableIn : ComputableIn O fun p : ℕ × ℕ ↦ memB p.1 p.2
  /-- The decider decides stage-domain membership. -/
  memB_iff : ∀ i x, memB i x = true ↔ x ∈ C.domainAt i

variable {C} (cert : C.DecidableStagesCertificate)

/-- The pair a candidate code denotes. -/
private def candOf (n : ℕ) : ℕ × ℕ :=
  (n.unpair.1, n.unpair.2)

private theorem candOf_pair (q : ℕ × ℕ) : candOf (Nat.pair q.1 q.2) = q := by
  simp [candOf]

/-- The candidate test of the normalization search: code `n` denotes a valid pair
equivalent to `p`. Partial only through the comparison, which halts on every candidate
once `p` is valid. -/
private def normTest (p : ℕ × ℕ) (n : ℕ) : Part Bool :=
  bif cert.memB n.unpair.1 n.unpair.2 then C.limEquivTest p (candOf n)
  else Part.some false

private theorem normTest_dom {p : ℕ × ℕ} (hp : C.limMem p) (n : ℕ) :
    (normTest cert p n).Dom := by
  rw [normTest]
  rcases hm : cert.memB n.unpair.1 n.unpair.2 with - | -
  · exact trivial
  · obtain ⟨b, hb, -⟩ :=
      C.limEquivTest_spec hp ((cert.memB_iff n.unpair.1 n.unpair.2).1 hm)
    exact Part.dom_iff_mem.2 ⟨b, hb⟩

private theorem normTest_true_iff {p : ℕ × ℕ} (hp : C.limMem p) (n : ℕ) :
    true ∈ normTest cert p n ↔ C.limMem (candOf n) ∧ C.limEquiv p (candOf n) := by
  rw [normTest]
  rcases hm : cert.memB n.unpair.1 n.unpair.2 with - | -
  · simp only [cond_false]
    constructor
    · intro h
      exact absurd (Part.mem_some_iff.1 h).symm (by simp)
    · rintro ⟨hval, -⟩
      exact absurd ((cert.memB_iff n.unpair.1 n.unpair.2).2 hval) (by simp [hm])
  · have hqmem : C.limMem (candOf n) :=
      (cert.memB_iff n.unpair.1 n.unpair.2).1 hm
    obtain ⟨b, hb, hbiff⟩ := C.limEquivTest_spec hp hqmem
    simp only [cond_true]
    exact ⟨fun htrue ↦ ⟨hqmem, hbiff.1 (Part.mem_unique hb htrue)⟩,
      fun hh ↦ hbiff.2 hh.2 ▸ hb⟩

private theorem normTest_exists {p : ℕ × ℕ} (hp : C.limMem p) :
    ∃ n, true ∈ normTest cert p n :=
  ⟨Nat.pair p.1 p.2, (normTest_true_iff cert hp _).2
    (by rw [candOf_pair]; exact ⟨hp, C.limEquiv_refl p⟩)⟩

/-- Equivalent valid representatives have identical candidate tests — the engine of
representative-independence. -/
private theorem normTest_congr {p q : ℕ × ℕ} (hp : C.limMem p) (hq : C.limMem q)
    (h : C.limEquiv p q) : normTest cert p = normTest cert q := by
  funext n
  rw [normTest, normTest]
  rcases hm : cert.memB n.unpair.1 n.unpair.2 with - | -
  · rfl
  · have hqmem : C.limMem (candOf n) :=
      (cert.memB_iff n.unpair.1 n.unpair.2).1 hm
    obtain ⟨b₁, hb₁, hbiff₁⟩ := C.limEquivTest_spec hp hqmem
    obtain ⟨b₂, hb₂, hbiff₂⟩ := C.limEquivTest_spec hq hqmem
    simp only [cond_true]
    have hbeq : b₁ = b₂ := by
      have hiff : (b₁ = true) ↔ (b₂ = true) := by
        rw [hbiff₁, hbiff₂]
        exact ⟨fun hc ↦ C.limEquiv_trans hq hp hqmem (C.limEquiv_symm h) hc,
          fun hc ↦ C.limEquiv_trans hp hq hqmem h hc⟩
      cases b₁ <;> cases b₂ <;> simp_all
    ext v
    exact ⟨fun hv ↦ (Part.mem_unique hv hb₁) ▸ hbeq ▸ hb₂,
      fun hv ↦ (Part.mem_unique hv hb₂) ▸ hbeq ▸ hb₁⟩

/-- The normalization program: on a valid representative, search for the least code of
a valid equivalent pair; on invalid input, return the input. Total. -/
private def normProg (p : ℕ × ℕ) : Part (ℕ × ℕ) :=
  bif cert.memB p.1 p.2 then (Nat.rfind (normTest cert p)).map candOf
  else Part.some p

private theorem normProg_dom (p : ℕ × ℕ) : (normProg cert p).Dom := by
  rw [normProg]
  rcases hm : cert.memB p.1 p.2 with - | -
  · exact trivial
  · have hp := (cert.memB_iff p.1 p.2).1 hm
    obtain ⟨n, hn⟩ := normTest_exists cert hp
    have hdom : (Nat.rfind (normTest cert p)).Dom :=
      Nat.rfind_dom.2 ⟨n, hn, fun {m} _ ↦ normTest_dom cert hp m⟩
    obtain ⟨k, hk⟩ := Part.dom_iff_mem.1 hdom
    exact Part.dom_iff_mem.2 ⟨candOf k, (Part.mem_map_iff _).2 ⟨k, hk, rfl⟩⟩

/-- The canonical representative: the pair denoted by the least code of a valid pair
equivalent to the input (the input itself off the limit domain). Exists only under an
explicit decidable-stages certificate. -/
noncomputable def normalize (p : ℕ × ℕ) : ℕ × ℕ :=
  (normProg cert p).get (normProg_dom cert p)

private theorem normalize_mem (p : ℕ × ℕ) : normalize cert p ∈ normProg cert p :=
  Part.get_mem _

/-- Gate: normalization is valid and equivalent on valid representatives. -/
theorem normalize_spec {p : ℕ × ℕ} (hp : C.limMem p) :
    C.limMem (normalize cert p) ∧ C.limEquiv p (normalize cert p) := by
  have h := normalize_mem cert p
  rw [show normProg cert p = (Nat.rfind (normTest cert p)).map candOf from by
    rw [normProg, (cert.memB_iff p.1 p.2).2 hp]; rfl] at h
  obtain ⟨n, hn, heq⟩ := (Part.mem_map_iff _).1 h
  have hspec := (normTest_true_iff cert hp n).1 (Nat.rfind_spec hn)
  rw [← heq]
  exact ⟨hspec.1, hspec.2⟩

/-- Representative-independence half: equivalent valid representatives normalize
identically. -/
theorem normalize_eq_of_limEquiv {p q : ℕ × ℕ} (hp : C.limMem p) (hq : C.limMem q)
    (h : C.limEquiv p q) : normalize cert p = normalize cert q := by
  have hcongr := normTest_congr cert hp hq h
  have e₁ : normProg cert p = (Nat.rfind (normTest cert p)).map candOf := by
    rw [normProg, (cert.memB_iff p.1 p.2).2 hp]
    rfl
  have e₂ : normProg cert q = (Nat.rfind (normTest cert q)).map candOf := by
    rw [normProg, (cert.memB_iff q.1 q.2).2 hq]
    rfl
  have heq : normProg cert p = normProg cert q := by
    rw [e₁, e₂, hcongr]
  unfold normalize
  simp only [heq]

/-- Gate: for valid representatives, equal normalization is exactly limit
equivalence. -/
theorem normalize_eq_iff {p q : ℕ × ℕ} (hp : C.limMem p) (hq : C.limMem q) :
    normalize cert p = normalize cert q ↔ C.limEquiv p q := by
  constructor
  · intro h
    obtain ⟨hval_p, hequiv_p⟩ := normalize_spec cert hp
    obtain ⟨hval_q, hequiv_q⟩ := normalize_spec cert hq
    exact C.limEquiv_trans hp hval_p hq hequiv_p
      (h ▸ C.limEquiv_symm hequiv_q)
  · exact normalize_eq_of_limEquiv cert hp hq

/-- Gate: normalization is idempotent on valid representatives. -/
theorem normalize_normalize {p : ℕ × ℕ} (hp : C.limMem p) :
    normalize cert (normalize cert p) = normalize cert p := by
  obtain ⟨hval, hequiv⟩ := normalize_spec cert hp
  exact (normalize_eq_iff cert hval hp).2 (C.limEquiv_symm hequiv)

attribute [local irreducible] CeDomainChainIn.transportTo
  CeDomainChainIn.limEquivTest in
/-- The candidate test is partial recursive uniformly in the representative. -/
private theorem normTest_recursiveIn :
    RecursiveIn O fun q : (ℕ × ℕ) × ℕ ↦ normTest cert q.1 q.2 := by
  have hunpair₁ : ComputableIn O fun q : (ℕ × ℕ) × ℕ ↦ q.2.unpair.1 :=
    ComputableIn.fst.comp (ComputableIn.unpair.comp ComputableIn.snd)
  have hunpair₂ : ComputableIn O fun q : (ℕ × ℕ) × ℕ ↦ q.2.unpair.2 :=
    ComputableIn.snd.comp (ComputableIn.unpair.comp ComputableIn.snd)
  have hguard : ComputableIn O fun q : (ℕ × ℕ) × ℕ ↦
      encode (cert.memB q.2.unpair.1 q.2.unpair.2) :=
    ComputableIn.encode.comp
      (cert.memB_computableIn.comp (hunpair₁.pair hunpair₂))
  have htest : RecursiveIn₂ O fun (q : (ℕ × ℕ) × ℕ) (_ : ℕ) ↦
      C.limEquivTest q.1 (candOf q.2) :=
    ((C.limEquivTest_recursiveIn.comp
      ((ComputableIn.fst.comp ComputableIn.fst).pair
        ((hunpair₁.comp ComputableIn.fst).pair
          (hunpair₂.comp ComputableIn.fst)))) :
      RecursiveIn O fun r : ((ℕ × ℕ) × ℕ) × ℕ ↦
        C.limEquivTest r.1.1 (candOf r.1.2)).to₂
  refine (RecursiveIn.nat_casesOn_right hguard
    (ComputableIn.const (false : Bool)) htest).of_eq fun q ↦ ?_
  rcases hm : cert.memB q.2.unpair.1 q.2.unpair.2 with - | -
  · rw [normTest, hm]
    rfl
  · rw [normTest, hm]
    rfl

/-- Normalization is computable under the certificate. -/
theorem normalize_computableIn : ComputableIn O (normalize cert) := by
  have hcand : ComputableIn O fun n : ℕ ↦ candOf n :=
    (ComputableIn.fst.comp ComputableIn.unpair).pair
      (ComputableIn.snd.comp ComputableIn.unpair)
  have hRfind : RecursiveIn O fun p : ℕ × ℕ ↦
      (Nat.rfind (normTest cert p)).map candOf :=
    RecursiveIn.map (RecursiveIn.rfind (normTest_recursiveIn cert))
      ((hcand.comp ComputableIn.snd).to₂)
  have hguard : ComputableIn O fun p : ℕ × ℕ ↦ encode (cert.memB p.1 p.2) :=
    ComputableIn.encode.comp cert.memB_computableIn
  have hProg : RecursiveIn O (normProg cert) := by
    refine (RecursiveIn.nat_casesOn_right hguard ComputableIn.id
      (((hRfind.comp ComputableIn.fst) :
        RecursiveIn O fun r : (ℕ × ℕ) × ℕ ↦
          (Nat.rfind (normTest cert r.1)).map candOf).to₂)).of_eq fun p ↦ ?_
    rcases hm : cert.memB p.1 p.2 with - | -
    · rw [normProg, hm]
      rfl
    · rw [normProg, hm]
      rfl
  exact hProg.of_eq fun p ↦ (Part.some_get (normProg_dom cert p)).symm

/-- Gate: the canonical-representative domain is decidable — computably, under the
certificate. -/
theorem isCanonical_computablePredIn :
    ComputablePredIn O fun p : ℕ × ℕ ↦
      cert.memB p.1 p.2 = true ∧ normalize cert p = p := by
  have h₁ : ComputablePredIn O fun p : ℕ × ℕ ↦ cert.memB p.1 p.2 = true :=
    ⟨fun _ ↦ instDecidableEqBool _ _,
      ((Primrec.eq (α := Bool)).decide.to_comp.computableIn₂ (O := O)).comp
        cert.memB_computableIn (ComputableIn.const true)⟩
  have h₂ : ComputablePredIn O fun p : ℕ × ℕ ↦ normalize cert p = p := by
    refine ⟨fun p ↦ decidable_of_iff _ Encodable.encode_injective.eq_iff, ?_⟩
    exact (((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp
      (ComputableIn.encode.comp (normalize_computableIn cert))
      ComputableIn.encode).of_eq
      fun p ↦ decide_eq_decide.2 Encodable.encode_injective.eq_iff
  exact h₁.and h₂

/-- Gate: normalized stage injections are injective on stage domains. -/
theorem normalize_stageInto_injOn {i x₁ x₂ : ℕ} (hx₁ : x₁ ∈ C.domainAt i)
    (hx₂ : x₂ ∈ C.domainAt i)
    (h : normalize cert (stageInto i x₁) = normalize cert (stageInto i x₂)) :
    x₁ = x₂ := by
  have hequiv := (normalize_eq_iff cert (p := stageInto i x₁)
    (q := stageInto i x₂) hx₁ hx₂).1 h
  obtain ⟨z, hz₁, hz₂⟩ := hequiv
  have hmax : max i i = i := Nat.max_self i
  rw [show (stageInto i x₁).1 = i from rfl, show (stageInto i x₂).1 = i from rfl,
    hmax] at hz₁ hz₂
  have e₁ : z = x₁ := Part.mem_some_iff.1 (by rwa [transportTo_self] at hz₁)
  have e₂ : z = x₂ := Part.mem_some_iff.1 (by rwa [transportTo_self] at hz₂)
  omega

/-- Gate: normalized stage injections commute with chain transport. -/
theorem normalize_stageInto_transport {i j x y : ℕ} (hij : i ≤ j)
    (hx : x ∈ C.domainAt i) (hy : y ∈ C.transportTo i j x) :
    normalize cert (stageInto i x) = normalize cert (stageInto j y) := by
  have hydom : y ∈ C.domainAt j := by
    obtain ⟨w, hw, hwdom⟩ := C.transportTo_dom j hij hx
    rwa [Part.mem_unique hy hw]
  refine (normalize_eq_iff cert (p := stageInto i x) (q := stageInto j y)
    hx hydom).2 ⟨y, ?_, ?_⟩
  · rw [show max (stageInto i x).1 (stageInto j y).1 = j from by
      simp [stageInto]; omega]
    exact hy
  · rw [show max (stageInto i x).1 (stageInto j y).1 = j from by
      simp [stageInto]; omega]
    rw [show (stageInto j y).1 = j from rfl, transportTo_self]
    exact Part.mem_some _

end CeDomainChainIn
