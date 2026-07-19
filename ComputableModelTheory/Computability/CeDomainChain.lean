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

The Level-1 limit carrier is the **raw pair type** `ℕ × ℕ` (stage, code) — no
quotient is formed. Its equivalence `limEquiv` holds when both elements transport to
the maximum of their stages and agree there; on the (c.e., never claimed decidable)
limit domain it is a genuine equivalence relation, with transitivity by pushing to a
common later stage and descending along transport injectivity. The comparison is
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
private theorem limEquiv_push {p q : ℕ × ℕ} (hp : C.limMem p)
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


end CeDomainChainIn
