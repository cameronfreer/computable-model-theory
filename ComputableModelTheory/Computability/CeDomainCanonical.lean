/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.CeDomainChain

/-!
# Canonical representatives of a c.e. domain chain, uncertified

The carrier of the effective direct limit, at Level 1 — with **no** decidable-stages certificate.
What makes that possible is choosing the representative by *least raw index* rather than by
maintaining a list of already-accepted representatives:

```
rawRep n       = (n.unpair.1, C.enum n.unpair.1 n.unpair.2)
canonicalPart p = least n with p ≡ rawRep n
Accepted n      ↔ canonicalPart (rawRep n) = n
```

`rawRep` is a *total* enumeration of valid representatives — every value it produces is in its
stage's domain by construction, and every valid pair is hit. So canonicalization is a single
unbounded search rather than a stateful recursion, and `Accepted` is a plain equation rather than a
predicate about a history.

Extensionally this is the usual "first-discovered class" construction: `Accepted n` says no earlier
raw index is equivalent to `rawRep n`. But nothing here recurses on a list, so there is no
accepted-list invariant to maintain and no induction to keep in step with the enumeration.

**The search is deliberately partial.** `limEquivTest` is undefined off valid inputs, so
`canonicalPart` uses `RecursiveIn.rfind` and not the total variant. For a valid `p` every earlier
comparison halts and raw-surjectivity supplies a successful candidate, which is
`canonicalPart_dom_of_limMem`; no exact-domain claim is made or wanted.

**No extra base witness.** `rawRep 0` is valid outright, since the chain's stage enumerations are
already total — a fact bought once, upstream, when the scheduled stages were totalized. So
`Accepted 0` comes for free, giving nonemptiness of the carrier.

**And no fallback is needed anyway.** Idempotence gives `range_canonicalRaw`: the accepted codes are
*exactly* the range of `canonicalRaw`, so that function enumerates the carrier outright — no
membership test, no default value.
-/

open Encodable Part

namespace CeDomainChainIn

variable {O : Set (ℕ →. ℕ)} (C : CeDomainChainIn O)

/-! ### A total enumeration of valid representatives -/

/-- Decode a code as a stage together with an enumeration step, and read off that stage's value.
Total, and valid by construction. -/
def rawRep (n : ℕ) : ℕ × ℕ :=
  (n.unpair.1, C.enum n.unpair.1 n.unpair.2)

@[simp] theorem rawRep_fst (n : ℕ) : (C.rawRep n).1 = n.unpair.1 := rfl

/-- **Every raw representative is valid.** -/
theorem rawRep_limMem (n : ℕ) : C.limMem (C.rawRep n) :=
  ⟨n.unpair.2, rfl⟩

theorem rawRep_computableIn : ComputableIn O (C.rawRep) := by
  have hfst : ComputableIn O fun n : ℕ ↦ n.unpair.1 :=
    (Primrec.fst.comp Primrec.unpair).to_comp.computableIn
  have hsnd : ComputableIn O fun n : ℕ ↦ n.unpair.2 :=
    (Primrec.snd.comp Primrec.unpair).to_comp.computableIn
  exact hfst.pair (C.enum_computableIn.comp (hfst.pair hsnd))

/-- **And every valid pair is a raw representative.** This is what makes the search below succeed. -/
theorem exists_rawRep_eq {p : ℕ × ℕ} (hp : C.limMem p) : ∃ n, C.rawRep n = p := by
  obtain ⟨m, hm⟩ := hp
  refine ⟨Nat.pair p.1 m, ?_⟩
  rw [rawRep, Nat.unpair_pair, hm]

/-! ### Canonicalization by least raw index -/

/-- The least raw index equivalent to `p`. **Partial on purpose**: the comparison is undefined off
valid inputs, so this is `rfind`, not its total variant. -/
noncomputable def canonicalPart (p : ℕ × ℕ) : Part ℕ :=
  Nat.rfind fun n ↦ C.limEquivTest p (C.rawRep n)

theorem canonicalPart_recursiveIn : RecursiveIn O C.canonicalPart := by
  have hpair : ComputableIn O fun q : (ℕ × ℕ) × ℕ ↦ (q.1, C.rawRep q.2) :=
    ComputableIn.fst.pair (C.rawRep_computableIn.comp ComputableIn.snd)
  exact RecursiveIn.rfind ((C.limEquivTest_recursiveIn.comp hpair).to₂)

/-- The comparison halts on every pair of valid representatives. -/
private theorem limEquivTest_dom_of_limMem {p q : ℕ × ℕ} (hp : C.limMem p) (hq : C.limMem q) :
    (C.limEquivTest p q).Dom := by
  obtain ⟨b, hb, -⟩ := C.limEquivTest_spec hp hq
  exact Part.dom_iff_mem.2 ⟨b, hb⟩

/-- **The search succeeds on valid input.** Every earlier comparison halts because both sides are
valid, and raw-surjectivity supplies a candidate. No exact domain is claimed. -/
theorem canonicalPart_dom_of_limMem {p : ℕ × ℕ} (hp : C.limMem p) : (C.canonicalPart p).Dom := by
  obtain ⟨n₀, hn₀⟩ := C.exists_rawRep_eq hp
  have htrue : true ∈ C.limEquivTest p (C.rawRep n₀) := by
    obtain ⟨b, hb, hiff⟩ := C.limEquivTest_spec hp (C.rawRep_limMem n₀)
    rwa [hiff.2 (hn₀ ▸ C.limEquiv_refl p)] at hb
  exact Nat.rfind_dom.2 ⟨n₀, htrue, fun {m} _ ↦
    C.limEquivTest_dom_of_limMem hp (C.rawRep_limMem m)⟩

/-- A found index really is equivalent to the input. -/
theorem limEquiv_rawRep_of_mem_canonicalPart {p : ℕ × ℕ} (hp : C.limMem p) {n : ℕ}
    (hn : n ∈ C.canonicalPart p) : C.limEquiv p (C.rawRep n) := by
  obtain ⟨b, hb, hiff⟩ := C.limEquivTest_spec hp (C.rawRep_limMem n)
  exact hiff.1 (Part.mem_unique (Nat.rfind_spec hn) hb ▸ rfl)

/-- And it is the least such. -/
theorem le_of_mem_canonicalPart {p : ℕ × ℕ} {n m : ℕ} (hn : n ∈ C.canonicalPart p)
    (hm : true ∈ C.limEquivTest p (C.rawRep m)) : n ≤ m := by
  by_contra hlt
  exact absurd hm (by
    have := (Nat.rfind_min hn (Nat.lt_of_not_le hlt))
    intro hmem
    exact absurd (Part.mem_unique hmem this) (by simp))

/-! ### The canonical index of a raw code -/

/-- The canonical raw index of a raw code: total, because raw codes are valid. -/
noncomputable def canonicalRaw (n : ℕ) : ℕ :=
  (C.canonicalPart (C.rawRep n)).get (C.canonicalPart_dom_of_limMem (C.rawRep_limMem n))

theorem mem_canonicalPart_canonicalRaw (n : ℕ) :
    C.canonicalRaw n ∈ C.canonicalPart (C.rawRep n) :=
  Part.get_mem _

/-- **The canonical index never increases the code.** -/
theorem canonicalRaw_le (n : ℕ) : C.canonicalRaw n ≤ n := by
  refine C.le_of_mem_canonicalPart (C.mem_canonicalPart_canonicalRaw n) ?_
  obtain ⟨b, hb, hiff⟩ := C.limEquivTest_spec (C.rawRep_limMem n) (C.rawRep_limMem n)
  rwa [hiff.2 (C.limEquiv_refl _)] at hb

/-- **Canonicalizing does not change the class.** -/
theorem limEquiv_canonicalRaw (n : ℕ) :
    C.limEquiv (C.rawRep n) (C.rawRep (C.canonicalRaw n)) :=
  C.limEquiv_rawRep_of_mem_canonicalPart (C.rawRep_limMem n) (C.mem_canonicalPart_canonicalRaw n)

/-- Equivalent raw codes canonicalize to the same index — the fact everything below rests on. -/
theorem canonicalRaw_congr {n m : ℕ} (h : C.limEquiv (C.rawRep n) (C.rawRep m)) :
    C.canonicalRaw n = C.canonicalRaw m := by
  have key : ∀ {a b : ℕ}, C.limEquiv (C.rawRep a) (C.rawRep b) →
      C.canonicalRaw a ≤ C.canonicalRaw b := by
    intro a b hab
    refine C.le_of_mem_canonicalPart (C.mem_canonicalPart_canonicalRaw a) ?_
    have hchain : C.limEquiv (C.rawRep a) (C.rawRep (C.canonicalRaw b)) :=
      C.limEquiv_trans (C.rawRep_limMem a) (C.rawRep_limMem b)
        (C.rawRep_limMem (C.canonicalRaw b)) hab (C.limEquiv_canonicalRaw b)
    obtain ⟨c, hc, hiff⟩ :=
      C.limEquivTest_spec (C.rawRep_limMem a) (C.rawRep_limMem (C.canonicalRaw b))
    rwa [hiff.2 hchain] at hc
  exact Nat.le_antisymm (key h) (key (C.limEquiv_symm h))

/-- **Idempotence.** -/
theorem canonicalRaw_idem (n : ℕ) : C.canonicalRaw (C.canonicalRaw n) = C.canonicalRaw n :=
  C.canonicalRaw_congr (C.limEquiv_symm (C.limEquiv_canonicalRaw n))

/-! ### Accepted codes -/

/-- A code is **accepted** when it is its own canonical index. Extensionally: no earlier raw index
is equivalent to it.

This unfolds to an equality of naturals, so `Decidable` is available for free; what this layer does
not expose is a `ComputablePredIn O` API for it. That is a statement about what has been *needed*,
not an obstruction — `canonicalRaw_computableIn` below makes acceptedness oracle-computable the
moment a consumer wants it. Unbounded search is not itself a barrier to oracle computability, since
the search is total on raw codes. -/
def Accepted (n : ℕ) : Prop :=
  C.canonicalRaw n = n

theorem accepted_canonicalRaw (n : ℕ) : C.Accepted (C.canonicalRaw n) :=
  C.canonicalRaw_idem n

/-- **Accepted codes are equivalent exactly when equal** — so accepted codes name the limit's
elements without repetition. -/
theorem accepted_limEquiv_iff {n m : ℕ} (hn : C.Accepted n) (hm : C.Accepted m) :
    C.limEquiv (C.rawRep n) (C.rawRep m) ↔ n = m := by
  constructor
  · intro h
    rw [← hn, ← hm]
    exact C.canonicalRaw_congr h
  · rintro rfl
    exact C.limEquiv_refl _

/-- **`0` is accepted**, with no extra hypothesis: the chain's stage enumerations are already total,
so `rawRep 0` is valid outright. This is the fallback a total enumeration of the limit needs, and it
is why the extensional limit asks for no base witness of its own. -/
theorem accepted_zero : C.Accepted 0 :=
  Nat.le_zero.1 (C.canonicalRaw_le 0)

/-- Canonicalization is computable in the oracle: the search is partial recursive and total on raw
codes, so the totalized version is computable. Unbounded search is no barrier here. -/
theorem canonicalRaw_computableIn : ComputableIn O C.canonicalRaw :=
  ((C.canonicalPart_recursiveIn.comp C.rawRep_computableIn).computableIn_get
    fun n ↦ C.canonicalPart_dom_of_limMem (C.rawRep_limMem n)).of_eq fun _ ↦ rfl

/-- **The accepted codes are exactly the range of canonicalization.** So an enumeration of the
limit's carrier is `canonicalRaw` itself — no membership test and no fallback value. -/
theorem range_canonicalRaw : Set.range C.canonicalRaw = {n | C.Accepted n} := by
  ext n
  constructor
  · rintro ⟨m, rfl⟩
    exact C.accepted_canonicalRaw m
  · intro hn
    exact ⟨n, hn⟩

/-- A found index is itself accepted: nothing earlier is equivalent to it either. -/
theorem accepted_of_mem_canonicalPart {p : ℕ × ℕ} (hp : C.limMem p) {k : ℕ}
    (hk : k ∈ C.canonicalPart p) : C.Accepted k := by
  refine Nat.le_antisymm (C.canonicalRaw_le k) (C.le_of_mem_canonicalPart hk ?_)
  have hchain : C.limEquiv p (C.rawRep (C.canonicalRaw k)) :=
    C.limEquiv_trans hp (C.rawRep_limMem k) (C.rawRep_limMem (C.canonicalRaw k))
      (C.limEquiv_rawRep_of_mem_canonicalPart hp hk) (C.limEquiv_canonicalRaw k)
  obtain ⟨b, hb, hiff⟩ := C.limEquivTest_spec hp (C.rawRep_limMem (C.canonicalRaw k))
  rwa [hiff.2 hchain] at hb

/-! ### The stage maps

The map carrying a stage element to its canonical code. Partial, for the same reason
`canonicalPart` is; total exactly where the element is in its stage. -/

/-- Send a stage element to the canonical code of its class. -/
noncomputable def stageIntoPart (i x : ℕ) : Part ℕ :=
  C.canonicalPart (i, x)

theorem stageIntoPart_recursiveIn :
    RecursiveIn O fun p : ℕ × ℕ ↦ C.stageIntoPart p.1 p.2 :=
  C.canonicalPart_recursiveIn.of_eq fun _ ↦ rfl

theorem stageIntoPart_dom {i x : ℕ} (hx : x ∈ C.domainAt i) : (C.stageIntoPart i x).Dom :=
  C.canonicalPart_dom_of_limMem hx

/-- The value is an accepted code. -/
theorem accepted_of_mem_stageIntoPart {i x : ℕ} (hx : x ∈ C.domainAt i) {k : ℕ}
    (hk : k ∈ C.stageIntoPart i x) : C.Accepted k :=
  C.accepted_of_mem_canonicalPart (p := (i, x)) hx hk

/-- And it names the element's own class. -/
theorem limEquiv_of_mem_stageIntoPart {i x : ℕ} (hx : x ∈ C.domainAt i) {k : ℕ}
    (hk : k ∈ C.stageIntoPart i x) : C.limEquiv (i, x) (C.rawRep k) :=
  C.limEquiv_rawRep_of_mem_canonicalPart (p := (i, x)) hx hk

/-- Equivalence within a single stage is equality — the transport is the identity there. -/
theorem eq_of_limEquiv_same_stage {i x y : ℕ} (h : C.limEquiv (i, x) (i, y)) : x = y := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  rw [show max i i = i from Nat.max_self i, C.transportTo_self] at hz₁ hz₂
  have h₁ : z = x := Part.mem_some_iff.1 hz₁
  have h₂ : z = y := Part.mem_some_iff.1 hz₂
  rw [← h₁, ← h₂]

/-- **The stage maps are injective on their stage.** Immediate from accepted codes being equivalent
only when equal. -/
theorem stageIntoPart_injOn {i x y k : ℕ} (hx : x ∈ C.domainAt i) (hy : y ∈ C.domainAt i)
    (hkx : k ∈ C.stageIntoPart i x) (hky : k ∈ C.stageIntoPart i y) : x = y := by
  refine C.eq_of_limEquiv_same_stage (C.limEquiv_trans (p := (i, x)) (q := C.rawRep k)
    (r := (i, y)) hx (C.rawRep_limMem k) hy (C.limEquiv_of_mem_stageIntoPart hx hkx) ?_)
  exact C.limEquiv_symm (C.limEquiv_of_mem_stageIntoPart hy hky)

end CeDomainChainIn
